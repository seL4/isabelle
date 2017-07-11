(*  Title:      HOL/Tools/BNF/bnf_lift.ML
    Author:     Julian Biendarra, TU Muenchen
    Author:     Dmitriy Traytel, ETH Zurich
    Copyright   2015

Lifting of BNFs through typedefs.
*)

signature BNF_LIFT =
sig
  datatype lift_bnf_option =
    Plugins_Option of Proof.context -> Plugin_Name.filter
  | No_Warn_Wits
  val copy_bnf:
    (((lift_bnf_option list * (binding option * (string * sort option)) list) *
      string) * thm option) * (binding * binding * binding) ->
      local_theory -> local_theory
  val copy_bnf_cmd:
    (((lift_bnf_option list * (binding option * (string * string option)) list) *
      string) * (Facts.ref * Token.src list) option) * (binding * binding * binding) ->
      local_theory -> local_theory
  val lift_bnf:
    ((((lift_bnf_option list * (binding option * (string * sort option)) list) *
      string) * term list option) * thm option) * (binding * binding * binding) ->
      ({context: Proof.context, prems: thm list} -> tactic) list ->
      local_theory -> local_theory
  val lift_bnf_cmd:
     ((((lift_bnf_option list * (binding option * (string * string option)) list) *
       string) * string list) * (Facts.ref * Token.src list) option) *
       (binding * binding * binding) -> local_theory -> Proof.state
end

structure BNF_Lift : BNF_LIFT =
struct

open Ctr_Sugar_Tactics
open BNF_Util
open BNF_Comp
open BNF_Def


(* typedef_bnf *)

datatype lift_bnf_option =
  Plugins_Option of Proof.context -> Plugin_Name.filter
| No_Warn_Wits;

fun typedef_bnf thm wits specs map_b rel_b pred_b opts lthy =
  let
    val plugins =
      get_first (fn Plugins_Option f => SOME (f lthy) | _ => NONE) (rev opts)
      |> the_default Plugin_Name.default_filter;
    val no_warn_wits = exists (fn No_Warn_Wits => true | _ => false) opts;

    (* extract Rep Abs F RepT AbsT *)
    val (_, [Rep_G, Abs_G, F]) = Term.strip_comb (HOLogic.dest_Trueprop (Thm.prop_of thm));
    val typ_Abs_G = dest_funT (fastype_of Abs_G);
    val RepT = fst typ_Abs_G; (* F *)
    val AbsT = snd typ_Abs_G; (* G *)
    val AbsT_name = fst (dest_Type AbsT);
    val tvs = AbsT |> dest_Type |> snd |> map (fst o dest_TVar);
    val alpha0s = map (TFree o snd) specs;

    val _ = length tvs = length alpha0s orelse
      error ("Expected " ^ string_of_int (length tvs) ^ " type argument(s) to " ^ quote AbsT_name);

    (* instantiate the new type variables newtvs to oldtvs *)
    val subst = subst_TVars (tvs ~~ alpha0s);
    val typ_subst = typ_subst_TVars (tvs ~~ alpha0s);

    val Rep_G = subst Rep_G;
    val Abs_G = subst Abs_G;
    val F = subst F;
    val RepT = typ_subst RepT;
    val AbsT = typ_subst AbsT;

    fun flatten_tyargs Ass =
      map dest_TFree alpha0s
      |> filter (fn T => exists (fn Ts => member (op =) Ts T) Ass);

    val Ds0 = filter (is_none o fst) specs |> map snd;

    (* get the bnf for RepT *)
    val ((bnf, (deads, alphas)),((_, unfolds), lthy)) =
      bnf_of_typ true Dont_Inline (Binding.qualify true AbsT_name) flatten_tyargs []
        Ds0 RepT ((empty_comp_cache, empty_unfolds), lthy);

    val set_bs =
      map (fn T => find_index (fn U => T = U) alpha0s) alphas
      |> map (the_default Binding.empty o fst o nth specs);

    val _ = (case alphas of [] => error "No live variables" | _ => ());

    val defs = #map_unfolds unfolds @ flat (#set_unfoldss unfolds) @ #rel_unfolds unfolds;

    (* number of live variables *)
    val lives = length alphas;

    (* state the three required properties *)
    val sorts = map Type.sort_of_atyp alphas;
    val names_lthy = fold Variable.declare_typ (alphas @ deads) lthy;
    val (alphas', names_lthy) = mk_TFrees' sorts names_lthy;
    val (betas, names_lthy) = mk_TFrees' sorts names_lthy;

    val map_F = mk_map_of_bnf deads alphas betas bnf;

    val (typ_fs, typ_aF) = fastype_of map_F |> strip_typeN lives ||> domain_type;
    val typ_pairs = map HOLogic.mk_prodT (alphas ~~ alphas');
    val typ_subst_pair = typ_subst_atomic (alphas ~~ typ_pairs);
    val typ_pair = typ_subst_pair RepT;

    val subst_b = subst_atomic_types (alphas ~~ betas);
    val subst_a' = subst_atomic_types (alphas ~~ alphas');
    val subst_pair = subst_atomic_types (alphas ~~ typ_pairs);
    val aF_set = F;
    val bF_set = subst_b F;
    val aF_set' = subst_a' F;
    val pairF_set = subst_pair F;
    val map_F_fst = mk_map_of_bnf deads typ_pairs alphas bnf;
    val map_F_snd = mk_map_of_bnf deads typ_pairs alphas' bnf;
    val wits_F = mk_wits_of_bnf
      (replicate (nwits_of_bnf bnf) deads)
      (replicate (nwits_of_bnf bnf) alphas) bnf;

    (* val map_closed_F = @{term "\<And>f x. x \<in> F \<Longrightarrow> map_F f x \<in> F"}; *)
    val (var_fs, names_lthy) = mk_Frees "f" typ_fs names_lthy;
    val (var_x, names_lthy) = mk_Frees "x" [typ_aF] names_lthy |>> the_single;
    val mem_x = HOLogic.mk_Trueprop (HOLogic.mk_mem (var_x, aF_set));
    val map_f = list_comb (map_F, var_fs);
    val mem_map = HOLogic.mk_Trueprop (HOLogic.mk_mem (map_f $ var_x, bF_set));
    val imp_map = Logic.mk_implies (mem_x, mem_map);
    val map_closed_F = fold_rev Logic.all var_fs (Logic.all var_x imp_map);

    (* val zip_closed_F = @{term "\<And>z. map_F fst z \<in> F \<Longrightarrow> map_F snd z \<in> F \<Longrightarrow> z \<in> F"}; *)
    val (var_zs, names_lthy) = mk_Frees "z" [typ_pair] names_lthy;
    val (pairs, names_lthy) = mk_Frees "tmp" typ_pairs names_lthy;
    val var_z = hd var_zs;
    val fsts = map (fst o Term.strip_comb o HOLogic.mk_fst) pairs;
    val snds = map (fst o Term.strip_comb o HOLogic.mk_snd) pairs;
    val map_fst = list_comb (list_comb (map_F_fst, fsts), var_zs);
    val mem_map_fst = HOLogic.mk_Trueprop (HOLogic.mk_mem (map_fst, aF_set));
    val map_snd = list_comb (list_comb (map_F_snd, snds), var_zs);
    val mem_map_snd = HOLogic.mk_Trueprop (HOLogic.mk_mem (map_snd, aF_set'));
    val mem_z = HOLogic.mk_Trueprop (HOLogic.mk_mem (var_z, pairF_set));
    val imp_zip = Logic.mk_implies (mem_map_fst, Logic.mk_implies (mem_map_snd, mem_z));
    val zip_closed_F = Logic.all var_z imp_zip;

    (* val wit_closed_F = @{term "wit_F a \<in> F"}; *)
    val (var_as, names_lthy) = mk_Frees "a" alphas names_lthy;
    val (var_bs, _) = mk_Frees "a" alphas names_lthy;
    fun binder_types_until_eq V T =
      let
        fun strip (TU as Type ("fun", [T, U])) = if V = TU then [] else T :: strip U
          | strip T = if V = T then [] else
              error ("Bad type for witness: " ^ quote (Syntax.string_of_typ lthy T));
      in strip T end;
    val Iwits = the_default wits_F (Option.map (map (`(map (fn T =>
      find_index (fn U => T = U) alphas) o binder_types_until_eq RepT o fastype_of))) wits);
    val wit_closed_Fs =
      Iwits |> map (fn (I, wit_F) =>
        let
          val vars = map (nth var_as) I;
          val wit_a = list_comb (wit_F, vars);
        in fold_rev Logic.all vars (HOLogic.mk_Trueprop (HOLogic.mk_mem (wit_a, aF_set))) end);

    val mk_wit_goals = mk_wit_goals var_as var_bs
      (mk_sets_of_bnf (replicate lives deads)  (replicate lives alphas) bnf);

    val goals = [map_closed_F, zip_closed_F] @ wit_closed_Fs @
      (case wits of NONE => [] | _ => maps mk_wit_goals Iwits);

    val lost_wits = filter_out (fn (J, _) => exists (fn (I, _) => I = J) Iwits) wits_F;
    val _ =
      if null lost_wits orelse no_warn_wits then ()
      else
        lost_wits
        |> map (Syntax.pretty_typ lthy o fastype_of o snd)
        |> Pretty.big_list
          "The following types of nonemptiness witnesses of the raw type's BNF were lost:"
        |> (fn pt => Pretty.chunks [pt,
          Pretty.para "You can specify a liftable witness (e.g., a term of one of the above types\
            \ that satisfies the typedef's invariant)\
            \ using the annotation [wits: <term>]."])
        |> Pretty.string_of
        |> warning;

    fun after_qed ([map_closed_thm] :: [zip_closed_thm] :: wit_thmss) lthy =
          let
            val (wit_closed_thms, wit_thms) =
              (case wits of
                NONE => (map the_single wit_thmss, wit_thms_of_bnf bnf)
              | _ => chop (length wit_closed_Fs) (map the_single wit_thmss))

            (*  construct map set bd rel wit *)
            (* val map_G = @{term "\<lambda>f. Abs_G o map_F f o Rep_G"}; *)
            val Abs_Gb = subst_b Abs_G;
            val map_G =
              fold_rev HOLogic.tupled_lambda var_fs
                (HOLogic.mk_comp (HOLogic.mk_comp (Abs_Gb, map_f), Rep_G));

            (* val sets_G = [@{term "set_F o Rep_G"}]; *)
            val sets_F = mk_sets_of_bnf (replicate lives deads) (replicate lives alphas) bnf;
            val sets_G = map (fn set_F => HOLogic.mk_comp (set_F, Rep_G)) sets_F;

            (* val bd_G = @{term "bd_F"}; *)
            val bd_F = mk_bd_of_bnf deads alphas bnf;
            val bd_G = bd_F;

            (* val rel_G = @{term "\<lambda>R. BNF_Def.vimage2p Rep_G Rep_G (rel_F R)"}; *)
            val rel_F = mk_rel_of_bnf deads alphas betas bnf;
            val (typ_Rs, _) = strip_typeN lives (fastype_of rel_F);

            val (var_Rs, names_lthy) = mk_Frees "R" typ_Rs lthy;
            val Rep_Gb = subst_b Rep_G;
            val rel_G = fold_rev absfree (map dest_Free var_Rs)
              (mk_vimage2p Rep_G Rep_Gb $ list_comb (rel_F, var_Rs));

            (* val pred_G = @{term "\<lambda>P. pred_F P o Rep_G"}; *)
            val pred_F = mk_pred_of_bnf deads alphas bnf;
            val (typ_Ps, _) = strip_typeN lives (fastype_of pred_F);

            val (var_Ps, names_lthy) = mk_Frees "P" typ_Ps names_lthy;
            val pred_G = fold_rev absfree (map dest_Free var_Ps)
              (HOLogic.mk_comp (list_comb (pred_F, var_Ps), Rep_G));

            (* val wits_G = [@{term "Abs_G o wit_F"}]; *)
            val (var_as, _) = mk_Frees "a" alphas names_lthy;
            val wits_G =
              map (fn (I, wit_F) =>
                let
                  val vs = map (nth var_as) I;
                in fold_rev absfree (map dest_Free vs) (Abs_G $ (list_comb (wit_F, vs))) end)
              Iwits;

            (* tactics *)
            val Rep_thm = thm RS @{thm type_definition.Rep};
            val Abs_inverse_thm = thm RS @{thm type_definition.Abs_inverse};
            val Abs_inject_thm = thm RS @{thm type_definition.Abs_inject};
            val Rep_cases_thm = thm RS @{thm type_definition.Rep_cases};
            val Rep_inverse_thm = thm RS @{thm type_definition.Rep_inverse};

            fun map_id0_tac ctxt =
              HEADGOAL (EVERY' [rtac ctxt ext,
                SELECT_GOAL (unfold_thms_tac ctxt [map_id0_of_bnf bnf, id_apply, o_apply,
                  Rep_inverse_thm]),
                rtac ctxt refl]);

            fun map_comp0_tac ctxt =
              HEADGOAL (EVERY' [rtac ctxt ext,
                SELECT_GOAL (unfold_thms_tac ctxt [map_comp0_of_bnf bnf, o_apply,
                  Rep_thm RS (map_closed_thm RS Abs_inverse_thm)]),
                rtac ctxt refl]);

            fun map_cong0_tac ctxt =
              HEADGOAL (EVERY' ([SELECT_GOAL (unfold_thms_tac ctxt [o_apply]),
                rtac ctxt (([Rep_thm RS map_closed_thm, Rep_thm RS map_closed_thm] MRS
                  Abs_inject_thm) RS iffD2),
                rtac ctxt (map_cong0_of_bnf bnf)] @ replicate lives (Goal.assume_rule_tac ctxt)));

            val set_map0s_tac =
              map (fn set_map => fn ctxt =>
                HEADGOAL (EVERY' [rtac ctxt ext,
                  SELECT_GOAL (unfold_thms_tac ctxt [set_map, o_apply,
                    Rep_thm RS (map_closed_thm RS Abs_inverse_thm)]),
                  rtac ctxt refl]))
             (set_map_of_bnf bnf);

            fun card_order_bd_tac ctxt = HEADGOAL (rtac ctxt (bd_card_order_of_bnf bnf));

            fun cinfinite_bd_tac ctxt = HEADGOAL (rtac ctxt (bd_cinfinite_of_bnf bnf));

            val set_bds_tac =
              map (fn set_bd => fn ctxt =>
                HEADGOAL (EVERY' [SELECT_GOAL (unfold_thms_tac ctxt [o_apply]), rtac ctxt set_bd]))
              (set_bd_of_bnf bnf);

            fun le_rel_OO_tac ctxt =
              HEADGOAL (EVERY' [rtac ctxt @{thm vimage2p_relcompp_mono},
                rtac ctxt ((rel_OO_of_bnf bnf RS sym) RS @{thm ord_eq_le_trans}),
                rtac ctxt @{thm order_refl}]);

            fun rel_OO_Grp_tac ctxt =
              HEADGOAL (EVERY' ([SELECT_GOAL (REPEAT_DETERM (HEADGOAL (rtac ctxt ext))),
                SELECT_GOAL (unfold_thms_tac ctxt [@{thm OO_Grp_alt}, mem_Collect_eq,
                  o_apply, @{thm vimage2p_def}, in_rel_of_bnf bnf, Bex_def, mem_Collect_eq]),
                rtac ctxt iffI,
                SELECT_GOAL (REPEAT_DETERM (HEADGOAL (eresolve0_tac [exE,conjE]))),
                rtac ctxt (zip_closed_thm OF (replicate 2 (Rep_thm RSN (2, @{thm ssubst_mem}))) RS
                  Rep_cases_thm),
                assume_tac ctxt,
                assume_tac ctxt,
                hyp_subst_tac ctxt,
                SELECT_GOAL (REPEAT_DETERM (HEADGOAL (rtac ctxt exI))),
                rtac ctxt conjI] @
                replicate (lives - 1) (rtac ctxt conjI THEN' assume_tac ctxt) @
                [assume_tac ctxt,
                SELECT_GOAL (REPEAT_DETERM (HEADGOAL (rtac ctxt conjI))),
                REPEAT_DETERM_N 2 o
                  etac ctxt (trans OF [iffD2 OF [Abs_inject_thm OF
                    [map_closed_thm OF [Rep_thm], Rep_thm]], Rep_inverse_thm]),
                SELECT_GOAL (REPEAT_DETERM (HEADGOAL (eresolve0_tac [exE,conjE]))),
                rtac ctxt exI,
                rtac ctxt conjI] @
                replicate (lives - 1) (rtac ctxt conjI THEN' assume_tac ctxt) @
                [assume_tac ctxt,
                rtac ctxt conjI,
                REPEAT_DETERM_N 2 o EVERY'
                  [rtac ctxt (iffD1 OF [Abs_inject_thm OF [map_closed_thm OF [Rep_thm], Rep_thm]]),
                  etac ctxt (Rep_inverse_thm RS sym RSN (2, trans))]]));

            fun pred_set_tac ctxt =
              HEADGOAL (EVERY'
                [rtac ctxt (pred_set_of_bnf bnf RS @{thm arg_cong[of _ _ "\<lambda>f. f o _"]} RS trans),
                SELECT_GOAL (unfold_thms_tac ctxt (@{thms Ball_comp_iff conj_comp_iff})),
                rtac ctxt refl]);

            fun wit_tac ctxt =
              HEADGOAL (EVERY'
                (map (fn thm => (EVERY'
                  [SELECT_GOAL (unfold_thms_tac ctxt (o_apply ::
                    (wit_closed_thms RL [Abs_inverse_thm]))),
                  dtac ctxt thm, assume_tac ctxt]))
                wit_thms));

            val tactics = [map_id0_tac, map_comp0_tac, map_cong0_tac] @ set_map0s_tac @
              [card_order_bd_tac, cinfinite_bd_tac] @ set_bds_tac @
              [le_rel_OO_tac, rel_OO_Grp_tac, pred_set_tac];

            val (bnf, lthy) = bnf_def Dont_Inline (user_policy Note_Some) true I
              tactics wit_tac NONE map_b rel_b pred_b set_bs
              (((((((Binding.empty, AbsT), map_G), sets_G), bd_G), wits_G), SOME rel_G), SOME pred_G)
              lthy;

            val (bnf, lthy) =
              morph_bnf_defs (Morphism.thm_morphism "BNF" (unfold_thms lthy defs)) bnf
              |> (fn bnf => note_bnf_defs bnf lthy);
          in
            lthy |> BNF_Def.register_bnf plugins AbsT_name bnf
          end
      | after_qed _ _ = raise Match;
  in
    (goals, after_qed, defs, lthy)
  end;


(* main commands *)

local

fun prepare_common prepare_name prepare_sort prepare_term prepare_thm
    (((((plugins, raw_specs), raw_Tname), raw_wits), xthm_opt), (map_b, rel_b, pred_b)) lthy =
  let
    val Tname = prepare_name lthy raw_Tname;
    val input_thm =
      (case xthm_opt of
        SOME xthm => prepare_thm lthy xthm
      | NONE => Typedef.get_info lthy Tname |> hd |> snd |> #type_definition);
    val wits = (Option.map o map) (prepare_term lthy) raw_wits;
    val specs =
      map (apsnd (apsnd (the_default @{sort type} o Option.map (prepare_sort lthy)))) raw_specs;

    val _ =
      (case HOLogic.dest_Trueprop (Thm.prop_of input_thm) of
        Const (@{const_name type_definition}, _) $ _ $ _ $ _ => ()
      | _ => error "Unsupported type of a theorem: only type_definition is supported");
  in
    typedef_bnf input_thm wits specs map_b rel_b pred_b plugins lthy
  end;

fun prepare_lift_bnf prepare_name prepare_sort prepare_term prepare_thm =
  (fn (goals, after_qed, definitions, lthy) =>
    lthy
    |> Proof.theorem NONE after_qed (map (single o rpair []) goals)
    |> Proof.refine_singleton
        (Method.Basic (fn ctxt => SIMPLE_METHOD (unfold_thms_tac ctxt definitions)))
    |> Proof.refine_singleton (Method.primitive_text (K I))) oo
  prepare_common prepare_name prepare_sort prepare_term prepare_thm o apfst (apfst (apsnd SOME));

fun prepare_solve prepare_name prepare_typ prepare_sort prepare_thm tacs =
  (fn (goals, after_qed, definitions, lthy) =>
    lthy
    |> after_qed (map2 (fn goal => fn tac => [Goal.prove lthy [] [] goal
        (fn (ctxtprems as {context = ctxt, prems = _}) =>
          unfold_thms_tac ctxt definitions THEN tac ctxtprems)])
      goals (tacs (length goals)))) oo
  prepare_common prepare_name prepare_typ prepare_sort prepare_thm;

in

val lift_bnf_cmd =
  prepare_lift_bnf
    (fst o dest_Type oo Proof_Context.read_type_name {proper = true, strict = false})
    Syntax.read_sort Syntax.read_term (singleton o Attrib.eval_thms);

fun lift_bnf args tacs =
  prepare_solve (K I) (K I) (K I) (K I) (K tacs) args;

val copy_bnf =
  apfst (apfst (rpair NONE))
  #> prepare_solve (K I) (K I) (K I) (K I)
    (fn n => replicate n (fn {context = ctxt, prems = _} => rtac ctxt UNIV_I 1));

val copy_bnf_cmd =
  apfst (apfst (rpair NONE))
  #> prepare_solve
    (fst o dest_Type oo Proof_Context.read_type_name {proper = true, strict = false})
    Syntax.read_sort Syntax.read_term (singleton o Attrib.eval_thms)
    (fn n => replicate n (fn {context = ctxt, prems = _} => rtac ctxt UNIV_I 1));

end;


(* outer syntax *)

local

val parse_wits =
  @{keyword "["} |-- (Parse.name --| @{keyword ":"} -- Scan.repeat Parse.term >>
    (fn ("wits", Ts) => Ts
      | (s, _) => error ("Unknown label " ^ quote s ^ " (expected \"wits\")"))) --|
  @{keyword "]"} || Scan.succeed [];

val parse_options =
  Scan.optional (@{keyword "("} |--
    Parse.list1 (Parse.group (K "option")
      (Plugin_Name.parse_filter >> Plugins_Option
      || Parse.reserved "no_warn_wits" >> K No_Warn_Wits))
    --| @{keyword ")"}) [];

val parse_plugins =
  Scan.optional (@{keyword "("} |-- Plugin_Name.parse_filter --| @{keyword ")"})
    (K Plugin_Name.default_filter) >> Plugins_Option >> single;

val parse_typedef_thm = Scan.option (Parse.reserved "via" |-- Parse.thm);

in

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword lift_bnf}
    "register a subtype of a bounded natural functor (BNF) as a BNF"
    ((parse_options -- parse_type_args_named_constrained -- Parse.type_const -- parse_wits --
      parse_typedef_thm -- parse_map_rel_pred_bindings) >> lift_bnf_cmd);

val _ =
  Outer_Syntax.local_theory @{command_keyword copy_bnf}
    "register a type copy of a bounded natural functor (BNF) as a BNF"
    ((parse_plugins -- parse_type_args_named_constrained -- Parse.type_const --
      parse_typedef_thm -- parse_map_rel_pred_bindings) >> copy_bnf_cmd);

end;

end;
