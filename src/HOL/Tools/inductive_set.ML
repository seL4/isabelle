(*  Title:      HOL/Tools/inductive_set.ML
    Author:     Stefan Berghofer, TU Muenchen

Wrapper for defining inductive sets using package for inductive predicates,
including infrastructure for converting between predicates and sets.
*)

signature INDUCTIVE_SET =
sig
  val to_set_att: thm list -> attribute
  val to_pred_att: thm list -> attribute
  val to_pred : thm list -> Context.generic -> thm -> thm
  val pred_set_conv_att: attribute
  val add_inductive_i:
    Inductive.inductive_flags ->
    ((binding * typ) * mixfix) list ->
    (string * typ) list ->
    (Attrib.binding * term) list -> thm list ->
    local_theory -> Inductive.inductive_result * local_theory
  val add_inductive: bool -> bool ->
    (binding * string option * mixfix) list ->
    (binding * string option * mixfix) list ->
    (Attrib.binding * string) list -> (Facts.ref * Attrib.src list) list ->
    bool -> local_theory -> Inductive.inductive_result * local_theory
  val mono_add: attribute
  val mono_del: attribute
  val codegen_preproc: theory -> thm list -> thm list
  val setup: theory -> theory
end;

structure Inductive_Set: INDUCTIVE_SET =
struct

(**** simplify {(x1, ..., xn). (x1, ..., xn) : S} to S ****)

val collect_mem_simproc =
  Simplifier.simproc_global @{theory Set} "Collect_mem" ["Collect t"] (fn thy => fn ss =>
    fn S as Const (@{const_name Collect}, Type ("fun", [_, T])) $ t =>
         let val (u, _, ps) = HOLogic.strip_psplits t
         in case u of
           (c as Const (@{const_name Set.member}, _)) $ q $ S' =>
             (case try (HOLogic.strip_ptuple ps) q of
                NONE => NONE
              | SOME ts =>
                  if not (Term.is_open S') andalso
                    ts = map Bound (length ps downto 0)
                  then
                    let val simp = full_simp_tac (Simplifier.inherit_context ss
                      (HOL_basic_ss addsimps [@{thm split_paired_all}, @{thm split_conv}])) 1
                    in
                      SOME (Goal.prove (Simplifier.the_context ss) [] []
                        (Const ("==", T --> T --> propT) $ S $ S')
                        (K (EVERY
                          [rtac eq_reflection 1, rtac @{thm subset_antisym} 1,
                           rtac subsetI 1, dtac CollectD 1, simp,
                           rtac subsetI 1, rtac CollectI 1, simp])))
                    end
                  else NONE)
         | _ => NONE
         end
     | _ => NONE);

(***********************************************************************************)
(* simplifies (%x y. (x, y) : S & P x y) to (%x y. (x, y) : S Int {(x, y). P x y}) *)
(* and        (%x y. (x, y) : S | P x y) to (%x y. (x, y) : S Un {(x, y). P x y})  *)
(* used for converting "strong" (co)induction rules                                *)
(***********************************************************************************)

val anyt = Free ("t", TFree ("'t", []));

fun strong_ind_simproc tab =
  Simplifier.simproc_global_i @{theory HOL} "strong_ind" [anyt] (fn thy => fn ss => fn t =>
    let
      fun close p t f =
        let val vs = Term.add_vars t []
        in Drule.instantiate' [] (rev (map (SOME o cterm_of thy o Var) vs))
          (p (fold (Logic.all o Var) vs t) f)
        end;
      fun mkop @{const_name HOL.conj} T x =
            SOME (Const (@{const_name Lattices.inf}, T --> T --> T), x)
        | mkop @{const_name HOL.disj} T x =
            SOME (Const (@{const_name Lattices.sup}, T --> T --> T), x)
        | mkop _ _ _ = NONE;
      fun mk_collect p T t =
        let val U = HOLogic.dest_setT T
        in HOLogic.Collect_const U $
          HOLogic.mk_psplits (HOLogic.flat_tuple_paths p) U HOLogic.boolT t
        end;
      fun decomp (Const (s, _) $ ((m as Const (@{const_name Set.member},
            Type (_, [_, Type (_, [T, _])]))) $ p $ S) $ u) =
              mkop s T (m, p, S, mk_collect p T (head_of u))
        | decomp (Const (s, _) $ u $ ((m as Const (@{const_name Set.member},
            Type (_, [_, Type (_, [T, _])]))) $ p $ S)) =
              mkop s T (m, p, mk_collect p T (head_of u), S)
        | decomp _ = NONE;
      val simp = full_simp_tac (Simplifier.inherit_context ss
        (HOL_basic_ss addsimps [mem_Collect_eq, @{thm split_conv}])) 1;
      fun mk_rew t = (case strip_abs_vars t of
          [] => NONE
        | xs => (case decomp (strip_abs_body t) of
            NONE => NONE
          | SOME (bop, (m, p, S, S')) =>
              SOME (close (Goal.prove (Simplifier.the_context ss) [] [])
                (Logic.mk_equals (t, fold_rev Term.abs xs (m $ p $ (bop $ S $ S'))))
                (K (EVERY
                  [rtac eq_reflection 1, REPEAT (rtac ext 1), rtac iffI 1,
                   EVERY [etac conjE 1, rtac IntI 1, simp, simp,
                     etac IntE 1, rtac conjI 1, simp, simp] ORELSE
                   EVERY [etac disjE 1, rtac UnI1 1, simp, rtac UnI2 1, simp,
                     etac UnE 1, rtac disjI1 1, simp, rtac disjI2 1, simp]])))
                handle ERROR _ => NONE))
    in
      case strip_comb t of
        (h as Const (name, _), ts) => (case Symtab.lookup tab name of
          SOME _ =>
            let val rews = map mk_rew ts
            in
              if forall is_none rews then NONE
              else SOME (fold (fn th1 => fn th2 => Thm.combination th2 th1)
                (map2 (fn SOME r => K r | NONE => Thm.reflexive o cterm_of thy)
                   rews ts) (Thm.reflexive (cterm_of thy h)))
            end
        | NONE => NONE)
      | _ => NONE
    end);

(* only eta contract terms occurring as arguments of functions satisfying p *)
fun eta_contract p =
  let
    fun eta b (Abs (a, T, body)) =
          (case eta b body of
             body' as (f $ Bound 0) =>
               if Term.is_dependent f orelse not b then Abs (a, T, body')
               else incr_boundvars ~1 f
           | body' => Abs (a, T, body'))
      | eta b (t $ u) = eta b t $ eta (p (head_of t)) u
      | eta b t = t
  in eta false end;

fun eta_contract_thm p =
  Conv.fconv_rule (Conv.then_conv (Thm.beta_conversion true, fn ct =>
    Thm.transitive (Thm.eta_conversion ct)
      (Thm.symmetric (Thm.eta_conversion
        (cterm_of (theory_of_cterm ct) (eta_contract p (term_of ct)))))));


(***********************************************************)
(* rules for converting between predicate and set notation *)
(*                                                         *)
(* rules for converting predicates to sets have the form   *)
(* P (%x y. (x, y) : s) = (%x y. (x, y) : S s)             *)
(*                                                         *)
(* rules for converting sets to predicates have the form   *)
(* S {(x, y). p x y} = {(x, y). P p x y}                   *)
(*                                                         *)
(* where s and p are parameters                            *)
(***********************************************************)

structure PredSetConvData = Generic_Data
(
  type T =
    {(* rules for converting predicates to sets *)
     to_set_simps: thm list,
     (* rules for converting sets to predicates *)
     to_pred_simps: thm list,
     (* arities of functions of type t set => ... => u set *)
     set_arities: (typ * (int list list option list * int list list option)) list Symtab.table,
     (* arities of functions of type (t => ... => bool) => u => ... => bool *)
     pred_arities: (typ * (int list list option list * int list list option)) list Symtab.table};
  val empty = {to_set_simps = [], to_pred_simps = [],
    set_arities = Symtab.empty, pred_arities = Symtab.empty};
  val extend = I;
  fun merge
    ({to_set_simps = to_set_simps1, to_pred_simps = to_pred_simps1,
      set_arities = set_arities1, pred_arities = pred_arities1},
     {to_set_simps = to_set_simps2, to_pred_simps = to_pred_simps2,
      set_arities = set_arities2, pred_arities = pred_arities2}) : T =
    {to_set_simps = Thm.merge_thms (to_set_simps1, to_set_simps2),
     to_pred_simps = Thm.merge_thms (to_pred_simps1, to_pred_simps2),
     set_arities = Symtab.merge_list (op =) (set_arities1, set_arities2),
     pred_arities = Symtab.merge_list (op =) (pred_arities1, pred_arities2)};
);

fun name_type_of (Free p) = SOME p
  | name_type_of (Const p) = SOME p
  | name_type_of _ = NONE;

fun map_type f (Free (s, T)) = Free (s, f T)
  | map_type f (Var (ixn, T)) = Var (ixn, f T)
  | map_type f _ = error "map_type";

fun find_most_specific is_inst f eq xs T =
  find_first (fn U => is_inst (T, f U)
    andalso forall (fn U' => eq (f U, f U') orelse not
      (is_inst (T, f U') andalso is_inst (f U', f U)))
        xs) xs;

fun lookup_arity thy arities (s, T) = case Symtab.lookup arities s of
    NONE => NONE
  | SOME xs => find_most_specific (Sign.typ_instance thy) fst (op =) xs T;

fun lookup_rule thy f rules = find_most_specific
  (swap #> Pattern.matches thy) (f #> fst) (op aconv) rules;

fun infer_arities thy arities (optf, t) fs = case strip_comb t of
    (Abs (s, T, u), []) => infer_arities thy arities (NONE, u) fs
  | (Abs _, _) => infer_arities thy arities (NONE, Envir.beta_norm t) fs
  | (u, ts) => (case Option.map (lookup_arity thy arities) (name_type_of u) of
      SOME (SOME (_, (arity, _))) =>
        (fold (infer_arities thy arities) (arity ~~ List.take (ts, length arity)) fs
           handle General.Subscript => error "infer_arities: bad term")
    | _ => fold (infer_arities thy arities) (map (pair NONE) ts)
      (case optf of
         NONE => fs
       | SOME f => AList.update op = (u, the_default f
           (Option.map (fn g => inter (op =) g f) (AList.lookup op = fs u))) fs));


(**************************************************************)
(*    derive the to_pred equation from the to_set equation    *)
(*                                                            *)
(* 1. instantiate each set parameter with {(x, y). p x y}     *)
(* 2. apply %P. {(x, y). P x y} to both sides of the equation *)
(* 3. simplify                                                *)
(**************************************************************)

fun mk_to_pred_inst thy fs =
  map (fn (x, ps) =>
    let
      val (Ts, T) = strip_type (fastype_of x);
      val U = HOLogic.dest_setT T;
      val x' = map_type
        (K (Ts @ HOLogic.strip_ptupleT ps U ---> HOLogic.boolT)) x;
    in
      (cterm_of thy x,
       cterm_of thy (fold_rev (Term.abs o pair "x") Ts
         (HOLogic.Collect_const U $
            HOLogic.mk_psplits ps U HOLogic.boolT
              (list_comb (x', map Bound (length Ts - 1 downto 0))))))
    end) fs;

fun mk_to_pred_eq p fs optfs' T thm =
  let
    val thy = theory_of_thm thm;
    val insts = mk_to_pred_inst thy fs;
    val thm' = Thm.instantiate ([], insts) thm;
    val thm'' = (case optfs' of
        NONE => thm' RS sym
      | SOME fs' =>
          let
            val U = HOLogic.dest_setT (body_type T);
            val Ts = HOLogic.strip_ptupleT fs' U;
            (* FIXME: should cterm_instantiate increment indexes? *)
            val arg_cong' = Thm.incr_indexes (Thm.maxidx_of thm + 1) arg_cong;
            val (arg_cong_f, _) = arg_cong' |> cprop_of |> Drule.strip_imp_concl |>
              Thm.dest_comb |> snd |> Drule.strip_comb |> snd |> hd |> Thm.dest_comb
          in
            thm' RS (Drule.cterm_instantiate [(arg_cong_f,
              cterm_of thy (Abs ("P", Ts ---> HOLogic.boolT,
                HOLogic.Collect_const U $ HOLogic.mk_psplits fs' U
                  HOLogic.boolT (Bound 0))))] arg_cong' RS sym)
          end)
  in
    Simplifier.simplify (HOL_basic_ss addsimps [mem_Collect_eq, @{thm split_conv}]
      addsimprocs [collect_mem_simproc]) thm'' |>
        zero_var_indexes |> eta_contract_thm (equal p)
  end;


(**** declare rules for converting predicates to sets ****)

fun add ctxt thm (tab as {to_set_simps, to_pred_simps, set_arities, pred_arities}) =
  case prop_of thm of
    Const (@{const_name Trueprop}, _) $ (Const (@{const_name HOL.eq}, Type (_, [T, _])) $ lhs $ rhs) =>
      (case body_type T of
         @{typ bool} =>
           let
             val thy = Context.theory_of ctxt;
             fun factors_of t fs = case strip_abs_body t of
                 Const (@{const_name Set.member}, _) $ u $ S =>
                   if is_Free S orelse is_Var S then
                     let val ps = HOLogic.flat_tuple_paths u
                     in (SOME ps, (S, ps) :: fs) end
                   else (NONE, fs)
               | _ => (NONE, fs);
             val (h, ts) = strip_comb lhs
             val (pfs, fs) = fold_map factors_of ts [];
             val ((h', ts'), fs') = (case rhs of
                 Abs _ => (case strip_abs_body rhs of
                     Const (@{const_name Set.member}, _) $ u $ S =>
                       (strip_comb S, SOME (HOLogic.flat_tuple_paths u))
                   | _ => error "member symbol on right-hand side expected")
               | _ => (strip_comb rhs, NONE))
           in
             case (name_type_of h, name_type_of h') of
               (SOME (s, T), SOME (s', T')) =>
                 if exists (fn (U, _) =>
                   Sign.typ_instance thy (T', U) andalso
                   Sign.typ_instance thy (U, T'))
                     (Symtab.lookup_list set_arities s')
                 then
                   (warning ("Ignoring conversion rule for operator " ^ s'); tab)
                 else
                   {to_set_simps = thm :: to_set_simps,
                    to_pred_simps =
                      mk_to_pred_eq h fs fs' T' thm :: to_pred_simps,
                    set_arities = Symtab.insert_list op = (s',
                      (T', (map (AList.lookup op = fs) ts', fs'))) set_arities,
                    pred_arities = Symtab.insert_list op = (s,
                      (T, (pfs, fs'))) pred_arities}
             | _ => error "set / predicate constant expected"
           end
       | _ => error "equation between predicates expected")
  | _ => error "equation expected";

val pred_set_conv_att = Thm.declaration_attribute
  (fn thm => fn ctxt => PredSetConvData.map (add ctxt thm) ctxt);


(**** convert theorem in set notation to predicate notation ****)

fun is_pred tab t =
  case Option.map (Symtab.lookup tab o fst) (name_type_of t) of
    SOME (SOME _) => true | _ => false;

fun to_pred_simproc rules =
  let val rules' = map mk_meta_eq rules
  in
    Simplifier.simproc_global_i @{theory HOL} "to_pred" [anyt]
      (fn thy => K (lookup_rule thy (prop_of #> Logic.dest_equals) rules'))
  end;

fun to_pred_proc thy rules t = case lookup_rule thy I rules t of
    NONE => NONE
  | SOME (lhs, rhs) =>
      SOME (Envir.subst_term
        (Pattern.match thy (lhs, t) (Vartab.empty, Vartab.empty)) rhs);

fun to_pred thms ctxt thm =
  let
    val thy = Context.theory_of ctxt;
    val {to_pred_simps, set_arities, pred_arities, ...} =
      fold (add ctxt) thms (PredSetConvData.get ctxt);
    val fs = filter (is_Var o fst)
      (infer_arities thy set_arities (NONE, prop_of thm) []);
    (* instantiate each set parameter with {(x, y). p x y} *)
    val insts = mk_to_pred_inst thy fs
  in
    thm |>
    Thm.instantiate ([], insts) |>
    Simplifier.full_simplify (HOL_basic_ss addsimprocs
      [to_pred_simproc (mem_Collect_eq :: @{thm split_conv} :: to_pred_simps)]) |>
    eta_contract_thm (is_pred pred_arities) |>
    Rule_Cases.save thm
  end;

val to_pred_att = Thm.rule_attribute o to_pred;


(**** convert theorem in predicate notation to set notation ****)

fun to_set thms ctxt thm =
  let
    val thy = Context.theory_of ctxt;
    val {to_set_simps, pred_arities, ...} =
      fold (add ctxt) thms (PredSetConvData.get ctxt);
    val fs = filter (is_Var o fst)
      (infer_arities thy pred_arities (NONE, prop_of thm) []);
    (* instantiate each predicate parameter with %x y. (x, y) : s *)
    val insts = map (fn (x, ps) =>
      let
        val Ts = binder_types (fastype_of x);
        val l = length Ts;
        val k = length ps;
        val (Rs, Us) = chop (l - k - 1) Ts;
        val T = HOLogic.mk_ptupleT ps Us;
        val x' = map_type (K (Rs ---> HOLogic.mk_setT T)) x
      in
        (cterm_of thy x,
         cterm_of thy (fold_rev (Term.abs o pair "x") Ts
          (HOLogic.mk_mem (HOLogic.mk_ptuple ps T (map Bound (k downto 0)),
             list_comb (x', map Bound (l - 1 downto k + 1))))))
      end) fs;
  in
    thm |>
    Thm.instantiate ([], insts) |>
    Simplifier.full_simplify (HOL_basic_ss addsimps to_set_simps
        addsimprocs [strong_ind_simproc pred_arities, collect_mem_simproc]) |>
    Rule_Cases.save thm
  end;

val to_set_att = Thm.rule_attribute o to_set;


(**** preprocessor for code generator ****)

fun codegen_preproc thy =
  let
    val {to_pred_simps, set_arities, pred_arities, ...} =
      PredSetConvData.get (Context.Theory thy);
    fun preproc thm =
      if exists_Const (fn (s, _) => case Symtab.lookup set_arities s of
          NONE => false
        | SOME arities => exists (fn (_, (xs, _)) =>
            forall is_none xs) arities) (prop_of thm)
      then
        thm |>
        Simplifier.full_simplify (HOL_basic_ss addsimprocs
          [to_pred_simproc (mem_Collect_eq :: @{thm split_conv} :: to_pred_simps)]) |>
        eta_contract_thm (is_pred pred_arities)
      else thm
  in map preproc end;

fun code_ind_att optmod = to_pred_att [];


(**** definition of inductive sets ****)

fun add_ind_set_def
    {quiet_mode, verbose, alt_name, coind, no_elim, no_ind, skip_mono}
    cs intros monos params cnames_syn lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val {set_arities, pred_arities, to_pred_simps, ...} =
      PredSetConvData.get (Context.Proof lthy);
    fun infer (Abs (_, _, t)) = infer t
      | infer (Const (@{const_name Set.member}, _) $ t $ u) =
          infer_arities thy set_arities (SOME (HOLogic.flat_tuple_paths t), u)
      | infer (t $ u) = infer t #> infer u
      | infer _ = I;
    val new_arities = filter_out
      (fn (x as Free (_, T), _) => member (op =) params x andalso length (binder_types T) > 0
        | _ => false) (fold (snd #> infer) intros []);
    val params' = map (fn x =>
      (case AList.lookup op = new_arities x of
        SOME fs =>
          let
            val T = HOLogic.dest_setT (fastype_of x);
            val Ts = HOLogic.strip_ptupleT fs T;
            val x' = map_type (K (Ts ---> HOLogic.boolT)) x
          in
            (x, (x',
              (HOLogic.Collect_const T $
                 HOLogic.mk_psplits fs T HOLogic.boolT x',
               fold_rev (Term.abs o pair "x") Ts
                 (HOLogic.mk_mem
                   (HOLogic.mk_ptuple fs T (map Bound (length fs downto 0)), x)))))
          end
       | NONE => (x, (x, (x, x))))) params;
    val (params1, (params2, params3)) =
      params' |> map snd |> split_list ||> split_list;
    val paramTs = map fastype_of params;

    (* equations for converting sets to predicates *)
    val ((cs', cs_info), eqns) = cs |> map (fn c as Free (s, T) =>
      let
        val fs = the_default [] (AList.lookup op = new_arities c);
        val (Us, U) = strip_type T |> apsnd HOLogic.dest_setT;
        val _ = Us = paramTs orelse error (Pretty.string_of (Pretty.chunks
          [Pretty.str "Argument types",
           Pretty.block (Pretty.commas (map (Syntax.pretty_typ lthy) Us)),
           Pretty.str ("of " ^ s ^ " do not agree with types"),
           Pretty.block (Pretty.commas (map (Syntax.pretty_typ lthy) paramTs)),
           Pretty.str "of declared parameters"]));
        val Ts = HOLogic.strip_ptupleT fs U;
        val c' = Free (s ^ "p",
          map fastype_of params1 @ Ts ---> HOLogic.boolT)
      in
        ((c', (fs, U, Ts)),
         (list_comb (c, params2),
          HOLogic.Collect_const U $ HOLogic.mk_psplits fs U HOLogic.boolT
            (list_comb (c', params1))))
      end) |> split_list |>> split_list;
    val eqns' = eqns @
      map (prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq)
        (mem_Collect_eq :: @{thm split_conv} :: to_pred_simps);

    (* predicate version of the introduction rules *)
    val intros' =
      map (fn (name_atts, t) => (name_atts,
        t |>
        map_aterms (fn u =>
          (case AList.lookup op = params' u of
             SOME (_, (u', _)) => u'
           | NONE => u)) |>
        Pattern.rewrite_term thy [] [to_pred_proc thy eqns'] |>
        eta_contract (member op = cs' orf is_pred pred_arities))) intros;
    val cnames_syn' = map (fn (b, _) => (Binding.suffix_name "p" b, NoSyn)) cnames_syn;
    val monos' = map (to_pred [] (Context.Proof lthy)) monos;
    val ({preds, intrs, elims, raw_induct, eqs, ...}, lthy1) =
      Inductive.add_ind_def
        {quiet_mode = quiet_mode, verbose = verbose, alt_name = Binding.empty,
          coind = coind, no_elim = no_elim, no_ind = no_ind, skip_mono = skip_mono}
        cs' intros' monos' params1 cnames_syn' lthy;

    (* define inductive sets using previously defined predicates *)
    val (defs, lthy2) = lthy1
      |> Local_Theory.conceal  (* FIXME ?? *)
      |> fold_map Local_Theory.define
        (map (fn (((c, syn), (fs, U, _)), p) => ((c, syn), ((Thm.def_binding c, []),
           fold_rev lambda params (HOLogic.Collect_const U $
             HOLogic.mk_psplits fs U HOLogic.boolT (list_comb (p, params3))))))
           (cnames_syn ~~ cs_info ~~ preds))
      ||> Local_Theory.restore_naming lthy1;

    (* prove theorems for converting predicate to set notation *)
    val lthy3 = fold
      (fn (((p, c as Free (s, _)), (fs, U, Ts)), (_, (_, def))) => fn lthy =>
        let val conv_thm =
          Goal.prove lthy (map (fst o dest_Free) params) []
            (HOLogic.mk_Trueprop (HOLogic.mk_eq
              (list_comb (p, params3),
               fold_rev (Term.abs o pair "x") Ts
                (HOLogic.mk_mem (HOLogic.mk_ptuple fs U (map Bound (length fs downto 0)),
                  list_comb (c, params))))))
            (K (REPEAT (rtac ext 1) THEN simp_tac (HOL_basic_ss addsimps
              [def, mem_Collect_eq, @{thm split_conv}]) 1))
        in
          lthy |> Local_Theory.note ((Binding.name (s ^ "p_" ^ s ^ "_eq"),
            [Attrib.internal (K pred_set_conv_att)]),
              [conv_thm]) |> snd
        end) (preds ~~ cs ~~ cs_info ~~ defs) lthy2;

    (* convert theorems to set notation *)
    val rec_name =
      if Binding.is_empty alt_name then
        Binding.name (space_implode "_" (map (Binding.name_of o fst) cnames_syn))
      else alt_name;
    val cnames = map (Local_Theory.full_name lthy3 o #1) cnames_syn;  (* FIXME *)
    val (intr_names, intr_atts) = split_list (map fst intros);
    val raw_induct' = to_set [] (Context.Proof lthy3) raw_induct;
    val (intrs', elims', eqs', induct, inducts, lthy4) =
      Inductive.declare_rules rec_name coind no_ind cnames (map fst defs)
        (map (to_set [] (Context.Proof lthy3)) intrs) intr_names intr_atts
        (map (fn th => (to_set [] (Context.Proof lthy3) th,
           map (fst o fst) (fst (Rule_Cases.get th)),
           Rule_Cases.get_constraints th)) elims)
        (map (to_set [] (Context.Proof lthy3)) eqs) raw_induct' lthy3;
  in
    ({intrs = intrs', elims = elims', induct = induct, inducts = inducts,
      raw_induct = raw_induct', preds = map fst defs, eqs = eqs'},
     lthy4)
  end;

val add_inductive_i = Inductive.gen_add_inductive_i add_ind_set_def;
val add_inductive = Inductive.gen_add_inductive add_ind_set_def;

fun mono_att att =
  Thm.declaration_attribute (fn thm => fn context =>
    Thm.attribute_declaration att (to_pred [] context thm) context);

val mono_add = mono_att Inductive.mono_add;
val mono_del = mono_att Inductive.mono_del;


(** package setup **)

(* setup theory *)

val setup =
  Attrib.setup @{binding pred_set_conv} (Scan.succeed pred_set_conv_att)
    "declare rules for converting between predicate and set notation" #>
  Attrib.setup @{binding to_set} (Attrib.thms >> to_set_att)
    "convert rule to set notation" #>
  Attrib.setup @{binding to_pred} (Attrib.thms >> to_pred_att)
    "convert rule to predicate notation" #>
  Attrib.setup @{binding mono_set} (Attrib.add_del mono_add mono_del)
    "declaration of monotonicity rule for set operators" #>
  Simplifier.map_simpset_global (fn ss => ss addsimprocs [collect_mem_simproc]);


(* outer syntax *)

val ind_set_decl = Inductive.gen_ind_decl add_ind_set_def;

val _ =
  Outer_Syntax.local_theory' @{command_spec "inductive_set"} "define inductive sets"
    (ind_set_decl false);

val _ =
  Outer_Syntax.local_theory' @{command_spec "coinductive_set"} "define coinductive sets"
    (ind_set_decl true);

end;
