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
  val add_inductive:
    Inductive.flags ->
    ((binding * typ) * mixfix) list ->
    (string * typ) list ->
    (Attrib.binding * term) list -> thm list ->
    local_theory -> Inductive.result * local_theory
  val add_inductive_cmd: bool -> bool ->
    (binding * string option * mixfix) list ->
    (binding * string option * mixfix) list ->
    Specification.multi_specs_cmd -> (Facts.ref * Token.src list) list ->
    local_theory -> Inductive.result * local_theory
  val mono_add: attribute
  val mono_del: attribute
end;

structure Inductive_Set: INDUCTIVE_SET =
struct

(***********************************************************************************)
(* simplifies (%x y. (x, y) : S & P x y) to (%x y. (x, y) : S Int {(x, y). P x y}) *)
(* and        (%x y. (x, y) : S | P x y) to (%x y. (x, y) : S Un {(x, y). P x y})  *)
(* used for converting "strong" (co)induction rules                                *)
(***********************************************************************************)

val anyt = Free ("t", TFree ("'t", []));

fun strong_ind_simproc tab =
  Simplifier.make_simproc \<^context> "strong_ind"
   {lhss = [\<^term>\<open>x::'a::{}\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      let
        fun close p t f =
          let val vs = Term.add_vars t []
          in Thm.instantiate' [] (rev (map (SOME o Thm.cterm_of ctxt o Var) vs))
            (p (fold (Logic.all o Var) vs t) f)
          end;
        fun mkop \<^const_name>\<open>HOL.conj\<close> T x =
              SOME (Const (\<^const_name>\<open>Lattices.inf\<close>, T --> T --> T), x)
          | mkop \<^const_name>\<open>HOL.disj\<close> T x =
              SOME (Const (\<^const_name>\<open>Lattices.sup\<close>, T --> T --> T), x)
          | mkop _ _ _ = NONE;
        fun mk_collect p T t =
          let val U = HOLogic.dest_setT T
          in HOLogic.Collect_const U $
            HOLogic.mk_ptupleabs (HOLogic.flat_tuple_paths p) U HOLogic.boolT t
          end;
        fun decomp (Const (s, _) $ ((m as Const (\<^const_name>\<open>Set.member\<close>,
              Type (_, [_, Type (_, [T, _])]))) $ p $ S) $ u) =
                mkop s T (m, p, S, mk_collect p T (head_of u))
          | decomp (Const (s, _) $ u $ ((m as Const (\<^const_name>\<open>Set.member\<close>,
              Type (_, [_, Type (_, [T, _])]))) $ p $ S)) =
                mkop s T (m, p, mk_collect p T (head_of u), S)
          | decomp _ = NONE;
        val simp =
          full_simp_tac
            (put_simpset HOL_basic_ss ctxt addsimps @{thms mem_Collect_eq case_prod_conv}) 1;
        fun mk_rew t = (case strip_abs_vars t of
            [] => NONE
          | xs => (case decomp (strip_abs_body t) of
              NONE => NONE
            | SOME (bop, (m, p, S, S')) =>
                SOME (close (Goal.prove ctxt [] [])
                  (Logic.mk_equals (t, fold_rev Term.abs xs (m $ p $ (bop $ S $ S'))))
                  (K (EVERY
                    [resolve_tac ctxt [eq_reflection] 1,
                     REPEAT (resolve_tac ctxt @{thms ext} 1),
                     resolve_tac ctxt @{thms iffI} 1,
                     EVERY [eresolve_tac ctxt @{thms conjE} 1,
                       resolve_tac ctxt @{thms IntI} 1, simp, simp,
                       eresolve_tac ctxt @{thms IntE} 1,
                       resolve_tac ctxt @{thms conjI} 1, simp, simp] ORELSE
                     EVERY [eresolve_tac ctxt @{thms disjE} 1,
                       resolve_tac ctxt @{thms UnI1} 1, simp,
                       resolve_tac ctxt @{thms UnI2} 1, simp,
                       eresolve_tac ctxt @{thms UnE} 1,
                       resolve_tac ctxt @{thms disjI1} 1, simp,
                       resolve_tac ctxt @{thms disjI2} 1, simp]])))
                  handle ERROR _ => NONE))
      in
        (case strip_comb (Thm.term_of ct) of
          (h as Const (name, _), ts) =>
            if Symtab.defined tab name then
              let val rews = map mk_rew ts
              in
                if forall is_none rews then NONE
                else SOME (fold (fn th1 => fn th2 => Thm.combination th2 th1)
                  (map2 (fn SOME r => K r | NONE => Thm.reflexive o Thm.cterm_of ctxt)
                     rews ts) (Thm.reflexive (Thm.cterm_of ctxt h)))
              end
            else NONE
        | _ => NONE)
      end};

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

fun eta_contract_thm ctxt p =
  Conv.fconv_rule (Conv.then_conv (Thm.beta_conversion true, fn ct =>
    Thm.transitive (Thm.eta_conversion ct)
      (Thm.symmetric (Thm.eta_conversion (Thm.cterm_of ctxt (eta_contract p (Thm.term_of ct)))))));


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

structure Data = Generic_Data
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
    (Abs (_, _, u), []) => infer_arities thy arities (NONE, u) fs
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

fun mk_to_pred_inst ctxt fs =
  map (fn (x, ps) =>
    let
      val (Ts, T) = strip_type (fastype_of x);
      val U = HOLogic.dest_setT T;
      val x' = map_type
        (K (Ts @ HOLogic.strip_ptupleT ps U ---> HOLogic.boolT)) x;
    in
      (dest_Var x,
       Thm.cterm_of ctxt (fold_rev (Term.abs o pair "x") Ts
         (HOLogic.Collect_const U $
            HOLogic.mk_ptupleabs ps U HOLogic.boolT
              (list_comb (x', map Bound (length Ts - 1 downto 0))))))
    end) fs;

fun mk_to_pred_eq ctxt p fs optfs' T thm =
  let
    val insts = mk_to_pred_inst ctxt fs;
    val thm' = Thm.instantiate (TVars.empty, Vars.make insts) thm;
    val thm'' =
      (case optfs' of
        NONE => thm' RS sym
      | SOME fs' =>
          let
            val U = HOLogic.dest_setT (body_type T);
            val Ts = HOLogic.strip_ptupleT fs' U;
            val arg_cong' = Thm.incr_indexes (Thm.maxidx_of thm + 1) arg_cong;
            val (Var (arg_cong_f, _), _) = arg_cong' |> Thm.concl_of |>
              dest_comb |> snd |> strip_comb |> snd |> hd |> dest_comb;
          in
            thm' RS (infer_instantiate ctxt [(arg_cong_f,
              Thm.cterm_of ctxt (Abs ("P", Ts ---> HOLogic.boolT,
                HOLogic.Collect_const U $ HOLogic.mk_ptupleabs fs' U
                  HOLogic.boolT (Bound 0))))] arg_cong' RS sym)
          end)
  in
    Simplifier.simplify
      (put_simpset HOL_basic_ss ctxt addsimps @{thms mem_Collect_eq case_prod_conv}
        addsimprocs [\<^simproc>\<open>Collect_mem\<close>]) thm''
      |> zero_var_indexes |> eta_contract_thm ctxt (equal p)
  end;


(**** declare rules for converting predicates to sets ****)

exception Malformed of string;

fun add context thm (tab as {to_set_simps, to_pred_simps, set_arities, pred_arities}) =
  (case Thm.prop_of thm of
    Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, Type (_, [T, _])) $ lhs $ rhs) =>
      (case body_type T of
         \<^typ>\<open>bool\<close> =>
           let
             val thy = Context.theory_of context;
             val ctxt = Context.proof_of context;
             fun factors_of t fs = case strip_abs_body t of
                 Const (\<^const_name>\<open>Set.member\<close>, _) $ u $ S =>
                   if is_Free S orelse is_Var S then
                     let val ps = HOLogic.flat_tuple_paths u
                     in (SOME ps, (S, ps) :: fs) end
                   else (NONE, fs)
               | _ => (NONE, fs);
             val (h, ts) = strip_comb lhs
             val (pfs, fs) = fold_map factors_of ts [];
             val ((h', ts'), fs') = (case rhs of
                 Abs _ => (case strip_abs_body rhs of
                     Const (\<^const_name>\<open>Set.member\<close>, _) $ u $ S =>
                       (strip_comb S, SOME (HOLogic.flat_tuple_paths u))
                   | _ => raise Malformed "member symbol on right-hand side expected")
               | _ => (strip_comb rhs, NONE))
           in
             case (name_type_of h, name_type_of h') of
               (SOME (s, T), SOME (s', T')) =>
                 if exists (fn (U, _) =>
                   Sign.typ_instance thy (T', U) andalso
                   Sign.typ_instance thy (U, T'))
                     (Symtab.lookup_list set_arities s')
                 then
                   (if Context_Position.is_really_visible ctxt then
                     warning ("Ignoring conversion rule for operator " ^ s')
                    else (); tab)
                 else
                   {to_set_simps = Thm.trim_context thm :: to_set_simps,
                    to_pred_simps =
                      Thm.trim_context (mk_to_pred_eq ctxt h fs fs' T' thm) :: to_pred_simps,
                    set_arities = Symtab.insert_list op = (s',
                      (T', (map (AList.lookup op = fs) ts', fs'))) set_arities,
                    pred_arities = Symtab.insert_list op = (s,
                      (T, (pfs, fs'))) pred_arities}
             | _ => raise Malformed "set / predicate constant expected"
           end
       | _ => raise Malformed "equation between predicates expected")
  | _ => raise Malformed "equation expected")
  handle Malformed msg =>
    let
      val ctxt = Context.proof_of context
      val _ =
        if Context_Position.is_really_visible ctxt then
          warning ("Ignoring malformed set / predicate conversion rule: " ^ msg ^
            "\n" ^ Thm.string_of_thm ctxt thm)
        else ();
    in tab end;

val pred_set_conv_att = Thm.declaration_attribute
  (fn thm => fn ctxt => Data.map (add ctxt thm) ctxt);


(**** convert theorem in set notation to predicate notation ****)

fun is_pred tab t =
  case Option.map (Symtab.lookup tab o fst) (name_type_of t) of
    SOME (SOME _) => true | _ => false;

fun to_pred_simproc rules =
  let val rules' = map mk_meta_eq rules
  in
    Simplifier.make_simproc \<^context> "to_pred"
      {lhss = [anyt],
       proc = fn _ => fn ctxt => fn ct =>
        lookup_rule (Proof_Context.theory_of ctxt)
          (Thm.prop_of #> Logic.dest_equals) rules' (Thm.term_of ct)}
  end;

fun to_pred_proc thy rules t =
  case lookup_rule thy I rules t of
    NONE => NONE
  | SOME (lhs, rhs) =>
      SOME (Envir.subst_term
        (Pattern.match thy (lhs, t) (Vartab.empty, Vartab.empty)) rhs);

fun to_pred thms context thm =
  let
    val thy = Context.theory_of context;
    val ctxt = Context.proof_of context;
    val {to_pred_simps, set_arities, pred_arities, ...} =
      fold (add context) thms (Data.get context);
    val fs = filter (is_Var o fst)
      (infer_arities thy set_arities (NONE, Thm.prop_of thm) []);
    (* instantiate each set parameter with {(x, y). p x y} *)
    val insts = mk_to_pred_inst ctxt fs
  in
    thm |>
    Thm.instantiate (TVars.empty, Vars.make insts) |>
    Simplifier.full_simplify (put_simpset HOL_basic_ss ctxt addsimprocs
      [to_pred_simproc
        (@{thm mem_Collect_eq} :: @{thm case_prod_conv} :: map (Thm.transfer thy) to_pred_simps)]) |>
    eta_contract_thm ctxt (is_pred pred_arities) |>
    Rule_Cases.save thm
  end;

val to_pred_att = Thm.rule_attribute [] o to_pred;


(**** convert theorem in predicate notation to set notation ****)

fun to_set thms context thm =
  let
    val thy = Context.theory_of context;
    val ctxt = Context.proof_of context;
    val {to_set_simps, pred_arities, ...} =
      fold (add context) thms (Data.get context);
    val fs = filter (is_Var o fst)
      (infer_arities thy pred_arities (NONE, Thm.prop_of thm) []);
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
        (dest_Var x,
         Thm.cterm_of ctxt (fold_rev (Term.abs o pair "x") Ts
          (HOLogic.mk_mem (HOLogic.mk_ptuple ps T (map Bound (k downto 0)),
             list_comb (x', map Bound (l - 1 downto k + 1))))))
      end) fs;
  in
    thm |>
    Thm.instantiate (TVars.empty, Vars.make insts) |>
    Simplifier.full_simplify (put_simpset HOL_basic_ss ctxt addsimps to_set_simps
        addsimprocs [strong_ind_simproc pred_arities, \<^simproc>\<open>Collect_mem\<close>]) |>
    Rule_Cases.save thm
  end;

val to_set_att = Thm.rule_attribute [] o to_set;


(**** definition of inductive sets ****)

fun add_ind_set_def
    {quiet_mode, verbose, alt_name, coind, no_elim, no_ind, skip_mono}
    cs intros monos params cnames_syn lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val {set_arities, pred_arities, to_pred_simps, ...} =
      Data.get (Context.Proof lthy);
    fun infer (Abs (_, _, t)) = infer t
      | infer (Const (\<^const_name>\<open>Set.member\<close>, _) $ t $ u) =
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
                 HOLogic.mk_ptupleabs fs T HOLogic.boolT x',
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
          HOLogic.Collect_const U $ HOLogic.mk_ptupleabs fs U HOLogic.boolT
            (list_comb (c', params1))))
      end) |> split_list |>> split_list;
    val eqns' = eqns @
      map (Thm.prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq)
        (@{thm mem_Collect_eq} :: @{thm case_prod_conv} :: to_pred_simps);

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
      |> fold_map Local_Theory.define
        (map (fn (((b, mx), (fs, U, _)), p) =>
          ((b, mx), ((Thm.def_binding b, []),
            fold_rev lambda params (HOLogic.Collect_const U $
              HOLogic.mk_ptupleabs fs U HOLogic.boolT (list_comb (p, params3))))))
            (cnames_syn ~~ cs_info ~~ preds));

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
            (K (REPEAT (resolve_tac lthy @{thms ext} 1) THEN
              simp_tac (put_simpset HOL_basic_ss lthy addsimps
                [def, @{thm mem_Collect_eq}, @{thm case_prod_conv}]) 1))
        in
          lthy |> Local_Theory.note ((Binding.name (s ^ "p_" ^ s ^ "_eq"),
            [Attrib.internal (K pred_set_conv_att)]),
              [conv_thm]) |> snd
        end) (preds ~~ cs ~~ cs_info ~~ defs) lthy2;

    (* convert theorems to set notation *)
    val rec_name =
      if Binding.is_empty alt_name then Binding.conglomerate (map #1 cnames_syn) else alt_name;
    val cnames = map (Local_Theory.full_name lthy3 o #1) cnames_syn;  (* FIXME *)
    val spec_name = Binding.conglomerate (map #1 cnames_syn);
    val (intr_names, intr_atts) = split_list (map fst intros);
    val raw_induct' = to_set [] (Context.Proof lthy3) raw_induct;
    val (intrs', elims', eqs', induct, inducts, lthy4) =
      Inductive.declare_rules rec_name coind no_ind spec_name cnames (map fst defs)
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

val add_inductive = Inductive.gen_add_inductive add_ind_set_def;
val add_inductive_cmd = Inductive.gen_add_inductive_cmd add_ind_set_def;

fun mono_att att =
  Thm.declaration_attribute (fn thm => fn context =>
    Thm.attribute_declaration att (to_pred [] context thm) context);

val mono_add = mono_att Inductive.mono_add;
val mono_del = mono_att Inductive.mono_del;


(** package setup **)

(* attributes *)

val _ =
  Theory.setup
   (Attrib.setup \<^binding>\<open>pred_set_conv\<close> (Scan.succeed pred_set_conv_att)
      "declare rules for converting between predicate and set notation" #>
    Attrib.setup \<^binding>\<open>to_set\<close> (Attrib.thms >> to_set_att)
      "convert rule to set notation" #>
    Attrib.setup \<^binding>\<open>to_pred\<close> (Attrib.thms >> to_pred_att)
      "convert rule to predicate notation" #>
    Attrib.setup \<^binding>\<open>mono_set\<close> (Attrib.add_del mono_add mono_del)
      "declare of monotonicity rule for set operators");


(* commands *)                           

val ind_set_decl = Inductive.gen_ind_decl add_ind_set_def;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>inductive_set\<close> "define inductive sets"
    (ind_set_decl false);

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>coinductive_set\<close> "define coinductive sets"
    (ind_set_decl true);

end;
