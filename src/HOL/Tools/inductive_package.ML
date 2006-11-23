(*  Title:      HOL/Tools/inductive_package.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen

(Co)Inductive Definition module for HOL.

Features:
  * least or greatest fixedpoints
  * mutually recursive definitions
  * definitions involving arbitrary monotone operators
  * automatically proves introduction and elimination rules

  Introduction rules have the form
  [| M Pj ti, ..., Q x, ... |] ==> Pk t
  where M is some monotone operator (usually the identity)
  Q x is any side condition on the free variables
  ti, t are any terms
  Pj, Pk are two of the predicates being defined in mutual recursion
*)

signature INDUCTIVE_PACKAGE =
sig
  val quiet_mode: bool ref
  type inductive_result
  type inductive_info
  val get_inductive: Proof.context -> string -> inductive_info option
  val print_inductives: Proof.context -> unit
  val mono_add: attribute
  val mono_del: attribute
  val get_monos: Proof.context -> thm list
  val mk_cases: Proof.context -> term -> thm
  val inductive_forall_name: string
  val inductive_forall_def: thm
  val rulify: thm -> thm
  val inductive_cases: ((bstring * Attrib.src list) * string list) list ->
    Proof.context -> thm list list * local_theory
  val inductive_cases_i: ((bstring * Attrib.src list) * term list) list ->
    Proof.context -> thm list list * local_theory
  val add_inductive_i: bool -> bstring -> bool -> bool -> bool ->
    (string * typ option * mixfix) list ->
    (string * typ option) list -> ((bstring * Attrib.src list) * term) list -> thm list ->
      local_theory -> inductive_result * local_theory
  val add_inductive: bool -> bool -> (string * string option * mixfix) list ->
    (string * string option * mixfix) list ->
    ((bstring * Attrib.src list) * string) list -> (thmref * Attrib.src list) list ->
    local_theory -> inductive_result * local_theory
  val setup: theory -> theory
end;

structure InductivePackage: INDUCTIVE_PACKAGE =
struct


(** theory context references **)

val mono_name = "Orderings.mono";
val gfp_name = "FixedPoint.gfp";
val lfp_name = "FixedPoint.lfp";

val inductive_forall_name = "HOL.induct_forall";
val inductive_forall_def = thm "induct_forall_def";
val inductive_conj_name = "HOL.induct_conj";
val inductive_conj_def = thm "induct_conj_def";
val inductive_conj = thms "induct_conj";
val inductive_atomize = thms "induct_atomize";
val inductive_rulify = thms "induct_rulify";
val inductive_rulify_fallback = thms "induct_rulify_fallback";

val notTrueE = TrueI RSN (2, notE);
val notFalseI = Seq.hd (atac 1 notI);
val simp_thms' = map (fn s => mk_meta_eq (the (find_first
  (equal (term_of (read_cterm HOL.thy (s, propT))) o prop_of) simp_thms)))
  ["(~True) = False", "(~False) = True",
   "(True --> ?P) = ?P", "(False --> ?P) = True",
   "(?P & True) = ?P", "(True & ?P) = ?P"];



(** theory data **)

type inductive_result =
  {preds: term list, defs: thm list, elims: thm list, raw_induct: thm,
   induct: thm, intrs: thm list, mono: thm, unfold: thm};

type inductive_info =
  {names: string list, coind: bool} * inductive_result;

structure InductiveData = GenericDataFun
(struct
  val name = "HOL/inductive2";
  type T = inductive_info Symtab.table * thm list;

  val empty = (Symtab.empty, []);
  val extend = I;
  fun merge _ ((tab1, monos1), (tab2, monos2)) =
    (Symtab.merge (K true) (tab1, tab2), Drule.merge_rules (monos1, monos2));

  fun print generic (tab, monos) =
    [Pretty.strs ("(co)inductives:" ::
      map #1 (NameSpace.extern_table
        (Sign.const_space (Context.theory_of generic), tab))),  (* FIXME? *)
     Pretty.big_list "monotonicity rules:"
        (map (ProofContext.pretty_thm (Context.proof_of generic)) monos)]
    |> Pretty.chunks |> Pretty.writeln;
end);

val print_inductives = InductiveData.print o Context.Proof;


(* get and put data *)

val get_inductive = Symtab.lookup o #1 o InductiveData.get o Context.Proof;

fun the_inductive ctxt name =
  (case get_inductive ctxt name of
    NONE => error ("Unknown (co)inductive predicate " ^ quote name)
  | SOME info => info);

fun put_inductives names info = InductiveData.map (apfst (fn tab =>
  fold (fn name => Symtab.update_new (name, info)) names tab
    handle Symtab.DUP dup => error ("Duplicate definition of (co)inductive predicate " ^ quote dup)));



(** monotonicity rules **)

val get_monos = #2 o InductiveData.get o Context.Proof;
val map_monos = InductiveData.map o apsnd;

fun mk_mono thm =
  let
    fun eq2mono thm' = [(*standard*) (thm' RS (thm' RS eq_to_mono))] @
      (case concl_of thm of
          (_ $ (_ $ (Const ("Not", _) $ _) $ _)) => []
        | _ => [(*standard*) (thm' RS (thm' RS eq_to_mono2))]);
    val concl = concl_of thm
  in
    if can Logic.dest_equals concl then
      eq2mono (thm RS meta_eq_to_obj_eq)
    else if can (HOLogic.dest_eq o HOLogic.dest_Trueprop) concl then
      eq2mono thm
    else [thm]
  end;


(* attributes *)

val mono_add = Thm.declaration_attribute (map_monos o fold Drule.add_rule o mk_mono);
val mono_del = Thm.declaration_attribute (map_monos o fold Drule.del_rule o mk_mono);



(** misc utilities **)

val quiet_mode = ref false;
fun message s = if ! quiet_mode then () else writeln s;
fun clean_message s = if ! quick_and_dirty then () else message s;

val note_theorems = LocalTheory.notes Thm.theoremK;
val note_theorem = LocalTheory.note Thm.theoremK;

fun coind_prefix true = "co"
  | coind_prefix false = "";

fun log b m n = if m >= n then 0 else 1 + log b (b * m) n;

fun make_bool_args f g [] i = []
  | make_bool_args f g (x :: xs) i =
      (if i mod 2 = 0 then f x else g x) :: make_bool_args f g xs (i div 2);

fun make_bool_args' xs =
  make_bool_args (K HOLogic.false_const) (K HOLogic.true_const) xs;

fun find_arg T x [] = sys_error "find_arg"
  | find_arg T x ((p as (_, (SOME _, _))) :: ps) =
      apsnd (cons p) (find_arg T x ps)
  | find_arg T x ((p as (U, (NONE, y))) :: ps) =
      if T = U then (y, (U, (SOME x, y)) :: ps)
      else apsnd (cons p) (find_arg T x ps);

fun make_args Ts xs =
  map (fn (T, (NONE, ())) => Const ("arbitrary", T) | (_, (SOME t, ())) => t)
    (fold (fn (t, T) => snd o find_arg T t) xs (map (rpair (NONE, ())) Ts));

fun make_args' Ts xs Us =
  fst (fold_map (fn T => find_arg T ()) Us (Ts ~~ map (pair NONE) xs));

fun dest_predicate cs params t =
  let
    val k = length params;
    val (c, ts) = strip_comb t;
    val (xs, ys) = chop k ts;
    val i = find_index_eq c cs;
  in
    if xs = params andalso i >= 0 then
      SOME (c, i, ys, chop (length ys)
        (List.drop (binder_types (fastype_of c), k)))
    else NONE
  end;

fun mk_names a 0 = []
  | mk_names a 1 = [a]
  | mk_names a n = map (fn i => a ^ string_of_int i) (1 upto n);



(** process rules **)

local

fun err_in_rule thy name t msg =
  error (cat_lines ["Ill-formed introduction rule " ^ quote name,
    Sign.string_of_term thy t, msg]);

fun err_in_prem thy name t p msg =
  error (cat_lines ["Ill-formed premise", Sign.string_of_term thy p,
    "in introduction rule " ^ quote name, Sign.string_of_term thy t, msg]);

val bad_concl = "Conclusion of introduction rule must be an inductive predicate";

val bad_ind_occ = "Inductive predicate occurs in argument of inductive predicate";

val bad_app = "Inductive predicate must be applied to parameter(s) ";

fun atomize_term thy = MetaSimplifier.rewrite_term thy inductive_atomize [];

in

fun check_rule thy cs params ((name, att), rule) =
  let
    val params' = Term.variant_frees rule (Logic.strip_params rule);
    val frees = rev (map Free params');
    val concl = subst_bounds (frees, Logic.strip_assums_concl rule);
    val prems = map (curry subst_bounds frees) (Logic.strip_assums_hyp rule);
    val aprems = map (atomize_term thy) prems;
    val arule = list_all_free (params', Logic.list_implies (aprems, concl));

    fun check_ind err t = case dest_predicate cs params t of
        NONE => err (bad_app ^
          commas (map (Sign.string_of_term thy) params))
      | SOME (_, _, ys, _) =>
          if exists (fn c => exists (fn t => Logic.occs (c, t)) ys) cs
          then err bad_ind_occ else ();

    fun check_prem' prem t =
      if head_of t mem cs then
        check_ind (err_in_prem thy name rule prem) t
      else (case t of
          Abs (_, _, t) => check_prem' prem t
        | t $ u => (check_prem' prem t; check_prem' prem u)
        | _ => ());

    fun check_prem (prem, aprem) =
      if can HOLogic.dest_Trueprop aprem then check_prem' prem prem
      else err_in_prem thy name rule prem "Non-atomic premise";
  in
    (case concl of
       Const ("Trueprop", _) $ t =>
         if head_of t mem cs then
           (check_ind (err_in_rule thy name rule) t;
            List.app check_prem (prems ~~ aprems))
         else err_in_rule thy name rule bad_concl
     | _ => err_in_rule thy name rule bad_concl);
    ((name, att), arule)
  end;

val rulify =  (* FIXME norm_hhf *)
  hol_simplify inductive_conj
  #> hol_simplify inductive_rulify
  #> hol_simplify inductive_rulify_fallback
  (*#> standard*);

end;



(** proofs for (co)inductive predicates **)

(* prove monotonicity -- NOT subject to quick_and_dirty! *)

fun prove_mono predT fp_fun monos ctxt =
 (message "  Proving monotonicity ...";
  Goal.prove ctxt [] []   (*NO quick_and_dirty here!*)
    (HOLogic.mk_Trueprop
      (Const (mono_name, (predT --> predT) --> HOLogic.boolT) $ fp_fun))
    (fn _ => EVERY [rtac monoI 1,
      REPEAT (resolve_tac [le_funI, le_boolI'] 1),
      REPEAT (FIRST
        [atac 1,
         resolve_tac (List.concat (map mk_mono monos) @ get_monos ctxt) 1,
         etac le_funE 1, dtac le_boolD 1])]));


(* prove introduction rules *)

fun prove_intrs coind mono fp_def k intr_ts rec_preds_defs ctxt =
  let
    val _ = clean_message "  Proving the introduction rules ...";

    val unfold = funpow k (fn th => th RS fun_cong)
      (mono RS (fp_def RS
        (if coind then def_gfp_unfold else def_lfp_unfold)));

    fun select_disj 1 1 = []
      | select_disj _ 1 = [rtac disjI1]
      | select_disj n i = (rtac disjI2)::(select_disj (n - 1) (i - 1));

    val rules = [refl, TrueI, notFalseI, exI, conjI];

    val intrs = map_index (fn (i, intr) =>
      rulify (SkipProof.prove ctxt [] [] intr (fn _ => EVERY
       [rewrite_goals_tac rec_preds_defs,
        rtac (unfold RS iffD2) 1,
        EVERY1 (select_disj (length intr_ts) (i + 1)),
        (*Not ares_tac, since refl must be tried before any equality assumptions;
          backtracking may occur if the premises have extra variables!*)
        DEPTH_SOLVE_1 (resolve_tac rules 1 APPEND assume_tac 1)]))) intr_ts

  in (intrs, unfold) end;


(* prove elimination rules *)

fun prove_elims cs params intr_ts intr_names unfold rec_preds_defs ctxt =
  let
    val _ = clean_message "  Proving the elimination rules ...";

    val ([pname], ctxt') = Variable.variant_fixes ["P"] ctxt;
    val P = HOLogic.mk_Trueprop (Free (pname, HOLogic.boolT));

    fun dest_intr r =
      (the (dest_predicate cs params (HOLogic.dest_Trueprop (Logic.strip_assums_concl r))),
       Logic.strip_assums_hyp r, Logic.strip_params r);

    val intrs = map dest_intr intr_ts ~~ intr_names;

    val rules1 = [disjE, exE, FalseE];
    val rules2 = [conjE, FalseE, notTrueE];

    fun prove_elim c =
      let
        val Ts = List.drop (binder_types (fastype_of c), length params);
        val (anames, ctxt'') = Variable.variant_fixes (mk_names "a" (length Ts)) ctxt';
        val frees = map Free (anames ~~ Ts);

        fun mk_elim_prem ((_, _, us, _), ts, params') =
          list_all (params',
            Logic.list_implies (map (HOLogic.mk_Trueprop o HOLogic.mk_eq)
              (frees ~~ us) @ ts, P));
        val c_intrs = (List.filter (equal c o #1 o #1 o #1) intrs);
        val prems = HOLogic.mk_Trueprop (list_comb (c, params @ frees)) ::
           map mk_elim_prem (map #1 c_intrs)
      in
        (SkipProof.prove ctxt'' [] prems P
          (fn {prems, ...} => EVERY
            [cut_facts_tac [hd prems] 1,
             rewrite_goals_tac rec_preds_defs,
             dtac (unfold RS iffD1) 1,
             REPEAT (FIRSTGOAL (eresolve_tac rules1)),
             REPEAT (FIRSTGOAL (eresolve_tac rules2)),
             EVERY (map (fn prem =>
               DEPTH_SOLVE_1 (ares_tac [rewrite_rule rec_preds_defs prem, conjI] 1)) (tl prems))])
          |> rulify
          |> singleton (ProofContext.export ctxt'' ctxt),
         map #2 c_intrs)
      end

   in map prove_elim cs end;


(* derivation of simplified elimination rules *)

local

(*delete needless equality assumptions*)
val refl_thin = prove_goal HOL.thy "!!P. a = a ==> P ==> P" (fn _ => [assume_tac 1]);
val elim_rls = [asm_rl, FalseE, refl_thin, conjE, exE];
val elim_tac = REPEAT o Tactic.eresolve_tac elim_rls;

fun simp_case_tac solved ss i =
  EVERY' [elim_tac, asm_full_simp_tac ss, elim_tac, REPEAT o bound_hyp_subst_tac] i
  THEN_MAYBE (if solved then no_tac else all_tac);  (* FIXME !? *)

(*prop should have the form "P t" where P is an inductive predicate*)
val mk_cases_err = "mk_cases: proposition not an inductive predicate";

in

fun mk_cases ctxt prop =
  let
    val thy = ProofContext.theory_of ctxt;
    val ss = Simplifier.local_simpset_of ctxt;

    val c = #1 (Term.dest_Const (Term.head_of (HOLogic.dest_Trueprop
      (Logic.strip_imp_concl prop)))) handle TERM _ => error mk_cases_err;
    val (_, {elims, ...}) = the_inductive ctxt c;

    val cprop = Thm.cterm_of thy prop;
    val tac = ALLGOALS (simp_case_tac false ss) THEN prune_params_tac;
    fun mk_elim rl =
      Thm.implies_intr cprop (Tactic.rule_by_tactic tac (Thm.assume cprop RS rl))
      |> singleton (Variable.export (Variable.auto_fixes prop ctxt) ctxt);
  in
    (case get_first (try mk_elim) elims of
      SOME r => r
    | NONE => error (Pretty.string_of (Pretty.block
        [Pretty.str mk_cases_err, Pretty.fbrk, ProofContext.pretty_term ctxt prop])))
  end;

end;


(* inductive_cases *)

fun gen_inductive_cases prep_att prep_prop args lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val facts = args |> map (fn ((a, atts), props) =>
      ((a, map (prep_att thy) atts),
        map (Thm.no_attributes o single o mk_cases lthy o prep_prop lthy) props));
  in lthy |> note_theorems facts |>> map snd end;

val inductive_cases = gen_inductive_cases Attrib.intern_src ProofContext.read_prop;
val inductive_cases_i = gen_inductive_cases (K I) ProofContext.cert_prop;


fun ind_cases src =
  Method.syntax (Scan.repeat1 Args.prop) src
  #> (fn (ctxt, props) => Method.erule 0 (map (mk_cases ctxt) props));



(* prove induction rule *)

fun prove_indrule cs argTs bs xs rec_const params intr_ts mono
    fp_def rec_preds_defs ctxt =
  let
    val _ = clean_message "  Proving the induction rule ...";
    val thy = ProofContext.theory_of ctxt;

    (* predicates for induction rule *)

    val (pnames, ctxt') = Variable.variant_fixes (mk_names "P" (length cs)) ctxt;
    val preds = map Free (pnames ~~
      map (fn c => List.drop (binder_types (fastype_of c), length params) --->
        HOLogic.boolT) cs);

    (* transform an introduction rule into a premise for induction rule *)

    fun mk_ind_prem r =
      let
        fun subst s = (case dest_predicate cs params s of
            SOME (_, i, ys, (_, Ts)) =>
              let
                val k = length Ts;
                val bs = map Bound (k - 1 downto 0);
                val P = list_comb (List.nth (preds, i), ys @ bs);
                val Q = list_abs (mk_names "x" k ~~ Ts,
                  HOLogic.mk_binop inductive_conj_name (list_comb (s, bs), P))
              in (Q, case Ts of [] => SOME (s, P) | _ => NONE) end
          | NONE => (case s of
              (t $ u) => (fst (subst t) $ fst (subst u), NONE)
            | (Abs (a, T, t)) => (Abs (a, T, fst (subst t)), NONE)
            | _ => (s, NONE)));

        fun mk_prem (s, prems) = (case subst s of
              (_, SOME (t, u)) => t :: u :: prems
            | (t, _) => t :: prems);

        val SOME (_, i, ys, _) = dest_predicate cs params
          (HOLogic.dest_Trueprop (Logic.strip_assums_concl r))

      in list_all_free (Logic.strip_params r,
        Logic.list_implies (map HOLogic.mk_Trueprop (foldr mk_prem
          [] (map HOLogic.dest_Trueprop (Logic.strip_assums_hyp r))),
            HOLogic.mk_Trueprop (list_comb (List.nth (preds, i), ys))))
      end;

    val ind_prems = map mk_ind_prem intr_ts;

    (* make conclusions for induction rules *)

    val Tss = map (binder_types o fastype_of) preds;
    val (xnames, ctxt'') =
      Variable.variant_fixes (mk_names "x" (length (flat Tss))) ctxt';
    val mutual_ind_concl = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
        (map (fn (((xnames, Ts), c), P) =>
           let val frees = map Free (xnames ~~ Ts)
           in HOLogic.mk_imp
             (list_comb (c, params @ frees), list_comb (P, frees))
           end) (unflat Tss xnames ~~ Tss ~~ cs ~~ preds)));


    (* make predicate for instantiation of abstract induction rule *)

    val ind_pred = fold_rev lambda (bs @ xs) (foldr1 HOLogic.mk_conj
      (map_index (fn (i, P) => foldr HOLogic.mk_imp
         (list_comb (P, make_args' argTs xs (binder_types (fastype_of P))))
         (make_bool_args HOLogic.mk_not I bs i)) preds));

    val ind_concl = HOLogic.mk_Trueprop
      (HOLogic.mk_binrel "Orderings.less_eq" (rec_const, ind_pred));

    val raw_fp_induct = (mono RS (fp_def RS def_lfp_induct));

    val induct = SkipProof.prove ctxt'' [] ind_prems ind_concl
      (fn {prems, ...} => EVERY
        [rewrite_goals_tac [inductive_conj_def],
         DETERM (rtac raw_fp_induct 1),
         REPEAT (resolve_tac [le_funI, le_boolI] 1),
         rewrite_goals_tac (map mk_meta_eq [meet_fun_eq, meet_bool_eq] @ simp_thms'),
         (*This disjE separates out the introduction rules*)
         REPEAT (FIRSTGOAL (eresolve_tac [disjE, exE, FalseE])),
         (*Now break down the individual cases.  No disjE here in case
           some premise involves disjunction.*)
         REPEAT (FIRSTGOAL (etac conjE ORELSE' bound_hyp_subst_tac)),
         REPEAT (FIRSTGOAL
           (resolve_tac [conjI, impI] ORELSE' (etac notE THEN' atac))),
         EVERY (map (fn prem => DEPTH_SOLVE_1 (ares_tac [rewrite_rule
           (inductive_conj_def :: rec_preds_defs) prem, conjI, refl] 1)) prems)]);

    val lemma = SkipProof.prove ctxt'' [] []
      (Logic.mk_implies (ind_concl, mutual_ind_concl)) (fn _ => EVERY
        [rewrite_goals_tac rec_preds_defs,
         REPEAT (EVERY
           [REPEAT (resolve_tac [conjI, impI] 1),
            REPEAT (eresolve_tac [le_funE, le_boolE] 1),
            atac 1,
            rewrite_goals_tac simp_thms',
            atac 1])])

  in singleton (ProofContext.export ctxt'' ctxt) (induct RS lemma) end;



(** specification of (co)inductive predicates **)

fun mk_ind_def alt_name coind cs intr_ts monos
      params cnames_syn ctxt =
  let
    val fp_name = if coind then gfp_name else lfp_name;

    val argTs = fold (fn c => fn Ts => Ts @
      (List.drop (binder_types (fastype_of c), length params) \\ Ts)) cs [];
    val k = log 2 1 (length cs);
    val predT = replicate k HOLogic.boolT ---> argTs ---> HOLogic.boolT;
    val p :: xs = map Free (Variable.variant_frees ctxt intr_ts
      (("p", predT) :: (mk_names "x" (length argTs) ~~ argTs)));
    val bs = map Free (Variable.variant_frees ctxt (p :: xs @ intr_ts)
      (map (rpair HOLogic.boolT) (mk_names "b" k)));

    fun subst t = (case dest_predicate cs params t of
        SOME (_, i, ts, (Ts, Us)) =>
          let val zs = map Bound (length Us - 1 downto 0)
          in
            list_abs (map (pair "z") Us, list_comb (p,
              make_bool_args' bs i @ make_args argTs ((ts ~~ Ts) @ (zs ~~ Us))))
          end
      | NONE => (case t of
          t1 $ t2 => subst t1 $ subst t2
        | Abs (x, T, u) => Abs (x, T, subst u)
        | _ => t));

    (* transform an introduction rule into a conjunction  *)
    (*   [| p_i t; ... |] ==> p_j u                       *)
    (* is transformed into                                *)
    (*   b_j & x_j = u & p b_j t & ...                    *)

    fun transform_rule r =
      let
        val SOME (_, i, ts, (Ts, _)) = dest_predicate cs params
          (HOLogic.dest_Trueprop (Logic.strip_assums_concl r));
        val ps = make_bool_args HOLogic.mk_not I bs i @
          map HOLogic.mk_eq (make_args' argTs xs Ts ~~ ts) @
          map (subst o HOLogic.dest_Trueprop)
            (Logic.strip_assums_hyp r)
      in foldr (fn ((x, T), P) => HOLogic.exists_const T $ (Abs (x, T, P)))
        (if null ps then HOLogic.true_const else foldr1 HOLogic.mk_conj ps)
        (Logic.strip_params r)
      end

    (* make a disjunction of all introduction rules *)

    val fp_fun = fold_rev lambda (p :: bs @ xs)
      (if null intr_ts then HOLogic.false_const
       else foldr1 HOLogic.mk_disj (map transform_rule intr_ts));

    (* add definiton of recursive predicates to theory *)

    val rec_name = if alt_name = "" then
      space_implode "_" (map fst cnames_syn) else alt_name;

    val ((rec_const, (_, fp_def)), ctxt') = ctxt |>
      Variable.add_fixes (map (fst o dest_Free) params) |> snd |>
      fold Variable.declare_term intr_ts |>
      LocalTheory.def Thm.internalK
        ((rec_name, case cnames_syn of [(_, syn)] => syn | _ => NoSyn),
         (("", []), fold_rev lambda params
           (Const (fp_name, (predT --> predT) --> predT) $ fp_fun)));
    val fp_def' = Simplifier.rewrite (HOL_basic_ss addsimps [fp_def])
      (cterm_of (ProofContext.theory_of ctxt') (list_comb (rec_const, params)));
    val specs = if length cs < 2 then [] else
      map_index (fn (i, (name_mx, c)) =>
        let
          val Ts = List.drop (binder_types (fastype_of c), length params);
          val xs = map Free (Variable.variant_frees ctxt intr_ts
            (mk_names "x" (length Ts) ~~ Ts))
        in
          (name_mx, (("", []), fold_rev lambda (params @ xs)
            (list_comb (rec_const, params @ make_bool_args' bs i @
              make_args argTs (xs ~~ Ts)))))
        end) (cnames_syn ~~ cs);
    val (consts_defs, ctxt'') = fold_map (LocalTheory.def Thm.internalK) specs ctxt';
    val preds = (case cs of [_] => [rec_const] | _ => map #1 consts_defs);

    val mono = prove_mono predT fp_fun monos ctxt''

  in (ctxt'', rec_name, mono, fp_def', map (#2 o #2) consts_defs,
    list_comb (rec_const, params), preds, argTs, bs, xs)
  end;

fun add_ind_def verbose alt_name coind no_elim no_ind cs
    intros monos params cnames_syn ctxt =
  let
    val _ =
      if verbose then message ("Proofs for " ^ coind_prefix coind ^ "inductive predicate(s) " ^
        commas_quote (map fst cnames_syn)) else ();

    val cnames = map (Sign.full_name (ProofContext.theory_of ctxt) o #1) cnames_syn;
    val ((intr_names, intr_atts), intr_ts) = apfst split_list (split_list intros);

    val (ctxt1, rec_name, mono, fp_def, rec_preds_defs, rec_const, preds,
      argTs, bs, xs) = mk_ind_def alt_name coind cs intr_ts
        monos params cnames_syn ctxt;

    val (intrs, unfold) = prove_intrs coind mono fp_def (length bs + length xs)
      intr_ts rec_preds_defs ctxt1;
    val elims = if no_elim then [] else
      cnames ~~ map (apfst (singleton (ProofContext.export ctxt1 ctxt)))
        (prove_elims cs params intr_ts intr_names unfold rec_preds_defs ctxt1);
    val raw_induct = singleton (ProofContext.export ctxt1 ctxt)
      (if no_ind then Drule.asm_rl else
       if coind then ObjectLogic.rulify (rule_by_tactic
         (rewrite_tac [le_fun_def, le_bool_def] THEN
           fold_tac rec_preds_defs) (mono RS (fp_def RS def_coinduct)))
       else
         prove_indrule cs argTs bs xs rec_const params intr_ts mono fp_def
           rec_preds_defs ctxt1);
    val induct_cases = map (#1 o #1) intros;
    val ind_case_names = RuleCases.case_names induct_cases;
    val induct =
      if coind then
        (raw_induct, [RuleCases.case_names [rec_name],
          RuleCases.case_conclusion (rec_name, induct_cases),
          RuleCases.consumes 1])
      else if no_ind orelse length cs > 1 then
        (raw_induct, [ind_case_names, RuleCases.consumes 0])
      else (raw_induct RSN (2, rev_mp), [ind_case_names, RuleCases.consumes 1]);

    val (intrs', ctxt2) =
      ctxt1 |>
      note_theorems
        (map (NameSpace.qualified rec_name) intr_names ~~
         intr_atts ~~
         map (fn th => [([th], [Attrib.internal (ContextRules.intro_query NONE)])])
           (ProofContext.export ctxt1 ctxt intrs)) |>>
      map (hd o snd); (* FIXME? *)
    val (((_, elims'), (_, [induct'])), ctxt3) =
      ctxt2 |>
      note_theorem ((NameSpace.qualified rec_name "intros", []), intrs') ||>>
      fold_map (fn (name, (elim, cases)) =>
        note_theorem ((NameSpace.qualified (Sign.base_name name) "cases",
          [Attrib.internal (RuleCases.case_names cases),
           Attrib.internal (RuleCases.consumes 1),
           Attrib.internal (InductAttrib.cases_set name),
           Attrib.internal (ContextRules.elim_query NONE)]), [elim]) #>
        apfst (hd o snd)) elims ||>>
      note_theorem ((NameSpace.qualified rec_name (coind_prefix coind ^ "induct"),
        map Attrib.internal (#2 induct)), [rulify (#1 induct)]);

    val induct_att = if coind then InductAttrib.coinduct_set else InductAttrib.induct_set;
    val ctxt4 = if no_ind then ctxt3 else
      let val inducts = cnames ~~ ProjectRule.projects ctxt (1 upto length cnames) induct'
      in
        ctxt3 |>
        note_theorems [((NameSpace.qualified rec_name (coind_prefix coind ^ "inducts"), []),
          inducts |> map (fn (name, th) => ([th],
            [Attrib.internal ind_case_names,
             Attrib.internal (RuleCases.consumes 1),
             Attrib.internal (induct_att name)])))] |> snd
      end;

    val result =
      {preds = preds,
       defs = fp_def :: rec_preds_defs,
       mono = singleton (ProofContext.export ctxt1 ctxt) mono,
       unfold = singleton (ProofContext.export ctxt1 ctxt) unfold,
       intrs = intrs',
       elims = elims',
       raw_induct = rulify raw_induct,
       induct = induct'}

  in
    (result, LocalTheory.declaration (fn phi => (* FIXME *)
       (put_inductives cnames ({names = cnames, coind = coind}, result))) ctxt4)
  end;


(* external interfaces *)

fun add_inductive_i verbose alt_name coind no_elim no_ind cnames_syn pnames pre_intros monos ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val _ = Theory.requires thy "Inductive" (coind_prefix coind ^ "inductive definitions");

    val frees = fold (Term.add_frees o snd) pre_intros [];
    fun type_of s = (case AList.lookup op = frees s of
      NONE => error ("No such variable: " ^ s) | SOME T => T);

    val params = map
      (fn (s, SOME T) => Free (s, T) | (s, NONE) => Free (s, type_of s)) pnames;
    val cs = map
      (fn (s, SOME T, _) => Free (s, T) | (s, NONE, _) => Free (s, type_of s)) cnames_syn;
    val cnames_syn' = map (fn (s, _, mx) => (s, mx)) cnames_syn;

    fun close_rule (x, r) = (x, list_all_free (rev (fold_aterms
      (fn t as Free (v as (s, _)) =>
            if Variable.is_fixed ctxt s orelse member op = cs t orelse
              member op = params t then I else insert op = v
        | _ => I) r []), r));

    val intros = map (close_rule o check_rule thy cs params) pre_intros;
  in
    add_ind_def verbose alt_name coind no_elim no_ind cs intros monos
      params cnames_syn' ctxt
  end;

fun add_inductive verbose coind cnames_syn pnames_syn intro_srcs raw_monos ctxt =
  let
    val (_, ctxt') = Specification.read_specification (cnames_syn @ pnames_syn) [] ctxt;
    val intrs = map (fn spec => apsnd hd (hd (snd (fst
      (Specification.read_specification [] [apsnd single spec] ctxt'))))) intro_srcs;
    val pnames = map (fn (s, _, _) =>
      (s, SOME (ProofContext.infer_type ctxt' s))) pnames_syn;
    val cnames_syn' = map (fn (s, _, mx) =>
      (s, SOME (ProofContext.infer_type ctxt' s), mx)) cnames_syn;
    val (monos, ctxt'') = LocalTheory.theory_result (IsarCmd.apply_theorems raw_monos) ctxt;
  in
    add_inductive_i verbose "" coind false false cnames_syn' pnames intrs monos ctxt''
  end;



(** package setup **)

(* setup theory *)

val setup =
  InductiveData.init #>
  Method.add_methods [("ind_cases2", ind_cases,   (* FIXME "ind_cases" (?) *)
    "dynamic case analysis on predicates")] #>
  Attrib.add_attributes [("mono2", Attrib.add_del_args mono_add mono_del,   (* FIXME "mono" *)
    "declaration of monotonicity rule")];


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

(* FIXME tmp *)
fun flatten_specification specs = specs |> maps
  (fn (a, (concl, [])) => concl |> map
        (fn ((b, atts), [B]) =>
              if a = "" then ((b, atts), B)
              else if b = "" then ((a, atts), B)
              else error ("Illegal nested case names " ^ quote (NameSpace.append a b))
          | ((b, _), _) => error ("Illegal simultaneous specification " ^ quote b))
    | (a, _) => error ("Illegal local specification parameters for " ^ quote a));

fun ind_decl coind =
  P.opt_locale_target --
  P.fixes -- P.for_fixes --
  Scan.optional (P.$$$ "where" |-- P.!!! P.specification) [] --
  Scan.optional (P.$$$ "monos" |-- P.!!! P.xthms1) []
  >> (fn ((((loc, preds), params), specs), monos) =>
    Toplevel.local_theory loc
      (fn lthy => lthy
        |> add_inductive true coind preds params (flatten_specification specs) monos |> snd));

val inductiveP =
  OuterSyntax.command "inductive2" "define inductive predicates" K.thy_decl (ind_decl false);

val coinductiveP =
  OuterSyntax.command "coinductive2" "define coinductive predicates" K.thy_decl (ind_decl true);


val inductive_casesP =
  OuterSyntax.command "inductive_cases2"
    "create simplified instances of elimination rules (improper)" K.thy_script
    (P.opt_locale_target -- P.and_list1 P.spec
      >> (fn (loc, specs) => Toplevel.local_theory loc (snd o inductive_cases specs)));

val _ = OuterSyntax.add_keywords ["monos"];
val _ = OuterSyntax.add_parsers [inductiveP, coinductiveP, inductive_casesP];

end;

end;
