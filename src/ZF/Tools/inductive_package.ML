(*  Title:      ZF/Tools/inductive_package.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Fixedpoint definition module -- for Inductive/Coinductive Definitions

The functor will be instantiated for normal sums/products (inductive defs)
                         and non-standard sums/products (coinductive defs)

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations
*)

type inductive_result =
   {defs       : thm list,             (*definitions made in thy*)
    bnd_mono   : thm,                  (*monotonicity for the lfp definition*)
    dom_subset : thm,                  (*inclusion of recursive set in dom*)
    intrs      : thm list,             (*introduction rules*)
    elim       : thm,                  (*case analysis theorem*)
    mk_cases   : string -> thm,        (*generates case theorems*)
    induct     : thm,                  (*main induction rule*)
    mutual_induct : thm};              (*mutual induction rule*)


(*Functor's result signature*)
signature INDUCTIVE_PACKAGE =
sig
  (*Insert definitions for the recursive sets, which
     must *already* be declared as constants in parent theory!*)
  val add_inductive_i: bool -> term list * term ->
    ((bstring * term) * theory attribute list) list ->
    thm list * thm list * thm list * thm list -> theory -> theory * inductive_result
  val add_inductive_x: string list * string -> ((bstring * string) * theory attribute list) list
    -> thm list * thm list * thm list * thm list -> theory -> theory * inductive_result
  val add_inductive: string list * string ->
    ((bstring * string) * Args.src list) list ->
    (xstring * Args.src list) list * (xstring * Args.src list) list *
    (xstring * Args.src list) list * (xstring * Args.src list) list ->
    theory -> theory * inductive_result
end;


(*Declares functions to add fixedpoint/constructor defs to a theory.
  Recursive sets must *already* be declared as constants.*)
functor Add_inductive_def_Fun
    (structure Fp: FP and Pr : PR and CP: CARTPROD and Su : SU val coind: bool)
 : INDUCTIVE_PACKAGE =
struct

open Logic Ind_Syntax;

val co_prefix = if coind then "co" else "";


(* utils *)

(*make distinct individual variables a1, a2, a3, ..., an. *)
fun mk_frees a [] = []
  | mk_frees a (T::Ts) = Free(a,T) :: mk_frees (bump_string a) Ts;


(* add_inductive(_i) *)

(*internal version, accepting terms*)
fun add_inductive_i verbose (rec_tms, dom_sum)
  intr_specs (monos, con_defs, type_intrs, type_elims) thy =
let
  val _ = Theory.requires thy "Inductive" "(co)inductive definitions";
  val sign = sign_of thy;

  val (intr_names, intr_tms) = split_list (map fst intr_specs);
  val case_names = RuleCases.case_names intr_names;

  (*recT and rec_params should agree for all mutually recursive components*)
  val rec_hds = map head_of rec_tms;

  val dummy = assert_all is_Const rec_hds
          (fn t => "Recursive set not previously declared as constant: " ^
                   Sign.string_of_term sign t);

  (*Now we know they are all Consts, so get their names, type and params*)
  val rec_names = map (#1 o dest_Const) rec_hds
  and (Const(_,recT),rec_params) = strip_comb (hd rec_tms);

  val rec_base_names = map Sign.base_name rec_names;
  val dummy = assert_all Syntax.is_identifier rec_base_names
    (fn a => "Base name of recursive set not an identifier: " ^ a);

  local (*Checking the introduction rules*)
    val intr_sets = map (#2 o rule_concl_msg sign) intr_tms;
    fun intr_ok set =
        case head_of set of Const(a,recT) => a mem rec_names | _ => false;
  in
    val dummy =  assert_all intr_ok intr_sets
       (fn t => "Conclusion of rule does not name a recursive set: " ^
                Sign.string_of_term sign t);
  end;

  val dummy = assert_all is_Free rec_params
      (fn t => "Param in recursion term not a free variable: " ^
               Sign.string_of_term sign t);

  (*** Construct the fixedpoint definition ***)
  val mk_variant = variant (foldr add_term_names (intr_tms, []));

  val z' = mk_variant"z" and X' = mk_variant"X" and w' = mk_variant"w";

  fun dest_tprop (Const("Trueprop",_) $ P) = P
    | dest_tprop Q = error ("Ill-formed premise of introduction rule: " ^
                            Sign.string_of_term sign Q);

  (*Makes a disjunct from an introduction rule*)
  fun fp_part intr = (*quantify over rule's free vars except parameters*)
    let val prems = map dest_tprop (strip_imp_prems intr)
        val dummy = seq (fn rec_hd => seq (chk_prem rec_hd) prems) rec_hds
        val exfrees = term_frees intr \\ rec_params
        val zeq = FOLogic.mk_eq (Free(z',iT), #1 (rule_concl intr))
    in foldr FOLogic.mk_exists
             (exfrees, fold_bal FOLogic.mk_conj (zeq::prems))
    end;

  (*The Part(A,h) terms -- compose injections to make h*)
  fun mk_Part (Bound 0) = Free(X',iT) (*no mutual rec, no Part needed*)
    | mk_Part h         = Part_const $ Free(X',iT) $ Abs(w',iT,h);

  (*Access to balanced disjoint sums via injections*)
  val parts =
      map mk_Part (accesses_bal (fn t => Su.inl $ t, fn t => Su.inr $ t, Bound 0)
                                (length rec_tms));

  (*replace each set by the corresponding Part(A,h)*)
  val part_intrs = map (subst_free (rec_tms ~~ parts) o fp_part) intr_tms;

  val fp_abs = absfree(X', iT,
                   mk_Collect(z', dom_sum,
                              fold_bal FOLogic.mk_disj part_intrs));

  val fp_rhs = Fp.oper $ dom_sum $ fp_abs

  val dummy = seq (fn rec_hd => deny (rec_hd occs fp_rhs)
                             "Illegal occurrence of recursion operator")
           rec_hds;

  (*** Make the new theory ***)

  (*A key definition:
    If no mutual recursion then it equals the one recursive set.
    If mutual recursion then it differs from all the recursive sets. *)
  val big_rec_base_name = space_implode "_" rec_base_names;
  val big_rec_name = Sign.intern_const sign big_rec_base_name;


  val dummy = conditional verbose (fn () =>
    writeln ((if coind then "Coind" else "Ind") ^ "uctive definition " ^ quote big_rec_name));

  (*Forbid the inductive definition structure from clashing with a theory
    name.  This restriction may become obsolete as ML is de-emphasized.*)
  val dummy = deny (big_rec_base_name mem (Sign.stamp_names_of sign))
               ("Definition " ^ big_rec_base_name ^
                " would clash with the theory of the same name!");

  (*Big_rec... is the union of the mutually recursive sets*)
  val big_rec_tm = list_comb(Const(big_rec_name,recT), rec_params);

  (*The individual sets must already be declared*)
  val axpairs = map Logic.mk_defpair
        ((big_rec_tm, fp_rhs) ::
         (case parts of
             [_] => []                        (*no mutual recursion*)
           | _ => rec_tms ~~          (*define the sets as Parts*)
                  map (subst_atomic [(Free(X',iT),big_rec_tm)]) parts));

  (*tracing: print the fixedpoint definition*)
  val dummy = if !Ind_Syntax.trace then
              seq (writeln o Sign.string_of_term sign o #2) axpairs
          else ()

  (*add definitions of the inductive sets*)
  val thy1 = thy |> Theory.add_path big_rec_base_name
                 |> (#1 o PureThy.add_defs_i false (map Thm.no_attributes axpairs))


  (*fetch fp definitions from the theory*)
  val big_rec_def::part_rec_defs =
    map (get_def thy1)
        (case rec_names of [_] => rec_names
                         | _   => big_rec_base_name::rec_names);


  val sign1 = sign_of thy1;

  (********)
  val dummy = writeln "  Proving monotonicity...";

  val bnd_mono =
      prove_goalw_cterm []
        (cterm_of sign1
                  (FOLogic.mk_Trueprop (Fp.bnd_mono $ dom_sum $ fp_abs)))
        (fn _ =>
         [rtac (Collect_subset RS bnd_monoI) 1,
          REPEAT (ares_tac (basic_monos @ monos) 1)]);

  val dom_subset = standard (big_rec_def RS Fp.subs);

  val unfold = standard ([big_rec_def, bnd_mono] MRS Fp.Tarski);

  (********)
  val dummy = writeln "  Proving the introduction rules...";

  (*Mutual recursion?  Helps to derive subset rules for the
    individual sets.*)
  val Part_trans =
      case rec_names of
           [_] => asm_rl
         | _   => standard (Part_subset RS subset_trans);

  (*To type-check recursive occurrences of the inductive sets, possibly
    enclosed in some monotonic operator M.*)
  val rec_typechecks =
     [dom_subset] RL (asm_rl :: ([Part_trans] RL monos))
     RL [subsetD];

  (*Type-checking is hardest aspect of proof;
    disjIn selects the correct disjunct after unfolding*)
  fun intro_tacsf disjIn prems =
    [(*insert prems and underlying sets*)
     cut_facts_tac prems 1,
     DETERM (stac unfold 1),
     REPEAT (resolve_tac [Part_eqI,CollectI] 1),
     (*Now 2-3 subgoals: typechecking, the disjunction, perhaps equality.*)
     rtac disjIn 2,
     (*Not ares_tac, since refl must be tried before equality assumptions;
       backtracking may occur if the premises have extra variables!*)
     DEPTH_SOLVE_1 (resolve_tac [refl,exI,conjI] 2 APPEND assume_tac 2),
     (*Now solve the equations like Tcons(a,f) = Inl(?b4)*)
     rewrite_goals_tac con_defs,
     REPEAT (rtac refl 2),
     (*Typechecking; this can fail*)
     if !Ind_Syntax.trace then print_tac "The type-checking subgoal:"
     else all_tac,
     REPEAT (FIRSTGOAL (        dresolve_tac rec_typechecks
                        ORELSE' eresolve_tac (asm_rl::PartE::SigmaE2::
                                              type_elims)
                        ORELSE' hyp_subst_tac)),
     if !Ind_Syntax.trace then print_tac "The subgoal after monos, type_elims:"
     else all_tac,
     DEPTH_SOLVE (swap_res_tac (SigmaI::subsetI::type_intrs) 1)];

  (*combines disjI1 and disjI2 to get the corresponding nested disjunct...*)
  val mk_disj_rls =
      let fun f rl = rl RS disjI1
          and g rl = rl RS disjI2
      in  accesses_bal(f, g, asm_rl)  end;

  fun prove_intr (ct, tacsf) = prove_goalw_cterm part_rec_defs ct tacsf;

  val intrs = ListPair.map prove_intr
                (map (cterm_of sign1) intr_tms,
                 map intro_tacsf (mk_disj_rls(length intr_tms)))
               handle MetaSimplifier.SIMPLIFIER (msg,thm) => (print_thm thm; error msg);

  (********)
  val dummy = writeln "  Proving the elimination rule...";

  (*Breaks down logical connectives in the monotonic function*)
  val basic_elim_tac =
      REPEAT (SOMEGOAL (eresolve_tac (Ind_Syntax.elim_rls @ Su.free_SEs)
                ORELSE' bound_hyp_subst_tac))
      THEN prune_params_tac
          (*Mutual recursion: collapse references to Part(D,h)*)
      THEN fold_tac part_rec_defs;

  (*Elimination*)
  val elim = rule_by_tactic basic_elim_tac
                 (unfold RS Ind_Syntax.equals_CollectD)

  (*Applies freeness of the given constructors, which *must* be unfolded by
      the given defs.  Cannot simply use the local con_defs because
      con_defs=[] for inference systems.
    Proposition A should have the form t:Si where Si is an inductive set*)
  fun make_cases ss A =
    rule_by_tactic
      (basic_elim_tac THEN ALLGOALS (asm_full_simp_tac ss) THEN basic_elim_tac)
      (Thm.assume A RS elim)
      |> Drule.standard';
  fun mk_cases a = make_cases (*delayed evaluation of body!*)
    (simpset ()) (read_cterm (Thm.sign_of_thm elim) (a, propT));

  fun induction_rules raw_induct thy =
   let
     val dummy = writeln "  Proving the induction rule...";

     (*** Prove the main induction rule ***)

     val pred_name = "P";            (*name for predicate variables*)

     (*Used to make induction rules;
        ind_alist = [(rec_tm1,pred1),...] associates predicates with rec ops
        prem is a premise of an intr rule*)
     fun add_induct_prem ind_alist (prem as Const("Trueprop",_) $
                      (Const("op :",_)$t$X), iprems) =
          (case gen_assoc (op aconv) (ind_alist, X) of
               Some pred => prem :: FOLogic.mk_Trueprop (pred $ t) :: iprems
             | None => (*possibly membership in M(rec_tm), for M monotone*)
                 let fun mk_sb (rec_tm,pred) =
                             (rec_tm, Ind_Syntax.Collect_const$rec_tm$pred)
                 in  subst_free (map mk_sb ind_alist) prem :: iprems  end)
       | add_induct_prem ind_alist (prem,iprems) = prem :: iprems;

     (*Make a premise of the induction rule.*)
     fun induct_prem ind_alist intr =
       let val quantfrees = map dest_Free (term_frees intr \\ rec_params)
           val iprems = foldr (add_induct_prem ind_alist)
                              (Logic.strip_imp_prems intr,[])
           val (t,X) = Ind_Syntax.rule_concl intr
           val (Some pred) = gen_assoc (op aconv) (ind_alist, X)
           val concl = FOLogic.mk_Trueprop (pred $ t)
       in list_all_free (quantfrees, Logic.list_implies (iprems,concl)) end
       handle Bind => error"Recursion term not found in conclusion";

     (*Minimizes backtracking by delivering the correct premise to each goal.
       Intro rules with extra Vars in premises still cause some backtracking *)
     fun ind_tac [] 0 = all_tac
       | ind_tac(prem::prems) i =
             DEPTH_SOLVE_1 (ares_tac [prem, refl] i) THEN
             ind_tac prems (i-1);

     val pred = Free(pred_name, Ind_Syntax.iT --> FOLogic.oT);

     val ind_prems = map (induct_prem (map (rpair pred) rec_tms))
                         intr_tms;

     val dummy = if !Ind_Syntax.trace then
                 (writeln "ind_prems = ";
                  seq (writeln o Sign.string_of_term sign1) ind_prems;
                  writeln "raw_induct = "; print_thm raw_induct)
             else ();


     (*We use a MINIMAL simpset. Even FOL_ss contains too many simpules.
       If the premises get simplified, then the proofs could fail.*)
     val min_ss = empty_ss
           setmksimps (map mk_eq o ZF_atomize o gen_all)
           setSolver (mk_solver "minimal"
                      (fn prems => resolve_tac (triv_rls@prems)
                                   ORELSE' assume_tac
                                   ORELSE' etac FalseE));

     val quant_induct =
         prove_goalw_cterm part_rec_defs
           (cterm_of sign1
            (Logic.list_implies
             (ind_prems,
              FOLogic.mk_Trueprop (Ind_Syntax.mk_all_imp(big_rec_tm,pred)))))
           (fn prems =>
            [rtac (impI RS allI) 1,
             DETERM (etac raw_induct 1),
             (*Push Part inside Collect*)
             full_simp_tac (min_ss addsimps [Part_Collect]) 1,
             (*This CollectE and disjE separates out the introduction rules*)
             REPEAT (FIRSTGOAL (eresolve_tac [CollectE, disjE])),
             (*Now break down the individual cases.  No disjE here in case
               some premise involves disjunction.*)
             REPEAT (FIRSTGOAL (eresolve_tac [CollectE, exE, conjE]
                                ORELSE' hyp_subst_tac)),
             ind_tac (rev prems) (length prems) ]);

     val dummy = if !Ind_Syntax.trace then
                 (writeln "quant_induct = "; print_thm quant_induct)
             else ();


     (*** Prove the simultaneous induction rule ***)

     (*Make distinct predicates for each inductive set*)

     (*The components of the element type, several if it is a product*)
     val elem_type = CP.pseudo_type dom_sum;
     val elem_factors = CP.factors elem_type;
     val elem_frees = mk_frees "za" elem_factors;
     val elem_tuple = CP.mk_tuple Pr.pair elem_type elem_frees;

     (*Given a recursive set and its domain, return the "fsplit" predicate
       and a conclusion for the simultaneous induction rule.
       NOTE.  This will not work for mutually recursive predicates.  Previously
       a summand 'domt' was also an argument, but this required the domain of
       mutual recursion to invariably be a disjoint sum.*)
     fun mk_predpair rec_tm =
       let val rec_name = (#1 o dest_Const o head_of) rec_tm
           val pfree = Free(pred_name ^ "_" ^ Sign.base_name rec_name,
                            elem_factors ---> FOLogic.oT)
           val qconcl =
             foldr FOLogic.mk_all
               (elem_frees,
                FOLogic.imp $
                (Ind_Syntax.mem_const $ elem_tuple $ rec_tm)
                      $ (list_comb (pfree, elem_frees)))
       in  (CP.ap_split elem_type FOLogic.oT pfree,
            qconcl)
       end;

     val (preds,qconcls) = split_list (map mk_predpair rec_tms);

     (*Used to form simultaneous induction lemma*)
     fun mk_rec_imp (rec_tm,pred) =
         FOLogic.imp $ (Ind_Syntax.mem_const $ Bound 0 $ rec_tm) $
                          (pred $ Bound 0);

     (*To instantiate the main induction rule*)
     val induct_concl =
         FOLogic.mk_Trueprop
           (Ind_Syntax.mk_all_imp
            (big_rec_tm,
             Abs("z", Ind_Syntax.iT,
                 fold_bal FOLogic.mk_conj
                 (ListPair.map mk_rec_imp (rec_tms, preds)))))
     and mutual_induct_concl =
      FOLogic.mk_Trueprop(fold_bal FOLogic.mk_conj qconcls);

     val dummy = if !Ind_Syntax.trace then
                 (writeln ("induct_concl = " ^
                           Sign.string_of_term sign1 induct_concl);
                  writeln ("mutual_induct_concl = " ^
                           Sign.string_of_term sign1 mutual_induct_concl))
             else ();


     val lemma_tac = FIRST' [eresolve_tac [asm_rl, conjE, PartE, mp],
                             resolve_tac [allI, impI, conjI, Part_eqI],
                             dresolve_tac [spec, mp, Pr.fsplitD]];

     val need_mutual = length rec_names > 1;

     val lemma = (*makes the link between the two induction rules*)
       if need_mutual then
          (writeln "  Proving the mutual induction rule...";
           prove_goalw_cterm part_rec_defs
                 (cterm_of sign1 (Logic.mk_implies (induct_concl,
                                                   mutual_induct_concl)))
                 (fn prems =>
                  [cut_facts_tac prems 1,
                   REPEAT (rewrite_goals_tac [Pr.split_eq] THEN
                           lemma_tac 1)]))
       else (writeln "  [ No mutual induction rule needed ]";
             TrueI);

     val dummy = if !Ind_Syntax.trace then
                 (writeln "lemma = "; print_thm lemma)
             else ();


     (*Mutual induction follows by freeness of Inl/Inr.*)

     (*Simplification largely reduces the mutual induction rule to the
       standard rule*)
     val mut_ss =
         min_ss addsimps [Su.distinct, Su.distinct', Su.inl_iff, Su.inr_iff];

     val all_defs = con_defs @ part_rec_defs;

     (*Removes Collects caused by M-operators in the intro rules.  It is very
       hard to simplify
         list({v: tf. (v : t --> P_t(v)) & (v : f --> P_f(v))})
       where t==Part(tf,Inl) and f==Part(tf,Inr) to  list({v: tf. P_t(v)}).
       Instead the following rules extract the relevant conjunct.
     *)
     val cmonos = [subset_refl RS Collect_mono] RL monos
                   RLN (2,[rev_subsetD]);

     (*Minimizes backtracking by delivering the correct premise to each goal*)
     fun mutual_ind_tac [] 0 = all_tac
       | mutual_ind_tac(prem::prems) i =
           DETERM
            (SELECT_GOAL
               (
                (*Simplify the assumptions and goal by unfolding Part and
                  using freeness of the Sum constructors; proves all but one
                  conjunct by contradiction*)
                rewrite_goals_tac all_defs  THEN
                simp_tac (mut_ss addsimps [Part_iff]) 1  THEN
                IF_UNSOLVED (*simp_tac may have finished it off!*)
                  ((*simplify assumptions*)
                   (*some risk of excessive simplification here -- might have
                     to identify the bare minimum set of rewrites*)
                   full_simp_tac
                      (mut_ss addsimps conj_simps @ imp_simps @ quant_simps) 1
                   THEN
                   (*unpackage and use "prem" in the corresponding place*)
                   REPEAT (rtac impI 1)  THEN
                   rtac (rewrite_rule all_defs prem) 1  THEN
                   (*prem must not be REPEATed below: could loop!*)
                   DEPTH_SOLVE (FIRSTGOAL (ares_tac [impI] ORELSE'
                                           eresolve_tac (conjE::mp::cmonos))))
               ) i)
            THEN mutual_ind_tac prems (i-1);

     val mutual_induct_fsplit =
       if need_mutual then
         prove_goalw_cterm []
               (cterm_of sign1
                (Logic.list_implies
                   (map (induct_prem (rec_tms~~preds)) intr_tms,
                    mutual_induct_concl)))
               (fn prems =>
                [rtac (quant_induct RS lemma) 1,
                 mutual_ind_tac (rev prems) (length prems)])
       else TrueI;

     (** Uncurrying the predicate in the ordinary induction rule **)

     (*instantiate the variable to a tuple, if it is non-trivial, in order to
       allow the predicate to be "opened up".
       The name "x.1" comes from the "RS spec" !*)
     val inst =
         case elem_frees of [_] => I
            | _ => instantiate ([], [(cterm_of sign1 (Var(("x",1), Ind_Syntax.iT)),
                                      cterm_of sign1 elem_tuple)]);

     (*strip quantifier and the implication*)
     val induct0 = inst (quant_induct RS spec RSN (2,rev_mp));

     val Const ("Trueprop", _) $ (pred_var $ _) = concl_of induct0

     val induct = CP.split_rule_var(pred_var, elem_type-->FOLogic.oT, induct0)
                  |> standard
     and mutual_induct = CP.remove_split mutual_induct_fsplit

     val (thy', [induct', mutual_induct']) = thy |> PureThy.add_thms
      [((co_prefix ^ "induct", induct), [case_names, InductAttrib.induct_set_global big_rec_name]),
       (("mutual_induct", mutual_induct), [case_names])];
    in ((thy', induct'), mutual_induct')
    end;  (*of induction_rules*)

  val raw_induct = standard ([big_rec_def, bnd_mono] MRS Fp.induct)

  val ((thy2, induct), mutual_induct) =
    if not coind then induction_rules raw_induct thy1
    else (thy1 |> PureThy.add_thms [((co_prefix ^ "induct", raw_induct), [])] |> apsnd hd, TrueI)
  and defs = big_rec_def :: part_rec_defs


  val (thy3, ([bnd_mono', dom_subset', elim'], [defs', intrs'])) =
    thy2
    |> IndCases.declare big_rec_name make_cases
    |> PureThy.add_thms
      [(("bnd_mono", bnd_mono), []),
       (("dom_subset", dom_subset), []),
       (("cases", elim), [case_names, InductAttrib.cases_set_global big_rec_name])]
    |>>> (PureThy.add_thmss o map Thm.no_attributes)
        [("defs", defs),
         ("intros", intrs)];
  val (thy4, intrs'') =
    thy3 |> PureThy.add_thms ((intr_names ~~ intrs') ~~ map #2 intr_specs)
    |>> Theory.parent_path;
  in
    (thy4,
      {defs = defs',
       bnd_mono = bnd_mono',
       dom_subset = dom_subset',
       intrs = intrs'',
       elim = elim',
       mk_cases = mk_cases,
       induct = induct,
       mutual_induct = mutual_induct})
  end;


(*external version, accepting strings*)
fun add_inductive_x (srec_tms, sdom_sum) sintrs (monos, con_defs, type_intrs, type_elims) thy =
  let
    val read = Sign.simple_read_term (Theory.sign_of thy);
    val rec_tms = map (read Ind_Syntax.iT) srec_tms;
    val dom_sum = read Ind_Syntax.iT sdom_sum;
    val intr_tms = map (read propT o snd o fst) sintrs;
    val intr_specs = (map (fst o fst) sintrs ~~ intr_tms) ~~ map snd sintrs;
  in
    add_inductive_i true (rec_tms, dom_sum) intr_specs
      (monos, con_defs, type_intrs, type_elims) thy
  end


(*source version*)
fun add_inductive (srec_tms, sdom_sum) intr_srcs
    (raw_monos, raw_con_defs, raw_type_intrs, raw_type_elims) thy =
  let
    val intr_atts = map (map (Attrib.global_attribute thy) o snd) intr_srcs;
    val (thy', (((monos, con_defs), type_intrs), type_elims)) = thy
      |> IsarThy.apply_theorems raw_monos
      |>>> IsarThy.apply_theorems raw_con_defs
      |>>> IsarThy.apply_theorems raw_type_intrs
      |>>> IsarThy.apply_theorems raw_type_elims;
  in
    add_inductive_x (srec_tms, sdom_sum) (map fst intr_srcs ~~ intr_atts)
      (monos, con_defs, type_intrs, type_elims) thy'
  end;


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

fun mk_ind (((((doms, intrs), monos), con_defs), type_intrs), type_elims) =
  #1 o add_inductive doms (map P.triple_swap intrs) (monos, con_defs, type_intrs, type_elims);

val ind_decl =
  (P.$$$ "domains" |-- P.!!! (P.enum1 "+" P.term --
      ((P.$$$ "\\<subseteq>" || P.$$$ "<=") |-- P.term))) --
  (P.$$$ "intros" |--
    P.!!! (Scan.repeat1 (P.opt_thm_name ":" -- P.prop))) --
  Scan.optional (P.$$$ "monos" |-- P.!!! P.xthms1) [] --
  Scan.optional (P.$$$ "con_defs" |-- P.!!! P.xthms1) [] --
  Scan.optional (P.$$$ "type_intros" |-- P.!!! P.xthms1) [] --
  Scan.optional (P.$$$ "type_elims" |-- P.!!! P.xthms1) []
  >> (Toplevel.theory o mk_ind);

val inductiveP = OuterSyntax.command (co_prefix ^ "inductive")
  ("define " ^ co_prefix ^ "inductive sets") K.thy_decl ind_decl;

val _ = OuterSyntax.add_keywords
  ["domains", "intros", "monos", "con_defs", "type_intros", "type_elims"];
val _ = OuterSyntax.add_parsers [inductiveP];

end;

end;
