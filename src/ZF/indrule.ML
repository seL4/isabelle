(*  Title:      ZF/indrule.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Induction rule module -- for Inductive/Coinductive Definitions

Proves a strong induction rule and a mutual induction rule
*)

signature INDRULE =
  sig
  val induct        : thm                       (*main induction rule*)
  val mutual_induct : thm                       (*mutual induction rule*)
  end;


functor Indrule_Fun
    (structure Inductive: sig include INDUCTIVE_ARG INDUCTIVE_I end
     and Pr: PR and CP: CARTPROD and Su : SU and 
     Intr_elim: sig include INTR_ELIM INTR_ELIM_AUX end) : INDRULE  =
let

val sign = sign_of Inductive.thy;

val (Const(_,recT),rec_params) = strip_comb (hd Inductive.rec_tms);

val big_rec_name =
  Sign.intern_const sign (space_implode "_" (map Sign.base_name Intr_elim.rec_names));

val big_rec_tm = list_comb(Const(big_rec_name,recT), rec_params);

val _ = writeln "  Proving the induction rule...";

(*** Prove the main induction rule ***)

val pred_name = "P";            (*name for predicate variables*)

val big_rec_def::part_rec_defs = Intr_elim.defs;

(*Used to make induction rules;
   ind_alist = [(rec_tm1,pred1),...]  -- associates predicates with rec ops
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

val ind_prems = map (induct_prem (map (rpair pred) Inductive.rec_tms)) 
                    Inductive.intr_tms;

val _ = if !Ind_Syntax.trace then 
            (writeln "ind_prems = ";
	     seq (writeln o Sign.string_of_term sign) ind_prems;
	     writeln "raw_induct = "; print_thm Intr_elim.raw_induct)
        else ();


(*We use a MINIMAL simpset because others (such as FOL_ss) contain too many
  simplifications.  If the premises get simplified, then the proofs could 
  fail.  *)
val min_ss = empty_ss
      setmksimps (map mk_meta_eq o ZF_atomize o gen_all)
      setSolver  (fn prems => resolve_tac (triv_rls@prems) 
                              ORELSE' assume_tac
                              ORELSE' etac FalseE);

val quant_induct = 
    prove_goalw_cterm part_rec_defs 
      (cterm_of sign 
       (Logic.list_implies (ind_prems, 
                FOLogic.mk_Trueprop (Ind_Syntax.mk_all_imp(big_rec_tm,pred)))))
      (fn prems =>
       [rtac (impI RS allI) 1,
        DETERM (etac Intr_elim.raw_induct 1),
        (*Push Part inside Collect*)
        full_simp_tac (min_ss addsimps [Part_Collect]) 1,
        (*This CollectE and disjE separates out the introduction rules*)
	REPEAT (FIRSTGOAL (eresolve_tac [CollectE, disjE])),
	(*Now break down the individual cases.  No disjE here in case
          some premise involves disjunction.*)
        REPEAT (FIRSTGOAL (eresolve_tac [CollectE, exE, conjE] 
                           ORELSE' hyp_subst_tac)),
        ind_tac (rev prems) (length prems) ]);

val _ = if !Ind_Syntax.trace then 
            (writeln "quant_induct = "; print_thm quant_induct)
        else ();


(*** Prove the simultaneous induction rule ***)

(*Make distinct predicates for each inductive set*)

(*The components of the element type, several if it is a product*)
val elem_type = CP.pseudo_type Inductive.dom_sum;
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

val (preds,qconcls) = split_list (map mk_predpair Inductive.rec_tms);

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
            fold_bal (app FOLogic.conj) 
            (ListPair.map mk_rec_imp (Inductive.rec_tms,preds)))))
and mutual_induct_concl =
 FOLogic.mk_Trueprop(fold_bal (app FOLogic.conj) qconcls);

val _ = if !Ind_Syntax.trace then 
            (writeln ("induct_concl = " ^
		      Sign.string_of_term sign induct_concl);
             writeln ("mutual_induct_concl = " ^
		      Sign.string_of_term sign mutual_induct_concl))
        else ();


val lemma_tac = FIRST' [eresolve_tac [asm_rl, conjE, PartE, mp],
                        resolve_tac [allI, impI, conjI, Part_eqI],
                        dresolve_tac [spec, mp, Pr.fsplitD]];

val need_mutual = length Intr_elim.rec_names > 1;

val lemma = (*makes the link between the two induction rules*)
  if need_mutual then
     (writeln "  Proving the mutual induction rule...";
      prove_goalw_cterm part_rec_defs 
	    (cterm_of sign (Logic.mk_implies (induct_concl,
					      mutual_induct_concl)))
	    (fn prems =>
	     [cut_facts_tac prems 1, 
	      REPEAT (rewrite_goals_tac [Pr.split_eq] THEN
		      lemma_tac 1)]))
  else (writeln "  [ No mutual induction rule needed ]";
        TrueI);

val _ = if !Ind_Syntax.trace then 
            (writeln "lemma = "; print_thm lemma)
        else ();


(*Mutual induction follows by freeness of Inl/Inr.*)

(*Simplification largely reduces the mutual induction rule to the 
  standard rule*)
val mut_ss = 
    min_ss addsimps [Su.distinct, Su.distinct', Su.inl_iff, Su.inr_iff];

val all_defs = Inductive.con_defs @ part_rec_defs;

(*Removes Collects caused by M-operators in the intro rules.  It is very
  hard to simplify
    list({v: tf. (v : t --> P_t(v)) & (v : f --> P_f(v))}) 
  where t==Part(tf,Inl) and f==Part(tf,Inr) to  list({v: tf. P_t(v)}).
  Instead the following rules extract the relevant conjunct.
*)
val cmonos = [subset_refl RS Collect_mono] RL Inductive.monos
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
                 (mut_ss addsimps (conj_simps @ imp_simps @ quant_simps)) 1
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
          (cterm_of sign
           (Logic.list_implies 
              (map (induct_prem (Inductive.rec_tms~~preds)) Inductive.intr_tms,
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
       | _ => instantiate ([], [(cterm_of sign (Var(("x",1), Ind_Syntax.iT)), 
                                 cterm_of sign elem_tuple)]);

(*strip quantifier and the implication*)
val induct0 = inst (quant_induct RS spec RSN (2,rev_mp));

val Const ("Trueprop", _) $ (pred_var $ _) = concl_of induct0

in
  struct
  (*strip quantifier*)
  val induct = CP.split_rule_var(pred_var, elem_type-->FOLogic.oT, induct0) 
               |> standard;

  (*Just "True" unless there's true mutual recursion.  This saves storage.*)
  val mutual_induct = CP.remove_split mutual_induct_fsplit
  end
end;
