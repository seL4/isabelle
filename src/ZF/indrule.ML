(*  Title: 	ZF/indrule.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Induction rule module -- for Inductive/Coinductive Definitions

Proves a strong induction rule and a mutual induction rule
*)

signature INDRULE =
  sig
  val induct        : thm			(*main induction rule*)
  val mutual_induct : thm			(*mutual induction rule*)
  end;


functor Indrule_Fun
    (structure Inductive: sig include INDUCTIVE_ARG INDUCTIVE_I end
     and Pr: PR and Su : SU and Intr_elim: INTR_ELIM) : INDRULE  =
struct
open Logic Ind_Syntax Inductive Intr_elim;

val sign = sign_of thy;

val (Const(_,recT),rec_params) = strip_comb (hd rec_tms);

val big_rec_name = space_implode "_" rec_names;
val big_rec_tm = list_comb(Const(big_rec_name,recT), rec_params);

val _ = writeln "  Proving the induction rule...";

(*** Prove the main induction rule ***)

val pred_name = "P";		(*name for predicate variables*)

val big_rec_def::part_rec_defs = Intr_elim.defs;

(*Used to make induction rules;
   ind_alist = [(rec_tm1,pred1),...]  -- associates predicates with rec ops
   prem is a premise of an intr rule*)
fun add_induct_prem ind_alist (prem as Const("Trueprop",_) $ 
		 (Const("op :",_)$t$X), iprems) =
     (case gen_assoc (op aconv) (ind_alist, X) of
	  Some pred => prem :: mk_tprop (pred $ t) :: iprems
	| None => (*possibly membership in M(rec_tm), for M monotone*)
	    let fun mk_sb (rec_tm,pred) = (rec_tm, Collect_const$rec_tm$pred)
	    in  subst_free (map mk_sb ind_alist) prem :: iprems  end)
  | add_induct_prem ind_alist (prem,iprems) = prem :: iprems;

(*Make a premise of the induction rule.*)
fun induct_prem ind_alist intr =
  let val quantfrees = map dest_Free (term_frees intr \\ rec_params)
      val iprems = foldr (add_induct_prem ind_alist)
			 (strip_imp_prems intr,[])
      val (t,X) = rule_concl intr
      val (Some pred) = gen_assoc (op aconv) (ind_alist, X)
      val concl = mk_tprop (pred $ t)
  in list_all_free (quantfrees, list_implies (iprems,concl)) end
  handle Bind => error"Recursion term not found in conclusion";

(*Reduces backtracking by delivering the correct premise to each goal.
  Intro rules with extra Vars in premises still cause some backtracking *)
fun ind_tac [] 0 = all_tac
  | ind_tac(prem::prems) i = 
    	DEPTH_SOLVE_1 (ares_tac [prem, refl] i) THEN
	ind_tac prems (i-1);

val pred = Free(pred_name, iT-->oT);

val ind_prems = map (induct_prem (map (rpair pred) rec_tms)) intr_tms;

val quant_induct = 
    prove_goalw_cterm part_rec_defs 
      (cterm_of sign (list_implies (ind_prems, 
				    mk_tprop (mk_all_imp(big_rec_tm,pred)))))
      (fn prems =>
       [rtac (impI RS allI) 1,
	DETERM (etac raw_induct 1),
	(*Push Part inside Collect*)
	asm_full_simp_tac (FOL_ss addsimps [Part_Collect]) 1,
	REPEAT (FIRSTGOAL (eresolve_tac [CollectE, exE, conjE, disjE] ORELSE'
			   hyp_subst_tac)),
	ind_tac (rev prems) (length prems) ]);

(*** Prove the simultaneous induction rule ***)

(*Make distinct predicates for each inductive set*)

(*Sigmas and Cartesian products may nest ONLY to the right!*)
fun mk_pred_typ (t $ A $ Abs(_,_,B)) = 
        if t = Pr.sigma  then  iT --> mk_pred_typ B
                         else  iT --> oT
  | mk_pred_typ _           =  iT --> oT

(*Given a recursive set and its domain, return the "fsplit" predicate
  and a conclusion for the simultaneous induction rule.
  NOTE.  This will not work for mutually recursive predicates.  Previously
  a summand 'domt' was also an argument, but this required the domain of
  mutual recursion to invariably be a disjoint sum.*)
fun mk_predpair rec_tm = 
  let val rec_name = (#1 o dest_Const o head_of) rec_tm
      val T = mk_pred_typ dom_sum
      val pfree = Free(pred_name ^ "_" ^ rec_name, T)
      val frees = mk_frees "za" (binder_types T)
      val qconcl = 
	foldr mk_all (frees, 
		      imp $ (mem_const $ foldr1 (app Pr.pair) frees $ rec_tm)
			  $ (list_comb (pfree,frees)))
  in  (ap_split Pr.fsplit_const pfree (binder_types T), 
      qconcl)  
  end;

val (preds,qconcls) = split_list (map mk_predpair rec_tms);

(*Used to form simultaneous induction lemma*)
fun mk_rec_imp (rec_tm,pred) = 
    imp $ (mem_const $ Bound 0 $ rec_tm) $  (pred $ Bound 0);

(*To instantiate the main induction rule*)
val induct_concl = 
 mk_tprop(mk_all_imp(big_rec_tm,
		     Abs("z", iT, 
			 fold_bal (app conj) 
			          (map mk_rec_imp (rec_tms~~preds)))))
and mutual_induct_concl = mk_tprop(fold_bal (app conj) qconcls);

val lemma = (*makes the link between the two induction rules*)
    prove_goalw_cterm part_rec_defs 
	  (cterm_of sign (mk_implies (induct_concl,mutual_induct_concl)))
	  (fn prems =>
	   [cut_facts_tac prems 1, 
	    REPEAT (eresolve_tac [asm_rl, conjE, PartE, mp] 1
	     ORELSE resolve_tac [allI, impI, conjI, Part_eqI] 1
	     ORELSE dresolve_tac [spec, mp, Pr.fsplitD] 1)]);

(*Mutual induction follows by freeness of Inl/Inr.*)

(*Simplification largely reduces the mutual induction rule to the 
  standard rule*)
val mut_ss = 
    FOL_ss addsimps   [Su.distinct, Su.distinct', Su.inl_iff, Su.inr_iff];

val all_defs = con_defs@part_rec_defs;

(*Removes Collects caused by M-operators in the intro rules.  It is very
  hard to simplify
    list({v: tf. (v : t --> P_t(v)) & (v : f --> P_f(v))}) 
  where t==Part(tf,Inl) and f==Part(tf,Inr) to  list({v: tf. P_t(v)}).
  Instead the following rules extract the relevant conjunct.
*)
val cmonos = [subset_refl RS Collect_mono] RL monos RLN (2,[rev_subsetD]);

(*Avoids backtracking by delivering the correct premise to each goal*)
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
	     ((*simplify assumptions, but don't accept new rewrite rules!*)
	      asm_full_simp_tac (mut_ss setmksimps K[]) 1  THEN
	      (*unpackage and use "prem" in the corresponding place*)
	      REPEAT (rtac impI 1)  THEN
	      rtac (rewrite_rule all_defs prem) 1  THEN
	      (*prem must not be REPEATed below: could loop!*)
	      DEPTH_SOLVE (FIRSTGOAL (ares_tac [impI] ORELSE' 
				      eresolve_tac (conjE::mp::cmonos))))
	  ) i)
       THEN mutual_ind_tac prems (i-1);

val _ = writeln "  Proving the mutual induction rule...";

val mutual_induct_fsplit = 
    prove_goalw_cterm []
	  (cterm_of sign
	   (list_implies (map (induct_prem (rec_tms~~preds)) intr_tms,
			  mutual_induct_concl)))
	  (fn prems =>
	   [rtac (quant_induct RS lemma) 1,
	    mutual_ind_tac (rev prems) (length prems)]);

(*Attempts to remove all occurrences of fsplit*)
val fsplit_tac =
    REPEAT (SOMEGOAL (FIRST' [rtac Pr.fsplitI, 
			      dtac Pr.fsplitD,
			      etac Pr.fsplitE,	(*apparently never used!*)
			      bound_hyp_subst_tac]))
    THEN prune_params_tac;

(*strip quantifier*)
val induct = standard (quant_induct RS spec RSN (2,rev_mp));

val mutual_induct = rule_by_tactic fsplit_tac mutual_induct_fsplit;

end;
