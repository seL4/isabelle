(*  Title:      HOL/Tools/function_package/fundef_proof.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Internal proofs.
*)


signature FUNDEF_PROOF =
sig

    val mk_partial_rules_curried : theory -> thm list -> FundefCommon.curry_info option -> FundefCommon.prep_result 
				   -> thm -> thm list -> FundefCommon.fundef_result
end


structure FundefProof : FUNDEF_PROOF = 
struct

open FundefCommon
open FundefAbbrev

(* Theory dependencies *)
val subsetD = thm "subsetD"
val subset_refl = thm "subset_refl"
val split_apply = thm "Product_Type.split"
val wf_induct_rule = thm "wf_induct_rule";
val Pair_inject = thm "Product_Type.Pair_inject";

val acc_induct_rule = thm "acc_induct_rule" (* from: Accessible_Part *)
val acc_downward = thm "acc_downward"
val accI = thm "accI"

val ex1_implies_ex = thm "fundef_ex1_existence"   (* from: Fundef.thy *) 
val ex1_implies_un = thm "fundef_ex1_uniqueness"
val ex1_implies_iff = thm "fundef_ex1_iff"
val acc_subset_induct = thm "acc_subset_induct"





    
fun mk_simp thy names f_iff graph_is_function clause valthm =
    let
	val Names {R, acc_R, domT, z, ...} = names
	val ClauseInfo {qs, cqs, gs, lhs, rhs, ...} = clause
	val lhs_acc = cterm_of thy (Trueprop (mk_mem (lhs, acc_R))) (* "lhs : acc R" *)
	val z_smaller = cterm_of thy (Trueprop (mk_relmemT domT domT (z, lhs) R)) (* "(z, lhs) : R" *)
    in
	((assume z_smaller) RS ((assume lhs_acc) RS acc_downward))
	    |> (fn it => it COMP graph_is_function)
	    |> implies_intr z_smaller
	    |> forall_intr (cterm_of thy z)
	    |> (fn it => it COMP valthm)
	    |> implies_intr lhs_acc 
	    |> asm_simplify (HOL_basic_ss addsimps [f_iff])
	    |> fold forall_intr cqs
	    |> forall_elim_vars 0
	    |> varifyT
	    |> Drule.close_derivation
    end




fun mk_partial_induct_rule thy names complete_thm clauses =
    let
	val Names {domT, R, acc_R, x, z, a, P, D, ...} = names

	val x_D = assume (cterm_of thy (Trueprop (mk_mem (x, D))))
	val a_D = cterm_of thy (Trueprop (mk_mem (a, D)))

	val D_subset = cterm_of thy (Trueprop (mk_subset domT D acc_R))

	val D_dcl = (* "!!x z. [| x: D; (z,x):R |] ==> z:D" *)
	    mk_forall x
		      (mk_forall z (Logic.mk_implies (Trueprop (mk_mem (x, D)),
						      Logic.mk_implies (mk_relmem (z, x) R,
									Trueprop (mk_mem (z, D))))))
		      |> cterm_of thy


	(* Inductive Hypothesis: !!z. (z,x):R ==> P z *)
	val ihyp = all domT $ Abs ("z", domT, 
				   implies $ Trueprop (mk_relmemT domT domT (Bound 0, x) R)
					   $ Trueprop (P $ Bound 0))
		       |> cterm_of thy

	val aihyp = assume ihyp |> forall_elim_vars 0

	fun prove_case clause =
	    let
		val ClauseInfo {qs, cqs, ags, gs, lhs, rhs, case_hyp, RCs, ...} = clause
								       
		val replace_x_ss = HOL_basic_ss addsimps [case_hyp]
		val lhs_D = simplify replace_x_ss x_D (* lhs : D *)
		val sih = full_simplify replace_x_ss aihyp
					
					(* FIXME: Variable order destroyed by forall_intr_vars *)
		val P_recs = map (fn RCInfo {lRI, RIvs, ...} => (lRI RS sih) |> forall_intr_vars) RCs   (*  [P rec1, P rec2, ... ]  *)
			     
		val step = Trueprop (P $ lhs)
				    |> fold_rev (curry Logic.mk_implies o prop_of) P_recs
				    |> fold_rev (curry Logic.mk_implies) gs
				    |> curry Logic.mk_implies (Trueprop (mk_mem (lhs, D)))
				    |> fold_rev mk_forall qs
				    |> cterm_of thy
			   
		val P_lhs = assume step
				   |> fold forall_elim cqs
				   |> implies_elim_swp lhs_D 
				   |> fold_rev implies_elim_swp ags
				   |> fold implies_elim_swp P_recs
			    
		val res = cterm_of thy (Trueprop (P $ x))
				   |> Simplifier.rewrite replace_x_ss
				   |> symmetric (* P lhs == P x *)
				   |> (fn eql => equal_elim eql P_lhs) (* "P x" *)
				   |> implies_intr (cprop_of case_hyp)
				   |> fold_rev (implies_intr o cprop_of) ags
				   |> fold_rev forall_intr cqs
	    in
		(res, step)
	    end

	val (cases, steps) = split_list (map prove_case clauses)

	val istep =  complete_thm
			 |> fold (curry op COMP) cases (*  P x  *)
			 |> implies_intr ihyp
			 |> implies_intr (cprop_of x_D)
			 |> forall_intr (cterm_of thy x)
			   
	val subset_induct_rule = 
	    acc_subset_induct
		|> (curry op COMP) (assume D_subset)
		|> (curry op COMP) (assume D_dcl)
		|> (curry op COMP) (assume a_D)
		|> (curry op COMP) istep
		|> fold_rev implies_intr steps
		|> implies_intr a_D
		|> implies_intr D_dcl
		|> implies_intr D_subset
		|> forall_intr_frees
		|> forall_elim_vars 0

	val simple_induct_rule =
	    subset_induct_rule
		|> instantiate' [] [SOME (cterm_of thy acc_R)]
		|> (curry op COMP) subset_refl
		|> (curry op COMP) (acc_downward
					|> (instantiate' [SOME (ctyp_of thy domT)]
							 (map (SOME o cterm_of thy) [x, R, z]))
					|> forall_intr (cterm_of thy z)
					|> forall_intr (cterm_of thy x))
    in
	(varifyT subset_induct_rule, varifyT simple_induct_rule)
    end





(***********************************************)
(* Compat thms are stored in normal form (with vars) *)

(* replace this by a table later*)
fun store_compat_thms 0 cts = []
  | store_compat_thms n cts =
    let
	val (cts1, cts2) = chop n cts
    in
	(cts1 :: store_compat_thms (n - 1) cts2)
    end


(* needs i <= j *)
fun lookup_compat_thm i j cts =
    nth (nth cts (i - 1)) (j - i)
(***********************************************)


(* recover the order of Vars *)
fun get_var_order thy clauses =
    map (fn (ClauseInfo {cqs,...}, ClauseInfo {cqs',...}) => map (cterm_of thy o free_to_var o term_of) (cqs @ cqs')) (upairs clauses)


(* Returns "Gsi, Gsj', lhs_i = lhs_j' |-- rhs_j'_f = rhs_i_f" *)
(* if j < i, then turn around *)
fun get_compat_thm thy cts clausei clausej =
    let 
	val ClauseInfo {no=i, cqs=qsi, ags=gsi, lhs=lhsi, ...} = clausei
	val ClauseInfo {no=j, cqs'=qsj', ags'=gsj', lhs'=lhsj', ...} = clausej

	val lhsi_eq_lhsj' = cterm_of thy (Trueprop (mk_eq (lhsi, lhsj')))
    in if j < i then
	   let 
	       val (var_ord, compat) = lookup_compat_thm j i cts
	   in
	       compat         (* "!!qj qi'. Gsj => Gsi' => lhsj = lhsi' ==> rhsj = rhsi'" *)
		|> instantiate ([],(var_ord ~~ (qsj' @ qsi))) (* "Gsj' => Gsi => lhsj' = lhsi ==> rhsj' = rhsi" *)
		|> fold implies_elim_swp gsj'
		|> fold implies_elim_swp gsi
		|> implies_elim_swp ((assume lhsi_eq_lhsj') RS sym) (* "Gsj', Gsi, lhsi = lhsj' |-- rhsj' = rhsi" *)
	   end
       else
	   let
	       val (var_ord, compat) = lookup_compat_thm i j cts
	   in
	       compat        (* "?Gsi => ?Gsj' => ?lhsi = ?lhsj' ==> ?rhsi = ?rhsj'" *)
	         |> instantiate ([], (var_ord ~~ (qsi @ qsj'))) (* "Gsi => Gsj' => lhsi = lhsj' ==> rhsi = rhsj'" *)
		 |> fold implies_elim_swp gsi
		 |> fold implies_elim_swp gsj'
		 |> implies_elim_swp (assume lhsi_eq_lhsj')
		 |> (fn thm => thm RS sym) (* "Gsi, Gsj', lhsi = lhsj' |-- rhsj' = rhsi" *)
	   end
    end





(* Generates the replacement lemma with primed variables. A problem here is that one should not do
the complete requantification at the end to replace the variables. One should find a way to be more efficient
here. *)
fun mk_replacement_lemma thy (names:naming_context) ih_elim clause = 
    let 
	val Names {fvar, f, x, y, h, Pbool, G, ranT, domT, R, ...} = names 
	val ClauseInfo {qs,cqs,ags,lhs,rhs,cqs',ags',case_hyp, RCs, tree, ...} = clause

	val ih_elim_case = full_simplify (HOL_basic_ss addsimps [case_hyp]) ih_elim

	val Ris = map (fn RCInfo {lRIq, ...} => lRIq) RCs
	val h_assums = map (fn RCInfo {Gh, ...} => Gh) RCs
	val h_assums' = map (fn RCInfo {Gh', ...} => Gh') RCs

	val ih_elim_case_inst = instantiate' [] [NONE, SOME (cterm_of thy h)] ih_elim_case (* Should be done globally *)

	val (eql, _) = FundefCtxTree.rewrite_by_tree thy f h ih_elim_case_inst (Ris ~~ h_assums) tree

	val replace_lemma = (eql RS meta_eq_to_obj_eq)
				|> implies_intr (cprop_of case_hyp)
				|> fold_rev (implies_intr o cprop_of) h_assums
				|> fold_rev (implies_intr o cprop_of) ags
				|> fold_rev forall_intr cqs
				|> fold forall_elim cqs'
				|> fold implies_elim_swp ags'
				|> fold implies_elim_swp h_assums'
    in
	replace_lemma
    end




fun mk_uniqueness_clause thy names compat_store clausei clausej RLj =
    let
	val Names {f, h, y, ...} = names
	val ClauseInfo {no=i, lhs=lhsi, case_hyp, ...} = clausei
	val ClauseInfo {no=j, ags'=gsj', lhs'=lhsj', rhs'=rhsj', RCs=RCsj, ordcqs'=ordcqs'j, ...} = clausej

	val rhsj'h = Pattern.rewrite_term thy [(f,h)] [] rhsj'
	val compat = get_compat_thm thy compat_store clausei clausej
	val Ghsj' = map (fn RCInfo {Gh', ...} => Gh') RCsj

	val y_eq_rhsj'h = assume (cterm_of thy (Trueprop (mk_eq (y, rhsj'h))))
	val lhsi_eq_lhsj' = assume (cterm_of thy (Trueprop (mk_eq (lhsi, lhsj')))) (* lhs_i = lhs_j' |-- lhs_i = lhs_j'	*)

	val eq_pairs = assume (cterm_of thy (Trueprop (mk_eq (mk_prod (lhsi, y), mk_prod (lhsj',rhsj'h)))))
    in
	(trans OF [case_hyp, lhsi_eq_lhsj']) (* lhs_i = lhs_j' |-- x = lhs_j' *)
        |> implies_elim RLj (* Rj1' ... Rjk', lhs_i = lhs_j' |-- rhs_j'_h = rhs_j'_f *)
	|> (fn it => trans OF [it, compat]) (* lhs_i = lhs_j', Gj', Rj1' ... Rjk' |-- rhs_j'_h = rhs_i_f *)
	|> (fn it => trans OF [y_eq_rhsj'h, it]) (* lhs_i = lhs_j', Gj', Rj1' ... Rjk', y = rhs_j_h' |-- y = rhs_i_f *)
	|> implies_intr (cprop_of y_eq_rhsj'h)
	|> implies_intr (cprop_of lhsi_eq_lhsj') (* Gj', Rj1' ... Rjk' |-- [| lhs_i = lhs_j', y = rhs_j_h' |] ==> y = rhs_i_f *)
	|> (fn it => Drule.compose_single(it, 2, Pair_inject)) (* Gj', Rj1' ... Rjk' |-- (lhs_i, y) = (lhs_j', rhs_j_h') ==> y = rhs_i_f *)
	|> implies_elim_swp eq_pairs
	|> fold_rev (implies_intr o cprop_of) Ghsj' 
	|> fold_rev (implies_intr o cprop_of) gsj' (* Gj', Rj1', ..., Rjk' ==> (lhs_i, y) = (lhs_j', rhs_j_h') ==> y = rhs_i_f *)
	|> implies_intr (cprop_of eq_pairs)
	|> fold_rev forall_intr ordcqs'j
    end



fun mk_uniqueness_case thy names ihyp ih_intro G_cases compat_store clauses rep_lemmas clausei =
    let
	val Names {x, y, G, fvar, f, ranT, ...} = names
	val ClauseInfo {lhs, rhs, qs, cqs, ags, case_hyp, lGI, RCs, ...} = clausei

	val ih_intro_case = full_simplify (HOL_basic_ss addsimps [case_hyp]) ih_intro

	fun prep_RC (RCInfo {lRIq,RIvs, ...}) = lRIq
						    |> fold (forall_elim o cterm_of thy o Free) RIvs
						    |> (fn it => it RS ih_intro_case)
						    |> fold_rev (forall_intr o cterm_of thy o Free) RIvs

	val existence = lGI |> instantiate ([], [(cterm_of thy (free_to_var fvar), cterm_of thy f)])
			    |> fold (curry op COMP o prep_RC) RCs 


	val a = cterm_of thy (mk_prod (lhs, y))
	val P = cterm_of thy (mk_eq (y, rhs))
	val a_in_G = assume (cterm_of thy (Trueprop (mk_mem (term_of a, G))))

	val unique_clauses = map2 (mk_uniqueness_clause thy names compat_store clausei) clauses rep_lemmas

	val uniqueness = G_cases 
			     |> instantiate' [] [SOME a, SOME P]
			     |> implies_elim_swp a_in_G
			     |> fold implies_elim_swp unique_clauses
			     |> implies_intr (cprop_of a_in_G)
			     |> forall_intr (cterm_of thy y) 

	val P2 = cterm_of thy (lambda y (mk_mem (mk_prod (lhs, y), G))) (* P2 y := (lhs, y): G *)

	val exactly_one =
	    ex1I |> instantiate' [SOME (ctyp_of thy ranT)] [SOME P2, SOME (cterm_of thy rhs)]
		 |> curry (op COMP) existence
		 |> curry (op COMP) uniqueness
		 |> simplify (HOL_basic_ss addsimps [case_hyp RS sym])
		 |> implies_intr (cprop_of case_hyp) 
		 |> fold_rev (implies_intr o cprop_of) ags
		 |> fold_rev forall_intr cqs
	val function_value =
	    existence 
		|> fold_rev (implies_intr o cprop_of) ags
		|> implies_intr ihyp
		|> implies_intr (cprop_of case_hyp)
		|> forall_intr (cterm_of thy x)
		|> forall_elim (cterm_of thy lhs)
		|> curry (op RS) refl
    in
	(exactly_one, function_value)
    end



(* Does this work with Guards??? *)
fun mk_domain_intro thy names R_cases clause =
    let
	val Names {z, R, acc_R, ...} = names
	val ClauseInfo {qs, gs, lhs, rhs, ...} = clause

	val z_lhs = cterm_of thy (HOLogic.mk_prod (z,lhs))
	val z_acc = cterm_of thy (HOLogic.mk_mem (z,acc_R))

	val icases = R_cases 
			 |> instantiate' [] [SOME z_lhs, SOME z_acc]
			 |> forall_intr_frees
			 |> forall_elim_vars 0

	val goal = cterm_of thy (HOLogic.mk_Trueprop (HOLogic.mk_mem (lhs,acc_R)))
    in
	Goal.init goal 
		  |> SINGLE (resolve_tac [accI] 1) |> the
		  |> SINGLE (eresolve_tac [icases] 1)  |> the
		  |> SINGLE (CLASIMPSET auto_tac) |> the
		  |> Goal.conclude
		  |> forall_intr_frees
		  |> forall_elim_vars 0
		  |> varifyT
    end




fun mk_nest_term_case thy names R' ihyp clause =
    let
	val Names {x, z, ...} = names
	val ClauseInfo {qs,cqs,ags,lhs,rhs,tree,case_hyp,...} = clause

	val ih_case = full_simplify (HOL_basic_ss addsimps [case_hyp]) ihyp

	fun step (fixes, assumes) (_ $ arg) u (sub,(hyps,thms)) = 
	    let
		val used = map (fn ((f,a),thm) => FundefCtxTree.export_thm thy (f, map prop_of a) thm) (u @ sub)

		val hyp = mk_relmem (arg, lhs) R'
				    |> fold_rev (curry Logic.mk_implies o prop_of) used
				    |> FundefCtxTree.export_term (fixes, map prop_of assumes) 
				    |> fold_rev (curry Logic.mk_implies o prop_of) ags
				    |> fold_rev mk_forall qs
				    |> cterm_of thy

		val thm = assume hyp
				 |> fold forall_elim cqs
				 |> fold implies_elim_swp ags
				 |> FundefCtxTree.import_thm thy (fixes, assumes) (*  "(arg, lhs) : R'"  *)
				 |> fold implies_elim_swp used

		val acc = thm COMP ih_case

		val z_eq_arg = cterm_of thy (Trueprop (HOLogic.mk_eq (z, arg)))

		val arg_eq_z = (assume z_eq_arg) RS sym

		val z_acc = simplify (HOL_basic_ss addsimps [arg_eq_z]) acc (* fragile, slow... *)
				     |> implies_intr (cprop_of case_hyp)
				     |> implies_intr z_eq_arg

		val zx_eq_arg_lhs = cterm_of thy (Trueprop (mk_eq (mk_prod (z,x), mk_prod (arg,lhs))))

		val z_acc' = z_acc COMP (assume zx_eq_arg_lhs COMP Pair_inject)

		val ethm = z_acc'
			       |> FundefCtxTree.export_thm thy (fixes, (term_of zx_eq_arg_lhs) :: map prop_of (ags @ assumes))
			       |> fold_rev forall_intr cqs


		val sub' = sub @ [(([],[]), acc)]
	    in
		(sub', (hyp :: hyps, ethm :: thms))
	    end
	  | step _ _ _ _ = raise Match
    in
	FundefCtxTree.traverse_tree step tree
    end


fun mk_nest_term_rule thy names clauses =
    let
	val Names { R, acc_R, domT, x, z, ... } = names

	val R_elim = hd (#elims (snd (the (InductivePackage.get_inductive thy (fst (dest_Const R))))))

	val R' = Free ("R", fastype_of R)

	val wfR' = cterm_of thy (Trueprop (Const ("Wellfounded_Recursion.wf", mk_relT (domT, domT) --> boolT) $ R')) (* "wf R'" *)

	(* Inductive Hypothesis: !!z. (z,x):R' ==> z : acc R *)
	val ihyp = all domT $ Abs ("z", domT, 
				   implies $ Trueprop (mk_relmemT domT domT (Bound 0, x) R')
					   $ Trueprop ((Const ("op :", [domT, HOLogic.mk_setT domT] ---> boolT))
							   $ Bound 0 $ acc_R))
		       |> cterm_of thy

	val ihyp_a = assume ihyp |> forall_elim_vars 0

	val z_ltR_x = cterm_of thy (mk_relmem (z, x) R) (* "(z, x) : R" *)
	val z_acc = cterm_of thy (mk_mem (z, acc_R))

	val (hyps,cases) = fold (mk_nest_term_case thy names R' ihyp_a) clauses ([],[])
    in
	R_elim
	    |> freezeT
	    |> instantiate' [] [SOME (cterm_of thy (mk_prod (z,x))), SOME z_acc]
	    |> curry op COMP (assume z_ltR_x)
	    |> fold_rev (curry op COMP) cases
	    |> implies_intr z_ltR_x
	    |> forall_intr (cterm_of thy z)
	    |> (fn it => it COMP accI)
	    |> implies_intr ihyp
	    |> forall_intr (cterm_of thy x)
	    |> (fn it => Drule.compose_single(it,2,wf_induct_rule))
	    |> implies_elim_swp (assume wfR')
	    |> fold implies_intr hyps
	    |> implies_intr wfR'
	    |> forall_intr (cterm_of thy R')
	    |> forall_elim_vars 0
	    |> varifyT
    end




fun mk_partial_rules thy congs data complete_thm compat_thms =
    let
	val Prep {names, clauses, complete, compat, ...} = data
	val Names {G, R, acc_R, domT, ranT, f, f_def, x, z, fvarname, ...}:naming_context = names

(*	val _ = Output.debug "closing derivation: completeness"
	val _ = Output.debug (Proofterm.size_of_proof (proof_of complete_thm))
	val _ = Output.debug (map (Proofterm.size_of_proof o proof_of) compat_thms)*)
	val complete_thm = Drule.close_derivation complete_thm
(*	val _ = Output.debug "closing derivation: compatibility"*)
	val compat_thms = map Drule.close_derivation compat_thms
(*	val _ = Output.debug "  done"*)

	val complete_thm_fr = freezeT complete_thm
	val compat_thms_fr = map freezeT compat_thms
	val f_def_fr = freezeT f_def

	val instantiate_and_def = (instantiate' [SOME (ctyp_of thy domT), SOME (ctyp_of thy ranT)] 
						[SOME (cterm_of thy f), SOME (cterm_of thy G)])
				      #> curry op COMP (forall_intr_vars f_def_fr)
			  
	val inst_ex1_ex = instantiate_and_def ex1_implies_ex
	val inst_ex1_un = instantiate_and_def ex1_implies_un
	val inst_ex1_iff = instantiate_and_def ex1_implies_iff

	(* Inductive Hypothesis: !!z. (z,x):R ==> EX!y. (z,y):G *)
	val ihyp = all domT $ Abs ("z", domT, 
				   implies $ Trueprop (mk_relmemT domT domT (Bound 0, x) R)
					   $ Trueprop (Const ("Ex1", (ranT --> boolT) --> boolT) $
							     Abs ("y", ranT, mk_relmemT domT ranT (Bound 1, Bound 0) G)))
		       |> cterm_of thy
		   
	val ihyp_thm = assume ihyp
			      |> forall_elim_vars 0
		       
	val ih_intro = ihyp_thm RS inst_ex1_ex
	val ih_elim = ihyp_thm RS inst_ex1_un

	val _ = Output.debug "Proving Replacement lemmas..."
	val repLemmas = map (mk_replacement_lemma thy names ih_elim) clauses

	val n = length clauses
	val var_order = get_var_order thy clauses
	val compat_store = store_compat_thms n (var_order ~~ compat_thms_fr)

	val R_cases = hd (#elims (snd (the (InductivePackage.get_inductive thy (fst (dest_Const R)))))) |> freezeT
	val G_cases = hd (#elims (snd (the (InductivePackage.get_inductive thy (fst (dest_Const G)))))) |> freezeT

	val _ = Output.debug "Proving cases for unique existence..."
	val (ex1s, values) = split_list (map (mk_uniqueness_case thy names ihyp ih_intro G_cases compat_store clauses repLemmas) clauses)

	val _ = Output.debug "Proving: Graph is a function"
	val graph_is_function = complete_thm_fr
				    |> fold (curry op COMP) ex1s
				    |> implies_intr (ihyp)
				    |> implies_intr (cterm_of thy (Trueprop (mk_mem (x, acc_R))))
				    |> forall_intr (cterm_of thy x)
				    |> (fn it => Drule.compose_single (it, 2, acc_induct_rule)) (* "EX! y. (?x,y):G" *)
				    |> Drule.close_derivation

	val f_iff = (graph_is_function RS inst_ex1_iff)

	val _ = Output.debug "Proving simplification rules"
	val psimps  = map2 (mk_simp thy names f_iff graph_is_function) clauses values

	val _ = Output.debug "Proving partial induction rule"
	val (subset_pinduct, simple_pinduct) = mk_partial_induct_rule thy names complete_thm clauses

	val _ = Output.debug "Proving nested termination rule"
	val total_intro = mk_nest_term_rule thy names clauses

	val _ = Output.debug "Proving domain introduction rules"
	val dom_intros = map (mk_domain_intro thy names R_cases) clauses
    in 
	FundefResult {f=f, G=G, R=R, compatibility=compat_thms, completeness=complete_thm, 
	 psimps=psimps, subset_pinduct=subset_pinduct, simple_pinduct=simple_pinduct, total_intro=total_intro,
	 dom_intros=dom_intros}
    end


fun curry_induct_rule thy argTs induct =
    let
	val vnums = (1 upto (length argTs))
	val avars = map2 (fn T => fn i => Var (("a",i), T)) argTs vnums
	val atup = foldr1 HOLogic.mk_prod avars
	val Q = Var (("P",1),argTs ---> HOLogic.boolT)
	val P = tupled_lambda atup (list_comb (Q, avars))
    in
	induct |> freezeT
	       |> instantiate' [] [SOME (cterm_of thy atup), SOME (cterm_of thy P)]
	       |> zero_var_indexes
	       |> full_simplify (HOL_basic_ss addsimps [split_apply])
	       |> varifyT
    end



fun mk_partial_rules_curried thy congs NONE data complete_thm compat_thms =
    mk_partial_rules thy congs data complete_thm compat_thms 
  | mk_partial_rules_curried thy congs (SOME (Curry {curry_ss, argTs})) data complete_thm compat_thms =
    let
	val FundefResult {f, G, R, compatibility, completeness, psimps, subset_pinduct,simple_pinduct,total_intro,dom_intros} =
	    mk_partial_rules thy congs data complete_thm compat_thms 
	val cpsimps = map (simplify curry_ss) psimps
	val cpinduct = full_simplify curry_ss simple_pinduct
				     |> curry_induct_rule thy argTs
	val cdom_intros = map (full_simplify curry_ss) dom_intros
	val ctotal_intro = full_simplify curry_ss total_intro
    in
	FundefResult {f=f, G=G, R=R, compatibility=compat_thms, completeness=complete_thm, 
	 psimps=cpsimps, subset_pinduct=subset_pinduct, simple_pinduct=cpinduct, total_intro=ctotal_intro, dom_intros=cdom_intros}
    end

end


