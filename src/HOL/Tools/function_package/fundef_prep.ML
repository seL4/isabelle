(*  Title:      HOL/Tools/function_package/fundef_prep.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Preparation step: makes auxiliary definitions and generates
proof obligations.
*)

signature FUNDEF_PREP =
sig
    val prepare_fundef : theory -> thm list -> string -> term -> FundefCommon.glrs -> string list
			 -> FundefCommon.prep_result * theory

end





structure FundefPrep (*: FUNDEF_PREP*) =
struct


open FundefCommon
open FundefAbbrev 

(* Theory dependencies. *)
val Pair_inject = thm "Product_Type.Pair_inject";

val acc_induct_rule = thm "Accessible_Part.acc_induct_rule"

val ex1_implies_ex = thm "FunDef.fundef_ex1_existence"
val ex1_implies_un = thm "FunDef.fundef_ex1_uniqueness"
val ex1_implies_iff = thm "FunDef.fundef_ex1_iff"

val conjunctionI = thm "conjunctionI";



fun split_list3 [] = ([],[],[])
  | split_list3 ((x,y,z)::xyzs) = 
    let
	val (xs, ys, zs) = split_list3 xyzs
    in
	(x::xs,y::ys,z::zs)
    end


fun build_tree thy f congs ctx (qs, gs, lhs, rhs) =
    let
	(* FIXME: Save precomputed dependencies in a theory data slot *)
	val congs_deps = map (fn c => (c, FundefCtxTree.cong_deps c)) (congs @ FundefCtxTree.add_congs)

        val (_(*FIXME*), ctx') = ProofContext.add_fixes_i (map (fn Free (n, T) => (n, SOME T, NoSyn)) qs) ctx 
    in
	FundefCtxTree.mk_tree thy congs_deps f ctx' rhs
    end


fun find_calls tree =
    let
      fun add_Ri (fixes,assumes) (_ $ arg) _ (_, xs) = ([], (fixes, assumes, arg) :: xs)
	| add_Ri _ _ _ _ = raise Match
    in                                 
      rev (FundefCtxTree.traverse_tree add_Ri tree [])
    end



(* maps (qs,gs,lhs,ths) to (qs',gs',lhs',rhs') with primed variables *)
fun mk_primed_vars thy glrs =
    let
	val used = fold (fn (qs,_,_,_) => fold ((insert op =) o fst o dest_Free) qs) glrs []

	fun rename_vars (qs,gs,lhs,rhs) =
	    let
		val qs' = map (fn Free (v,T) => Free (variant used (v ^ "'"),T)) qs
		val rename_vars = Pattern.rewrite_term thy (qs ~~ qs') []
	    in
		(qs', map rename_vars gs, rename_vars lhs, rename_vars rhs)
	    end
    in
	map rename_vars glrs
    end



(* Chooses fresh free names, declares G and R, defines f and returns a record
   with all the information *)  
fun setup_context f glrs defname thy =
    let
	val Const (f_fullname, fT) = f
	val fname = Sign.base_name f_fullname

	val domT = domain_type fT 
	val ranT = range_type fT

	val GT = mk_relT (domT, ranT)
	val RT = mk_relT (domT, domT)
	val G_name = defname ^ "_graph"
	val R_name = defname ^ "_rel"

        val gfixes = [("h_fd", domT --> ranT),
	              ("y_fd", ranT),
	              ("x_fd", domT),
	              ("z_fd", domT),
	              ("a_fd", domT),
	              ("D_fd", HOLogic.mk_setT domT),
	              ("P_fd", domT --> boolT),
	              ("Pb_fd", boolT),
	              ("f_fd", fT)]

        val (fxnames, ctx) = (ProofContext.init thy)
                               |> ProofContext.add_fixes_i (map (fn (n,T) => (n, SOME T, NoSyn)) gfixes)

        val [h, y, x, z, a, D, P, Pbool, fvar] = map (fn (n,(_,T)) => Free (n, T)) (fxnames ~~ gfixes)
                                                                                    
        val Free (fvarname, _) = fvar

	val glrs' = mk_primed_vars thy glrs

	val thy = Sign.add_consts_i [(G_name, GT, NoSyn), (R_name, RT, NoSyn)] thy

	val G = Const (Sign.full_name thy G_name, GT)
	val R = Const (Sign.full_name thy R_name, RT)
	val acc_R = Const (acc_const_name, (fastype_of R) --> HOLogic.mk_setT domT) $ R

	val f_eq = Logic.mk_equals (f $ x, 
				    Const ("The", (ranT --> boolT) --> ranT) $
					  Abs ("y", ranT, mk_relmemT domT ranT (x, Bound 0) G))

	val ([f_def], thy) = PureThy.add_defs_i false [((fname ^ "_def", f_eq), [])] thy
    in
	(Names {f=f, glrs=glrs, glrs'=glrs', fvar=fvar, fvarname=fvarname, domT=domT, ranT=ranT, G=G, R=R, acc_R=acc_R, h=h, x=x, y=y, z=z, a=a, D=D, P=P, Pbool=Pbool, f_def=f_def, ctx=ctx}, thy)
    end





(* !!qs' qs. Gs ==> Gs' ==> lhs = lhs' ==> rhs = rhs' *)
fun mk_compat_impl ((qs, gs, lhs, rhs),(qs', gs', lhs', rhs')) =
    (implies $ Trueprop (mk_eq (lhs, lhs'))
	     $ Trueprop (mk_eq (rhs, rhs')))
	|> fold_rev (curry Logic.mk_implies) (gs @ gs')
        |> fold_rev mk_forall (qs @ qs')

(* all proof obligations *)
fun mk_compat_proof_obligations glrs glrs' =
    map (fn ((x,_), (_,y')) => mk_compat_impl (x,y')) (unordered_pairs (glrs ~~ glrs'))


fun mk_completeness names glrs =
    let
	val Names {domT, x, Pbool, ...} = names

	fun mk_case (qs, gs, lhs, _) = Trueprop Pbool
						|> curry Logic.mk_implies (Trueprop (mk_eq (x, lhs)))
						|> fold_rev (curry Logic.mk_implies) gs
						|> fold_rev mk_forall qs
    in
	Trueprop Pbool
		 |> fold_rev (curry Logic.mk_implies o mk_case) glrs
                 |> mk_forall_rename (x, "x")
                 |> mk_forall_rename (Pbool, "P")
    end


fun inductive_def_wrap defs (thy, const) = 
    let 
      val qdefs = map dest_all_all defs

      val (thy, {intrs = intrs_gen, elims = [elim_gen], ...}) = 
	  InductivePackage.add_inductive_i true (*verbose*)
					     false (*add_consts*)
					     "" (* no altname *)
					     false (* no coind *)
					     false (* elims, please *)
					     false (* induction thm please *)
					     [const] (* the constant *)
					     (map (fn (_,t) => (("", t),[])) qdefs) (* the intros *)
					     [] (* no special monos *)
					     thy

(* It would be nice if this worked... But this is actually HO-Unification... *)
(*      fun inst (qs, intr) intr_gen =
          Goal.init (cterm_of thy intr)
                    |> curry op COMP intr_gen
                    |> Goal.finish
                    |> fold_rev (forall_intr o cterm_of thy) qs*)

      fun inst (qs, intr) intr_gen =
          intr_gen 
            |> Thm.freezeT
            |> fold_rev (forall_intr o (fn Free (n, T) => cterm_of thy (Var ((n,0), T)))) qs

      val intrs = map2 inst qdefs intrs_gen
      val elim = elim_gen
                   |> Thm.freezeT
                   |> forall_intr_vars (* FIXME *)
    in
      (intrs, (thy, const, elim))
    end





(*
 * "!!qs xs. CS ==> G => (r, lhs) : R" 
 *)
fun mk_RIntro R (qs, gs, lhs, rhs) (rcfix, rcassm, rcarg) =
    mk_relmem (rcarg, lhs) R 
              |> fold_rev (curry Logic.mk_implies o prop_of) rcassm
              |> fold_rev (curry Logic.mk_implies) gs
              |> fold_rev (mk_forall o Free) rcfix
              |> fold_rev mk_forall qs


fun mk_GIntro thy f_const f_var G (qs, gs, lhs, rhs) RCs =
    let
      fun mk_h_assm (rcfix, rcassm, rcarg) =
          mk_relmem (rcarg, f_var $ rcarg) G
                    |> fold_rev (curry Logic.mk_implies o prop_of) rcassm
                    |> fold_rev (mk_forall o Free) rcfix
    in
      mk_relmem (lhs, rhs) G
                |> fold_rev (curry Logic.mk_implies o mk_h_assm) RCs
                |> fold_rev (curry Logic.mk_implies) gs
                |> Pattern.rewrite_term thy [(f_const, f_var)] []
                |> fold_rev mk_forall (f_var :: qs)
    end



fun mk_clause_info thy names no (qs,gs,lhs,rhs) tree RCs GIntro_thm RIntro_thms =
    let
	val Names {G, h, f, fvar, x, ...} = names 
				 
	val cqs = map (cterm_of thy) qs
	val ags = map (assume o cterm_of thy) gs

        val used = [] (* XXX *)
                  (* FIXME: What is the relationship between this and mk_primed_vars? *)
	val qs' = map (fn Free (v,T) => Free (variant used (v ^ "'"),T)) qs
	val cqs' = map (cterm_of thy) qs'

	val rename_vars = Pattern.rewrite_term thy (qs ~~ qs') []
	val ags' = map (assume o cterm_of thy o rename_vars) gs
	val lhs' = rename_vars lhs
	val rhs' = rename_vars rhs

        val lGI = GIntro_thm
                    |> forall_elim (cterm_of thy f)
                    |> fold forall_elim cqs
                    |> fold implies_elim_swp ags
		
        (* FIXME: Can be removed when inductive-package behaves nicely. *)
        val ordcqs' = map (cterm_of thy o Pattern.rewrite_term thy ((fvar,h)::(qs ~~ qs')) []) 
                          (term_frees (snd (dest_all_all (prop_of GIntro_thm))))
               	  
	fun mk_call_info (rcfix, rcassm, rcarg) RI =
	    let
                val crcfix = map (cterm_of thy o Free) rcfix

                val llRI = RI
                             |> fold forall_elim cqs
                             |> fold forall_elim crcfix
                             |> fold implies_elim_swp ags
                             |> fold implies_elim_swp rcassm

                val h_assum = 
                    mk_relmem (rcarg, h $ rcarg) G
                              |> fold_rev (curry Logic.mk_implies o prop_of) rcassm
                              |> fold_rev (mk_forall o Free) rcfix
                              |> Pattern.rewrite_term thy [(f, h)] []

		val Gh = assume (cterm_of thy h_assum)
		val Gh' = assume (cterm_of thy (rename_vars h_assum))
	    in
		RCInfo {RIvs=rcfix, Gh=Gh, Gh'=Gh', rcarg=rcarg, CCas=rcassm, llRI=llRI}
	    end

	val case_hyp = assume (cterm_of thy (Trueprop (mk_eq (x, lhs))))

        val RC_infos = map2 mk_call_info RCs RIntro_thms
    in
	ClauseInfo
	    {
	     no=no,
	     qs=qs, gs=gs, lhs=lhs, rhs=rhs,		 
	     cqs=cqs, ags=ags,		 
	     cqs'=cqs', ags'=ags', lhs'=lhs', rhs'=rhs', 
	     lGI=lGI, RCs=RC_infos,
	     tree=tree, case_hyp = case_hyp,
             ordcqs'=ordcqs'
	    }
    end





(* Copied from fundef_proof.ML: *)

(***********************************************)
(* Compat thms are stored in normal form (with vars) *)

(* replace this by a table later*)
fun store_compat_thms 0 thms = []
  | store_compat_thms n thms =
    let
	val (thms1, thms2) = chop n thms
    in
	(thms1 :: store_compat_thms (n - 1) thms2)
    end


(* needs i <= j *)
fun lookup_compat_thm i j cts =
    nth (nth cts (i - 1)) (j - i)
(***********************************************)


(* Returns "Gsi, Gsj', lhs_i = lhs_j' |-- rhs_j'_f = rhs_i_f" *)
(* if j < i, then turn around *)
fun get_compat_thm thy cts clausei clausej =
    let 
	val ClauseInfo {no=i, cqs=qsi, ags=gsi, lhs=lhsi, ...} = clausei
	val ClauseInfo {no=j, cqs'=qsj', ags'=gsj', lhs'=lhsj', ...} = clausej

	val lhsi_eq_lhsj' = cterm_of thy (Trueprop (mk_eq (lhsi, lhsj')))
    in if j < i then
	   let 
	       val compat = lookup_compat_thm j i cts
	   in
	       compat         (* "!!qj qi'. Gsj => Gsi' => lhsj = lhsi' ==> rhsj = rhsi'" *)
                |> fold forall_elim (qsj' @ qsi) (* "Gsj' => Gsi => lhsj' = lhsi ==> rhsj' = rhsi" *)
		|> fold implies_elim_swp gsj'
		|> fold implies_elim_swp gsi
		|> implies_elim_swp ((assume lhsi_eq_lhsj') RS sym) (* "Gsj', Gsi, lhsi = lhsj' |-- rhsj' = rhsi" *)
	   end
       else
	   let
	       val compat = lookup_compat_thm i j cts
	   in
	       compat        (* "!!qi qj'. Gsi => Gsj' => lhsi = lhsj' ==> rhsi = rhsj'" *)
                 |> fold forall_elim (qsi @ qsj') (* "Gsi => Gsj' => lhsi = lhsj' ==> rhsi = rhsj'" *)
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

	val Ris = map (fn RCInfo {llRI, ...} => llRI) RCs
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

	fun prep_RC (RCInfo {llRI, RIvs, CCas, ...}) = (llRI RS ih_intro_case)
                                                            |> fold_rev (implies_intr o cprop_of) CCas
						            |> fold_rev (forall_intr o cterm_of thy o Free) RIvs

	val existence = lGI (*|> instantiate ([], [(cterm_of thy (free_to_var fvar), cterm_of thy f)])*)
			    |> fold (curry op COMP o prep_RC) RCs 

	val a = cterm_of thy (mk_prod (lhs, y))
	val P = cterm_of thy (mk_eq (y, rhs))
	val a_in_G = assume (cterm_of thy (Trueprop (mk_mem (term_of a, G))))

	val unique_clauses = map2 (mk_uniqueness_clause thy names compat_store clausei) clauses rep_lemmas

	val uniqueness = G_cases 
                           |> forall_elim a
                           |> forall_elim P
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




fun prove_stuff thy congs names clauses complete compat compat_store G_elim R_elim =
    let
	val Names {G, R, acc_R, domT, ranT, f, f_def, x, z, fvarname, Pbool, ...}:naming_context = names

	val f_def_fr = Thm.freezeT f_def

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
		   
	val ihyp_thm = assume ihyp |> forall_elim_vars 0
	val ih_intro = ihyp_thm RS inst_ex1_ex
	val ih_elim = ihyp_thm RS inst_ex1_un

	val _ = Output.debug "Proving Replacement lemmas..."
	val repLemmas = map (mk_replacement_lemma thy names ih_elim) clauses

	val _ = Output.debug "Proving cases for unique existence..."
	val (ex1s, values) = split_list (map (mk_uniqueness_case thy names ihyp ih_intro G_elim compat_store clauses repLemmas) clauses)

	val _ = Output.debug "Proving: Graph is a function" (* FIXME: Rewrite this proof. *)
	val graph_is_function = complete 
                                  |> forall_elim_vars 0
				  |> fold (curry op COMP) ex1s
				  |> implies_intr (ihyp)
				  |> implies_intr (cterm_of thy (Trueprop (mk_mem (x, acc_R))))
				  |> forall_intr (cterm_of thy x)
				  |> (fn it => Drule.compose_single (it, 2, acc_induct_rule)) (* "EX! y. (?x,y):G" *)
                                  |> (fn it => fold (forall_intr o cterm_of thy) (term_vars (prop_of it)) it)
				  |> Drule.close_derivation

        val goal = complete COMP (graph_is_function COMP conjunctionI)
                            |> Drule.close_derivation

        val goalI = Goal.protect goal
                                 |> fold_rev (implies_intr o cprop_of) compat
                                 |> implies_intr (cprop_of complete)
    in
      (prop_of goal, goalI, inst_ex1_iff, values)
    end





(*
 * This is the first step in a function definition.
 *
 * Defines the function, the graph and the termination relation, synthesizes completeness
 * and comatibility conditions and returns everything.
 *)
fun prepare_fundef thy congs defname f qglrs used =
    let
      val (names, thy) = setup_context f qglrs defname thy
      val Names {G, R, ctx, glrs', fvar, ...} = names 

                         
      val n = length qglrs
      val trees = map (build_tree thy f congs ctx) qglrs
      val RCss = map find_calls trees

      val complete = mk_completeness names qglrs
                                     |> cterm_of thy
                                     |> assume

      val compat = mk_compat_proof_obligations qglrs glrs'
                           |> map (assume o cterm_of thy)

      val compat_store = compat
                           |> store_compat_thms n

      val R_intross = map2 (fn qglr => map (mk_RIntro R qglr)) qglrs RCss
      val G_intros = map2 (mk_GIntro thy f fvar G) qglrs RCss
                    
      val (GIntro_thms, (thy, _, G_elim)) = inductive_def_wrap G_intros (thy, G)
      val (RIntro_thmss, (thy, _, R_elim)) = fold_burrow inductive_def_wrap R_intross (thy, R)
 
      val clauses = map6 (mk_clause_info thy names) (1 upto n) qglrs trees RCss GIntro_thms RIntro_thmss
                  
      val (goal, goalI, ex1_iff, values) = prove_stuff thy congs names clauses complete compat compat_store G_elim R_elim
    in
	(Prep {names = names, goal = goal, goalI = goalI, values = values, clauses = clauses, ex1_iff = ex1_iff, R_cases = R_elim},
	 thy) 
    end




end
