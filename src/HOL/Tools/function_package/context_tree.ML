(*  Title:      HOL/Tools/function_package/context_tree.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Builds and traverses trees of nested contexts along a term.
*)


signature FUNDEF_CTXTREE =
sig
    type ctx_tree

    (* FIXME: This interface is a mess and needs to be cleaned up! *)
    val cong_deps : thm -> int IntGraph.T
    val add_congs : thm list

    val mk_tree: theory -> (thm * FundefCommon.depgraph) list -> term -> term -> FundefCommon.ctx_tree

    val add_context_varnames : FundefCommon.ctx_tree -> string list -> string list

    val export_term : (string * typ) list * term list -> term -> term
    val export_thm : theory -> (string * typ) list * term list -> thm -> thm
    val import_thm : theory -> (string * typ) list * thm list -> thm -> thm


    val traverse_tree : 
   ((string * typ) list * thm list -> term ->
   (((string * typ) list * thm list) * thm) list ->
   (((string * typ) list * thm list) * thm) list * 'b ->
   (((string * typ) list * thm list) * thm) list * 'b)
   -> FundefCommon.ctx_tree -> 'b -> 'b

    val rewrite_by_tree : theory -> 'a -> term -> thm -> (thm * thm) list -> FundefCommon.ctx_tree -> thm * (thm * thm) list
end

structure FundefCtxTree : FUNDEF_CTXTREE =
struct

open FundefCommon


(* Maps "Trueprop A = B" to "A" *)
val rhs_of = snd o HOLogic.dest_eq o HOLogic.dest_Trueprop
(* Maps "A == B" to "B" *)
val meta_rhs_of = snd o Logic.dest_equals



(*** Dependency analysis for congruence rules ***)

fun branch_vars t = 
    let	val (assumes, term) = dest_implies_list (snd (dest_all_all t))
    in (fold (curry add_term_vars) assumes [], term_vars term)
    end

fun cong_deps crule =
    let
	val branches = map branch_vars (prems_of crule)
	val num_branches = (1 upto (length branches)) ~~ branches
    in
	IntGraph.empty
	    |> fold (fn (i,_)=> IntGraph.new_node (i,i)) num_branches
	    |> fold (fn ((i,(c1,_)),(j,(_, t2))) => if i = j orelse null (c1 inter t2) then I else IntGraph.add_edge_acyclic (i,j))
	    (product num_branches num_branches)
    end
    
val add_congs = map (fn c => c RS eq_reflection) [cong, ext] 



(* Called on the INSTANTIATED branches of the congruence rule *)
fun mk_branch t = 
    let
	val (fixes, impl) = dest_all_all t
	val (assumes, term) = dest_implies_list impl
    in
	(map dest_Free fixes, assumes, rhs_of term)
    end





exception CTREE_INTERNAL of string

fun find_cong_rule thy ((r,dep)::rs) t =
    (let
	val (c, subs) = (meta_rhs_of (concl_of r), prems_of r)

	val subst = Pattern.match thy (c, t) (Vartab.empty, Vartab.empty)

	val branches = map (mk_branch o Envir.beta_norm o Envir.subst_vars subst) subs
     in
	 (r, dep, branches)
     end
    handle Pattern.MATCH => find_cong_rule thy rs t)
  | find_cong_rule thy [] _ = raise CTREE_INTERNAL "No cong rule found!" (* Should never happen *)


fun matchcall f (a $ b) = if a = f then SOME b else NONE
  | matchcall f _ = NONE

fun mk_tree thy congs f t =
    case matchcall f t of
	SOME arg => RCall (t, mk_tree thy congs f arg)
      | NONE => 
	if not (exists_Const (curry op = (dest_Const f)) t) then Leaf t
	else 
	    let val (r, dep, branches) = find_cong_rule thy congs t in
		Cong (t, r, dep, map (fn (fixes, assumes, st) => 
					 (fixes, map (assume o cterm_of thy) assumes, mk_tree thy congs f st)) branches)
	    end
		
		
fun add_context_varnames (Leaf _) = I
  | add_context_varnames (Cong (_, _, _, sub)) = fold (fn (fs, _, st) => fold (curry op ins_string o fst) fs o add_context_varnames st) sub
  | add_context_varnames (RCall (_,st)) = add_context_varnames st
    

(* Poor man's contexts: Only fixes and assumes *)
fun compose (fs1, as1) (fs2, as2) = (fs1 @ fs2, as1 @ as2)

fun export_term (fixes, assumes) =
    fold_rev (curry Logic.mk_implies) assumes #> fold (mk_forall o Free) fixes

fun export_thm thy (fixes, assumes) =
    fold_rev (implies_intr o cterm_of thy) assumes
 #> fold_rev (forall_intr o cterm_of thy o Free) fixes

fun import_thm thy (fixes, athms) =
    fold (forall_elim o cterm_of thy o Free) fixes
 #> fold implies_elim_swp athms

fun assume_in_ctxt thy (fixes, athms) prop =
    let
	val global_assum = export_term (fixes, map prop_of athms) prop
    in
	(global_assum,
	 assume (cterm_of thy global_assum) |> import_thm thy (fixes, athms))
    end


(* folds in the order of the dependencies of a graph. *)
fun fold_deps G f x =
    let
	fun fill_table i (T, x) =
	    case Inttab.lookup T i of
		SOME _ => (T, x)
	      | NONE => 
		let
		    val (T', x') = fold fill_table (IntGraph.imm_succs G i) (T, x)
		    val (v, x'') = f (the o Inttab.lookup T') i x
		in
		    (Inttab.update (i, v) T', x'')
		end

	val (T, x) = fold fill_table (IntGraph.keys G) (Inttab.empty, x)
    in
	(Inttab.fold (cons o snd) T [], x)
    end


fun flatten xss = fold_rev append xss []

fun traverse_tree rcOp tr x =
    let 
	fun traverse_help ctx (Leaf _) u x = ([], x)
	  | traverse_help ctx (RCall (t, st)) u x =
	    rcOp ctx t u (traverse_help ctx st u x)
	  | traverse_help ctx (Cong (t, crule, deps, branches)) u x =
	    let
		fun sub_step lu i x =
		    let
			val (fixes, assumes, subtree) = nth branches (i - 1)
			val used = fold_rev (append o lu) (IntGraph.imm_succs deps i) u
			val (subs, x') = traverse_help (compose ctx (fixes, assumes)) subtree used x
			val exported_subs = map (apfst (compose (fixes, assumes))) subs
		    in
			(exported_subs, x')
		    end
	    in
		fold_deps deps sub_step x
			  |> apfst flatten
	    end
    in
	snd (traverse_help ([], []) tr [] x)
    end


fun is_refl thm = let val (l,r) = Logic.dest_equals (prop_of thm) in l = r end

fun rewrite_by_tree thy f h ih x tr =
    let
	fun rewrite_help fix f_as h_as x (Leaf t) = (reflexive (cterm_of thy t), x)
	  | rewrite_help fix f_as h_as x (RCall (_ $ arg, st)) =
	    let
		val (inner, (Ri,ha)::x') = rewrite_help fix f_as h_as x st
					   
					   (* Need not use the simplifier here. Can use primitive steps! *)
		val rew_ha = if is_refl inner then I else simplify (HOL_basic_ss addsimps [inner])
			     
		val h_a_eq_h_a' = combination (reflexive (cterm_of thy h)) inner
		val iRi = import_thm thy (fix, f_as) Ri (* a < lhs *)
		val iha = import_thm thy (fix, h_as) ha (* (a', h a') : G *)
				     |> rew_ha

		val inst_ih = instantiate' [] [SOME (cterm_of thy arg)] ih
		val eq = implies_elim (implies_elim inst_ih iRi) iha
			 
		val h_a'_eq_f_a' = eq RS eq_reflection
		val result = transitive h_a_eq_h_a' h_a'_eq_f_a'
	    in
		(result, x')
	    end
	  | rewrite_help fix f_as h_as x (Cong (t, crule, deps, branches)) =
	    let
		fun sub_step lu i x =
		    let
			val (fixes, assumes, st) = nth branches (i - 1)
			val used = fold_rev (cons o lu) (IntGraph.imm_succs deps i) []
			val used_rev = map (fn u_eq => (u_eq RS sym) RS eq_reflection) used
			val assumes' = map (simplify (HOL_basic_ss addsimps (filter_out is_refl used_rev))) assumes

			val (subeq, x') = rewrite_help (fix @ fixes) (f_as @ assumes) (h_as @ assumes') x st
			val subeq_exp = export_thm thy (fixes, map prop_of assumes) (subeq RS meta_eq_to_obj_eq)
		    in
			(subeq_exp, x')
		    end
		    
		val (subthms, x') = fold_deps deps sub_step x
	    in
		(fold_rev (curry op COMP) subthms crule, x')
	    end
	    
    in
	rewrite_help [] [] [] x tr
    end

end
