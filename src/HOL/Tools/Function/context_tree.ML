(*  Title:      HOL/Tools/Function/context_tree.ML
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Builds and traverses trees of nested contexts along a term.
*)

signature FUNDEF_CTXTREE =
sig
    type ctxt = (string * typ) list * thm list (* poor man's contexts: fixes + assumes *)
    type ctx_tree

    (* FIXME: This interface is a mess and needs to be cleaned up! *)
    val get_fundef_congs : Proof.context -> thm list
    val add_fundef_cong : thm -> Context.generic -> Context.generic
    val map_fundef_congs : (thm list -> thm list) -> Context.generic -> Context.generic

    val cong_add: attribute
    val cong_del: attribute

    val mk_tree: (string * typ) -> term -> Proof.context -> term -> ctx_tree

    val inst_tree: theory -> term -> term -> ctx_tree -> ctx_tree

    val export_term : ctxt -> term -> term
    val export_thm : theory -> ctxt -> thm -> thm
    val import_thm : theory -> ctxt -> thm -> thm

    val traverse_tree : 
   (ctxt -> term ->
   (ctxt * thm) list ->
   (ctxt * thm) list * 'b ->
   (ctxt * thm) list * 'b)
   -> ctx_tree -> 'b -> 'b

    val rewrite_by_tree : theory -> term -> thm -> (thm * thm) list -> ctx_tree -> thm * (thm * thm) list
end

structure FundefCtxTree : FUNDEF_CTXTREE =
struct

type ctxt = (string * typ) list * thm list

open FundefCommon
open FundefLib

structure FundefCongs = GenericDataFun
(
  type T = thm list
  val empty = []
  val extend = I
  fun merge _ = Thm.merge_thms
);

val get_fundef_congs = FundefCongs.get o Context.Proof
val map_fundef_congs = FundefCongs.map
val add_fundef_cong = FundefCongs.map o Thm.add_thm

(* congruence rules *)

val cong_add = Thm.declaration_attribute (map_fundef_congs o Thm.add_thm o safe_mk_meta_eq);
val cong_del = Thm.declaration_attribute (map_fundef_congs o Thm.del_thm o safe_mk_meta_eq);


type depgraph = int IntGraph.T

datatype ctx_tree 
  = Leaf of term
  | Cong of (thm * depgraph * (ctxt * ctx_tree) list)
  | RCall of (term * ctx_tree)


(* Maps "Trueprop A = B" to "A" *)
val rhs_of = snd o HOLogic.dest_eq o HOLogic.dest_Trueprop


(*** Dependency analysis for congruence rules ***)

fun branch_vars t = 
    let 
      val t' = snd (dest_all_all t)
      val (assumes, concl) = Logic.strip_horn t'
    in (fold Term.add_vars assumes [], Term.add_vars concl [])
    end

fun cong_deps crule =
    let
      val num_branches = map_index (apsnd branch_vars) (prems_of crule)
    in
      IntGraph.empty
        |> fold (fn (i,_)=> IntGraph.new_node (i,i)) num_branches
        |> fold_product (fn (i, (c1, _)) => fn (j, (_, t2)) => 
               if i = j orelse null (inter (op =) (c1, t2))
               then I else IntGraph.add_edge_acyclic (i,j))
             num_branches num_branches
    end
    
val default_congs = map (fn c => c RS eq_reflection) [@{thm "cong"}, @{thm "ext"}] 



(* Called on the INSTANTIATED branches of the congruence rule *)
fun mk_branch ctx t = 
    let
      val (ctx', fixes, impl) = dest_all_all_ctx ctx t
      val (assms, concl) = Logic.strip_horn impl
    in
      (ctx', fixes, assms, rhs_of concl)
    end
    
fun find_cong_rule ctx fvar h ((r,dep)::rs) t =
    (let
       val thy = ProofContext.theory_of ctx

       val tt' = Logic.mk_equals (Pattern.rewrite_term thy [(Free fvar, h)] [] t, t)
       val (c, subs) = (concl_of r, prems_of r)

       val subst = Pattern.match (ProofContext.theory_of ctx) (c, tt') (Vartab.empty, Vartab.empty)
       val branches = map (mk_branch ctx o Envir.beta_norm o Envir.subst_term subst) subs
       val inst = map (fn v =>
        (cterm_of thy (Var v), cterm_of thy (Envir.subst_term subst (Var v)))) (Term.add_vars c [])
     in
   (cterm_instantiate inst r, dep, branches)
     end
    handle Pattern.MATCH => find_cong_rule ctx fvar h rs t)
  | find_cong_rule _ _ _ [] _ = sys_error "Function/context_tree.ML: No cong rule found!"


fun mk_tree fvar h ctxt t =
    let 
      val congs = get_fundef_congs ctxt
      val congs_deps = map (fn c => (c, cong_deps c)) (congs @ default_congs) (* FIXME: Save in theory *)

      fun matchcall (a $ b) = if a = Free fvar then SOME b else NONE
        | matchcall _ = NONE

      fun mk_tree' ctx t =
          case matchcall t of
            SOME arg => RCall (t, mk_tree' ctx arg)
          | NONE => 
            if not (exists_subterm (fn Free v => v = fvar | _ => false) t) then Leaf t
            else 
              let val (r, dep, branches) = find_cong_rule ctx fvar h congs_deps t in
                Cong (r, dep, 
                      map (fn (ctx', fixes, assumes, st) => 
                              ((fixes, map (assume o cterm_of (ProofContext.theory_of ctx)) assumes), 
                               mk_tree' ctx' st)) branches)
              end
    in
      mk_tree' ctxt t
    end
    

fun inst_tree thy fvar f tr =
    let
      val cfvar = cterm_of thy fvar
      val cf = cterm_of thy f
               
      fun inst_term t = 
          subst_bound(f, abstract_over (fvar, t))

      val inst_thm = forall_elim cf o forall_intr cfvar 

      fun inst_tree_aux (Leaf t) = Leaf t
        | inst_tree_aux (Cong (crule, deps, branches)) =
          Cong (inst_thm crule, deps, map inst_branch branches)
        | inst_tree_aux (RCall (t, str)) =
          RCall (inst_term t, inst_tree_aux str)
      and inst_branch ((fxs, assms), str) = 
          ((fxs, map (assume o cterm_of thy o inst_term o prop_of) assms), inst_tree_aux str)
    in
      inst_tree_aux tr
    end


(* Poor man's contexts: Only fixes and assumes *)
fun compose (fs1, as1) (fs2, as2) = (fs1 @ fs2, as1 @ as2)

fun export_term (fixes, assumes) =
    fold_rev (curry Logic.mk_implies o prop_of) assumes 
 #> fold_rev (Logic.all o Free) fixes

fun export_thm thy (fixes, assumes) =
    fold_rev (implies_intr o cprop_of) assumes
 #> fold_rev (forall_intr o cterm_of thy o Free) fixes

fun import_thm thy (fixes, athms) =
    fold (forall_elim o cterm_of thy o Free) fixes
 #> fold Thm.elim_implies athms


(* folds in the order of the dependencies of a graph. *)
fun fold_deps G f x =
    let
      fun fill_table i (T, x) =
          case Inttab.lookup T i of
            SOME _ => (T, x)
          | NONE => 
            let
              val (T', x') = fold fill_table (IntGraph.imm_succs G i) (T, x)
              val (v, x'') = f (the o Inttab.lookup T') i x'
            in
              (Inttab.update (i, v) T', x'')
            end
            
      val (T, x) = fold fill_table (IntGraph.keys G) (Inttab.empty, x)
    in
      (Inttab.fold (cons o snd) T [], x)
    end
    
fun traverse_tree rcOp tr =
    let 
  fun traverse_help ctx (Leaf _) _ x = ([], x)
    | traverse_help ctx (RCall (t, st)) u x =
      rcOp ctx t u (traverse_help ctx st u x)
    | traverse_help ctx (Cong (_, deps, branches)) u x =
      let
    fun sub_step lu i x =
        let
          val (ctx', subtree) = nth branches i
          val used = fold_rev (append o lu) (IntGraph.imm_succs deps i) u
          val (subs, x') = traverse_help (compose ctx ctx') subtree used x
          val exported_subs = map (apfst (compose ctx')) subs (* FIXME: Right order of composition? *)
        in
          (exported_subs, x')
        end
      in
        fold_deps deps sub_step x
          |> apfst flat
      end
    in
      snd o traverse_help ([], []) tr []
    end

fun rewrite_by_tree thy h ih x tr =
    let
      fun rewrite_help _ _ x (Leaf t) = (reflexive (cterm_of thy t), x)
        | rewrite_help fix h_as x (RCall (_ $ arg, st)) =
          let
            val (inner, (lRi,ha)::x') = rewrite_help fix h_as x st (* "a' = a" *)
                                                     
            val iha = import_thm thy (fix, h_as) ha (* (a', h a') : G *)
                 |> Conv.fconv_rule (Conv.arg_conv (Conv.comb_conv (Conv.arg_conv (K inner))))
                                                    (* (a, h a) : G   *)
            val inst_ih = instantiate' [] [SOME (cterm_of thy arg)] ih
            val eq = implies_elim (implies_elim inst_ih lRi) iha (* h a = f a *)
                     
            val h_a'_eq_h_a = combination (reflexive (cterm_of thy h)) inner
            val h_a_eq_f_a = eq RS eq_reflection
            val result = transitive h_a'_eq_h_a h_a_eq_f_a
          in
            (result, x')
          end
        | rewrite_help fix h_as x (Cong (crule, deps, branches)) =
          let
            fun sub_step lu i x =
                let
                  val ((fixes, assumes), st) = nth branches i
                  val used = map lu (IntGraph.imm_succs deps i)
                             |> map (fn u_eq => (u_eq RS sym) RS eq_reflection)
                             |> filter_out Thm.is_reflexive

                  val assumes' = map (simplify (HOL_basic_ss addsimps used)) assumes
                                 
                  val (subeq, x') = rewrite_help (fix @ fixes) (h_as @ assumes') x st
                  val subeq_exp = export_thm thy (fixes, assumes) (subeq RS meta_eq_to_obj_eq)
                in
                  (subeq_exp, x')
                end
                
            val (subthms, x') = fold_deps deps sub_step x
          in
            (fold_rev (curry op COMP) subthms crule, x')
          end
    in
      rewrite_help [] [] x tr
    end
    
end
