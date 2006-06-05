(*  Title:      HOL/Tools/function_package/sum_tools.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Tools for mutual recursive definitions. This could actually be useful for other packages, too, but needs
some cleanup first...

*)

signature SUM_TOOLS =
sig
  type sum_tree
  type sum_path

  val projl_inl: thm
  val projr_inr: thm

  val mk_tree : typ list -> typ * sum_tree * sum_path list

  val mk_proj: sum_tree -> sum_path -> term -> term
  val mk_inj: sum_tree -> sum_path -> term -> term

  val mk_sumcases: sum_tree -> typ -> term list -> term
end


structure SumTools: SUM_TOOLS =
struct

val inlN = "Sum_Type.Inl"
val inrN = "Sum_Type.Inr"
val sumcaseN = "Datatype.sum.sum_case"

val projlN = "FunDef.lproj"
val projrN = "FunDef.rproj"
val projl_inl = thm "FunDef.lproj_inl"
val projr_inr = thm "FunDef.rproj_inr"



fun mk_sumT LT RT = Type ("+", [LT, RT])
fun mk_sumcase TL TR T l r = Const (sumcaseN, (TL --> T) --> (TR --> T) --> mk_sumT TL TR --> T) $ l $ r


datatype sum_tree 
  = Leaf of typ
  | Branch of (typ * (typ * sum_tree) * (typ * sum_tree))

type sum_path = bool list (* true: left, false: right *)

fun sum_type_of (Leaf T) = T
  | sum_type_of (Branch (ST,(LT,_),(RT,_))) = ST


fun mk_tree Ts =
    let 
	fun mk_tree' 1 [T] = (T, Leaf T, [[]])
	  | mk_tree' n Ts =
	    let 
		val n2 = n div 2
		val (lTs, rTs) = chop n2 Ts
		val (TL, ltree, lpaths) = mk_tree' n2 lTs
		val (TR, rtree, rpaths) = mk_tree' (n - n2) rTs
		val T = mk_sumT TL TR
		val pths = map (cons true) lpaths @ map (cons false) rpaths 
	    in
		(T, Branch (T, (TL, ltree), (TR, rtree)), pths)
	    end
    in
	mk_tree' (length Ts) Ts
    end


fun mk_inj (Leaf _) [] t = t
  | mk_inj (Branch (ST, (LT, tr), _)) (true::pth) t = 
    Const (inlN, LT --> ST) $ mk_inj tr pth t
  | mk_inj (Branch (ST, _, (RT, tr))) (false::pth) t = 
    Const (inrN, RT --> ST) $ mk_inj tr pth t
  | mk_inj _ _ _ = sys_error "mk_inj"

fun mk_proj (Leaf _) [] t = t
  | mk_proj (Branch (ST, (LT, tr), _)) (true::pth) t = 
    mk_proj tr pth (Const (projlN, ST --> LT) $ t)
  | mk_proj (Branch (ST, _, (RT, tr))) (false::pth) t = 
    mk_proj tr pth (Const (projrN, ST --> RT) $ t)
  | mk_proj _ _ _ = sys_error "mk_proj"


fun mk_sumcases tree T ts =
    let
	fun mk_sumcases' (Leaf _) (t::ts) = (t,ts)
	  | mk_sumcases' (Branch (ST, (LT, ltr), (RT, rtr))) ts =
	    let
		val (lcase, ts') = mk_sumcases' ltr ts
		val (rcase, ts'') = mk_sumcases' rtr ts'
	    in
		(mk_sumcase LT RT T lcase rcase, ts'')
	    end
	  | mk_sumcases' _ [] = sys_error "mk_sumcases"
    in
	fst (mk_sumcases' tree ts)
    end

end




