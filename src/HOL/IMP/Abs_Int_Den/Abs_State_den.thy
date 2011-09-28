(* Author: Tobias Nipkow *)

theory Abs_State_den
imports Abs_Int_den0_fun
  "~~/src/HOL/Library/Char_ord" "~~/src/HOL/Library/List_lexord"
  (* Library import merely to allow string lists to be sorted for output *)
begin

subsection "Abstract State with Computable Ordering"

text{* A concrete type of state with computable @{text"\<sqsubseteq>"}: *}

datatype 'a astate = FunDom "string \<Rightarrow> 'a" "string list"

fun "fun" where "fun (FunDom f _) = f"
fun dom where "dom (FunDom _ A) = A"

definition [simp]: "inter_list xs ys = [x\<leftarrow>xs. x \<in> set ys]"

definition "list S = [(x,fun S x). x \<leftarrow> sort(dom S)]"

definition "lookup F x = (if x : set(dom F) then fun F x else Top)"

definition "update F x y =
  FunDom ((fun F)(x:=y)) (if x \<in> set(dom F) then dom F else x # dom F)"

lemma lookup_update: "lookup (update S x y) = (lookup S)(x:=y)"
by(rule ext)(auto simp: lookup_def update_def)

instantiation astate :: (SL_top) SL_top
begin

definition "le_astate F G = (ALL x : set(dom G). lookup F x \<sqsubseteq> fun G x)"

definition
"join_astate F G =
 FunDom (\<lambda>x. fun F x \<squnion> fun G x) (inter_list (dom F) (dom G))"

definition "Top = FunDom (\<lambda>x. Top) []"

instance
proof
  case goal2 thus ?case
    apply(auto simp: le_astate_def)
    by (metis lookup_def preord_class.le_trans top)
qed (auto simp: le_astate_def lookup_def join_astate_def Top_astate_def)

end

end
