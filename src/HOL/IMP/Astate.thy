(* Author: Tobias Nipkow *)

theory Astate
imports AbsInt0_fun
begin

subsection "Abstract State with Computable Ordering"

text{* A concrete type of state with computable @{text"\<sqsubseteq>"}: *}

datatype 'a astate = FunDom "string \<Rightarrow> 'a" "string list"

fun "fun" where "fun (FunDom f _) = f"
fun dom where "dom (FunDom _ A) = A"

definition "list S = [(x,fun S x). x \<leftarrow> dom S]"

definition "lookup F x = (if x : set(dom F) then fun F x else Top)"

definition "update F x y =
  FunDom ((fun F)(x:=y)) (if x : set(dom F) then dom F else x # dom F)"

lemma lookup_update: "lookup (update S x y) = (lookup S)(x:=y)"
by(rule ext)(auto simp: lookup_def update_def)

instantiation astate :: (SL_top) SL_top
begin

definition "le_astate F G = (ALL x : set(dom G). lookup F x \<sqsubseteq> fun G x)"

definition
"join_astate F G =
 FunDom (%x. fun F x \<squnion> fun G x) ([x\<leftarrow>dom F. x : set(dom G)])"

definition "Top = FunDom (%x. Top) []"

instance
proof
  case goal2 thus ?case
    apply(auto simp: le_astate_def)
    by (metis lookup_def preord_class.le_trans top)
qed (auto simp: le_astate_def lookup_def join_astate_def Top_astate_def)

end

end
