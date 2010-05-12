(*  Title:      HOL/SMT/Tools/smt_additional_facts.ML
    Author:     Sascha Boehme, TU Muenchen

Include additional facts.
*)

signature SMT_ADDITIONAL_FACTS =
sig
  val add_facts: thm list -> thm list
end

structure SMT_Additional_Facts: SMT_ADDITIONAL_FACTS =
struct

infix 2 ??
fun (ex ?? f) thms = if exists (ex o Thm.prop_of) thms then f thms else thms



(* pairs *)

val pair_rules = [@{thm fst_conv}, @{thm snd_conv}, @{thm pair_collapse}]

val pair_type = (fn Type (@{type_name "*"}, _) => true | _ => false)
val exists_pair_type = Term.exists_type (Term.exists_subtype pair_type)

val add_pair_rules = exists_pair_type ?? append pair_rules



(* function update *)

val fun_upd_rules = [@{thm fun_upd_same}, @{thm fun_upd_apply}]

val is_fun_upd = (fn Const (@{const_name fun_upd}, _) => true | _ => false)
val exists_fun_upd = Term.exists_subterm is_fun_upd

val add_fun_upd_rules = exists_fun_upd ?? append fun_upd_rules


(* include additional facts *)

val add_facts = add_pair_rules #> add_fun_upd_rules

end
