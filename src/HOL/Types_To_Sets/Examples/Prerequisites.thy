(*  Title:      HOL/Types_To_Sets/Examples/Prerequisites.thy
    Author:     Ondřej Kunčar, TU München
*)

theory Prerequisites
  imports Main
  keywords "lemmas_with" :: thy_decl
begin

context
  fixes Rep Abs A T
  assumes type: "type_definition Rep Abs A"
  assumes T_def: "T \<equiv> (\<lambda>(x::'a) (y::'b). x = Rep y)"
begin

lemma type_definition_Domainp: "Domainp T = (\<lambda>x. x \<in> A)"
proof -
  interpret type_definition Rep Abs A by(rule type)
  show ?thesis
    unfolding Domainp_iff[abs_def] T_def fun_eq_iff
    by (metis Abs_inverse Rep)
qed

end

subsection \<open>setting up transfer for local typedef\<close>

lemmas [transfer_rule] = \<comment> \<open>prefer right-total rules\<close>
  right_total_All_transfer
  right_total_UNIV_transfer
  right_total_Ex_transfer

locale local_typedef = fixes S ::"'b set" and s::"'s itself"
  assumes Ex_type_definition_S: "\<exists>(Rep::'s \<Rightarrow> 'b) (Abs::'b \<Rightarrow> 's). type_definition Rep Abs S"
begin

definition "rep = fst (SOME (Rep::'s \<Rightarrow> 'b, Abs). type_definition Rep Abs S)"
definition "Abs = snd (SOME (Rep::'s \<Rightarrow> 'b, Abs). type_definition Rep Abs S)"

lemma type_definition_S: "type_definition rep Abs S"
  unfolding Abs_def rep_def split_beta'
  by (rule someI_ex) (use Ex_type_definition_S in auto)

lemma rep_in_S[simp]: "rep x \<in> S"
  and rep_inverse[simp]: "Abs (rep x) = x"
  and Abs_inverse[simp]: "y \<in> S \<Longrightarrow> rep (Abs y) = y"
  using type_definition_S
  unfolding type_definition_def by auto

definition cr_S where "cr_S \<equiv> \<lambda>s b. s = rep b"
lemmas Domainp_cr_S = type_definition_Domainp[OF type_definition_S cr_S_def, transfer_domain_rule]
lemmas right_total_cr_S = typedef_right_total[OF type_definition_S cr_S_def, transfer_rule]
  and bi_unique_cr_S = typedef_bi_unique[OF type_definition_S cr_S_def, transfer_rule]
  and left_unique_cr_S = typedef_left_unique[OF type_definition_S cr_S_def, transfer_rule]
  and right_unique_cr_S = typedef_right_unique[OF type_definition_S cr_S_def, transfer_rule]

lemma cr_S_rep[intro, simp]: "cr_S (rep a) a" by (simp add: cr_S_def)
lemma cr_S_Abs[intro, simp]: "a\<in>S \<Longrightarrow> cr_S a (Abs a)" by (simp add: cr_S_def)

end

subsection \<open>some \<close>

subsection \<open>Tool support\<close>

lemmas subset_iff' = subset_iff[folded Ball_def]

ML \<open>
structure More_Simplifier =
struct

fun asm_full_var_simplify ctxt thm =
  let
    val ((_, [thm']), ctxt') = Variable.import false [thm] ctxt
  in
    Simplifier.asm_full_simplify ctxt' thm'
    |> singleton (Variable.export ctxt' ctxt)
    |> Drule.zero_var_indexes
  end

fun var_simplify_only ctxt ths thm =
  asm_full_var_simplify (Simplifier.clear_simpset ctxt addsimps ths) thm

val var_simplified = Attrib.thms >>
  (fn ths => Thm.rule_attribute ths
    (fn context => var_simplify_only (Context.proof_of context) ths))

val _ = Theory.setup (Attrib.setup \<^binding>\<open>var_simplified\<close> var_simplified "simplified rule (with vars)")

end
\<close>

ML \<open>
val _ = Outer_Syntax.local_theory' \<^command_keyword>\<open>lemmas_with\<close> "note theorems with (the same) attributes"
    (Parse.attribs --| \<^keyword>\<open>:\<close> -- Parse_Spec.name_facts -- Parse.for_fixes
     >> (fn (((attrs),facts), fixes) =>
      #2 oo Specification.theorems_cmd Thm.theoremK
        (map (apsnd (map (apsnd (fn xs => attrs@xs)))) facts) fixes))
\<close>

end
