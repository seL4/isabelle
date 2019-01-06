(*  Title:      HOL/Predicate_Compile.thy
    Author:     Stefan Berghofer, Lukas Bulwahn, Florian Haftmann, TU Muenchen
*)

section \<open>A compiler for predicates defined by introduction rules\<close>

theory Predicate_Compile
imports Random_Sequence Quickcheck_Exhaustive
keywords
  "code_pred" :: thy_goal and
  "values" :: diag
begin

ML_file \<open>Tools/Predicate_Compile/predicate_compile_aux.ML\<close>
ML_file \<open>Tools/Predicate_Compile/predicate_compile_compilations.ML\<close>
ML_file \<open>Tools/Predicate_Compile/core_data.ML\<close>
ML_file \<open>Tools/Predicate_Compile/mode_inference.ML\<close>
ML_file \<open>Tools/Predicate_Compile/predicate_compile_proof.ML\<close>
ML_file \<open>Tools/Predicate_Compile/predicate_compile_core.ML\<close>
ML_file \<open>Tools/Predicate_Compile/predicate_compile_data.ML\<close>
ML_file \<open>Tools/Predicate_Compile/predicate_compile_fun.ML\<close>
ML_file \<open>Tools/Predicate_Compile/predicate_compile_pred.ML\<close>
ML_file \<open>Tools/Predicate_Compile/predicate_compile_specialisation.ML\<close>
ML_file \<open>Tools/Predicate_Compile/predicate_compile.ML\<close>


subsection \<open>Set membership as a generator predicate\<close>

text \<open>
  Introduce a new constant for membership to allow 
  fine-grained control in code equations. 
\<close>

definition contains :: "'a set => 'a => bool"
where "contains A x \<longleftrightarrow> x \<in> A"

definition contains_pred :: "'a set => 'a => unit Predicate.pred"
where "contains_pred A x = (if x \<in> A then Predicate.single () else bot)"

lemma pred_of_setE:
  assumes "Predicate.eval (pred_of_set A) x"
  obtains "contains A x"
using assms by(simp add: contains_def)

lemma pred_of_setI: "contains A x ==> Predicate.eval (pred_of_set A) x"
by(simp add: contains_def)

lemma pred_of_set_eq: "pred_of_set \<equiv> \<lambda>A. Predicate.Pred (contains A)"
by(simp add: contains_def[abs_def] pred_of_set_def o_def)

lemma containsI: "x \<in> A ==> contains A x" 
by(simp add: contains_def)

lemma containsE: assumes "contains A x"
  obtains A' x' where "A = A'" "x = x'" "x \<in> A"
using assms by(simp add: contains_def)

lemma contains_predI: "contains A x ==> Predicate.eval (contains_pred A x) ()"
by(simp add: contains_pred_def contains_def)

lemma contains_predE: 
  assumes "Predicate.eval (contains_pred A x) y"
  obtains "contains A x"
using assms by(simp add: contains_pred_def contains_def split: if_split_asm)

lemma contains_pred_eq: "contains_pred \<equiv> \<lambda>A x. Predicate.Pred (\<lambda>y. contains A x)"
by(rule eq_reflection)(auto simp add: contains_pred_def fun_eq_iff contains_def intro: pred_eqI)

lemma contains_pred_notI:
   "\<not> contains A x ==> Predicate.eval (Predicate.not_pred (contains_pred A x)) ()"
by(simp add: contains_pred_def contains_def not_pred_eq)

setup \<open>
let
  val Fun = Predicate_Compile_Aux.Fun
  val Input = Predicate_Compile_Aux.Input
  val Output = Predicate_Compile_Aux.Output
  val Bool = Predicate_Compile_Aux.Bool
  val io = Fun (Input, Fun (Output, Bool))
  val ii = Fun (Input, Fun (Input, Bool))
in
  Core_Data.PredData.map (Graph.new_node 
    (\<^const_name>\<open>contains\<close>, 
     Core_Data.PredData {
       pos = Position.thread_data (),
       intros = [(NONE, @{thm containsI})], 
       elim = SOME @{thm containsE}, 
       preprocessed = true,
       function_names = [(Predicate_Compile_Aux.Pred, 
         [(io, \<^const_name>\<open>pred_of_set\<close>), (ii, \<^const_name>\<open>contains_pred\<close>)])], 
       predfun_data = [
         (io, Core_Data.PredfunData {
            elim = @{thm pred_of_setE}, intro = @{thm pred_of_setI},
            neg_intro = NONE, definition = @{thm pred_of_set_eq}
          }),
         (ii, Core_Data.PredfunData {
            elim = @{thm contains_predE}, intro = @{thm contains_predI}, 
            neg_intro = SOME @{thm contains_pred_notI}, definition = @{thm contains_pred_eq}
          })],
       needs_random = []}))
end
\<close>

hide_const (open) contains contains_pred
hide_fact (open) pred_of_setE pred_of_setI pred_of_set_eq 
  containsI containsE contains_predI contains_predE contains_pred_eq contains_pred_notI

end
