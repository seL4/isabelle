theory FunDef
imports Accessible_Part
uses 
("Tools/function_package/fundef_common.ML")
("Tools/function_package/fundef_lib.ML")
("Tools/function_package/context_tree.ML")
("Tools/function_package/fundef_prep.ML")
("Tools/function_package/fundef_proof.ML")
("Tools/function_package/termination.ML")
("Tools/function_package/fundef_package.ML")
begin

lemma fundef_ex1_existence:
assumes f_def: "\<And>x. f x \<equiv> THE y. (x,y)\<in>G"
assumes ex1: "\<exists>!y. (x,y)\<in>G"
shows "(x, f x)\<in>G"
  by (simp only:f_def, rule theI', rule ex1)

lemma fundef_ex1_uniqueness:
assumes f_def: "\<And>x. f x \<equiv> THE y. (x,y)\<in>G"
assumes ex1: "\<exists>!y. (x,y)\<in>G"
assumes elm: "(x, h x)\<in>G"
shows "h x = f x"
  by (simp only:f_def, rule the1_equality[symmetric], rule ex1, rule elm)

lemma fundef_ex1_iff:
assumes f_def: "\<And>x. f x \<equiv> THE y. (x,y)\<in>G"
assumes ex1: "\<exists>!y. (x,y)\<in>G"
shows "((x, y)\<in>G) = (f x = y)"
  apply (auto simp:ex1 f_def the1_equality)
  by (rule theI', rule ex1)

lemma True_implies: "(True \<Longrightarrow> PROP P) \<equiv> PROP P"
  by simp


use "Tools/function_package/fundef_common.ML"
use "Tools/function_package/fundef_lib.ML"
use "Tools/function_package/context_tree.ML"
use "Tools/function_package/fundef_prep.ML"
use "Tools/function_package/fundef_proof.ML"
use "Tools/function_package/termination.ML"
use "Tools/function_package/fundef_package.ML"

setup FundefPackage.setup



end
