theory FunDef
imports Accessible_Part Datatype Recdef
uses 
("Tools/function_package/sum_tools.ML")
("Tools/function_package/fundef_common.ML")
("Tools/function_package/fundef_lib.ML")
("Tools/function_package/context_tree.ML")
("Tools/function_package/fundef_prep.ML")
("Tools/function_package/fundef_proof.ML")
("Tools/function_package/termination.ML")
("Tools/function_package/mutual.ML")
("Tools/function_package/fundef_package.ML")
("Tools/function_package/fundef_datatype.ML")
("Tools/function_package/auto_term.ML")
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


subsection {* Projections *}
consts
  lpg::"(('a + 'b) * 'a) set"
  rpg::"(('a + 'b) * 'b) set"

inductive lpg
intros
  "(Inl x, x) : lpg"
inductive rpg
intros
  "(Inr y, y) : rpg"
definition
  "lproj x = (THE y. (x,y) : lpg)"
  "rproj x = (THE y. (x,y) : rpg)"

lemma lproj_inl:
  "lproj (Inl x) = x"
  by (auto simp:lproj_def intro: the_equality lpg.intros elim: lpg.cases)
lemma rproj_inr:
  "rproj (Inr x) = x"
  by (auto simp:rproj_def intro: the_equality rpg.intros elim: rpg.cases)




use "Tools/function_package/sum_tools.ML"
use "Tools/function_package/fundef_common.ML"
use "Tools/function_package/fundef_lib.ML"
use "Tools/function_package/context_tree.ML"
use "Tools/function_package/fundef_prep.ML"
use "Tools/function_package/fundef_proof.ML"
use "Tools/function_package/termination.ML"
use "Tools/function_package/mutual.ML"
use "Tools/function_package/fundef_package.ML"

setup FundefPackage.setup

use "Tools/function_package/fundef_datatype.ML"
setup FundefDatatype.setup

use "Tools/function_package/auto_term.ML"
setup FundefAutoTerm.setup


lemmas [fundef_cong] = 
  let_cong if_cong image_cong INT_cong UN_cong bex_cong ball_cong imp_cong


end
