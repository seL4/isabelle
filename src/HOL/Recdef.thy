(*  Title:      HOL/Recdef.thy
    Author:     Konrad Slind and Markus Wenzel, TU Muenchen
*)

header {* TFL: recursive function definitions *}

theory Recdef
imports FunDef Plain
uses
  ("Tools/TFL/casesplit.ML")
  ("Tools/TFL/utils.ML")
  ("Tools/TFL/usyntax.ML")
  ("Tools/TFL/dcterm.ML")
  ("Tools/TFL/thms.ML")
  ("Tools/TFL/rules.ML")
  ("Tools/TFL/thry.ML")
  ("Tools/TFL/tfl.ML")
  ("Tools/TFL/post.ML")
  ("Tools/recdef.ML")
begin

inductive
  wfrec_rel :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => 'a => 'b => bool"
  for R :: "('a * 'a) set"
  and F :: "('a => 'b) => 'a => 'b"
where
  wfrecI: "ALL z. (z, x) : R --> wfrec_rel R F z (g z) ==>
            wfrec_rel R F x (F g x)"

constdefs
  cut        :: "('a => 'b) => ('a * 'a)set => 'a => 'a => 'b"
  "cut f r x == (%y. if (y,x):r then f y else undefined)"

  adm_wf :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => bool"
  "adm_wf R F == ALL f g x.
     (ALL z. (z, x) : R --> f z = g z) --> F f x = F g x"

  wfrec :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => 'a => 'b"
  [code del]: "wfrec R F == %x. THE y. wfrec_rel R (%f x. F (cut f R x) x) x y"

subsection{*Well-Founded Recursion*}

text{*cut*}

lemma cuts_eq: "(cut f r x = cut g r x) = (ALL y. (y,x):r --> f(y)=g(y))"
by (simp add: expand_fun_eq cut_def)

lemma cut_apply: "(x,a):r ==> (cut f r a)(x) = f(x)"
by (simp add: cut_def)

text{*Inductive characterization of wfrec combinator; for details see:
John Harrison, "Inductive definitions: automation and application"*}

lemma wfrec_unique: "[| adm_wf R F; wf R |] ==> EX! y. wfrec_rel R F x y"
apply (simp add: adm_wf_def)
apply (erule_tac a=x in wf_induct)
apply (rule ex1I)
apply (rule_tac g = "%x. THE y. wfrec_rel R F x y" in wfrec_rel.wfrecI)
apply (fast dest!: theI')
apply (erule wfrec_rel.cases, simp)
apply (erule allE, erule allE, erule allE, erule mp)
apply (fast intro: the_equality [symmetric])
done

lemma adm_lemma: "adm_wf R (%f x. F (cut f R x) x)"
apply (simp add: adm_wf_def)
apply (intro strip)
apply (rule cuts_eq [THEN iffD2, THEN subst], assumption)
apply (rule refl)
done

lemma wfrec: "wf(r) ==> wfrec r H a = H (cut (wfrec r H) r a) a"
apply (simp add: wfrec_def)
apply (rule adm_lemma [THEN wfrec_unique, THEN the1_equality], assumption)
apply (rule wfrec_rel.wfrecI)
apply (intro strip)
apply (erule adm_lemma [THEN wfrec_unique, THEN theI'])
done


text{** This form avoids giant explosions in proofs.  NOTE USE OF ==*}
lemma def_wfrec: "[| f==wfrec r H;  wf(r) |] ==> f(a) = H (cut f r a) a"
apply auto
apply (blast intro: wfrec)
done


lemma tfl_wf_induct: "ALL R. wf R -->  
       (ALL P. (ALL x. (ALL y. (y,x):R --> P y) --> P x) --> (ALL x. P x))"
apply clarify
apply (rule_tac r = R and P = P and a = x in wf_induct, assumption, blast)
done

lemma tfl_cut_apply: "ALL f R. (x,a):R --> (cut f R a)(x) = f(x)"
apply clarify
apply (rule cut_apply, assumption)
done

lemma tfl_wfrec:
     "ALL M R f. (f=wfrec R M) --> wf R --> (ALL x. f x = M (cut f R x) x)"
apply clarify
apply (erule wfrec)
done

lemma tfl_eq_True: "(x = True) --> x"
  by blast

lemma tfl_rev_eq_mp: "(x = y) --> y --> x";
  by blast

lemma tfl_simp_thm: "(x --> y) --> (x = x') --> (x' --> y)"
  by blast

lemma tfl_P_imp_P_iff_True: "P ==> P = True"
  by blast

lemma tfl_imp_trans: "(A --> B) ==> (B --> C) ==> (A --> C)"
  by blast

lemma tfl_disj_assoc: "(a \<or> b) \<or> c == a \<or> (b \<or> c)"
  by simp

lemma tfl_disjE: "P \<or> Q ==> P --> R ==> Q --> R ==> R"
  by blast

lemma tfl_exE: "\<exists>x. P x ==> \<forall>x. P x --> Q ==> Q"
  by blast

use "Tools/TFL/casesplit.ML"
use "Tools/TFL/utils.ML"
use "Tools/TFL/usyntax.ML"
use "Tools/TFL/dcterm.ML"
use "Tools/TFL/thms.ML"
use "Tools/TFL/rules.ML"
use "Tools/TFL/thry.ML"
use "Tools/TFL/tfl.ML"
use "Tools/TFL/post.ML"
use "Tools/recdef.ML"
setup Recdef.setup

text {*Wellfoundedness of @{text same_fst}*}

definition
 same_fst :: "('a => bool) => ('a => ('b * 'b)set) => (('a*'b)*('a*'b))set"
where
    "same_fst P R == {((x',y'),(x,y)) . x'=x & P x & (y',y) : R x}"
   --{*For @{text rec_def} declarations where the first n parameters
       stay unchanged in the recursive call. *}

lemma same_fstI [intro!]:
     "[| P x; (y',y) : R x |] ==> ((x,y'),(x,y)) : same_fst P R"
by (simp add: same_fst_def)

lemma wf_same_fst:
  assumes prem: "(!!x. P x ==> wf(R x))"
  shows "wf(same_fst P R)"
apply (simp cong del: imp_cong add: wf_def same_fst_def)
apply (intro strip)
apply (rename_tac a b)
apply (case_tac "wf (R a)")
 apply (erule_tac a = b in wf_induct, blast)
apply (blast intro: prem)
done

text {*Rule setup*}

lemmas [recdef_simp] =
  inv_image_def
  measure_def
  lex_prod_def
  same_fst_def
  less_Suc_eq [THEN iffD2]

lemmas [recdef_cong] =
  if_cong let_cong image_cong INT_cong UN_cong bex_cong ball_cong imp_cong

lemmas [recdef_wf] =
  wf_trancl
  wf_less_than
  wf_lex_prod
  wf_inv_image
  wf_measure
  wf_pred_nat
  wf_same_fst
  wf_empty

end
