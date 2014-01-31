(*  Title:      HOL/Wfrec.thy
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Konrad Slind
*)

header {* Well-Founded Recursion Combinator *}

theory Wfrec
imports Wellfounded
begin

inductive
  wfrec_rel :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => 'a => 'b => bool"
  for R :: "('a * 'a) set"
  and F :: "('a => 'b) => 'a => 'b"
where
  wfrecI: "ALL z. (z, x) : R --> wfrec_rel R F z (g z) ==>
            wfrec_rel R F x (F g x)"

definition
  cut        :: "('a => 'b) => ('a * 'a)set => 'a => 'a => 'b" where
  "cut f r x == (%y. if (y,x):r then f y else undefined)"

definition
  adm_wf :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => bool" where
  "adm_wf R F == ALL f g x.
     (ALL z. (z, x) : R --> f z = g z) --> F f x = F g x"

definition
  wfrec :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => 'a => 'b" where
  "wfrec R F == %x. THE y. wfrec_rel R (%f x. F (cut f R x) x) x y"

lemma cuts_eq: "(cut f r x = cut g r x) = (ALL y. (y,x):r --> f(y)=g(y))"
by (simp add: fun_eq_iff cut_def)

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
apply (blast intro: the_equality [symmetric])
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


subsection {* Wellfoundedness of @{text same_fst} *}

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

end
