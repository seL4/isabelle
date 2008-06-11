(*  Title:      HOLCF/Tr.thy
    ID:         $Id$
    Author:     Franz Regensburger

Introduce infix if_then_else_fi and boolean connectives andalso, orelse.
*)

header {* The type of lifted booleans *}

theory Tr
imports Lift
begin

defaultsort pcpo

types
  tr = "bool lift"

translations
  "tr" <= (type) "bool lift"

definition
  TT :: "tr" where
  "TT = Def True"

definition
  FF :: "tr" where
  "FF = Def False"

definition
  trifte :: "'c \<rightarrow> 'c \<rightarrow> tr \<rightarrow> 'c" where
  ifte_def: "trifte = (\<Lambda> t e. FLIFT b. if b then t else e)"
abbreviation
  cifte_syn :: "[tr, 'c, 'c] \<Rightarrow> 'c"  ("(3If _/ (then _/ else _) fi)" 60)  where
  "If b then e1 else e2 fi == trifte\<cdot>e1\<cdot>e2\<cdot>b"

definition
  trand :: "tr \<rightarrow> tr \<rightarrow> tr" where
  andalso_def: "trand = (\<Lambda> x y. If x then y else FF fi)"
abbreviation
  andalso_syn :: "tr \<Rightarrow> tr \<Rightarrow> tr"  ("_ andalso _" [36,35] 35)  where
  "x andalso y == trand\<cdot>x\<cdot>y"

definition
  tror :: "tr \<rightarrow> tr \<rightarrow> tr" where
  orelse_def: "tror = (\<Lambda> x y. If x then TT else y fi)"
abbreviation
  orelse_syn :: "tr \<Rightarrow> tr \<Rightarrow> tr"  ("_ orelse _"  [31,30] 30)  where
  "x orelse y == tror\<cdot>x\<cdot>y"

definition
  neg :: "tr \<rightarrow> tr" where
  "neg = flift2 Not"

definition
  If2 :: "[tr, 'c, 'c] \<Rightarrow> 'c" where
  "If2 Q x y = (If Q then x else y fi)"

translations
  "\<Lambda> (CONST TT). t" == "CONST trifte\<cdot>t\<cdot>\<bottom>"
  "\<Lambda> (CONST FF). t" == "CONST trifte\<cdot>\<bottom>\<cdot>t"


text {* Exhaustion and Elimination for type @{typ tr} *}

lemma Exh_tr: "t = \<bottom> \<or> t = TT \<or> t = FF"
apply (unfold FF_def TT_def)
apply (induct t)
apply fast
apply fast
done

lemma trE: "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; p = TT \<Longrightarrow> Q; p = FF \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (rule Exh_tr [THEN disjE])
apply fast
apply (erule disjE)
apply fast
apply fast
done

text {* tactic for tr-thms with case split *}

lemmas tr_defs = andalso_def orelse_def neg_def ifte_def TT_def FF_def


text {* distinctness for type @{typ tr} *}

lemma dist_less_tr [simp]:
  "\<not> TT \<sqsubseteq> \<bottom>" "\<not> FF \<sqsubseteq> \<bottom>" "\<not> TT \<sqsubseteq> FF" "\<not> FF \<sqsubseteq> TT"
by (simp_all add: tr_defs)

lemma dist_eq_tr [simp]:
  "TT \<noteq> \<bottom>" "FF \<noteq> \<bottom>" "TT \<noteq> FF" "\<bottom> \<noteq> TT" "\<bottom> \<noteq> FF" "FF \<noteq> TT"
by (simp_all add: tr_defs)

text {* lemmas about andalso, orelse, neg and if *}

lemma ifte_thms [simp]:
  "If \<bottom> then e1 else e2 fi = \<bottom>"
  "If FF then e1 else e2 fi = e2"
  "If TT then e1 else e2 fi = e1"
by (simp_all add: ifte_def TT_def FF_def)

lemma andalso_thms [simp]:
  "(TT andalso y) = y"
  "(FF andalso y) = FF"
  "(\<bottom> andalso y) = \<bottom>"
  "(y andalso TT) = y"
  "(y andalso y) = y"
apply (unfold andalso_def, simp_all)
apply (rule_tac p=y in trE, simp_all)
apply (rule_tac p=y in trE, simp_all)
done

lemma orelse_thms [simp]:
  "(TT orelse y) = TT"
  "(FF orelse y) = y"
  "(\<bottom> orelse y) = \<bottom>"
  "(y orelse FF) = y"
  "(y orelse y) = y"
apply (unfold orelse_def, simp_all)
apply (rule_tac p=y in trE, simp_all)
apply (rule_tac p=y in trE, simp_all)
done

lemma neg_thms [simp]:
  "neg\<cdot>TT = FF"
  "neg\<cdot>FF = TT"
  "neg\<cdot>\<bottom> = \<bottom>"
by (simp_all add: neg_def TT_def FF_def)

text {* split-tac for If via If2 because the constant has to be a constant *}

lemma split_If2:
  "P (If2 Q x y) = ((Q = \<bottom> \<longrightarrow> P \<bottom>) \<and> (Q = TT \<longrightarrow> P x) \<and> (Q = FF \<longrightarrow> P y))"
apply (unfold If2_def)
apply (rule_tac p = "Q" in trE)
apply (simp_all)
done

ML {*
val split_If_tac =
  simp_tac (HOL_basic_ss addsimps [@{thm If2_def} RS sym])
    THEN' (split_tac [@{thm split_If2}])
*}

subsection "Rewriting of HOLCF operations to HOL functions"

lemma andalso_or:
  "t \<noteq> \<bottom> \<Longrightarrow> ((t andalso s) = FF) = (t = FF \<or> s = FF)"
apply (rule_tac p = "t" in trE)
apply simp_all
done

lemma andalso_and:
  "t \<noteq> \<bottom> \<Longrightarrow> ((t andalso s) \<noteq> FF) = (t \<noteq> FF \<and> s \<noteq> FF)"
apply (rule_tac p = "t" in trE)
apply simp_all
done

lemma Def_bool1 [simp]: "(Def x \<noteq> FF) = x"
by (simp add: FF_def)

lemma Def_bool2 [simp]: "(Def x = FF) = (\<not> x)"
by (simp add: FF_def)

lemma Def_bool3 [simp]: "(Def x = TT) = x"
by (simp add: TT_def)

lemma Def_bool4 [simp]: "(Def x \<noteq> TT) = (\<not> x)"
by (simp add: TT_def)

lemma If_and_if:
  "(If Def P then A else B fi) = (if P then A else B)"
apply (rule_tac p = "Def P" in trE)
apply (auto simp add: TT_def[symmetric] FF_def[symmetric])
done

subsection {* Compactness *}

lemma compact_TT [simp]: "compact TT"
by (rule compact_chfin)

lemma compact_FF [simp]: "compact FF"
by (rule compact_chfin)

end
