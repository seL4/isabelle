(*  Title:      HOL/HOLCF/Tr.thy
    Author:     Franz Regensburger
*)

section \<open>The type of lifted booleans\<close>

theory Tr
  imports Lift
begin

subsection \<open>Type definition and constructors\<close>

type_synonym tr = "bool lift"

translations
  (type) "tr" \<leftharpoondown> (type) "bool lift"

definition TT :: "tr"
  where "TT = Def True"

definition FF :: "tr"
  where "FF = Def False"

text \<open>Exhaustion and Elimination for type \<^typ>\<open>tr\<close>\<close>

lemma Exh_tr: "t = \<bottom> \<or> t = TT \<or> t = FF"
  by (induct t) (auto simp: FF_def TT_def)

lemma trE [case_names bottom TT FF, cases type: tr]:
  "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; p = TT \<Longrightarrow> Q; p = FF \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (induct p) (auto simp: FF_def TT_def)

lemma tr_induct [case_names bottom TT FF, induct type: tr]:
  "P \<bottom> \<Longrightarrow> P TT \<Longrightarrow> P FF \<Longrightarrow> P x"
  by (cases x) simp_all

text \<open>distinctness for type \<^typ>\<open>tr\<close>\<close>

lemma dist_below_tr [simp]:
  "TT \<notsqsubseteq> \<bottom>" "FF \<notsqsubseteq> \<bottom>" "TT \<notsqsubseteq> FF" "FF \<notsqsubseteq> TT"
  by (simp_all add: TT_def FF_def)

lemma dist_eq_tr [simp]: "TT \<noteq> \<bottom>" "FF \<noteq> \<bottom>" "TT \<noteq> FF" "\<bottom> \<noteq> TT" "\<bottom> \<noteq> FF" "FF \<noteq> TT"
  by (simp_all add: TT_def FF_def)

lemma TT_below_iff [simp]: "TT \<sqsubseteq> x \<longleftrightarrow> x = TT"
  by (induct x) simp_all

lemma FF_below_iff [simp]: "FF \<sqsubseteq> x \<longleftrightarrow> x = FF"
  by (induct x) simp_all

lemma not_below_TT_iff [simp]: "x \<notsqsubseteq> TT \<longleftrightarrow> x = FF"
  by (induct x) simp_all

lemma not_below_FF_iff [simp]: "x \<notsqsubseteq> FF \<longleftrightarrow> x = TT"
  by (induct x) simp_all


subsection \<open>Case analysis\<close>

default_sort pcpo

definition tr_case :: "'a \<rightarrow> 'a \<rightarrow> tr \<rightarrow> 'a"
  where "tr_case = (\<Lambda> t e (Def b). if b then t else e)"

abbreviation cifte_syn :: "[tr, 'c, 'c] \<Rightarrow> 'c"  (\<open>(If (_)/ then (_)/ else (_))\<close> [0, 0, 60] 60)
  where "If b then e1 else e2 \<equiv> tr_case\<cdot>e1\<cdot>e2\<cdot>b"

translations
  "\<Lambda> (XCONST TT). t" \<rightleftharpoons> "CONST tr_case\<cdot>t\<cdot>\<bottom>"
  "\<Lambda> (XCONST FF). t" \<rightleftharpoons> "CONST tr_case\<cdot>\<bottom>\<cdot>t"

lemma ifte_thms [simp]:
  "If \<bottom> then e1 else e2 = \<bottom>"
  "If FF then e1 else e2 = e2"
  "If TT then e1 else e2 = e1"
  by (simp_all add: tr_case_def TT_def FF_def)


subsection \<open>Boolean connectives\<close>

definition trand :: "tr \<rightarrow> tr \<rightarrow> tr"
  where andalso_def: "trand = (\<Lambda> x y. If x then y else FF)"

abbreviation andalso_syn :: "tr \<Rightarrow> tr \<Rightarrow> tr"  (\<open>_ andalso _\<close> [36,35] 35)
  where "x andalso y \<equiv> trand\<cdot>x\<cdot>y"

definition tror :: "tr \<rightarrow> tr \<rightarrow> tr"
  where orelse_def: "tror = (\<Lambda> x y. If x then TT else y)"

abbreviation orelse_syn :: "tr \<Rightarrow> tr \<Rightarrow> tr"  (\<open>_ orelse _\<close>  [31,30] 30)
  where "x orelse y \<equiv> tror\<cdot>x\<cdot>y"

definition neg :: "tr \<rightarrow> tr"
  where "neg = flift2 Not"

definition If2 :: "tr \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"
  where "If2 Q x y = (If Q then x else y)"

text \<open>tactic for tr-thms with case split\<close>

lemmas tr_defs = andalso_def orelse_def neg_def tr_case_def TT_def FF_def

text \<open>lemmas about andalso, orelse, neg and if\<close>

lemma andalso_thms [simp]:
  "(TT andalso y) = y"
  "(FF andalso y) = FF"
  "(\<bottom> andalso y) = \<bottom>"
  "(y andalso TT) = y"
  "(y andalso y) = y"
      apply (unfold andalso_def, simp_all)
   apply (cases y, simp_all)
  apply (cases y, simp_all)
  done

lemma orelse_thms [simp]:
  "(TT orelse y) = TT"
  "(FF orelse y) = y"
  "(\<bottom> orelse y) = \<bottom>"
  "(y orelse FF) = y"
  "(y orelse y) = y"
      apply (unfold orelse_def, simp_all)
   apply (cases y, simp_all)
  apply (cases y, simp_all)
  done

lemma neg_thms [simp]:
  "neg\<cdot>TT = FF"
  "neg\<cdot>FF = TT"
  "neg\<cdot>\<bottom> = \<bottom>"
  by (simp_all add: neg_def TT_def FF_def)

text \<open>split-tac for If via If2 because the constant has to be a constant\<close>

lemma split_If2: "P (If2 Q x y) \<longleftrightarrow> ((Q = \<bottom> \<longrightarrow> P \<bottom>) \<and> (Q = TT \<longrightarrow> P x) \<and> (Q = FF \<longrightarrow> P y))"
  by (cases Q) (simp_all add: If2_def)

(* FIXME unused!? *)
ML \<open>
fun split_If_tac ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm If2_def} RS sym])
    THEN' (split_tac ctxt [@{thm split_If2}])
\<close>

subsection "Rewriting of HOLCF operations to HOL functions"

lemma andalso_or: "t \<noteq> \<bottom> \<Longrightarrow> (t andalso s) = FF \<longleftrightarrow> t = FF \<or> s = FF"
  by (cases t) simp_all

lemma andalso_and: "t \<noteq> \<bottom> \<Longrightarrow> ((t andalso s) \<noteq> FF) \<longleftrightarrow> t \<noteq> FF \<and> s \<noteq> FF"
  by (cases t) simp_all

lemma Def_bool1 [simp]: "Def x \<noteq> FF \<longleftrightarrow> x"
  by (simp add: FF_def)

lemma Def_bool2 [simp]: "Def x = FF \<longleftrightarrow> \<not> x"
  by (simp add: FF_def)

lemma Def_bool3 [simp]: "Def x = TT \<longleftrightarrow> x"
  by (simp add: TT_def)

lemma Def_bool4 [simp]: "Def x \<noteq> TT \<longleftrightarrow> \<not> x"
  by (simp add: TT_def)

lemma If_and_if: "(If Def P then A else B) = (if P then A else B)"
  by (cases "Def P") (auto simp add: TT_def[symmetric] FF_def[symmetric])


subsection \<open>Compactness\<close>

lemma compact_TT: "compact TT"
  by (rule compact_chfin)

lemma compact_FF: "compact FF"
  by (rule compact_chfin)

end
