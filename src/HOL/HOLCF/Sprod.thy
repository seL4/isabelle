(*  Title:      HOL/HOLCF/Sprod.thy
    Author:     Franz Regensburger
    Author:     Brian Huffman
*)

section \<open>The type of strict products\<close>

theory Sprod
  imports Cfun
begin

default_sort pcpo


subsection \<open>Definition of strict product type\<close>

definition "sprod = {p::'a \<times> 'b. p = \<bottom> \<or> (fst p \<noteq> \<bottom> \<and> snd p \<noteq> \<bottom>)}"

pcpodef ('a, 'b) sprod  (\<open>(\<open>notation=\<open>infix strict product\<close>\<close>_ \<otimes>/ _)\<close> [21,20] 20) = "sprod :: ('a \<times> 'b) set"
  by (simp_all add: sprod_def)

instance sprod :: ("{chfin,pcpo}", "{chfin,pcpo}") chfin
  by (rule typedef_chfin [OF type_definition_sprod below_sprod_def])

type_notation (ASCII)
  sprod  (infixr \<open>**\<close> 20)


subsection \<open>Definitions of constants\<close>

definition sfst :: "('a ** 'b) \<rightarrow> 'a"
  where "sfst = (\<Lambda> p. fst (Rep_sprod p))"

definition ssnd :: "('a ** 'b) \<rightarrow> 'b"
  where "ssnd = (\<Lambda> p. snd (Rep_sprod p))"

definition spair :: "'a \<rightarrow> 'b \<rightarrow> ('a ** 'b)"
  where "spair = (\<Lambda> a b. Abs_sprod (seq\<cdot>b\<cdot>a, seq\<cdot>a\<cdot>b))"

definition ssplit :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> ('a ** 'b) \<rightarrow> 'c"
  where "ssplit = (\<Lambda> f p. seq\<cdot>p\<cdot>(f\<cdot>(sfst\<cdot>p)\<cdot>(ssnd\<cdot>p)))"

syntax
  "_stuple" :: "[logic, args] \<Rightarrow> logic"  (\<open>(\<open>indent=1 notation=\<open>mixfix strict tuple\<close>\<close>'(:_,/ _:'))\<close>)
translations
  "(:x, y, z:)" \<rightleftharpoons> "(:x, (:y, z:):)"
  "(:x, y:)" \<rightleftharpoons> "CONST spair\<cdot>x\<cdot>y"

translations
  "\<Lambda>(CONST spair\<cdot>x\<cdot>y). t" \<rightleftharpoons> "CONST ssplit\<cdot>(\<Lambda> x y. t)"


subsection \<open>Case analysis\<close>

lemma spair_sprod: "(seq\<cdot>b\<cdot>a, seq\<cdot>a\<cdot>b) \<in> sprod"
  by (simp add: sprod_def seq_conv_if)

lemma Rep_sprod_spair: "Rep_sprod (:a, b:) = (seq\<cdot>b\<cdot>a, seq\<cdot>a\<cdot>b)"
  by (simp add: spair_def cont_Abs_sprod Abs_sprod_inverse spair_sprod)

lemmas Rep_sprod_simps =
  Rep_sprod_inject [symmetric] below_sprod_def
  prod_eq_iff below_prod_def
  Rep_sprod_strict Rep_sprod_spair

lemma sprodE [case_names bottom spair, cases type: sprod]:
  obtains "p = \<bottom>" | x y where "p = (:x, y:)" and "x \<noteq> \<bottom>" and "y \<noteq> \<bottom>"
  using Rep_sprod [of p] by (auto simp add: sprod_def Rep_sprod_simps)

lemma sprod_induct [case_names bottom spair, induct type: sprod]:
  "\<lbrakk>P \<bottom>; \<And>x y. \<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> P (:x, y:)\<rbrakk> \<Longrightarrow> P x"
  by (cases x) simp_all


subsection \<open>Properties of \emph{spair}\<close>

lemma spair_strict1 [simp]: "(:\<bottom>, y:) = \<bottom>"
  by (simp add: Rep_sprod_simps)

lemma spair_strict2 [simp]: "(:x, \<bottom>:) = \<bottom>"
  by (simp add: Rep_sprod_simps)

lemma spair_bottom_iff [simp]: "(:x, y:) = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (simp add: Rep_sprod_simps seq_conv_if)

lemma spair_below_iff: "(:a, b:) \<sqsubseteq> (:c, d:) \<longleftrightarrow> a = \<bottom> \<or> b = \<bottom> \<or> (a \<sqsubseteq> c \<and> b \<sqsubseteq> d)"
  by (simp add: Rep_sprod_simps seq_conv_if)

lemma spair_eq_iff: "(:a, b:) = (:c, d:) \<longleftrightarrow> a = c \<and> b = d \<or> (a = \<bottom> \<or> b = \<bottom>) \<and> (c = \<bottom> \<or> d = \<bottom>)"
  by (simp add: Rep_sprod_simps seq_conv_if)

lemma spair_strict: "x = \<bottom> \<or> y = \<bottom> \<Longrightarrow> (:x, y:) = \<bottom>"
  by simp

lemma spair_strict_rev: "(:x, y:) \<noteq> \<bottom> \<Longrightarrow> x \<noteq> \<bottom> \<and> y \<noteq> \<bottom>"
  by simp

lemma spair_defined: "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> (:x, y:) \<noteq> \<bottom>"
  by simp

lemma spair_defined_rev: "(:x, y:) = \<bottom> \<Longrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by simp

lemma spair_below: "x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> (:x, y:) \<sqsubseteq> (:a, b:) \<longleftrightarrow> x \<sqsubseteq> a \<and> y \<sqsubseteq> b"
  by (simp add: spair_below_iff)

lemma spair_eq: "x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> (:x, y:) = (:a, b:) \<longleftrightarrow> x = a \<and> y = b"
  by (simp add: spair_eq_iff)

lemma spair_inject: "x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> (:x, y:) = (:a, b:) \<Longrightarrow> x = a \<and> y = b"
  by (rule spair_eq [THEN iffD1])

lemma inst_sprod_pcpo2: "\<bottom> = (:\<bottom>, \<bottom>:)"
  by simp

lemma sprodE2: "(\<And>x y. p = (:x, y:) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (cases p) (simp only: inst_sprod_pcpo2, simp)


subsection \<open>Properties of \emph{sfst} and \emph{ssnd}\<close>

lemma sfst_strict [simp]: "sfst\<cdot>\<bottom> = \<bottom>"
  by (simp add: sfst_def cont_Rep_sprod Rep_sprod_strict)

lemma ssnd_strict [simp]: "ssnd\<cdot>\<bottom> = \<bottom>"
  by (simp add: ssnd_def cont_Rep_sprod Rep_sprod_strict)

lemma sfst_spair [simp]: "y \<noteq> \<bottom> \<Longrightarrow> sfst\<cdot>(:x, y:) = x"
  by (simp add: sfst_def cont_Rep_sprod Rep_sprod_spair)

lemma ssnd_spair [simp]: "x \<noteq> \<bottom> \<Longrightarrow> ssnd\<cdot>(:x, y:) = y"
  by (simp add: ssnd_def cont_Rep_sprod Rep_sprod_spair)

lemma sfst_bottom_iff [simp]: "sfst\<cdot>p = \<bottom> \<longleftrightarrow> p = \<bottom>"
  by (cases p) simp_all

lemma ssnd_bottom_iff [simp]: "ssnd\<cdot>p = \<bottom> \<longleftrightarrow> p = \<bottom>"
  by (cases p) simp_all

lemma sfst_defined: "p \<noteq> \<bottom> \<Longrightarrow> sfst\<cdot>p \<noteq> \<bottom>"
  by simp

lemma ssnd_defined: "p \<noteq> \<bottom> \<Longrightarrow> ssnd\<cdot>p \<noteq> \<bottom>"
  by simp

lemma spair_sfst_ssnd: "(:sfst\<cdot>p, ssnd\<cdot>p:) = p"
  by (cases p) simp_all

lemma below_sprod: "x \<sqsubseteq> y \<longleftrightarrow> sfst\<cdot>x \<sqsubseteq> sfst\<cdot>y \<and> ssnd\<cdot>x \<sqsubseteq> ssnd\<cdot>y"
  by (simp add: Rep_sprod_simps sfst_def ssnd_def cont_Rep_sprod)

lemma eq_sprod: "x = y \<longleftrightarrow> sfst\<cdot>x = sfst\<cdot>y \<and> ssnd\<cdot>x = ssnd\<cdot>y"
  by (auto simp add: po_eq_conv below_sprod)

lemma sfst_below_iff: "sfst\<cdot>x \<sqsubseteq> y \<longleftrightarrow> x \<sqsubseteq> (:y, ssnd\<cdot>x:)"
  by (cases "x = \<bottom>", simp, cases "y = \<bottom>", simp, simp add: below_sprod)

lemma ssnd_below_iff: "ssnd\<cdot>x \<sqsubseteq> y \<longleftrightarrow> x \<sqsubseteq> (:sfst\<cdot>x, y:)"
  by (cases "x = \<bottom>", simp, cases "y = \<bottom>", simp, simp add: below_sprod)


subsection \<open>Compactness\<close>

lemma compact_sfst: "compact x \<Longrightarrow> compact (sfst\<cdot>x)"
  by (rule compactI) (simp add: sfst_below_iff)

lemma compact_ssnd: "compact x \<Longrightarrow> compact (ssnd\<cdot>x)"
  by (rule compactI) (simp add: ssnd_below_iff)

lemma compact_spair: "compact x \<Longrightarrow> compact y \<Longrightarrow> compact (:x, y:)"
  by (rule compact_sprod) (simp add: Rep_sprod_spair seq_conv_if)

lemma compact_spair_iff: "compact (:x, y:) \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom> \<or> (compact x \<and> compact y)"
  apply (safe elim!: compact_spair)
     apply (drule compact_sfst, simp)
    apply (drule compact_ssnd, simp)
   apply simp
  apply simp
  done


subsection \<open>Properties of \emph{ssplit}\<close>

lemma ssplit1 [simp]: "ssplit\<cdot>f\<cdot>\<bottom> = \<bottom>"
  by (simp add: ssplit_def)

lemma ssplit2 [simp]: "x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> ssplit\<cdot>f\<cdot>(:x, y:) = f\<cdot>x\<cdot>y"
  by (simp add: ssplit_def)

lemma ssplit3 [simp]: "ssplit\<cdot>spair\<cdot>z = z"
  by (cases z) simp_all


subsection \<open>Strict product preserves flatness\<close>

instance sprod :: (flat, flat) flat
proof
  fix x y :: "'a \<otimes> 'b"
  assume "x \<sqsubseteq> y"
  then show "x = \<bottom> \<or> x = y"
    apply (induct x, simp)
    apply (induct y, simp)
    apply (simp add: spair_below_iff flat_below_iff)
    done
qed

end
