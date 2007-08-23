(*
  ID:     $Id$
  Author: Brian Huffman
*)

header {* Binary Integers as an Inductive Datatype *}

theory BinInduct imports Main begin

subsection {* Injectivity and distinctness of constructors *}

lemma BIT_eq: "x BIT a = y BIT b \<Longrightarrow> x = y \<and> a = b"
  by (simp add: eq_number_of_BIT_BIT [unfolded number_of_is_id])

lemma BIT_eq_iff: "(x BIT a = y BIT b) = (x = y \<and> a = b)"
  by (safe dest!: BIT_eq)

lemma BIT_eq_Pls: "(w BIT b = Numeral.Pls) = (w = Numeral.Pls \<and> b = bit.B0)"
  by (subst Pls_0_eq [symmetric], simp only: BIT_eq_iff)

lemma BIT_eq_Min: "(w BIT b = Numeral.Min) = (w = Numeral.Min \<and> b = bit.B1)"
  by (subst Min_1_eq [symmetric], simp only: BIT_eq_iff)

lemma Pls_eq_BIT: "(Numeral.Pls = w BIT b) = (w = Numeral.Pls \<and> b = bit.B0)"
  by (subst eq_commute, rule BIT_eq_Pls)

lemma Min_eq_BIT: "(Numeral.Min = w BIT b) = (w = Numeral.Min \<and> b = bit.B1)"
  by (subst eq_commute, rule BIT_eq_Min)

lemma Min_neq_Pls: "Numeral.Min \<noteq> Numeral.Pls"
  unfolding Min_def Pls_def by simp

lemma Pls_neq_Min: "Numeral.Pls \<noteq> Numeral.Min"
  unfolding Min_def Pls_def by simp

lemmas bin_injects [simp] =
  BIT_eq_iff BIT_eq_Pls BIT_eq_Min
  Pls_eq_BIT Min_eq_BIT Min_neq_Pls Pls_neq_Min


subsection {* Induction and case analysis *}

inductive
  is_numeral :: "int \<Rightarrow> bool"
where
  Pls: "is_numeral Numeral.Pls"
| Min: "is_numeral Numeral.Min"
| B0: "is_numeral z \<Longrightarrow> is_numeral (z BIT bit.B0)"
| B1: "is_numeral z \<Longrightarrow> is_numeral (z BIT bit.B1)"

lemma is_numeral_succ: "is_numeral z \<Longrightarrow> is_numeral (Numeral.succ z)"
  by (erule is_numeral.induct, simp_all add: is_numeral.intros)

lemma is_numeral_pred: "is_numeral z \<Longrightarrow> is_numeral (Numeral.pred z)"
  by (erule is_numeral.induct, simp_all add: is_numeral.intros)

lemma is_numeral_uminus: "is_numeral z \<Longrightarrow> is_numeral (uminus z)"
  by (erule is_numeral.induct, simp_all add: is_numeral.intros is_numeral_pred)

lemma is_numeral_int: "is_numeral (int n)"
  apply (induct "n")
  apply (simp add: is_numeral.Pls [unfolded Numeral.Pls_def])
  apply (drule is_numeral_succ [unfolded Numeral.succ_def])
  apply (simp add: add_commute)
  done

lemma is_numeral: "is_numeral z"
  by (induct "z") (simp_all only: is_numeral_int is_numeral_uminus)

lemma int_bin_induct [case_names Pls Min B0 B1]:
  assumes Pls: "P Numeral.Pls"
  assumes Min: "P Numeral.Min"
  assumes B0: "\<And>x. \<lbrakk>P x; x \<noteq> Numeral.Pls\<rbrakk> \<Longrightarrow> P (x BIT bit.B0)"
  assumes B1: "\<And>x. \<lbrakk>P x; x \<noteq> Numeral.Min\<rbrakk> \<Longrightarrow> P (x BIT bit.B1)"
  shows "P x"
proof (induct x rule: is_numeral.induct [OF is_numeral])
  from Pls show "P Numeral.Pls" .
  from Min show "P Numeral.Min" .
  fix z
  show "P z \<Longrightarrow> P (z BIT bit.B0)"
    by (cases "z = Numeral.Pls", auto intro: Pls B0)
  show "P z \<Longrightarrow> P (z BIT bit.B1)"
    by (cases "z = Numeral.Min", auto intro: Min B1)
qed

lemma bin_induct [case_names Pls Min Bit]:
  assumes Pls: "P Numeral.Pls"
  assumes Min: "P Numeral.Min"
  assumes Bit: "\<And>bin bit. P bin \<Longrightarrow> P (bin BIT bit)"
  shows "P x"
  by (induct x rule: int_bin_induct) (auto intro: assms)

lemma BIT_exhausts: "\<exists>w b. x = w BIT b"
  by (induct x rule: bin_induct)
     (fast intro: Pls_0_eq [symmetric] Min_1_eq [symmetric])+

lemma BIT_cases: "(\<And>w b. x = w BIT b \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (insert BIT_exhausts [of x], auto)


subsection {* Destructors for BIT *}

definition
  bin_rest :: "int \<Rightarrow> int" where
  "bin_rest x = (THE w. \<exists>b. x = w BIT b)"

definition
  bin_last :: "int \<Rightarrow> bit" where
  "bin_last x = (THE b. \<exists>w. x = w BIT b)"

lemma bin_rest_BIT [simp]: "bin_rest (w BIT b) = w"
  by (unfold bin_rest_def, rule the_equality, fast, simp)

lemma bin_rest_Pls [simp]: "bin_rest Numeral.Pls = Numeral.Pls"
  by (subst Pls_0_eq [symmetric], rule bin_rest_BIT)

lemma bin_rest_Min [simp]: "bin_rest Numeral.Min = Numeral.Min"
  by (subst Min_1_eq [symmetric], rule bin_rest_BIT)

lemma bin_last_BIT [simp]: "bin_last (w BIT b) = b"
  by (unfold bin_last_def, rule the_equality, fast, simp)

lemma bin_last_Pls [simp]: "bin_last Numeral.Pls = bit.B0"
  by (subst Pls_0_eq [symmetric], rule bin_last_BIT)

lemma bin_last_Min [simp]: "bin_last Numeral.Min = bit.B1"
  by (subst Min_1_eq [symmetric], rule bin_last_BIT)

lemma bin_rest_BIT_bin_last: "(bin_rest x) BIT (bin_last x) = x"
  by (cases x rule: BIT_cases) simp

lemma wf_bin_rest:
  "wf {(bin_rest w, w) |w. w \<noteq> Numeral.Pls \<and> w \<noteq> Numeral.Min}"
  apply (rule wfUNIVI, simp (no_asm_use))
  apply (rename_tac "z", induct_tac "z" rule: bin_induct)
  apply (drule spec, erule mp, simp)+
  done

subsection {* Size function *}

function
  binsize :: "int \<Rightarrow> nat"
where
  "binsize z = (if z = Numeral.Pls \<or> z = Numeral.Min
                 then 0 else Suc (binsize (bin_rest z)))"
  by pat_completeness simp

termination binsize
  apply (relation "{(bin_rest w, w) |w. w \<noteq> Numeral.Pls \<and> w \<noteq> Numeral.Min}")
  apply (rule wf_bin_rest)
  apply simp
  done

instance int :: size
  int_size_def: "size \<equiv> binsize" ..

lemma int_size_simps [simp]:
  "size Numeral.Pls = 0"
  "size Numeral.Min = 0"
  "size (w BIT bit.B0) = (if w = Numeral.Pls then 0 else Suc (size w))"
  "size (w BIT bit.B1) = (if w = Numeral.Min then 0 else Suc (size w))"
  unfolding int_size_def by simp_all

lemma size_bin_rest [simp]: "size (bin_rest w) = size w - 1"
  by (induct w rule: int_bin_induct) simp_all

lemma int_size_gt_zero_iff [simp]:
  "(0 < size w) = (w \<noteq> Numeral.Pls \<and> w \<noteq> Numeral.Min)"
  by (induct w rule: int_bin_induct) simp_all

end
