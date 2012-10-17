(* Author: Tobias Nipkow *)

theory Abs_Int3
imports Abs_Int2_ivl
begin

subsubsection "Welltypedness"

class Lc =
fixes Lc :: "com \<Rightarrow> 'a set"

instantiation st :: (type)Lc
begin

definition Lc_st :: "com \<Rightarrow> 'a st set" where
"Lc_st c = L (vars c)"

instance ..

end

instantiation acom :: (Lc)Lc
begin

definition Lc_acom :: "com \<Rightarrow> 'a acom set" where
"Lc c = {C. strip C = c \<and> (\<forall>a\<in>set(annos C). a \<in> Lc c)}"

instance ..

end

instantiation option :: (Lc)Lc
begin

definition Lc_option :: "com \<Rightarrow> 'a option set" where
"Lc c = {None} \<union> Some ` Lc c"

lemma Lc_option_simps[simp]: "None \<in> Lc c" "(Some x \<in> Lc c) = (x \<in> Lc c)"
by(auto simp: Lc_option_def)

instance ..

end

lemma Lc_option_iff_wt[simp]: fixes a :: "_ st option"
shows "(a \<in> Lc c) = (a \<in> L (vars c))"
by(auto simp add: L_option_def Lc_st_def split: option.splits)


context Abs_Int1
begin

lemma step'_in_Lc: "C \<in> Lc c \<Longrightarrow> S \<in> Lc c \<Longrightarrow> step' S C \<in> Lc c"
apply(auto simp add: Lc_acom_def)
by(metis step'_in_L[simplified L_acom_def mem_Collect_eq] order_refl)

end


subsection "Widening and Narrowing"

class widen =
fixes widen :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<nabla>" 65)

class narrow =
fixes narrow :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<triangle>" 65)

class WN = widen + narrow + preord +
assumes widen1: "x \<sqsubseteq> x \<nabla> y"
assumes widen2: "y \<sqsubseteq> x \<nabla> y"
assumes narrow1: "y \<sqsubseteq> x \<Longrightarrow> y \<sqsubseteq> x \<triangle> y"
assumes narrow2: "y \<sqsubseteq> x \<Longrightarrow> x \<triangle> y \<sqsubseteq> x"

class WN_Lc = widen + narrow + preord + Lc +
assumes widen1: "x \<in> Lc c \<Longrightarrow> y \<in> Lc c \<Longrightarrow> x \<sqsubseteq> x \<nabla> y"
assumes widen2: "x \<in> Lc c \<Longrightarrow> y \<in> Lc c \<Longrightarrow> y \<sqsubseteq> x \<nabla> y"
assumes narrow1: "y \<sqsubseteq> x \<Longrightarrow> y \<sqsubseteq> x \<triangle> y"
assumes narrow2: "y \<sqsubseteq> x \<Longrightarrow> x \<triangle> y \<sqsubseteq> x"
assumes Lc_widen[simp]: "x \<in> Lc c \<Longrightarrow> y \<in> Lc c \<Longrightarrow> x \<nabla> y \<in> Lc c"
assumes Lc_narrow[simp]: "x \<in> Lc c \<Longrightarrow> y \<in> Lc c \<Longrightarrow> x \<triangle> y \<in> Lc c"


instantiation ivl :: WN
begin

definition "widen_ivl ivl1 ivl2 =
  ((*if is_empty ivl1 then ivl2 else
   if is_empty ivl2 then ivl1 else*)
     case (ivl1,ivl2) of (Ivl l1 h1, Ivl l2 h2) \<Rightarrow>
       Ivl (if le_option False l2 l1 \<and> l2 \<noteq> l1 then None else l1)
           (if le_option True h1 h2 \<and> h1 \<noteq> h2 then None else h1))"

definition "narrow_ivl ivl1 ivl2 =
  ((*if is_empty ivl1 \<or> is_empty ivl2 then empty else*)
     case (ivl1,ivl2) of (Ivl l1 h1, Ivl l2 h2) \<Rightarrow>
       Ivl (if l1 = None then l2 else l1)
           (if h1 = None then h2 else h1))"

instance
proof qed
  (auto simp add: widen_ivl_def narrow_ivl_def le_option_def le_ivl_def empty_def split: ivl.split option.split if_splits)

end


instantiation st :: (WN)WN_Lc
begin

definition "widen_st F1 F2 = FunDom (\<lambda>x. fun F1 x \<nabla> fun F2 x) (dom F1)"

definition "narrow_st F1 F2 = FunDom (\<lambda>x. fun F1 x \<triangle> fun F2 x) (dom F1)"

instance
proof
  case goal1 thus ?case
    by(simp add: widen_st_def le_st_def WN_class.widen1)
next
  case goal2 thus ?case
    by(simp add: widen_st_def le_st_def WN_class.widen2 Lc_st_def L_st_def)
next
  case goal3 thus ?case
    by(auto simp: narrow_st_def le_st_def WN_class.narrow1)
next
  case goal4 thus ?case
    by(auto simp: narrow_st_def le_st_def WN_class.narrow2)
next
  case goal5 thus ?case by(auto simp: widen_st_def Lc_st_def L_st_def)
next
  case goal6 thus ?case by(auto simp: narrow_st_def Lc_st_def L_st_def)
qed

end


instantiation option :: (WN_Lc)WN_Lc
begin

fun widen_option where
"None \<nabla> x = x" |
"x \<nabla> None = x" |
"(Some x) \<nabla> (Some y) = Some(x \<nabla> y)"

fun narrow_option where
"None \<triangle> x = None" |
"x \<triangle> None = None" |
"(Some x) \<triangle> (Some y) = Some(x \<triangle> y)"

instance
proof
  case goal1 thus ?case
    by(induct x y rule: widen_option.induct)(simp_all add: widen1)
next
  case goal2 thus ?case
    by(induct x y rule: widen_option.induct)(simp_all add: widen2)
next
  case goal3 thus ?case
    by(induct x y rule: narrow_option.induct) (simp_all add: narrow1)
next
  case goal4 thus ?case
    by(induct x y rule: narrow_option.induct) (simp_all add: narrow2)
next
  case goal5 thus ?case
    by(induction x y rule: widen_option.induct)(auto simp: Lc_st_def)
next
  case goal6 thus ?case
    by(induction x y rule: narrow_option.induct)(auto simp: Lc_st_def)
qed

end


fun map2_acom :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a acom \<Rightarrow> 'a acom \<Rightarrow> 'a acom" where
"map2_acom f (SKIP {a1}) (SKIP {a2}) = (SKIP {f a1 a2})" |
"map2_acom f (x ::= e {a1}) (x' ::= e' {a2}) = (x ::= e {f a1 a2})" |
"map2_acom f (C1;C2) (D1;D2) = (map2_acom f C1 D1; map2_acom f C2 D2)" |
"map2_acom f (IF b THEN {p1} C1 ELSE {p2} C2 {a1}) (IF b' THEN {q1} D1 ELSE {q2} D2 {a2}) =
  (IF b THEN {f p1 q1} map2_acom f C1 D1 ELSE {f p2 q2} map2_acom f C2 D2 {f a1 a2})" |
"map2_acom f ({a1} WHILE b DO {p} C {a2}) ({a3} WHILE b' DO {p'} C' {a4}) =
  ({f a1 a3} WHILE b DO {f p p'} map2_acom f C C' {f a2 a4})"


instantiation acom :: (widen)widen
begin
definition "widen_acom = map2_acom (op \<nabla>)"
instance ..
end

instantiation acom :: (narrow)narrow
begin
definition "narrow_acom = map2_acom (op \<triangle>)"
instance ..
end

instantiation acom :: (WN_Lc)WN_Lc
begin

lemma widen_acom1: fixes C1 :: "'a acom" shows
  "\<lbrakk>\<forall>a\<in>set(annos C1). a \<in> Lc c; \<forall>a\<in>set (annos C2). a \<in> Lc c; strip C1 = strip C2\<rbrakk>
   \<Longrightarrow> C1 \<sqsubseteq> C1 \<nabla> C2"
by(induct C1 C2 rule: le_acom.induct)
  (auto simp: widen_acom_def widen1 Lc_acom_def)

lemma widen_acom2: fixes C1 :: "'a acom" shows
  "\<lbrakk>\<forall>a\<in>set(annos C1). a \<in> Lc c; \<forall>a\<in>set (annos C2). a \<in> Lc c; strip C1 = strip C2\<rbrakk>
   \<Longrightarrow> C2 \<sqsubseteq> C1 \<nabla> C2"
by(induct C1 C2 rule: le_acom.induct)
  (auto simp: widen_acom_def widen2 Lc_acom_def)

lemma strip_map2_acom[simp]:
 "strip C1 = strip C2 \<Longrightarrow> strip(map2_acom f C1 C2) = strip C1"
by(induct f C1 C2 rule: map2_acom.induct) simp_all

lemma strip_widen_acom[simp]:
  "strip C1 = strip C2 \<Longrightarrow> strip(C1 \<nabla> C2) = strip C1"
by(simp add: widen_acom_def)

lemma strip_narrow_acom[simp]:
  "strip C1 = strip C2 \<Longrightarrow> strip(C1 \<triangle> C2) = strip C1"
by(simp add: narrow_acom_def)

lemma annos_map2_acom[simp]: "strip C2 = strip C1 \<Longrightarrow>
  annos(map2_acom f C1 C2) = map (%(x,y).f x y) (zip (annos C1) (annos C2))"
by(induction f C1 C2 rule: map2_acom.induct)(simp_all add: size_annos_same2)

instance
proof
  case goal1 thus ?case by(auto simp: Lc_acom_def widen_acom1)
next
  case goal2 thus ?case by(auto simp: Lc_acom_def widen_acom2)
next
  case goal3 thus ?case
    by(induct x y rule: le_acom.induct)(simp_all add: narrow_acom_def narrow1)
next
  case goal4 thus ?case
    by(induct x y rule: le_acom.induct)(simp_all add: narrow_acom_def narrow2)
next
  case goal5 thus ?case
    by(auto simp: Lc_acom_def widen_acom_def split_conv elim!: in_set_zipE)
next
  case goal6 thus ?case
    by(auto simp: Lc_acom_def narrow_acom_def split_conv elim!: in_set_zipE)
qed

end

lemma widen_o_in_L[simp]: fixes x1 x2 :: "_ st option"
shows "x1 \<in> L X \<Longrightarrow> x2 \<in> L X \<Longrightarrow> x1 \<nabla> x2 \<in> L X"
by(induction x1 x2 rule: widen_option.induct)
  (simp_all add: widen_st_def L_st_def)

lemma narrow_o_in_L[simp]: fixes x1 x2 :: "_ st option"
shows "x1 \<in> L X \<Longrightarrow> x2 \<in> L X \<Longrightarrow> x1 \<triangle> x2 \<in> L X"
by(induction x1 x2 rule: narrow_option.induct)
  (simp_all add: narrow_st_def L_st_def)

lemma widen_c_in_L: fixes C1 C2 :: "_ st option acom"
shows "strip C1 = strip C2 \<Longrightarrow> C1 \<in> L X \<Longrightarrow> C2 \<in> L X \<Longrightarrow> C1 \<nabla> C2 \<in> L X"
by(induction C1 C2 rule: le_acom.induct)
  (auto simp: widen_acom_def)

lemma narrow_c_in_L: fixes C1 C2 :: "_ st option acom"
shows "strip C1 = strip C2 \<Longrightarrow> C1 \<in> L X \<Longrightarrow> C2 \<in> L X \<Longrightarrow> C1 \<triangle> C2 \<in> L X"
by(induction C1 C2 rule: le_acom.induct)
  (auto simp: narrow_acom_def)

lemma bot_in_Lc[simp]: "bot c \<in> Lc c"
by(simp add: Lc_acom_def bot_def)


subsubsection "Post-fixed point computation"

definition iter_widen :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('a::{preord,widen})option"
where "iter_widen f = while_option (\<lambda>x. \<not> f x \<sqsubseteq> x) (\<lambda>x. x \<nabla> f x)"

definition iter_narrow :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('a::{preord,narrow})option"
where "iter_narrow f = while_option (\<lambda>x. \<not> x \<sqsubseteq> x \<triangle> f x) (\<lambda>x. x \<triangle> f x)"

definition pfp_wn :: "('a::{preord,widen,narrow} \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option"
where "pfp_wn f x =
  (case iter_widen f x of None \<Rightarrow> None | Some p \<Rightarrow> iter_narrow f p)"


lemma iter_widen_pfp: "iter_widen f x = Some p \<Longrightarrow> f p \<sqsubseteq> p"
by(auto simp add: iter_widen_def dest: while_option_stop)

lemma iter_widen_inv:
assumes "!!x. P x \<Longrightarrow> P(f x)" "!!x1 x2. P x1 \<Longrightarrow> P x2 \<Longrightarrow> P(x1 \<nabla> x2)" and "P x"
and "iter_widen f x = Some y" shows "P y"
using while_option_rule[where P = "P", OF _ assms(4)[unfolded iter_widen_def]]
by (blast intro: assms(1-3))

lemma strip_while: fixes f :: "'a acom \<Rightarrow> 'a acom"
assumes "\<forall>C. strip (f C) = strip C" and "while_option P f C = Some C'"
shows "strip C' = strip C"
using while_option_rule[where P = "\<lambda>C'. strip C' = strip C", OF _ assms(2)]
by (metis assms(1))

lemma strip_iter_widen: fixes f :: "'a::{preord,widen} acom \<Rightarrow> 'a acom"
assumes "\<forall>C. strip (f C) = strip C" and "iter_widen f C = Some C'"
shows "strip C' = strip C"
proof-
  have "\<forall>C. strip(C \<nabla> f C) = strip C"
    by (metis assms(1) strip_map2_acom widen_acom_def)
  from strip_while[OF this] assms(2) show ?thesis by(simp add: iter_widen_def)
qed

lemma iter_narrow_pfp:
assumes mono: "!!x1 x2::_::WN_Lc. P x1 \<Longrightarrow> P x2 \<Longrightarrow> x1 \<sqsubseteq> x2 \<Longrightarrow> f x1 \<sqsubseteq> f x2"
and Pinv: "!!x. P x \<Longrightarrow> P(f x)" "!!x1 x2. P x1 \<Longrightarrow> P x2 \<Longrightarrow> P(x1 \<triangle> x2)"
and "P p0" and "f p0 \<sqsubseteq> p0" and "iter_narrow f p0 = Some p"
shows "P p \<and> f p \<sqsubseteq> p"
proof-
  let ?Q = "%p. P p \<and> f p \<sqsubseteq> p \<and> p \<sqsubseteq> p0"
  { fix p assume "?Q p"
    note P = conjunct1[OF this] and 12 = conjunct2[OF this]
    note 1 = conjunct1[OF 12] and 2 = conjunct2[OF 12]
    let ?p' = "p \<triangle> f p"
    have "?Q ?p'"
    proof auto
      show "P ?p'" by (blast intro: P Pinv)
      have "f ?p' \<sqsubseteq> f p" by(rule mono[OF `P (p \<triangle> f p)`  P narrow2[OF 1]])
      also have "\<dots> \<sqsubseteq> ?p'" by(rule narrow1[OF 1])
      finally show "f ?p' \<sqsubseteq> ?p'" .
      have "?p' \<sqsubseteq> p" by (rule narrow2[OF 1])
      also have "p \<sqsubseteq> p0" by(rule 2)
      finally show "?p' \<sqsubseteq> p0" .
    qed
  }
  thus ?thesis
    using while_option_rule[where P = ?Q, OF _ assms(6)[simplified iter_narrow_def]]
    by (blast intro: assms(4,5) le_refl)
qed

lemma pfp_wn_pfp:
assumes mono: "!!x1 x2::_::WN_Lc. P x1 \<Longrightarrow> P x2 \<Longrightarrow> x1 \<sqsubseteq> x2 \<Longrightarrow> f x1 \<sqsubseteq> f x2"
and Pinv: "P x"  "!!x. P x \<Longrightarrow> P(f x)"
  "!!x1 x2. P x1 \<Longrightarrow> P x2 \<Longrightarrow> P(x1 \<nabla> x2)"
  "!!x1 x2. P x1 \<Longrightarrow> P x2 \<Longrightarrow> P(x1 \<triangle> x2)"
and pfp_wn: "pfp_wn f x = Some p" shows "P p \<and> f p \<sqsubseteq> p"
proof-
  from pfp_wn obtain p0
    where its: "iter_widen f x = Some p0" "iter_narrow f p0 = Some p"
    by(auto simp: pfp_wn_def split: option.splits)
  have "P p0" by (blast intro: iter_widen_inv[where P="P"] its(1) Pinv(1-3))
  thus ?thesis
    by - (assumption |
          rule iter_narrow_pfp[where P=P] mono Pinv(2,4) iter_widen_pfp its)+
qed

lemma strip_pfp_wn:
  "\<lbrakk> \<forall>C. strip(f C) = strip C; pfp_wn f C = Some C' \<rbrakk> \<Longrightarrow> strip C' = strip C"
by(auto simp add: pfp_wn_def iter_narrow_def split: option.splits)
  (metis (no_types) narrow_acom_def strip_iter_widen strip_map2_acom strip_while)


locale Abs_Int2 = Abs_Int1_mono
where \<gamma>=\<gamma> for \<gamma> :: "'av::{WN,lattice} \<Rightarrow> val set"
begin

definition AI_wn :: "com \<Rightarrow> 'av st option acom option" where
"AI_wn c = pfp_wn (step' (top c)) (bot c)"

lemma AI_wn_sound: "AI_wn c = Some C \<Longrightarrow> CS c \<le> \<gamma>\<^isub>c C"
proof(simp add: CS_def AI_wn_def)
  assume 1: "pfp_wn (step' (top c)) (bot c) = Some C"
  have 2: "(strip C = c & C \<in> L(vars c)) \<and> step' \<top>\<^bsub>c\<^esub> C \<sqsubseteq> C"
    by(rule pfp_wn_pfp[where x="bot c"])
      (simp_all add: 1 mono_step'_top widen_c_in_L narrow_c_in_L)
  have 3: "strip (\<gamma>\<^isub>c (step' \<top>\<^bsub>c\<^esub> C)) = c" by(simp add: strip_pfp_wn[OF _ 1])
  have "lfp c (step UNIV) \<le> \<gamma>\<^isub>c (step' \<top>\<^bsub>c\<^esub> C)"
  proof(rule lfp_lowerbound[simplified,OF 3])
    show "step UNIV (\<gamma>\<^isub>c (step' \<top>\<^bsub>c\<^esub> C)) \<le> \<gamma>\<^isub>c (step' \<top>\<^bsub>c\<^esub> C)"
    proof(rule step_preserves_le[OF _ _ _ top_in_L])
      show "UNIV \<subseteq> \<gamma>\<^isub>o \<top>\<^bsub>c\<^esub>" by simp
      show "\<gamma>\<^isub>c (step' \<top>\<^bsub>c\<^esub> C) \<le> \<gamma>\<^isub>c C" by(rule mono_gamma_c[OF conjunct2[OF 2]])
      show "C \<in> L(vars c)" using 2 by blast
    qed
  qed
  from this 2 show "lfp c (step UNIV) \<le> \<gamma>\<^isub>c C"
    by (blast intro: mono_gamma_c order_trans)
qed

end

interpretation Abs_Int2
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = plus_ivl
and test_num' = in_ivl
and filter_plus' = filter_plus_ivl and filter_less' = filter_less_ivl
defines AI_ivl' is AI_wn
..


subsubsection "Tests"

(* Trick to make the code generator happy. *)
lemma [code]: "equal_class.equal (x::'a st) y = equal_class.equal x y"
by(rule refl)

definition "step_up_ivl n =
  ((\<lambda>C. C \<nabla> step_ivl (top(strip C)) C)^^n)"
definition "step_down_ivl n =
  ((\<lambda>C. C \<triangle> step_ivl (top (strip C)) C)^^n)"

text{* For @{const test3_ivl}, @{const AI_ivl} needed as many iterations as
the loop took to execute. In contrast, @{const AI_ivl'} converges in a
constant number of steps: *}

value "show_acom (step_up_ivl 1 (bot test3_ivl))"
value "show_acom (step_up_ivl 2 (bot test3_ivl))"
value "show_acom (step_up_ivl 3 (bot test3_ivl))"
value "show_acom (step_up_ivl 4 (bot test3_ivl))"
value "show_acom (step_up_ivl 5 (bot test3_ivl))"
value "show_acom (step_up_ivl 6 (bot test3_ivl))"
value "show_acom (step_up_ivl 7 (bot test3_ivl))"
value "show_acom (step_up_ivl 8 (bot test3_ivl))"
value "show_acom (step_down_ivl 1 (step_up_ivl 8 (bot test3_ivl)))"
value "show_acom (step_down_ivl 2 (step_up_ivl 8 (bot test3_ivl)))"
value "show_acom (step_down_ivl 3 (step_up_ivl 8 (bot test3_ivl)))"
value "show_acom (step_down_ivl 4 (step_up_ivl 8 (bot test3_ivl)))"
value "show_acom_opt (AI_ivl' test3_ivl)"


text{* Now all the analyses terminate: *}

value "show_acom_opt (AI_ivl' test4_ivl)"
value "show_acom_opt (AI_ivl' test5_ivl)"
value "show_acom_opt (AI_ivl' test6_ivl)"


subsubsection "Generic Termination Proof"

locale Measure_WN = Measure1 where m=m for m :: "'av::WN \<Rightarrow> nat" +
fixes n :: "'av \<Rightarrow> nat"
assumes m_widen: "~ y \<sqsubseteq> x \<Longrightarrow> m(x \<nabla> y) < m x"
assumes n_mono: "x \<sqsubseteq> y \<Longrightarrow> n x \<le> n y"
assumes n_narrow: "y \<sqsubseteq> x \<Longrightarrow> ~ x \<sqsubseteq> x \<triangle> y \<Longrightarrow> n(x \<triangle> y) < n x"

begin

lemma m_s_widen: "S1 \<in> L X \<Longrightarrow> S2 \<in> L X \<Longrightarrow> finite X \<Longrightarrow>
  ~ S2 \<sqsubseteq> S1 \<Longrightarrow> m_s(S1 \<nabla> S2) < m_s S1"
proof(auto simp add: le_st_def m_s_def L_st_def widen_st_def)
  assume "finite(dom S1)"
  have 1: "\<forall>x\<in>dom S1. m(fun S1 x) \<ge> m(fun S1 x \<nabla> fun S2 x)"
    by (metis m1 WN_class.widen1)
  fix x assume "x \<in> dom S1" "\<not> fun S2 x \<sqsubseteq> fun S1 x"
  hence 2: "EX x : dom S1. m(fun S1 x) > m(fun S1 x \<nabla> fun S2 x)"
    using m_widen by blast
  from setsum_strict_mono_ex1[OF `finite(dom S1)` 1 2]
  show "(\<Sum>x\<in>dom S1. m (fun S1 x \<nabla> fun S2 x)) < (\<Sum>x\<in>dom S1. m (fun S1 x))" .
qed

lemma m_o_widen: "\<lbrakk> S1 \<in> L X; S2 \<in> L X; finite X; \<not> S2 \<sqsubseteq> S1 \<rbrakk> \<Longrightarrow>
  m_o (card X) (S1 \<nabla> S2) < m_o (card X) S1"
by(auto simp: m_o_def L_st_def m_s_h less_Suc_eq_le m_s_widen
        split: option.split)

lemma m_c_widen:
  "C1 \<in> Lc c \<Longrightarrow> C2 \<in> Lc c \<Longrightarrow> \<not> C2 \<sqsubseteq> C1 \<Longrightarrow> m_c (C1 \<nabla> C2) < m_c C1"
apply(auto simp: Lc_acom_def m_c_def Let_def widen_acom_def)
apply(subgoal_tac "length(annos C2) = length(annos C1)")
prefer 2 apply (simp add: size_annos_same2)
apply (auto)
apply(rule setsum_strict_mono_ex1)
apply simp
apply (clarsimp)
apply(simp add: m_o1 finite_cvars widen1[where c = "strip C2"])
apply(auto simp: le_iff_le_annos listrel_iff_nth)
apply(rule_tac x=i in bexI)
prefer 2 apply simp
apply(rule m_o_widen)
apply (simp add: finite_cvars)+
done


definition n_s :: "'av st \<Rightarrow> nat" ("n\<^isub>s") where
"n\<^isub>s S = (\<Sum>x\<in>dom S. n(fun S x))"

lemma n_s_mono: assumes "S1 \<sqsubseteq> S2" shows "n\<^isub>s S1 \<le> n\<^isub>s S2"
proof-
  from assms have [simp]: "dom S1 = dom S2" "\<forall>x\<in>dom S1. fun S1 x \<sqsubseteq> fun S2 x"
    by(simp_all add: le_st_def)
  have "(\<Sum>x\<in>dom S1. n(fun S1 x)) \<le> (\<Sum>x\<in>dom S1. n(fun S2 x))"
    by(rule setsum_mono)(simp add: le_st_def n_mono)
  thus ?thesis by(simp add: n_s_def)
qed

lemma n_s_narrow:
assumes "finite(dom S1)" and "S2 \<sqsubseteq> S1" "\<not> S1 \<sqsubseteq> S1 \<triangle> S2"
shows "n\<^isub>s (S1 \<triangle> S2) < n\<^isub>s S1"
proof-
  from `S2\<sqsubseteq>S1` have [simp]: "dom S1 = dom S2" "\<forall>x\<in>dom S1. fun S2 x \<sqsubseteq> fun S1 x"
    by(simp_all add: le_st_def)
  have 1: "\<forall>x\<in>dom S1. n(fun (S1 \<triangle> S2) x) \<le> n(fun S1 x)"
    by(auto simp: le_st_def narrow_st_def n_mono WN_class.narrow2)
  have 2: "\<exists>x\<in>dom S1. n(fun (S1 \<triangle> S2) x) < n(fun S1 x)" using `\<not> S1 \<sqsubseteq> S1 \<triangle> S2`
    by(force simp: le_st_def narrow_st_def intro: n_narrow)
  have "(\<Sum>x\<in>dom S1. n(fun (S1 \<triangle> S2) x)) < (\<Sum>x\<in>dom S1. n(fun S1 x))"
    apply(rule setsum_strict_mono_ex1[OF `finite(dom S1)`]) using 1 2 by blast+
  moreover have "dom (S1 \<triangle> S2) = dom S1" by(simp add: narrow_st_def)
  ultimately show ?thesis by(simp add: n_s_def)
qed


definition n_o :: "'av st option \<Rightarrow> nat" ("n\<^isub>o") where
"n\<^isub>o opt = (case opt of None \<Rightarrow> 0 | Some S \<Rightarrow> n\<^isub>s S + 1)"

lemma n_o_mono: "S1 \<sqsubseteq> S2 \<Longrightarrow> n\<^isub>o S1 \<le> n\<^isub>o S2"
by(induction S1 S2 rule: le_option.induct)(auto simp: n_o_def n_s_mono)

lemma n_o_narrow:
  "S1 \<in> L X \<Longrightarrow> S2 \<in> L X \<Longrightarrow> finite X
  \<Longrightarrow> S2 \<sqsubseteq> S1 \<Longrightarrow> \<not> S1 \<sqsubseteq> S1 \<triangle> S2 \<Longrightarrow> n\<^isub>o (S1 \<triangle> S2) < n\<^isub>o S1"
apply(induction S1 S2 rule: narrow_option.induct)
apply(auto simp: n_o_def L_st_def n_s_narrow)
done


definition n_c :: "'av st option acom \<Rightarrow> nat" ("n\<^isub>c") where
"n\<^isub>c C = (let as = annos C in \<Sum>i<size as. n\<^isub>o (as!i))"

lemma n_c_narrow: "C1 \<in> Lc c \<Longrightarrow> C2 \<in> Lc c \<Longrightarrow>
  C2 \<sqsubseteq> C1 \<Longrightarrow> \<not> C1 \<sqsubseteq> C1 \<triangle> C2 \<Longrightarrow> n\<^isub>c (C1 \<triangle> C2) < n\<^isub>c C1"
apply(auto simp: n_c_def Let_def Lc_acom_def narrow_acom_def)
apply(subgoal_tac "length(annos C2) = length(annos C1)")
prefer 2 apply (simp add: size_annos_same2)
apply (auto)
apply(rule setsum_strict_mono_ex1)
apply simp
apply (clarsimp)
apply(rule n_o_mono)
apply(rule narrow2)
apply(fastforce simp: le_iff_le_annos listrel_iff_nth)
apply(auto simp: le_iff_le_annos listrel_iff_nth)
apply(rule_tac x=i in bexI)
prefer 2 apply simp
apply(rule n_o_narrow[where X = "vars(strip C1)"])
apply (simp add: finite_cvars)+
done

end


lemma iter_widen_termination:
fixes m :: "'a::WN_Lc \<Rightarrow> nat"
assumes P_f: "\<And>C. P C \<Longrightarrow> P(f C)"
and P_widen: "\<And>C1 C2. P C1 \<Longrightarrow> P C2 \<Longrightarrow> P(C1 \<nabla> C2)"
and m_widen: "\<And>C1 C2. P C1 \<Longrightarrow> P C2 \<Longrightarrow> ~ C2 \<sqsubseteq> C1 \<Longrightarrow> m(C1 \<nabla> C2) < m C1"
and "P C" shows "EX C'. iter_widen f C = Some C'"
proof(simp add: iter_widen_def,
      rule measure_while_option_Some[where P = P and f=m])
  show "P C" by(rule `P C`)
next
  fix C assume "P C" "\<not> f C \<sqsubseteq> C" thus "P (C \<nabla> f C) \<and> m (C \<nabla> f C) < m C"
    by(simp add: P_f P_widen m_widen)
qed

lemma iter_narrow_termination:
fixes n :: "'a::WN_Lc \<Rightarrow> nat"
assumes P_f: "\<And>C. P C \<Longrightarrow> P(f C)"
and P_narrow: "\<And>C1 C2. P C1 \<Longrightarrow> P C2 \<Longrightarrow> P(C1 \<triangle> C2)"
and mono: "\<And>C1 C2. P C1 \<Longrightarrow> P C2 \<Longrightarrow> C1 \<sqsubseteq> C2 \<Longrightarrow> f C1 \<sqsubseteq> f C2"
and n_narrow: "\<And>C1 C2. P C1 \<Longrightarrow> P C2 \<Longrightarrow> C2 \<sqsubseteq> C1 \<Longrightarrow> ~ C1 \<sqsubseteq> C1 \<triangle> C2 \<Longrightarrow> n(C1 \<triangle> C2) < n C1"
and init: "P C" "f C \<sqsubseteq> C" shows "EX C'. iter_narrow f C = Some C'"
proof(simp add: iter_narrow_def,
      rule measure_while_option_Some[where f=n and P = "%C. P C \<and> f C \<sqsubseteq> C"])
  show "P C \<and> f C \<sqsubseteq> C" using init by blast
next
  fix C assume 1: "P C \<and> f C \<sqsubseteq> C" and 2: "\<not> C \<sqsubseteq> C \<triangle> f C"
  hence "P (C \<triangle> f C)" by(simp add: P_f P_narrow)
  moreover then have "f (C \<triangle> f C) \<sqsubseteq> C \<triangle> f C"
    by (metis narrow1 narrow2 1 mono preord_class.le_trans)
  moreover have "n (C \<triangle> f C) < n C" using 1 2 by(simp add: n_narrow P_f)
  ultimately show "(P (C \<triangle> f C) \<and> f (C \<triangle> f C) \<sqsubseteq> C \<triangle> f C) \<and> n(C \<triangle> f C) < n C"
    by blast
qed

locale Abs_Int2_measure =
  Abs_Int2 where \<gamma>=\<gamma> + Measure_WN where m=m
  for \<gamma> :: "'av::{WN,lattice} \<Rightarrow> val set" and m :: "'av \<Rightarrow> nat"


subsubsection "Termination: Intervals"

definition m_ivl :: "ivl \<Rightarrow> nat" where
"m_ivl ivl = (case ivl of Ivl l h \<Rightarrow>
     (case l of None \<Rightarrow> 0 | Some _ \<Rightarrow> 1) + (case h of None \<Rightarrow> 0 | Some _ \<Rightarrow> 1))"

lemma m_ivl_height: "m_ivl ivl \<le> 2"
by(simp add: m_ivl_def split: ivl.split option.split)

lemma m_ivl_anti_mono: "(y::ivl) \<sqsubseteq> x \<Longrightarrow> m_ivl x \<le> m_ivl y"
by(auto simp: m_ivl_def le_option_def le_ivl_def
        split: ivl.split option.split if_splits)

lemma m_ivl_widen:
  "~ y \<sqsubseteq> x \<Longrightarrow> m_ivl(x \<nabla> y) < m_ivl x"
by(auto simp: m_ivl_def widen_ivl_def le_option_def le_ivl_def
        split: ivl.splits option.splits if_splits)

definition n_ivl :: "ivl \<Rightarrow> nat" where
"n_ivl ivl = 2 - m_ivl ivl"

lemma n_ivl_mono: "(x::ivl) \<sqsubseteq> y \<Longrightarrow> n_ivl x \<le> n_ivl y"
unfolding n_ivl_def by (metis diff_le_mono2 m_ivl_anti_mono)

lemma n_ivl_narrow:
  "~ x \<sqsubseteq> x \<triangle> y \<Longrightarrow> n_ivl(x \<triangle> y) < n_ivl x"
by(auto simp: n_ivl_def m_ivl_def narrow_ivl_def le_option_def le_ivl_def
        split: ivl.splits option.splits if_splits)


interpretation Abs_Int2_measure
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = plus_ivl
and test_num' = in_ivl
and filter_plus' = filter_plus_ivl and filter_less' = filter_less_ivl
and m = m_ivl and n = n_ivl and h = 2
proof
  case goal1 thus ?case by(rule m_ivl_anti_mono)
next
  case goal2 thus ?case by(rule m_ivl_height)
next
  case goal3 thus ?case by(rule m_ivl_widen)
next
  case goal4 thus ?case by(rule n_ivl_mono)
next
  case goal5 from goal5(2) show ?case by(rule n_ivl_narrow)
  -- "note that the first assms is unnecessary for intervals"
qed


lemma iter_winden_step_ivl_termination:
  "\<exists>C. iter_widen (step_ivl (top c)) (bot c) = Some C"
apply(rule iter_widen_termination[where m = "m_c" and P = "%C. C \<in> Lc c"])
apply (simp_all add: step'_in_Lc m_c_widen)
done

lemma iter_narrow_step_ivl_termination:
  "C0 \<in> Lc c \<Longrightarrow> step_ivl (top c) C0 \<sqsubseteq> C0 \<Longrightarrow>
  \<exists>C. iter_narrow (step_ivl (top c)) C0 = Some C"
apply(rule iter_narrow_termination[where n = "n_c" and P = "%C. C \<in> Lc c"])
apply (simp add: step'_in_Lc)
apply (simp)
apply(rule mono_step'_top)
apply(simp add: Lc_acom_def L_acom_def)
apply(simp add: Lc_acom_def L_acom_def)
apply assumption
apply(erule (3) n_c_narrow)
apply assumption
apply assumption
done

theorem AI_ivl'_termination:
  "\<exists>C. AI_ivl' c = Some C"
apply(auto simp: AI_wn_def pfp_wn_def iter_winden_step_ivl_termination
           split: option.split)
apply(rule iter_narrow_step_ivl_termination)
apply(blast intro: iter_widen_inv[where f = "step' \<top>\<^bsub>c\<^esub>" and P = "%C. C \<in> Lc c"] bot_in_Lc Lc_widen step'_in_Lc[where S = "\<top>\<^bsub>c\<^esub>" and c=c, simplified])
apply(erule iter_widen_pfp)
done

(*unused_thms Abs_Int_init -*)

subsubsection "Counterexamples"

text{* Widening is increasing by assumption,
but @{prop"x \<sqsubseteq> f x"} is not an invariant of widening. It can already
be lost after the first step: *}

lemma assumes "!!x y::'a::WN. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
and "x \<sqsubseteq> f x" and "\<not> f x \<sqsubseteq> x" shows "x \<nabla> f x \<sqsubseteq> f(x \<nabla> f x)"
nitpick[card = 3, expect = genuine, show_consts]
(*
1 < 2 < 3,
f x = 2,
x widen y = 3 -- guarantees termination with top=3
x = 1
Now f is mono, x <= f x, not f x <= x
but x widen f x = 3, f 3 = 2, but not 3 <= 2
*)
oops

text{* Widening terminates but may converge more slowly than Kleene iteration.
In the following model, Kleene iteration goes from 0 to the least pfp
in one step but widening takes 2 steps to reach a strictly larger pfp: *}
lemma assumes "!!x y::'a::WN. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
and "x \<sqsubseteq> f x" and "\<not> f x \<sqsubseteq> x" and "f(f x) \<sqsubseteq> f x"
shows "f(x \<nabla> f x) \<sqsubseteq> x \<nabla> f x"
nitpick[card = 4, expect = genuine, show_consts]
(*

   0 < 1 < 2 < 3
f: 1   1   3   3

0 widen 1 = 2
2 widen 3 = 3
and x widen y arbitrary, eg 3, which guarantees termination

Kleene: f(f 0) = f 1 = 1 <= 1 = f 1

but

because not f 0 <= 0, we obtain 0 widen f 0 = 0 wide 1 = 2,
which is again not a pfp: not f 2 = 3 <= 2
Another widening step yields 2 widen f 2 = 2 widen 3 = 3
*)
oops

end
