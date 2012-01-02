(* Author: Tobias Nipkow *)

theory Abs_Int2
imports Abs_Int1_ivl
begin


subsection "Widening and Narrowing"

class WN = SL_top +
fixes widen :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<nabla>" 65)
assumes widen1: "x \<sqsubseteq> x \<nabla> y"
assumes widen2: "y \<sqsubseteq> x \<nabla> y"
fixes narrow :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<triangle>" 65)
assumes narrow1: "y \<sqsubseteq> x \<Longrightarrow> y \<sqsubseteq> x \<triangle> y"
assumes narrow2: "y \<sqsubseteq> x \<Longrightarrow> x \<triangle> y \<sqsubseteq> x"


instantiation ivl :: WN
begin

definition "widen_ivl ivl1 ivl2 =
  ((*if is_empty ivl1 then ivl2 else
   if is_empty ivl2 then ivl1 else*)
     case (ivl1,ivl2) of (I l1 h1, I l2 h2) \<Rightarrow>
       I (if le_option False l2 l1 \<and> l2 \<noteq> l1 then None else l1)
         (if le_option True h1 h2 \<and> h1 \<noteq> h2 then None else h1))"

definition "narrow_ivl ivl1 ivl2 =
  ((*if is_empty ivl1 \<or> is_empty ivl2 then empty else*)
     case (ivl1,ivl2) of (I l1 h1, I l2 h2) \<Rightarrow>
       I (if l1 = None then l2 else l1)
         (if h1 = None then h2 else h1))"

instance
proof qed
  (auto simp add: widen_ivl_def narrow_ivl_def le_option_def le_ivl_def empty_def split: ivl.split option.split if_splits)

end

instantiation st :: (WN)WN
begin

definition "widen_st F1 F2 =
  FunDom (\<lambda>x. fun F1 x \<nabla> fun F2 x) (inter_list (dom F1) (dom F2))"

definition "narrow_st F1 F2 =
  FunDom (\<lambda>x. fun F1 x \<triangle> fun F2 x) (inter_list (dom F1) (dom F2))"

instance
proof
  case goal1 thus ?case
    by(simp add: widen_st_def le_st_def lookup_def widen1)
next
  case goal2 thus ?case
    by(simp add: widen_st_def le_st_def lookup_def widen2)
next
  case goal3 thus ?case
    by(auto simp: narrow_st_def le_st_def lookup_def narrow1)
next
  case goal4 thus ?case
    by(auto simp: narrow_st_def le_st_def lookup_def narrow2)
qed

end

instantiation option :: (WN)WN
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
  case goal1 show ?case
    by(induct x y rule: widen_option.induct) (simp_all add: widen1)
next
  case goal2 show ?case
    by(induct x y rule: widen_option.induct) (simp_all add: widen2)
next
  case goal3 thus ?case
    by(induct x y rule: narrow_option.induct) (simp_all add: narrow1)
next
  case goal4 thus ?case
    by(induct x y rule: narrow_option.induct) (simp_all add: narrow2)
qed

end

fun map2_acom :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a acom \<Rightarrow> 'a acom \<Rightarrow> 'a acom" where
"map2_acom f (SKIP {a1}) (SKIP {a2}) = (SKIP {f a1 a2})" |
"map2_acom f (x ::= e {a1}) (x' ::= e' {a2}) = (x ::= e {f a1 a2})" |
"map2_acom f (c1;c2) (c1';c2') = (map2_acom f c1 c1'; map2_acom f c2 c2')" |
"map2_acom f (IF b THEN c1 ELSE c2 {a1}) (IF b' THEN c1' ELSE c2' {a2}) =
  (IF b THEN map2_acom f c1 c1' ELSE map2_acom f c2 c2' {f a1 a2})" |
"map2_acom f ({a1} WHILE b DO c {a2}) ({a3} WHILE b' DO c' {a4}) =
  ({f a1 a3} WHILE b DO map2_acom f c c' {f a2 a4})"

abbreviation widen_acom :: "('a::WN)acom \<Rightarrow> 'a acom \<Rightarrow> 'a acom" (infix "\<nabla>\<^sub>c" 65)
where "widen_acom == map2_acom (op \<nabla>)"

abbreviation narrow_acom :: "('a::WN)acom \<Rightarrow> 'a acom \<Rightarrow> 'a acom" (infix "\<triangle>\<^sub>c" 65)
where "narrow_acom == map2_acom (op \<triangle>)"

lemma widen1_acom: "strip c = strip c' \<Longrightarrow> c \<sqsubseteq> c \<nabla>\<^sub>c c'"
by(induct c c' rule: le_acom.induct)(simp_all add: widen1)

lemma widen2_acom: "strip c = strip c' \<Longrightarrow> c' \<sqsubseteq> c \<nabla>\<^sub>c c'"
by(induct c c' rule: le_acom.induct)(simp_all add: widen2)

lemma narrow1_acom: "y \<sqsubseteq> x \<Longrightarrow> y \<sqsubseteq> x \<triangle>\<^sub>c y"
by(induct y x rule: le_acom.induct) (simp_all add: narrow1)

lemma narrow2_acom: "y \<sqsubseteq> x \<Longrightarrow> x \<triangle>\<^sub>c y \<sqsubseteq> x"
by(induct y x rule: le_acom.induct) (simp_all add: narrow2)


subsubsection "Post-fixed point computation"

definition
  prefp :: "(('a::preord) \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option" where
"prefp f = while_option (\<lambda>x. \<not> x \<sqsubseteq> f x) f"

definition
  pfp_WN :: "(('a::WN)option acom \<Rightarrow> 'a option acom) \<Rightarrow> com \<Rightarrow> 'a option acom option"
where "pfp_WN f c = (case lpfp\<^isub>c (\<lambda>c. c \<nabla>\<^sub>c f c) c of None \<Rightarrow> None
                     | Some c' \<Rightarrow> prefp (\<lambda>c. c \<triangle>\<^sub>c f c) c')"

lemma strip_map2_acom:
 "strip c1 = strip c2 \<Longrightarrow> strip(map2_acom f c1 c2) = strip c1"
by(induct f c1 c2 rule: map2_acom.induct) simp_all

lemma lpfp_step_up_pfp:
 "\<lbrakk> \<forall>c. strip(f c) = strip c;  lpfp\<^isub>c (\<lambda>c. c \<nabla>\<^sub>c f c) c = Some c' \<rbrakk> \<Longrightarrow> f c' \<sqsubseteq> c'"
by (metis (no_types) assms lpfpc_pfp le_trans widen2_acom)

lemma iter_down_pfp: assumes "mono f" and "f x0 \<sqsubseteq> x0" 
and "prefp (\<lambda>c. c \<triangle>\<^sub>c f c) x0 = Some x"
shows "f x \<sqsubseteq> x \<and> x \<sqsubseteq> x0" (is "?P x")
proof-
  { fix x assume "?P x"
    note 1 = conjunct1[OF this] and 2 = conjunct2[OF this]
    let ?x' = "x \<triangle>\<^sub>c f x"
    have "?P ?x'"
    proof
      have "f ?x' \<sqsubseteq> f x"  by(rule monoD[OF `mono f` narrow2_acom[OF 1]])
      also have "\<dots> \<sqsubseteq> ?x'" by(rule narrow1_acom[OF 1])
      finally show "f ?x' \<sqsubseteq> ?x'" .
      have "?x' \<sqsubseteq> x" by (rule narrow2_acom[OF 1])
      also have "x \<sqsubseteq> x0" by(rule 2)
      finally show "?x' \<sqsubseteq> x0" .
    qed
  }
  with while_option_rule[where P = ?P, OF _ assms(3)[simplified prefp_def]]
    assms(2) le_refl
  show ?thesis by blast
qed


lemma pfp_WN_pfp:
  "\<lbrakk> \<forall>c. strip (f c) = strip c;  mono f;  pfp_WN f c = Some c' \<rbrakk> \<Longrightarrow> f c' \<sqsubseteq> c'"
unfolding pfp_WN_def
by (auto dest: iter_down_pfp lpfp_step_up_pfp split: option.splits)

lemma strip_while: fixes f :: "'a acom \<Rightarrow> 'a acom"
assumes "\<forall>c. strip (f c) = strip c" and "while_option P f c = Some c'"
shows "strip c' = strip c"
using while_option_rule[where P = "\<lambda>c'. strip c' = strip c", OF _ assms(2)]
by (metis assms(1))

lemma strip_pfp_WN:
  "\<lbrakk> \<forall>c. strip(f c) = strip c; pfp_WN f c = Some c' \<rbrakk> \<Longrightarrow> strip c' = c"
apply(auto simp add: pfp_WN_def prefp_def split: option.splits)
by (metis (no_types) strip_lpfpc strip_map2_acom strip_while)

locale Abs_Int2 = Abs_Int1_mono
where \<gamma>=\<gamma> for \<gamma> :: "'av::{WN,L_top_bot} \<Rightarrow> val set"
begin

definition AI_WN :: "com \<Rightarrow> 'av st option acom option" where
"AI_WN = pfp_WN (step' \<top>)"

lemma AI_WN_sound: "AI_WN c = Some c' \<Longrightarrow> CS UNIV c \<le> \<gamma>\<^isub>c c'"
proof(simp add: CS_def AI_WN_def)
  assume 1: "pfp_WN (step' \<top>) c = Some c'"
  from pfp_WN_pfp[OF allI[OF strip_step'] mono_step' 1]
  have 2: "step' \<top> c' \<sqsubseteq> c'" .
  have 3: "strip (\<gamma>\<^isub>c (step' \<top> c')) = c" by(simp add: strip_pfp_WN[OF _ 1])
  have "lfp (step UNIV) c \<le> \<gamma>\<^isub>c (step' \<top> c')"
  proof(rule lfp_lowerbound[simplified,OF 3])
    show "step UNIV (\<gamma>\<^isub>c (step' \<top> c')) \<le> \<gamma>\<^isub>c (step' \<top> c')"
    proof(rule step_preserves_le[OF _ _])
      show "UNIV \<subseteq> \<gamma>\<^isub>o \<top>" by simp
      show "\<gamma>\<^isub>c (step' \<top> c') \<le> \<gamma>\<^isub>c c'" by(rule mono_gamma_c[OF 2])
    qed
  qed
  from this 2 show "lfp (step UNIV) c \<le> \<gamma>\<^isub>c c'"
    by (blast intro: mono_gamma_c order_trans)
qed

end

interpretation Abs_Int2
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = plus_ivl
and filter_plus' = filter_plus_ivl and filter_less' = filter_less_ivl
defines AI_ivl' is AI_WN
proof qed


subsubsection "Tests"

definition "step_up_ivl n = ((\<lambda>c. c \<nabla>\<^sub>c step_ivl \<top> c)^^n)"
definition "step_down_ivl n = ((\<lambda>c. c \<triangle>\<^sub>c step_ivl \<top> c)^^n)"

text{* For @{const test3_ivl}, @{const AI_ivl} needed as many iterations as
the loop took to execute. In contrast, @{const AI_ivl} converges in a
constant number of steps: *}

value [code] "show_acom (step_up_ivl 1 (\<bottom>\<^sub>c test3_ivl))"
value [code] "show_acom (step_up_ivl 2 (\<bottom>\<^sub>c test3_ivl))"
value [code] "show_acom (step_up_ivl 3 (\<bottom>\<^sub>c test3_ivl))"
value [code] "show_acom (step_up_ivl 4 (\<bottom>\<^sub>c test3_ivl))"
value [code] "show_acom (step_up_ivl 5 (\<bottom>\<^sub>c test3_ivl))"
value [code] "show_acom (step_down_ivl 1 (step_up_ivl 5 (\<bottom>\<^sub>c test3_ivl)))"
value [code] "show_acom (step_down_ivl 2 (step_up_ivl 5 (\<bottom>\<^sub>c test3_ivl)))"
value [code] "show_acom (step_down_ivl 3 (step_up_ivl 5 (\<bottom>\<^sub>c test3_ivl)))"

text{* Now all the analyses terminate: *}

value [code] "show_acom_opt (AI_ivl' test4_ivl)"
value [code] "show_acom_opt (AI_ivl' test5_ivl)"
value [code] "show_acom_opt (AI_ivl' test6_ivl)"

end
