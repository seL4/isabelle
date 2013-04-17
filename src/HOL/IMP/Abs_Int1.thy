(* Author: Tobias Nipkow *)

theory Abs_Int1
imports Abs_State
begin

(* FIXME mv *)
instantiation acom :: (type) vars
begin

definition "vars_acom = vars o strip"

instance ..

end

lemma finite_Cvars: "finite(vars(C::'a acom))"
by(simp add: vars_acom_def)


lemma le_iff_le_annos_zip: "C1 \<le> C2 \<longleftrightarrow>
 (\<forall> (a1,a2) \<in> set(zip (annos C1) (annos C2)). a1 \<le> a2) \<and> strip C1 = strip C2"
by(induct C1 C2 rule: less_eq_acom.induct) (auto simp: size_annos_same2)

lemma le_iff_le_annos: "C1 \<le> C2 \<longleftrightarrow>
  strip C1 = strip C2 \<and> (\<forall> i<size(annos C1). annos C1 ! i \<le> annos C2 ! i)"
by(auto simp add: le_iff_le_annos_zip set_zip) (metis size_annos_same2)

(* FIXME mv *)
lemma post_in_annos: "post C \<in> set(annos C)"
by(induction C) auto


subsection "Computable Abstract Interpretation"

text{* Abstract interpretation over type @{text st} instead of functions. *}

context Gamma
begin

fun aval' :: "aexp \<Rightarrow> 'av st \<Rightarrow> 'av" where
"aval' (N i) S = num' i" |
"aval' (V x) S = fun S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

lemma aval'_sound: "s : \<gamma>\<^isub>s S \<Longrightarrow> aval a s : \<gamma>(aval' a S)"
by (induction a) (auto simp: gamma_num' gamma_plus' \<gamma>_st_def)

lemma gamma_Step_subcomm: fixes C1 C2 :: "'a::semilattice_sup acom"
  assumes "!!x e S. f1 x e (\<gamma>\<^isub>o S) \<subseteq> \<gamma>\<^isub>o (f2 x e S)"
          "!!b S. g1 b (\<gamma>\<^isub>o S) \<subseteq> \<gamma>\<^isub>o (g2 b S)"
  shows "Step f1 g1 (\<gamma>\<^isub>o S) (\<gamma>\<^isub>c C) \<le> \<gamma>\<^isub>c (Step f2 g2 S C)"
proof(induction C arbitrary: S)
qed (auto simp: assms intro!: mono_gamma_o sup_ge1 sup_ge2)

lemma in_gamma_update: "\<lbrakk> s : \<gamma>\<^isub>s S; i : \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) : \<gamma>\<^isub>s(update S x a)"
by(simp add: \<gamma>_st_def)

end


text{* The for-clause (here and elsewhere) only serves the purpose of fixing
the name of the type parameter @{typ 'av} which would otherwise be renamed to
@{typ 'a}. *}

locale Abs_Int = Gamma where \<gamma>=\<gamma> for \<gamma> :: "'av::semilattice \<Rightarrow> val set"
begin

definition "step' = Step
  (\<lambda>x e S. case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(update S x (aval' e S)))
  (\<lambda>b S. S)"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI c = pfp (step' \<top>) (bot c)"


lemma strip_step'[simp]: "strip(step' S C) = strip C"
by(simp add: step'_def)


text{* Soundness: *}

lemma step_step': "step (\<gamma>\<^isub>o S) (\<gamma>\<^isub>c C) \<le> \<gamma>\<^isub>c (step' S C)"
unfolding step_def step'_def
by(rule gamma_Step_subcomm)
  (auto simp: intro!: aval'_sound in_gamma_update split: option.splits)

lemma AI_sound: "AI c = Some C \<Longrightarrow> CS c \<le> \<gamma>\<^isub>c C"
proof(simp add: CS_def AI_def)
  assume 1: "pfp (step' \<top>) (bot c) = Some C"
  have pfp': "step' \<top> C \<le> C" by(rule pfp_pfp[OF 1])
  have 2: "step (\<gamma>\<^isub>o \<top>) (\<gamma>\<^isub>c C) \<le> \<gamma>\<^isub>c C"  --"transfer the pfp'"
  proof(rule order_trans)
    show "step (\<gamma>\<^isub>o \<top>) (\<gamma>\<^isub>c C) \<le> \<gamma>\<^isub>c (step' \<top> C)" by(rule step_step')
    show "... \<le> \<gamma>\<^isub>c C" by (metis mono_gamma_c[OF pfp'])
  qed
  have 3: "strip (\<gamma>\<^isub>c C) = c" by(simp add: strip_pfp[OF _ 1] step'_def)
  have "lfp c (step (\<gamma>\<^isub>o \<top>)) \<le> \<gamma>\<^isub>c C"
    by(rule lfp_lowerbound[simplified,where f="step (\<gamma>\<^isub>o \<top>)", OF 3 2])
  thus "lfp c (step UNIV) \<le> \<gamma>\<^isub>c C" by simp
qed

end


subsubsection "Monotonicity"

lemma le_sup_disj: "x \<le> y \<or> x \<le> z \<Longrightarrow> x \<le> y \<squnion> (z::_::semilattice_sup)"
by (metis sup_ge1 sup_ge2 order_trans)

theorem mono2_Step: fixes C1 :: "'a::semilattice acom"
  assumes "!!x e S1 S2. S1 \<le> S2 \<Longrightarrow> f x e S1 \<le> f x e S2"
          "!!b S1 S2. S1 \<le> S2 \<Longrightarrow> g b S1 \<le> g b S2"
  shows "S1 \<le> S2 \<Longrightarrow> C1 \<le> C2 \<Longrightarrow> Step f g S1 C1 \<le> Step f g S2 C2"
by(induction C1 C2 arbitrary: S1 S2 rule: less_eq_acom.induct)
  (auto simp: mono_post assms le_sup_disj)


locale Abs_Int_mono = Abs_Int +
assumes mono_plus': "a1 \<le> b1 \<Longrightarrow> a2 \<le> b2 \<Longrightarrow> plus' a1 a2 \<le> plus' b1 b2"
begin

lemma mono_aval': "S1 \<le> S2 \<Longrightarrow> aval' e S1 \<le> aval' e S2"
by(induction e) (auto simp: mono_plus' mono_fun)

theorem mono_step': "S1 \<le> S2 \<Longrightarrow> C1 \<le> C2 \<Longrightarrow> step' S1 C1 \<le> step' S2 C2"
unfolding step'_def
by(rule mono2_Step) (auto simp: mono_aval' split: option.split)

lemma mono_step'_top: "C \<le> C' \<Longrightarrow> step' \<top> C \<le> step' \<top> C'"
by (metis mono_step' order_refl)

lemma AI_least_pfp: assumes "AI c = Some C" "step' \<top> C' \<le> C'" "strip C' = c"
shows "C \<le> C'"
by(rule pfp_bot_least[OF _ _ assms(2,3) assms(1)[unfolded AI_def]])
  (simp_all add: mono_step'_top)

end


subsubsection "Termination"

lemma pfp_termination:
fixes x0 :: "'a::order" and m :: "'a \<Rightarrow> nat"
assumes mono: "\<And>x y. I x \<Longrightarrow> I y \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
and m: "\<And>x y. I x \<Longrightarrow> I y \<Longrightarrow> x < y \<Longrightarrow> m x > m y"
and I: "\<And>x y. I x \<Longrightarrow> I(f x)" and "I x0" and "x0 \<le> f x0"
shows "\<exists>x. pfp f x0 = Some x"
proof(simp add: pfp_def, rule wf_while_option_Some[where P = "%x. I x & x \<le> f x"])
  show "wf {(y,x). ((I x \<and> x \<le> f x) \<and> \<not> f x \<le> x) \<and> y = f x}"
    by(rule wf_subset[OF wf_measure[of m]]) (auto simp: m I)
next
  show "I x0 \<and> x0 \<le> f x0" using `I x0` `x0 \<le> f x0` by blast
next
  fix x assume "I x \<and> x \<le> f x" thus "I(f x) \<and> f x \<le> f(f x)"
    by (blast intro: I mono)
qed


locale Measure1 =
fixes m :: "'av::{order,top} \<Rightarrow> nat"
fixes h :: "nat"
assumes h: "m x \<le> h"
begin

definition m_s :: "vname set \<Rightarrow> 'av st \<Rightarrow> nat" ("m\<^isub>s") where
"m_s X S = (\<Sum> x \<in> X. m(fun S x))"

lemma m_s_h: "finite X \<Longrightarrow> m_s X S \<le> h * card X"
by(simp add: m_s_def) (metis nat_mult_commute of_nat_id setsum_bounded[OF h])

definition m_o :: "vname set \<Rightarrow> 'av st option \<Rightarrow> nat" ("m\<^isub>o") where
"m_o X opt = (case opt of None \<Rightarrow> h * card X + 1 | Some S \<Rightarrow> m_s X S)"

lemma m_o_h: "finite X \<Longrightarrow> m_o X opt \<le> (h*card X + 1)"
by(auto simp add: m_o_def m_s_h le_SucI split: option.split dest:m_s_h)

definition m_c :: "'av st option acom \<Rightarrow> nat" ("m\<^isub>c") where
"m_c C = (\<Sum>i<size(annos C). m_o (vars C) (annos C ! i))"

text{* Upper complexity bound: *}
lemma m_c_h: "m_c C \<le> size(annos C) * (h * card(vars C) + 1)"
proof-
  let ?X = "vars C" let ?n = "card ?X" let ?a = "size(annos C)"
  have "m_c C = (\<Sum>i<?a. m_o ?X (annos C ! i))" by(simp add: m_c_def)
  also have "\<dots> \<le> (\<Sum>i<?a. h * ?n + 1)"
    apply(rule setsum_mono) using m_o_h[OF finite_Cvars] by simp
  also have "\<dots> = ?a * (h * ?n + 1)" by simp
  finally show ?thesis .
qed

end

text{* The predicates @{text "top_on X a"} that follow describe that @{text a} is some object
that maps all variables in @{text X} to @{term \<top>}.
This is an important invariant for the termination proof where we argue that only
the finitely many variables in the program change. That the others do not change
follows because they remain @{term \<top>}. *}

class top_on =
fixes top_on :: "vname set \<Rightarrow> 'a \<Rightarrow> bool"

instantiation st :: (top)top_on
begin

fun top_on_st :: "vname set \<Rightarrow> 'a st \<Rightarrow> bool" where
"top_on_st X F = (\<forall>x\<in>X. fun F x = \<top>)"

instance ..

end

instantiation option :: (top_on)top_on
begin

fun top_on_option :: "vname set \<Rightarrow> 'a option \<Rightarrow> bool" where
"top_on_option X (Some F) = top_on X F" |
"top_on_option X None = True"

instance ..

end

instantiation acom :: (top_on)top_on
begin

definition top_on_acom :: "vname set \<Rightarrow> 'a acom \<Rightarrow> bool" where
"top_on_acom X C = (\<forall>a \<in> set(annos C). top_on X a)"

instance ..

end

lemma top_on_top: "top_on X (\<top>::_ st option)"
by(auto simp: top_option_def fun_top)

lemma top_on_bot: "top_on X (bot c)"
by(auto simp add: top_on_acom_def bot_def)

lemma top_on_post: "top_on X C \<Longrightarrow> top_on X (post C)"
by(simp add: top_on_acom_def post_in_annos)

lemma top_on_acom_simps:
  "top_on X (SKIP {Q}) = top_on X Q"
  "top_on X (x ::= e {Q}) = top_on X Q"
  "top_on X (C1;C2) = (top_on X C1 \<and> top_on X C2)"
  "top_on X (IF b THEN {P1} C1 ELSE {P2} C2 {Q}) =
   (top_on X P1 \<and> top_on X C1 \<and> top_on X P2 \<and> top_on X C2 \<and> top_on X Q)"
  "top_on X ({I} WHILE b DO {P} C {Q}) =
   (top_on X I \<and> top_on X C \<and> top_on X P \<and> top_on X Q)"
by(auto simp add: top_on_acom_def)

lemma top_on_sup:
  "top_on X o1 \<Longrightarrow> top_on X o2 \<Longrightarrow> top_on X (o1 \<squnion> o2 :: _ st option)"
apply(induction o1 o2 rule: sup_option.induct)
apply(auto)
by transfer simp

lemma top_on_Step: fixes C :: "('a::semilattice)st option acom"
assumes "!!x e S. \<lbrakk>top_on X S; x \<notin> X; vars e \<subseteq> -X\<rbrakk> \<Longrightarrow> top_on X (f x e S)"
        "!!b S. top_on X S \<Longrightarrow> vars b \<subseteq> -X \<Longrightarrow> top_on X (g b S)"
shows "\<lbrakk> vars C \<subseteq> -X; top_on X S; top_on X C \<rbrakk> \<Longrightarrow> top_on X (Step f g S C)"
proof(induction C arbitrary: S)
qed (auto simp: top_on_acom_simps vars_acom_def top_on_post top_on_sup assms)


locale Measure = Measure1 +
assumes m2: "x < y \<Longrightarrow> m x > m y"
begin

lemma m1: "x \<le> y \<Longrightarrow> m x \<ge> m y"
by(auto simp: le_less m2)

lemma m_s2_rep: assumes "finite(X)" and "S1 = S2 on -X" and "\<forall>x. S1 x \<le> S2 x" and "S1 \<noteq> S2"
shows "(\<Sum>x\<in>X. m (S2 x)) < (\<Sum>x\<in>X. m (S1 x))"
proof-
  from assms(3) have 1: "\<forall>x\<in>X. m(S1 x) \<ge> m(S2 x)" by (simp add: m1)
  from assms(2,3,4) have "EX x:X. S1 x < S2 x"
    by(simp add: fun_eq_iff) (metis Compl_iff le_neq_trans)
  hence 2: "\<exists>x\<in>X. m(S1 x) > m(S2 x)" by (metis m2)
  from setsum_strict_mono_ex1[OF `finite X` 1 2]
  show "(\<Sum>x\<in>X. m (S2 x)) < (\<Sum>x\<in>X. m (S1 x))" .
qed

lemma m_s2: "finite(X) \<Longrightarrow> fun S1 = fun S2 on -X \<Longrightarrow> S1 < S2 \<Longrightarrow> m_s X S1 > m_s X S2"
apply(auto simp add: less_st_def m_s_def)
apply (transfer fixing: m)
apply(simp add: less_eq_st_rep_iff eq_st_def m_s2_rep)
done

lemma m_o2: "finite X \<Longrightarrow> top_on (-X) o1 \<Longrightarrow> top_on (-X) o2 \<Longrightarrow>
  o1 < o2 \<Longrightarrow> m_o X o1 > m_o X o2"
proof(induction o1 o2 rule: less_eq_option.induct)
  case 1 thus ?case by (auto simp: m_o_def m_s2 less_option_def)
next
  case 2 thus ?case by(auto simp: m_o_def less_option_def le_imp_less_Suc m_s_h)
next
  case 3 thus ?case by (auto simp: less_option_def)
qed

lemma m_o1: "finite X \<Longrightarrow> top_on (-X) o1 \<Longrightarrow> top_on (-X) o2 \<Longrightarrow>
  o1 \<le> o2 \<Longrightarrow> m_o X o1 \<ge> m_o X o2"
by(auto simp: le_less m_o2)


lemma m_c2: "top_on (-vars C1) C1 \<Longrightarrow> top_on (-vars C2) C2 \<Longrightarrow>
  C1 < C2 \<Longrightarrow> m_c C1 > m_c C2"
proof(auto simp add: le_iff_le_annos m_c_def size_annos_same[of C1 C2] vars_acom_def less_acom_def)
  let ?X = "vars(strip C2)"
  assume top: "top_on (- vars(strip C2)) C1"  "top_on (- vars(strip C2)) C2"
  and strip_eq: "strip C1 = strip C2"
  and 0: "\<forall>i<size(annos C2). annos C1 ! i \<le> annos C2 ! i"
  hence 1: "\<forall>i<size(annos C2). m_o ?X (annos C1 ! i) \<ge> m_o ?X (annos C2 ! i)"
    apply (auto simp: all_set_conv_all_nth vars_acom_def top_on_acom_def)
    by (metis finite_cvars m_o1 size_annos_same2)
  fix i assume i: "i < size(annos C2)" "\<not> annos C2 ! i \<le> annos C1 ! i"
  have topo1: "top_on (- ?X) (annos C1 ! i)"
    using i(1) top(1) by(simp add: top_on_acom_def size_annos_same[OF strip_eq])
  have topo2: "top_on (- ?X) (annos C2 ! i)"
    using i(1) top(2) by(simp add: top_on_acom_def size_annos_same[OF strip_eq])
  from i have "m_o ?X (annos C1 ! i) > m_o ?X (annos C2 ! i)" (is "?P i")
    by (metis 0 less_option_def m_o2[OF finite_cvars topo1] topo2)
  hence 2: "\<exists>i < size(annos C2). ?P i" using `i < size(annos C2)` by blast
  show "(\<Sum>i<size(annos C2). m_o ?X (annos C2 ! i))
         < (\<Sum>i<size(annos C2). m_o ?X (annos C1 ! i))"
    apply(rule setsum_strict_mono_ex1) using 1 2 by (auto)
qed

end


locale Abs_Int_measure =
  Abs_Int_mono where \<gamma>=\<gamma> + Measure where m=m
  for \<gamma> :: "'av::semilattice \<Rightarrow> val set" and m :: "'av \<Rightarrow> nat"
begin

lemma top_on_step': "\<lbrakk> vars C \<subseteq> -X; top_on X C \<rbrakk> \<Longrightarrow> top_on X (step' \<top> C)"
unfolding step'_def
by(rule top_on_Step)
  (auto simp add: top_option_def fun_top split: option.splits)

lemma AI_Some_measure: "\<exists>C. AI c = Some C"
unfolding AI_def
apply(rule pfp_termination[where I = "\<lambda>C. strip C = c \<and> top_on (- vars C) C" and m="m_c"])
apply(simp_all add: m_c2 mono_step'_top bot_least top_on_bot)
apply(auto simp add: top_on_step' vars_acom_def)
done

end

end
