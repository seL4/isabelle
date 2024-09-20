theory CR
imports Lam_Funs
begin

text \<open>The Church-Rosser proof from Barendregt's book\<close>

lemma forget: 
  assumes asm: "x\<sharp>L"
  shows "L[x::=P] = L"
using asm
proof (nominal_induct L avoiding: x P rule: lam.strong_induct)
  case (Var z)
  have "x\<sharp>Var z" by fact
  thus "(Var z)[x::=P] = (Var z)" by (simp add: fresh_atm)
next 
  case (App M1 M2)
  have "x\<sharp>App M1 M2" by fact
  moreover
  have ih1: "x\<sharp>M1 \<Longrightarrow> M1[x::=P] = M1" by fact
  moreover
  have ih1: "x\<sharp>M2 \<Longrightarrow> M2[x::=P] = M2" by fact
  ultimately show "(App M1 M2)[x::=P] = (App M1 M2)" by simp
next
  case (Lam z M)
  have vc: "z\<sharp>x" "z\<sharp>P" by fact+
  have ih: "x\<sharp>M \<Longrightarrow>  M[x::=P] = M" by fact
  have asm: "x\<sharp>Lam [z].M" by fact
  then have "x\<sharp>M" using vc by (simp add: fresh_atm abs_fresh)
  then have "M[x::=P] = M" using ih by simp
  then show "(Lam [z].M)[x::=P] = Lam [z].M" using vc by simp
qed

lemma forget_automatic: 
  assumes asm: "x\<sharp>L"
  shows "L[x::=P] = L"
  using asm 
by (nominal_induct L avoiding: x P rule: lam.strong_induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact: 
  fixes z::"name"
  assumes asms: "z\<sharp>N" "z\<sharp>L"
  shows "z\<sharp>(N[y::=L])"
using asms
proof (nominal_induct N avoiding: z y L rule: lam.strong_induct)
  case (Var u)
  have "z\<sharp>(Var u)" "z\<sharp>L" by fact+
  thus "z\<sharp>((Var u)[y::=L])" by simp
next
  case (App N1 N2)
  have ih1: "\<lbrakk>z\<sharp>N1; z\<sharp>L\<rbrakk> \<Longrightarrow> z\<sharp>N1[y::=L]" by fact
  moreover
  have ih2: "\<lbrakk>z\<sharp>N2; z\<sharp>L\<rbrakk> \<Longrightarrow> z\<sharp>N2[y::=L]" by fact
  moreover 
  have "z\<sharp>App N1 N2" "z\<sharp>L" by fact+
  ultimately show "z\<sharp>((App N1 N2)[y::=L])" by simp 
next
  case (Lam u N1)
  have vc: "u\<sharp>z" "u\<sharp>y" "u\<sharp>L" by fact+
  have "z\<sharp>Lam [u].N1" by fact
  hence "z\<sharp>N1" using vc by (simp add: abs_fresh fresh_atm)
  moreover
  have ih: "\<lbrakk>z\<sharp>N1; z\<sharp>L\<rbrakk> \<Longrightarrow> z\<sharp>(N1[y::=L])" by fact
  moreover
  have  "z\<sharp>L" by fact
  ultimately show "z\<sharp>(Lam [u].N1)[y::=L]" using vc by (simp add: abs_fresh)
qed

lemma fresh_fact_automatic: 
  fixes z::"name"
  assumes asms: "z\<sharp>N" "z\<sharp>L"
  shows "z\<sharp>(N[y::=L])"
  using asms 
by (nominal_induct N avoiding: z y L rule: lam.strong_induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact': 
  fixes a::"name"
  assumes a: "a\<sharp>t2"
  shows "a\<sharp>t1[a::=t2]"
using a 
by (nominal_induct t1 avoiding: a t2 rule: lam.strong_induct)
   (auto simp add: abs_fresh fresh_atm)

lemma substitution_lemma:  
  assumes a: "x\<noteq>y"
  and     b: "x\<sharp>L"
  shows "M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
using a b
proof (nominal_induct M avoiding: x y N L rule: lam.strong_induct)
  case (Var z) (* case 1: Variables*)
  have "x\<noteq>y" by fact
  have "x\<sharp>L" by fact
  show "Var z[x::=N][y::=L] = Var z[y::=L][x::=N[y::=L]]" (is "?LHS = ?RHS")
  proof -
    { (*Case 1.1*)
      assume  "z=x"
      have "(1)": "?LHS = N[y::=L]" using \<open>z=x\<close> by simp
      have "(2)": "?RHS = N[y::=L]" using \<open>z=x\<close> \<open>x\<noteq>y\<close> by simp
      from "(1)" "(2)" have "?LHS = ?RHS"  by simp
    }
    moreover 
    { (*Case 1.2*)
      assume "z=y" and "z\<noteq>x" 
      have "(1)": "?LHS = L"               using \<open>z\<noteq>x\<close> \<open>z=y\<close> by simp
      have "(2)": "?RHS = L[x::=N[y::=L]]" using \<open>z=y\<close> by simp
      have "(3)": "L[x::=N[y::=L]] = L"    using \<open>x\<sharp>L\<close> by (simp add: forget)
      from "(1)" "(2)" "(3)" have "?LHS = ?RHS" by simp
    }
    moreover 
    { (*Case 1.3*)
      assume "z\<noteq>x" and "z\<noteq>y"
      have "(1)": "?LHS = Var z" using \<open>z\<noteq>x\<close> \<open>z\<noteq>y\<close> by simp
      have "(2)": "?RHS = Var z" using \<open>z\<noteq>x\<close> \<open>z\<noteq>y\<close> by simp
      from "(1)" "(2)" have "?LHS = ?RHS" by simp
    }
    ultimately show "?LHS = ?RHS" by blast
  qed
next
  case (Lam z M1) (* case 2: lambdas *)
  have ih: "\<lbrakk>x\<noteq>y; x\<sharp>L\<rbrakk> \<Longrightarrow> M1[x::=N][y::=L] = M1[y::=L][x::=N[y::=L]]" by fact
  have "x\<noteq>y" by fact
  have "x\<sharp>L" by fact
  have fs: "z\<sharp>x" "z\<sharp>y" "z\<sharp>N" "z\<sharp>L" by fact+
  hence "z\<sharp>N[y::=L]" by (simp add: fresh_fact)
  show "(Lam [z].M1)[x::=N][y::=L] = (Lam [z].M1)[y::=L][x::=N[y::=L]]" (is "?LHS=?RHS") 
  proof - 
    have "?LHS = Lam [z].(M1[x::=N][y::=L])" using \<open>z\<sharp>x\<close> \<open>z\<sharp>y\<close> \<open>z\<sharp>N\<close> \<open>z\<sharp>L\<close> by simp
    also from ih have "\<dots> = Lam [z].(M1[y::=L][x::=N[y::=L]])" using \<open>x\<noteq>y\<close> \<open>x\<sharp>L\<close> by simp
    also have "\<dots> = (Lam [z].(M1[y::=L]))[x::=N[y::=L]]" using \<open>z\<sharp>x\<close> \<open>z\<sharp>N[y::=L]\<close> by simp
    also have "\<dots> = ?RHS" using  \<open>z\<sharp>y\<close> \<open>z\<sharp>L\<close> by simp
    finally show "?LHS = ?RHS" .
  qed
next
  case (App M1 M2) (* case 3: applications *)
  thus "(App M1 M2)[x::=N][y::=L] = (App M1 M2)[y::=L][x::=N[y::=L]]" by simp
qed

lemma substitution_lemma_automatic:  
  assumes asm: "x\<noteq>y" "x\<sharp>L"
  shows "M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
  using asm 
by (nominal_induct M avoiding: x y N L rule: lam.strong_induct)
   (auto simp add: fresh_fact forget)

section \<open>Beta Reduction\<close>

inductive
  "Beta" :: "lam\<Rightarrow>lam\<Rightarrow>bool" (\<open> _ \<longrightarrow>\<^sub>\<beta> _\<close> [80,80] 80)
where
    b1[intro]: "s1\<longrightarrow>\<^sub>\<beta>s2 \<Longrightarrow> (App s1 t)\<longrightarrow>\<^sub>\<beta>(App s2 t)"
  | b2[intro]: "s1\<longrightarrow>\<^sub>\<beta>s2 \<Longrightarrow> (App t s1)\<longrightarrow>\<^sub>\<beta>(App t s2)"
  | b3[intro]: "s1\<longrightarrow>\<^sub>\<beta>s2 \<Longrightarrow> (Lam [a].s1)\<longrightarrow>\<^sub>\<beta> (Lam [a].s2)"
  | b4[intro]: "a\<sharp>s2 \<Longrightarrow> (App (Lam [a].s1) s2)\<longrightarrow>\<^sub>\<beta>(s1[a::=s2])"

equivariance Beta

nominal_inductive Beta
  by (simp_all add: abs_fresh fresh_fact')

inductive
  "Beta_star"  :: "lam\<Rightarrow>lam\<Rightarrow>bool" (\<open> _ \<longrightarrow>\<^sub>\<beta>\<^sup>* _\<close> [80,80] 80)
where
    bs1[intro, simp]: "M \<longrightarrow>\<^sub>\<beta>\<^sup>* M"
  | bs2[intro]: "\<lbrakk>M1\<longrightarrow>\<^sub>\<beta>\<^sup>* M2; M2 \<longrightarrow>\<^sub>\<beta> M3\<rbrakk> \<Longrightarrow> M1 \<longrightarrow>\<^sub>\<beta>\<^sup>* M3"

equivariance Beta_star

lemma beta_star_trans:
  assumes a1: "M1\<longrightarrow>\<^sub>\<beta>\<^sup>* M2"
  and     a2: "M2\<longrightarrow>\<^sub>\<beta>\<^sup>* M3"
  shows "M1 \<longrightarrow>\<^sub>\<beta>\<^sup>* M3"
using a2 a1
by (induct) (auto)

section \<open>One-Reduction\<close>

inductive
  One :: "lam\<Rightarrow>lam\<Rightarrow>bool" (\<open> _ \<longrightarrow>\<^sub>1 _\<close> [80,80] 80)
where
    o1[intro!]:      "M\<longrightarrow>\<^sub>1M"
  | o2[simp,intro!]: "\<lbrakk>t1\<longrightarrow>\<^sub>1t2;s1\<longrightarrow>\<^sub>1s2\<rbrakk> \<Longrightarrow> (App t1 s1)\<longrightarrow>\<^sub>1(App t2 s2)"
  | o3[simp,intro!]: "s1\<longrightarrow>\<^sub>1s2 \<Longrightarrow> (Lam [a].s1)\<longrightarrow>\<^sub>1(Lam [a].s2)"
  | o4[simp,intro!]: "\<lbrakk>a\<sharp>(s1,s2); s1\<longrightarrow>\<^sub>1s2;t1\<longrightarrow>\<^sub>1t2\<rbrakk> \<Longrightarrow> (App (Lam [a].t1) s1)\<longrightarrow>\<^sub>1(t2[a::=s2])"

equivariance One

nominal_inductive One
  by (simp_all add: abs_fresh fresh_fact')

inductive
  "One_star"  :: "lam\<Rightarrow>lam\<Rightarrow>bool" (\<open> _ \<longrightarrow>\<^sub>1\<^sup>* _\<close> [80,80] 80)
where
    os1[intro, simp]: "M \<longrightarrow>\<^sub>1\<^sup>* M"
  | os2[intro]: "\<lbrakk>M1\<longrightarrow>\<^sub>1\<^sup>* M2; M2 \<longrightarrow>\<^sub>1 M3\<rbrakk> \<Longrightarrow> M1 \<longrightarrow>\<^sub>1\<^sup>* M3"

equivariance One_star 

lemma one_star_trans:
  assumes a1: "M1\<longrightarrow>\<^sub>1\<^sup>* M2" 
  and     a2: "M2\<longrightarrow>\<^sub>1\<^sup>* M3"
  shows "M1\<longrightarrow>\<^sub>1\<^sup>* M3"
using a2 a1
by (induct) (auto)

lemma one_fresh_preserv:
  fixes a :: "name"
  assumes a: "t\<longrightarrow>\<^sub>1s"
  and     b: "a\<sharp>t"
  shows "a\<sharp>s"
using a b
proof (induct)
  case o1 thus ?case by simp
next
  case o2 thus ?case by simp
next
  case (o3 s1 s2 c)
  have ih: "a\<sharp>s1 \<Longrightarrow>  a\<sharp>s2" by fact
  have c: "a\<sharp>Lam [c].s1" by fact
  show ?case
  proof (cases "a=c")
    assume "a=c" thus "a\<sharp>Lam [c].s2" by (simp add: abs_fresh)
  next
    assume d: "a\<noteq>c" 
    with c have "a\<sharp>s1" by (simp add: abs_fresh)
    hence "a\<sharp>s2" using ih by simp
    thus "a\<sharp>Lam [c].s2" using d by (simp add: abs_fresh) 
  qed
next 
  case (o4 c t1 t2 s1 s2)
  have i1: "a\<sharp>t1 \<Longrightarrow> a\<sharp>t2" by fact
  have i2: "a\<sharp>s1 \<Longrightarrow> a\<sharp>s2" by fact
  have as: "a\<sharp>App (Lam [c].s1) t1" by fact
  hence c1: "a\<sharp>Lam [c].s1" and c2: "a\<sharp>t1" by (simp add: fresh_prod)+
  from c2 i1 have c3: "a\<sharp>t2" by simp
  show "a\<sharp>s2[c::=t2]"
  proof (cases "a=c")
    assume "a=c"
    thus "a\<sharp>s2[c::=t2]" using c3 by (simp add: fresh_fact')
  next
    assume d1: "a\<noteq>c"
    from c1 d1 have "a\<sharp>s1" by (simp add: abs_fresh)
    hence "a\<sharp>s2" using i2 by simp
    thus "a\<sharp>s2[c::=t2]" using c3 by (simp add: fresh_fact)
  qed
qed

lemma one_fresh_preserv_automatic:
  fixes a :: "name"
  assumes a: "t\<longrightarrow>\<^sub>1s"
  and     b: "a\<sharp>t"
  shows "a\<sharp>s"
using a b
apply(nominal_induct avoiding: a rule: One.strong_induct)
apply(auto simp add: abs_fresh fresh_atm fresh_fact)
done

lemma subst_rename: 
  assumes a: "c\<sharp>t1"
  shows "t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2]"
using a
by (nominal_induct t1 avoiding: a c t2 rule: lam.strong_induct)
   (auto simp add: calc_atm fresh_atm abs_fresh)

lemma one_abs: 
  assumes a: "Lam [a].t\<longrightarrow>\<^sub>1t'"
  shows "\<exists>t''. t'=Lam [a].t'' \<and> t\<longrightarrow>\<^sub>1t''"
proof -
  have "a\<sharp>Lam [a].t" by (simp add: abs_fresh)
  with a have "a\<sharp>t'" by (simp add: one_fresh_preserv)
  with a show ?thesis
    by (cases rule: One.strong_cases[where a="a" and aa="a"])
       (auto simp add: lam.inject abs_fresh alpha)
qed

lemma one_app: 
  assumes a: "App t1 t2 \<longrightarrow>\<^sub>1 t'"
  shows "(\<exists>s1 s2. t' = App s1 s2 \<and> t1 \<longrightarrow>\<^sub>1 s1 \<and> t2 \<longrightarrow>\<^sub>1 s2) \<or> 
         (\<exists>a s s1 s2. t1 = Lam [a].s \<and> t' = s1[a::=s2] \<and> s \<longrightarrow>\<^sub>1 s1 \<and> t2 \<longrightarrow>\<^sub>1 s2 \<and> a\<sharp>(t2,s2))"
using a by (erule_tac One.cases) (auto simp add: lam.inject)

lemma one_red: 
  assumes a: "App (Lam [a].t1) t2 \<longrightarrow>\<^sub>1 M" "a\<sharp>(t2,M)"
  shows "(\<exists>s1 s2. M = App (Lam [a].s1) s2 \<and> t1 \<longrightarrow>\<^sub>1 s1 \<and> t2 \<longrightarrow>\<^sub>1 s2) \<or> 
         (\<exists>s1 s2. M = s1[a::=s2] \<and> t1 \<longrightarrow>\<^sub>1 s1 \<and> t2 \<longrightarrow>\<^sub>1 s2)" 
using a
by (cases rule: One.strong_cases [where a="a" and aa="a"])
   (auto dest: one_abs simp add: lam.inject abs_fresh alpha fresh_prod)

text \<open>first case in Lemma 3.2.4\<close>

lemma one_subst_aux:
  assumes a: "N\<longrightarrow>\<^sub>1N'"
  shows "M[x::=N] \<longrightarrow>\<^sub>1 M[x::=N']"
using a
proof (nominal_induct M avoiding: x N N' rule: lam.strong_induct)
  case (Var y) 
  thus "Var y[x::=N] \<longrightarrow>\<^sub>1 Var y[x::=N']" by (cases "x=y") auto
next
  case (App P Q) (* application case - third line *)
  thus "(App P Q)[x::=N] \<longrightarrow>\<^sub>1  (App P Q)[x::=N']" using o2 by simp
next 
  case (Lam y P) (* abstraction case - fourth line *)
  thus "(Lam [y].P)[x::=N] \<longrightarrow>\<^sub>1 (Lam [y].P)[x::=N']" using o3 by simp
qed

lemma one_subst_aux_automatic:
  assumes a: "N\<longrightarrow>\<^sub>1N'"
  shows "M[x::=N] \<longrightarrow>\<^sub>1 M[x::=N']"
using a
by (nominal_induct M avoiding: x N N' rule: lam.strong_induct)
   (auto simp add: fresh_prod fresh_atm)

lemma one_subst: 
  assumes a: "M\<longrightarrow>\<^sub>1M'"
  and     b: "N\<longrightarrow>\<^sub>1N'"
  shows "M[x::=N]\<longrightarrow>\<^sub>1M'[x::=N']" 
using a b
proof (nominal_induct M M' avoiding: N N' x rule: One.strong_induct)
  case (o1 M)
  thus ?case by (simp add: one_subst_aux)
next
  case (o2 M1 M2 N1 N2)
  thus ?case by simp
next
  case (o3 a M1 M2)
  thus ?case by simp
next
  case (o4 a N1 N2 M1 M2 N N' x)
  have vc: "a\<sharp>N" "a\<sharp>N'" "a\<sharp>x" "a\<sharp>N1" "a\<sharp>N2" by fact+
  have asm: "N\<longrightarrow>\<^sub>1N'" by fact
  show ?case
  proof -
    have "(App (Lam [a].M1) N1)[x::=N] = App (Lam [a].(M1[x::=N])) (N1[x::=N])" using vc by simp
    moreover have "App (Lam [a].(M1[x::=N])) (N1[x::=N]) \<longrightarrow>\<^sub>1 M2[x::=N'][a::=N2[x::=N']]" 
      using o4 asm by (simp add: fresh_fact)
    moreover have "M2[x::=N'][a::=N2[x::=N']] = M2[a::=N2][x::=N']" 
      using vc by (simp add: substitution_lemma fresh_atm)
    ultimately show "(App (Lam [a].M1) N1)[x::=N] \<longrightarrow>\<^sub>1 M2[a::=N2][x::=N']" by simp
  qed
qed

lemma one_subst_automatic: 
  assumes a: "M\<longrightarrow>\<^sub>1M'" 
  and     b: "N\<longrightarrow>\<^sub>1N'"
  shows "M[x::=N]\<longrightarrow>\<^sub>1M'[x::=N']" 
using a b
by (nominal_induct M M' avoiding: N N' x rule: One.strong_induct)
   (auto simp add: one_subst_aux substitution_lemma fresh_atm fresh_fact)

lemma diamond[rule_format]:
  fixes    M :: "lam"
  and      M1:: "lam"
  assumes a: "M\<longrightarrow>\<^sub>1M1" 
  and     b: "M\<longrightarrow>\<^sub>1M2"
  shows "\<exists>M3. M1\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3"
  using a b
proof (nominal_induct avoiding: M1 M2 rule: One.strong_induct)
  case (o1 M) (* case 1 --- M1 = M *)
  thus "\<exists>M3. M\<longrightarrow>\<^sub>1M3 \<and>  M2\<longrightarrow>\<^sub>1M3" by blast
next
  case (o4 x Q Q' P P') (* case 2 --- a beta-reduction occurs*)
  have vc: "x\<sharp>Q" "x\<sharp>Q'" "x\<sharp>M2" by fact+
  have i1: "\<And>M2. Q \<longrightarrow>\<^sub>1M2 \<Longrightarrow> (\<exists>M3. Q'\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3)" by fact
  have i2: "\<And>M2. P \<longrightarrow>\<^sub>1M2 \<Longrightarrow> (\<exists>M3. P'\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3)" by fact
  have "App (Lam [x].P) Q \<longrightarrow>\<^sub>1 M2" by fact
  hence "(\<exists>P' Q'. M2 = App (Lam [x].P') Q' \<and> P\<longrightarrow>\<^sub>1P' \<and> Q\<longrightarrow>\<^sub>1Q') \<or> 
         (\<exists>P' Q'. M2 = P'[x::=Q'] \<and> P\<longrightarrow>\<^sub>1P' \<and> Q\<longrightarrow>\<^sub>1Q')" using vc by (simp add: one_red)
  moreover (* subcase 2.1 *)
  { assume "\<exists>P' Q'. M2 = App (Lam [x].P') Q' \<and> P\<longrightarrow>\<^sub>1P' \<and> Q\<longrightarrow>\<^sub>1Q'"
    then obtain P'' and Q'' where 
      b1: "M2=App (Lam [x].P'') Q''" and b2: "P\<longrightarrow>\<^sub>1P''" and b3: "Q\<longrightarrow>\<^sub>1Q''" by blast
    from b2 i2 have "(\<exists>M3. P'\<longrightarrow>\<^sub>1M3 \<and> P''\<longrightarrow>\<^sub>1M3)" by simp
    then obtain P''' where
      c1: "P'\<longrightarrow>\<^sub>1P'''" and c2: "P''\<longrightarrow>\<^sub>1P'''" by force
    from b3 i1 have "(\<exists>M3. Q'\<longrightarrow>\<^sub>1M3 \<and> Q''\<longrightarrow>\<^sub>1M3)" by simp
    then obtain Q''' where
      d1: "Q'\<longrightarrow>\<^sub>1Q'''" and d2: "Q''\<longrightarrow>\<^sub>1Q'''" by force
    from c1 c2 d1 d2 
    have "P'[x::=Q']\<longrightarrow>\<^sub>1P'''[x::=Q'''] \<and> App (Lam [x].P'') Q'' \<longrightarrow>\<^sub>1 P'''[x::=Q''']" 
      using vc b3 by (auto simp add: one_subst one_fresh_preserv)
    hence "\<exists>M3. P'[x::=Q']\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3" using b1 by blast
  }
  moreover (* subcase 2.2 *)
  { assume "\<exists>P' Q'. M2 = P'[x::=Q'] \<and> P\<longrightarrow>\<^sub>1P' \<and> Q\<longrightarrow>\<^sub>1Q'"
    then obtain P'' Q'' where
      b1: "M2=P''[x::=Q'']" and b2: "P\<longrightarrow>\<^sub>1P''" and  b3: "Q\<longrightarrow>\<^sub>1Q''" by blast
    from b2 i2 have "(\<exists>M3. P'\<longrightarrow>\<^sub>1M3 \<and> P''\<longrightarrow>\<^sub>1M3)" by simp
    then obtain P''' where
      c1: "P'\<longrightarrow>\<^sub>1P'''" and c2: "P''\<longrightarrow>\<^sub>1P'''" by blast
    from b3 i1 have "(\<exists>M3. Q'\<longrightarrow>\<^sub>1M3 \<and> Q''\<longrightarrow>\<^sub>1M3)" by simp
    then obtain Q''' where
      d1: "Q'\<longrightarrow>\<^sub>1Q'''" and d2: "Q''\<longrightarrow>\<^sub>1Q'''" by blast
    from c1 c2 d1 d2 
    have "P'[x::=Q']\<longrightarrow>\<^sub>1P'''[x::=Q'''] \<and> P''[x::=Q'']\<longrightarrow>\<^sub>1P'''[x::=Q''']" 
      by (force simp add: one_subst)
    hence "\<exists>M3. P'[x::=Q']\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3" using b1 by blast
  }
  ultimately show "\<exists>M3. P'[x::=Q']\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3" by blast
next
  case (o2 P P' Q Q') (* case 3 *)
  have i0: "P\<longrightarrow>\<^sub>1P'" by fact
  have i0': "Q\<longrightarrow>\<^sub>1Q'" by fact
  have i1: "\<And>M2. Q \<longrightarrow>\<^sub>1M2 \<Longrightarrow> (\<exists>M3. Q'\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3)" by fact
  have i2: "\<And>M2. P \<longrightarrow>\<^sub>1M2 \<Longrightarrow> (\<exists>M3. P'\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3)" by fact
  assume "App P Q \<longrightarrow>\<^sub>1 M2"
  hence "(\<exists>P'' Q''. M2 = App P'' Q'' \<and> P\<longrightarrow>\<^sub>1P'' \<and> Q\<longrightarrow>\<^sub>1Q'') \<or> 
         (\<exists>x P' P'' Q'. P = Lam [x].P' \<and> M2 = P''[x::=Q'] \<and> P'\<longrightarrow>\<^sub>1 P'' \<and> Q\<longrightarrow>\<^sub>1Q' \<and> x\<sharp>(Q,Q'))" 
    by (simp add: one_app[simplified])
  moreover (* subcase 3.1 *)
  { assume "\<exists>P'' Q''. M2 = App P'' Q'' \<and> P\<longrightarrow>\<^sub>1P'' \<and> Q\<longrightarrow>\<^sub>1Q''"
    then obtain P'' and Q'' where 
      b1: "M2=App P'' Q''" and b2: "P\<longrightarrow>\<^sub>1P''" and b3: "Q\<longrightarrow>\<^sub>1Q''" by blast
    from b2 i2 have "(\<exists>M3. P'\<longrightarrow>\<^sub>1M3 \<and> P''\<longrightarrow>\<^sub>1M3)" by simp
    then obtain P''' where
      c1: "P'\<longrightarrow>\<^sub>1P'''" and c2: "P''\<longrightarrow>\<^sub>1P'''" by blast
    from b3 i1 have "\<exists>M3. Q'\<longrightarrow>\<^sub>1M3 \<and> Q''\<longrightarrow>\<^sub>1M3" by simp
    then obtain Q''' where
      d1: "Q'\<longrightarrow>\<^sub>1Q'''" and d2: "Q''\<longrightarrow>\<^sub>1Q'''" by blast
    from c1 c2 d1 d2 
    have "App P' Q'\<longrightarrow>\<^sub>1App P''' Q''' \<and> App P'' Q'' \<longrightarrow>\<^sub>1 App P''' Q'''" by blast
    hence "\<exists>M3. App P' Q'\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3" using b1 by blast
  }
  moreover (* subcase 3.2 *)
  { assume "\<exists>x P1 P'' Q''. P = Lam [x].P1 \<and> M2 = P''[x::=Q''] \<and> P1\<longrightarrow>\<^sub>1 P'' \<and> Q\<longrightarrow>\<^sub>1Q'' \<and> x\<sharp>(Q,Q'')"
    then obtain x P1 P1'' Q'' where
      b0: "P = Lam [x].P1" and b1: "M2 = P1''[x::=Q'']" and 
      b2: "P1\<longrightarrow>\<^sub>1P1''" and  b3: "Q\<longrightarrow>\<^sub>1Q''" and vc: "x\<sharp>(Q,Q'')" by blast
    from b0 i0 have "\<exists>P1'. P'=Lam [x].P1' \<and> P1\<longrightarrow>\<^sub>1P1'" by (simp add: one_abs)      
    then obtain P1' where g1: "P'=Lam [x].P1'" and g2: "P1\<longrightarrow>\<^sub>1P1'" by blast 
    from g1 b0 b2 i2 have "(\<exists>M3. (Lam [x].P1')\<longrightarrow>\<^sub>1M3 \<and> (Lam [x].P1'')\<longrightarrow>\<^sub>1M3)" by simp
    then obtain P1''' where
      c1: "(Lam [x].P1')\<longrightarrow>\<^sub>1P1'''" and c2: "(Lam [x].P1'')\<longrightarrow>\<^sub>1P1'''" by blast
    from c1 have "\<exists>R1. P1'''=Lam [x].R1 \<and> P1'\<longrightarrow>\<^sub>1R1" by (simp add: one_abs)
    then obtain R1 where r1: "P1'''=Lam [x].R1" and r2: "P1'\<longrightarrow>\<^sub>1R1" by blast
    from c2 have "\<exists>R2. P1'''=Lam [x].R2 \<and> P1''\<longrightarrow>\<^sub>1R2" by (simp add: one_abs)
    then obtain R2 where r3: "P1'''=Lam [x].R2" and r4: "P1''\<longrightarrow>\<^sub>1R2" by blast
    from r1 r3 have r5: "R1=R2" by (simp add: lam.inject alpha)
    from b3 i1 have "(\<exists>M3. Q'\<longrightarrow>\<^sub>1M3 \<and> Q''\<longrightarrow>\<^sub>1M3)" by simp
    then obtain Q''' where
      d1: "Q'\<longrightarrow>\<^sub>1Q'''" and d2: "Q''\<longrightarrow>\<^sub>1Q'''" by blast
    from g1 r2 d1 r4 r5 d2 
    have "App P' Q'\<longrightarrow>\<^sub>1R1[x::=Q'''] \<and> P1''[x::=Q'']\<longrightarrow>\<^sub>1R1[x::=Q''']" 
      using vc i0' by (simp add: one_subst one_fresh_preserv)
    hence "\<exists>M3. App P' Q'\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3" using b1 by blast
  }
  ultimately show "\<exists>M3. App P' Q'\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3" by blast
next
  case (o3 P P' x) (* case 4 *)
  have i1: "P\<longrightarrow>\<^sub>1P'" by fact
  have i2: "\<And>M2. P \<longrightarrow>\<^sub>1M2 \<Longrightarrow> (\<exists>M3. P'\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3)" by fact
  have "(Lam [x].P)\<longrightarrow>\<^sub>1 M2" by fact
  hence "\<exists>P''. M2=Lam [x].P'' \<and> P\<longrightarrow>\<^sub>1P''" by (simp add: one_abs)
  then obtain P'' where b1: "M2=Lam [x].P''" and b2: "P\<longrightarrow>\<^sub>1P''" by blast
  from i2 b1 b2 have "\<exists>M3. (Lam [x].P')\<longrightarrow>\<^sub>1M3 \<and> (Lam [x].P'')\<longrightarrow>\<^sub>1M3" by blast
  then obtain M3 where c1: "(Lam [x].P')\<longrightarrow>\<^sub>1M3" and c2: "(Lam [x].P'')\<longrightarrow>\<^sub>1M3" by blast
  from c1 have "\<exists>R1. M3=Lam [x].R1 \<and> P'\<longrightarrow>\<^sub>1R1" by (simp add: one_abs)
  then obtain R1 where r1: "M3=Lam [x].R1" and r2: "P'\<longrightarrow>\<^sub>1R1" by blast
  from c2 have "\<exists>R2. M3=Lam [x].R2 \<and> P''\<longrightarrow>\<^sub>1R2" by (simp add: one_abs)
  then obtain R2 where r3: "M3=Lam [x].R2" and r4: "P''\<longrightarrow>\<^sub>1R2" by blast
  from r1 r3 have r5: "R1=R2" by (simp add: lam.inject alpha)
  from r2 r4 have "(Lam [x].P')\<longrightarrow>\<^sub>1(Lam [x].R1) \<and> (Lam [x].P'')\<longrightarrow>\<^sub>1(Lam [x].R2)" 
    by (simp add: one_subst)
  thus "\<exists>M3. (Lam [x].P')\<longrightarrow>\<^sub>1M3 \<and> M2\<longrightarrow>\<^sub>1M3" using b1 r5 by blast
qed

lemma one_lam_cong: 
  assumes a: "t1\<longrightarrow>\<^sub>\<beta>\<^sup>*t2" 
  shows "(Lam [a].t1)\<longrightarrow>\<^sub>\<beta>\<^sup>*(Lam [a].t2)"
  using a
proof induct
  case bs1 thus ?case by simp
next
  case (bs2 y z) 
  thus ?case by (blast dest: b3)
qed

lemma one_app_congL: 
  assumes a: "t1\<longrightarrow>\<^sub>\<beta>\<^sup>*t2" 
  shows "App t1 s\<longrightarrow>\<^sub>\<beta>\<^sup>* App t2 s"
  using a
proof induct
  case bs1 thus ?case by simp
next
  case bs2 thus ?case by (blast dest: b1)
qed
  
lemma one_app_congR: 
  assumes a: "t1\<longrightarrow>\<^sub>\<beta>\<^sup>*t2" 
  shows "App s t1 \<longrightarrow>\<^sub>\<beta>\<^sup>* App s t2"
using a
proof induct
  case bs1 thus ?case by simp
next 
  case bs2 thus ?case by (blast dest: b2)
qed

lemma one_app_cong: 
  assumes a1: "t1\<longrightarrow>\<^sub>\<beta>\<^sup>*t2" 
  and     a2: "s1\<longrightarrow>\<^sub>\<beta>\<^sup>*s2" 
  shows "App t1 s1\<longrightarrow>\<^sub>\<beta>\<^sup>* App t2 s2"
proof -
  have "App t1 s1 \<longrightarrow>\<^sub>\<beta>\<^sup>* App t2 s1" using a1 by (rule one_app_congL)
  moreover
  have "App t2 s1 \<longrightarrow>\<^sub>\<beta>\<^sup>* App t2 s2" using a2 by (rule one_app_congR)
  ultimately show ?thesis by (rule beta_star_trans)
qed

lemma one_beta_star: 
  assumes a: "(t1\<longrightarrow>\<^sub>1t2)" 
  shows "(t1\<longrightarrow>\<^sub>\<beta>\<^sup>*t2)"
  using a
proof(nominal_induct rule: One.strong_induct)
  case o1 thus ?case by simp
next
  case o2 thus ?case by (blast intro!: one_app_cong)
next
  case o3 thus ?case by (blast intro!: one_lam_cong)
next 
  case (o4 a s1 s2 t1 t2)
  have vc: "a\<sharp>s1" "a\<sharp>s2" by fact+
  have a1: "t1\<longrightarrow>\<^sub>\<beta>\<^sup>*t2" and a2: "s1\<longrightarrow>\<^sub>\<beta>\<^sup>*s2" by fact+
  have c1: "(App (Lam [a].t2) s2) \<longrightarrow>\<^sub>\<beta> (t2 [a::= s2])" using vc by (simp add: b4)
  from a1 a2 have c2: "App (Lam [a].t1 ) s1 \<longrightarrow>\<^sub>\<beta>\<^sup>* App (Lam [a].t2 ) s2" 
    by (blast intro!: one_app_cong one_lam_cong)
  show ?case using c2 c1 by (blast intro: beta_star_trans)
qed
 
lemma one_star_lam_cong: 
  assumes a: "t1\<longrightarrow>\<^sub>1\<^sup>*t2" 
  shows "(Lam  [a].t1)\<longrightarrow>\<^sub>1\<^sup>* (Lam [a].t2)"
  using a
proof induct
  case os1 thus ?case by simp
next
  case os2 thus ?case by (blast intro: one_star_trans)
qed

lemma one_star_app_congL: 
  assumes a: "t1\<longrightarrow>\<^sub>1\<^sup>*t2" 
  shows "App t1 s\<longrightarrow>\<^sub>1\<^sup>* App t2 s"
  using a
proof induct
  case os1 thus ?case by simp
next
  case os2 thus ?case by (blast intro: one_star_trans)
qed

lemma one_star_app_congR: 
  assumes a: "t1\<longrightarrow>\<^sub>1\<^sup>*t2" 
  shows "App s t1 \<longrightarrow>\<^sub>1\<^sup>* App s t2"
  using a
proof induct
  case os1 thus ?case by simp
next
  case os2 thus ?case by (blast intro: one_star_trans)
qed

lemma beta_one_star: 
  assumes a: "t1\<longrightarrow>\<^sub>\<beta>t2" 
  shows "t1\<longrightarrow>\<^sub>1\<^sup>*t2"
  using a
proof(induct)
  case b1 thus ?case by (blast intro!: one_star_app_congL)
next
  case b2 thus ?case by (blast intro!: one_star_app_congR)
next
  case b3 thus ?case by (blast intro!: one_star_lam_cong)
next
  case b4 thus ?case by auto 
qed

lemma trans_closure: 
  shows "(M1\<longrightarrow>\<^sub>1\<^sup>*M2) = (M1\<longrightarrow>\<^sub>\<beta>\<^sup>*M2)"
proof
  assume "M1 \<longrightarrow>\<^sub>1\<^sup>* M2"
  then show "M1\<longrightarrow>\<^sub>\<beta>\<^sup>*M2"
  proof induct
    case (os1 M1) thus "M1\<longrightarrow>\<^sub>\<beta>\<^sup>*M1" by simp
  next
    case (os2 M1 M2 M3)
    have "M2\<longrightarrow>\<^sub>1M3" by fact
    then have "M2\<longrightarrow>\<^sub>\<beta>\<^sup>*M3" by (rule one_beta_star)
    moreover have "M1\<longrightarrow>\<^sub>\<beta>\<^sup>*M2" by fact
    ultimately show "M1\<longrightarrow>\<^sub>\<beta>\<^sup>*M3" by (auto intro: beta_star_trans)
  qed
next
  assume "M1 \<longrightarrow>\<^sub>\<beta>\<^sup>* M2" 
  then show "M1\<longrightarrow>\<^sub>1\<^sup>*M2"
  proof induct
    case (bs1 M1) thus  "M1\<longrightarrow>\<^sub>1\<^sup>*M1" by simp
  next
    case (bs2 M1 M2 M3) 
    have "M2\<longrightarrow>\<^sub>\<beta>M3" by fact
    then have "M2\<longrightarrow>\<^sub>1\<^sup>*M3" by (rule beta_one_star)
    moreover have "M1\<longrightarrow>\<^sub>1\<^sup>*M2" by fact
    ultimately show "M1\<longrightarrow>\<^sub>1\<^sup>*M3" by (auto intro: one_star_trans)
  qed
qed

lemma cr_one:
  assumes a: "t\<longrightarrow>\<^sub>1\<^sup>*t1" 
  and     b: "t\<longrightarrow>\<^sub>1t2"
  shows "\<exists>t3. t1\<longrightarrow>\<^sub>1t3 \<and> t2\<longrightarrow>\<^sub>1\<^sup>*t3"
  using a b
proof (induct arbitrary: t2)
  case os1 thus ?case by force
next
  case (os2 t s1 s2 t2)  
  have b: "s1 \<longrightarrow>\<^sub>1 s2" by fact
  have h: "\<And>t2. t \<longrightarrow>\<^sub>1 t2 \<Longrightarrow> (\<exists>t3. s1 \<longrightarrow>\<^sub>1 t3 \<and> t2 \<longrightarrow>\<^sub>1\<^sup>* t3)" by fact
  have c: "t \<longrightarrow>\<^sub>1 t2" by fact
  show "\<exists>t3. s2 \<longrightarrow>\<^sub>1 t3 \<and>  t2 \<longrightarrow>\<^sub>1\<^sup>* t3" 
  proof -
    from c h have "\<exists>t3. s1 \<longrightarrow>\<^sub>1 t3 \<and> t2 \<longrightarrow>\<^sub>1\<^sup>* t3" by blast
    then obtain t3 where c1: "s1 \<longrightarrow>\<^sub>1 t3" and c2: "t2 \<longrightarrow>\<^sub>1\<^sup>* t3" by blast
    have "\<exists>t4. s2 \<longrightarrow>\<^sub>1 t4 \<and> t3 \<longrightarrow>\<^sub>1 t4" using b c1 by (blast intro: diamond)
    thus ?thesis using c2 by (blast intro: one_star_trans)
  qed
qed

lemma cr_one_star: 
  assumes a: "t\<longrightarrow>\<^sub>1\<^sup>*t2"
      and b: "t\<longrightarrow>\<^sub>1\<^sup>*t1"
    shows "\<exists>t3. t1\<longrightarrow>\<^sub>1\<^sup>*t3\<and>t2\<longrightarrow>\<^sub>1\<^sup>*t3"
using a b
proof (induct arbitrary: t1)
  case (os1 t) then show ?case by force
next 
  case (os2 t s1 s2 t1)
  have c: "t \<longrightarrow>\<^sub>1\<^sup>* s1" by fact
  have c': "t \<longrightarrow>\<^sub>1\<^sup>* t1" by fact
  have d: "s1 \<longrightarrow>\<^sub>1 s2" by fact
  have "t \<longrightarrow>\<^sub>1\<^sup>* t1 \<Longrightarrow> (\<exists>t3.  t1 \<longrightarrow>\<^sub>1\<^sup>* t3 \<and> s1 \<longrightarrow>\<^sub>1\<^sup>* t3)" by fact
  then obtain t3 where f1: "t1 \<longrightarrow>\<^sub>1\<^sup>* t3"
                   and f2: "s1 \<longrightarrow>\<^sub>1\<^sup>* t3" using c' by blast
  from cr_one d f2 have "\<exists>t4. t3\<longrightarrow>\<^sub>1t4 \<and> s2\<longrightarrow>\<^sub>1\<^sup>*t4" by blast
  then obtain t4 where g1: "t3\<longrightarrow>\<^sub>1t4"
                   and g2: "s2\<longrightarrow>\<^sub>1\<^sup>*t4" by blast
  have "t1\<longrightarrow>\<^sub>1\<^sup>*t4" using f1 g1 by (blast intro: one_star_trans)
  thus ?case using g2 by blast
qed
  
lemma cr_beta_star: 
  assumes a1: "t\<longrightarrow>\<^sub>\<beta>\<^sup>*t1" 
  and     a2: "t\<longrightarrow>\<^sub>\<beta>\<^sup>*t2" 
  shows "\<exists>t3. t1\<longrightarrow>\<^sub>\<beta>\<^sup>*t3\<and>t2\<longrightarrow>\<^sub>\<beta>\<^sup>*t3"
proof -
  from a1 have "t\<longrightarrow>\<^sub>1\<^sup>*t1" by (simp only: trans_closure)
  moreover
  from a2 have "t\<longrightarrow>\<^sub>1\<^sup>*t2" by (simp only: trans_closure)
  ultimately have "\<exists>t3. t1\<longrightarrow>\<^sub>1\<^sup>*t3 \<and> t2\<longrightarrow>\<^sub>1\<^sup>*t3" by (blast intro: cr_one_star) 
  then obtain t3 where "t1\<longrightarrow>\<^sub>1\<^sup>*t3" and "t2\<longrightarrow>\<^sub>1\<^sup>*t3" by blast
  hence "t1\<longrightarrow>\<^sub>\<beta>\<^sup>*t3" and "t2\<longrightarrow>\<^sub>\<beta>\<^sup>*t3" by (simp_all only: trans_closure)
  then show "\<exists>t3. t1\<longrightarrow>\<^sub>\<beta>\<^sup>*t3\<and>t2\<longrightarrow>\<^sub>\<beta>\<^sup>*t3" by blast
qed

end

