
theory cr
imports lam_substs
begin

lemma forget[rule_format]: 
  shows "a\<sharp>t1 \<longrightarrow> t1[a::=t2] = t1"
proof (nominal_induct t1 rule: lam_induct)
  case (Var a t2 b) 
  show ?case by (simp, simp add: fresh_atm)
next 
  case App
  thus ?case by (simp add: fresh_prod)
next
  case (Lam a t2 c t)
  have i: "\<forall>a b. a\<sharp>t \<longrightarrow>  t[a::=b] = t" by fact
  have "c\<sharp>(a,t2)" by fact
  hence a: "a\<noteq>c" and b: "c\<sharp>t2" by (auto simp add: fresh_prod fresh_atm)
  show ?case
  proof 
    assume "a\<sharp>Lam [c].t" 
    hence "a\<sharp>t" using a by (force simp add: abs_fresh)
    hence "t[a::=t2] = t" using i by simp
    thus "(Lam [c].t)[a::=t2] = Lam [c].t" using a b by (simp add: alpha)
  qed
qed

lemma forget[rule_format]: 
  shows "a\<sharp>t1 \<longrightarrow> t1[a::=t2] = t1"
apply (nominal_induct t1 rule: lam_induct)
apply(auto simp add: abs_fresh fresh_atm fresh_prod)
done

lemma fresh_fact[rule_format]: 
  fixes   b :: "name"
  and    a  :: "name"
  and    t1 :: "lam"
  and    t2 :: "lam" 
  shows "a\<sharp>t1\<longrightarrow>a\<sharp>t2\<longrightarrow>a\<sharp>(t1[b::=t2])"
proof (nominal_induct t1 rule: lam_induct)
  case (Var a b t2 c) 
  show ?case by (simp)
next
  case App 
  thus ?case by (simp add: fresh_prod)
next
  case (Lam a b t2 c t)
  have  i: "\<forall>(a::name) b t2. a\<sharp>t\<longrightarrow>a\<sharp>t2\<longrightarrow>a\<sharp>(t[b::=t2])" by fact
  have "c\<sharp>(a,b,t2)" by fact
  hence b: "c\<noteq>a \<and> c\<noteq>b \<and> c\<sharp>t2" by (simp add: fresh_prod fresh_atm) 
  show ?case 
  proof (intro strip)
    assume a1: "a\<sharp>t2"
    assume a2: "a\<sharp>Lam [c].t"
    hence "a\<sharp>t" using b by (force simp add: abs_fresh)
    hence "a\<sharp>t[b::=t2]" using a1 i by simp
    thus "a\<sharp>(Lam [c].t)[b::=t2]" using b by (simp add: abs_fresh)
  qed
qed

lemma fresh_fact[rule_format]: 
  fixes   b :: "name"
  and    a  :: "name"
  and    t1 :: "lam"
  and    t2 :: "lam" 
  shows "a\<sharp>t1\<longrightarrow>a\<sharp>t2\<longrightarrow>a\<sharp>(t1[b::=t2])"
apply(nominal_induct t1 rule: lam_induct)
apply(auto simp add: abs_fresh fresh_prod fresh_atm)
done

lemma subs_lemma:  
  fixes x::"name"
  and   y::"name"
  and   L::"lam"
  and   M::"lam"
  and   N::"lam"
  shows "x\<noteq>y\<longrightarrow>x\<sharp>L\<longrightarrow>M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
proof (nominal_induct M rule: lam_induct)
  case (Var L N x y z) (* case 1: Variables*)
  show ?case
  proof (intro strip)
    assume a1: "x\<noteq>y"
    and    a2: "x\<sharp>L"
    show "Var z[x::=N][y::=L] = Var z[y::=L][x::=N[y::=L]]" (is "?LHS = ?RHS")
    proof -
      have "z=x \<or> (z\<noteq>x \<and> z=y) \<or> (z\<noteq>x \<and> z\<noteq>y)" by force 
      moreover (*Case 1.1*)
      { assume c1: "z=x"
	have c1l: "?LHS = N[y::=L]"    using c1    by simp
	have c1r: "?RHS = N[y::=L]"    using c1 a1 by simp
	from c1l and c1r have "?LHS = ?RHS"  by simp
      }
      moreover (*Case 1.2*)
      { assume c2: "z\<noteq>x \<and> z=y"
	have c2l: "?LHS = L"               using c2 by force
	have c2r: "?RHS = L[x::=N[y::=L]]" using c2 by force
	have c2x: "L[x::=N[y::=L]] = L"    using a2 by (simp add: forget)
	from c2l and c2r and c2x have "?LHS = ?RHS" by simp
      }
      moreover (*Case 1.3*)
      { assume c3: "z\<noteq>x \<and> z\<noteq>y"
	have c3l: "?LHS = Var z" using c3 by force
	have c3r: "?RHS = Var z" using c3 by force
	from c3l and c3r have "?LHS = ?RHS" by simp
      }
      ultimately show "?LHS = ?RHS" by blast
    qed
  qed
next
  case (Lam L N x y z M1) (* case 2: lambdas *)
  assume f1: "z\<sharp>(L,N,x,y)"
  from f1 have f2: "z \<sharp> N[y::=L]" by (simp add: fresh_fact fresh_prod)
  show ?case
  proof (intro strip)
    assume  a1: "x\<noteq>y"
    and     a2: "x\<sharp>L"
    show "(Lam [z].M1)[x::=N][y::=L] = (Lam [z].M1)[y::=L][x::=N[y::=L]]" (is "?LHS=?RHS") 
    proof -
      have "?LHS = Lam [z].(M1[x::=N][y::=L])"             using f1 
	by (simp add: fresh_prod fresh_atm)
      also have "\<dots> = Lam [z].(M1[y::=L][x::=N[y::=L]])"   using a1 a2 Lam(2)  by simp
      also have "\<dots> = (Lam [z].(M1[y::=L]))[x::=N[y::=L]]" using f1 f2 
	by (simp add: fresh_prod fresh_atm)
      also have "\<dots> = ?RHS" using f1 by (simp add: fresh_prod fresh_atm)
      finally show "?LHS = ?RHS" .
    qed
  qed
next
  case (App L N x y M1 M2) (* case 3: applications *)
  show ?case
  proof (intro strip)
    assume a1: "x\<noteq>y"
    and    a2: "x\<sharp>L"
    from a1 a2 App show "(App M1 M2)[x::=N][y::=L] = (App M1 M2)[y::=L][x::=N[y::=L]]" by simp
  qed
qed

lemma subs_lemma: 
  fixes x::"name"
  and   y::"name"
  and   L::"lam"
  and   M::"lam"
  and   N::"lam"
  shows "x\<noteq>y\<longrightarrow>x\<sharp>L\<longrightarrow>M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
proof (nominal_induct M rule: lam_induct)
  case (Var L N x y z) (* case 1: Variables*)
  show ?case
  proof -
    have "z=x \<or> (z\<noteq>x \<and> z=y) \<or> (z\<noteq>x \<and> z\<noteq>y)" by force
    thus "x\<noteq>y\<longrightarrow>x\<sharp>L\<longrightarrow>Var z[x::=N][y::=L] = Var z[y::=L][x::=N[y::=L]]" 
    using forget by force
  qed
next
  case (Lam L N x y z M1) (* case 2: lambdas *)
  assume f1: "z\<sharp>(L,N,x,y)" 
  hence f2: "z\<sharp>N[y::=L]" by (simp add: fresh_fact fresh_prod)
  show ?case
  proof (intro strip)
    assume a1: "x\<noteq>y"
    and    a2: "x\<sharp>L"
    show "(Lam [z].M1)[x::=N][y::=L] = (Lam [z].M1)[y::=L][x::=N[y::=L]]" (is "?LHS=?RHS") 
    proof -
      have "?LHS = Lam [z].(M1[x::=N][y::=L])" using f1 by (simp add: fresh_prod fresh_atm)
      also have "\<dots> = Lam [z].(M1[y::=L][x::=N[y::=L]])"   using a1 a2 Lam(2)  by simp
      also have "\<dots> = ?RHS" using f1 f2 by (simp add: fresh_prod fresh_atm)
      finally show "?LHS = ?RHS" .
    qed
  qed
next
  case (App L N x y M1 M2) (* case 3: applications *)
  thus "x\<noteq>y\<longrightarrow>x\<sharp>L\<longrightarrow>(App M1 M2)[x::=N][y::=L] = (App M1 M2)[y::=L][x::=N[y::=L]]" by simp
qed

lemma subs_lemma:  
  fixes x::"name"
  and   y::"name"
  and   L::"lam"
  and   M::"lam"
  and   N::"lam"
  shows "x\<noteq>y\<longrightarrow>x\<sharp>L\<longrightarrow>M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
apply(nominal_induct M rule: lam_induct)
apply(auto simp add: fresh_fact forget fresh_prod fresh_atm)
done

lemma subst_rename[rule_format]: 
  fixes  c  :: "name"
  and    a  :: "name"
  and    t1 :: "lam"
  and    t2 :: "lam"
  shows "c\<sharp>t1 \<longrightarrow> (t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2])"
proof (nominal_induct t1 rule: lam_induct)
  case (Var a c t2 b)
  show "c\<sharp>(Var b) \<longrightarrow> (Var b)[a::=t2] = ([(c,a)]\<bullet>(Var b))[c::=t2]" by (simp add: calc_atm fresh_atm)
next
  case App thus ?case by (force simp add: fresh_prod)
next
  case (Lam a c t2 b s)
  have i: "\<forall>a c t2. c\<sharp>s \<longrightarrow> (s[a::=t2] = ([(c,a)]\<bullet>s)[c::=t2])" by fact
  have f: "b\<sharp>(a,c,t2)" by fact
  from f have a:"b\<noteq>c" and b: "b\<noteq>a" and c: "b\<sharp>t2" by (simp add: fresh_prod fresh_atm)+
  show "c\<sharp>Lam [b].s \<longrightarrow> (Lam [b].s)[a::=t2] = ([(c,a)]\<bullet>(Lam [b].s))[c::=t2]" (is "_ \<longrightarrow> ?LHS = ?RHS")
  proof
    assume "c\<sharp>Lam [b].s"
    hence "c\<sharp>s" using a by (force simp add: abs_fresh)
    hence d: "s[a::=t2] = ([(c,a)]\<bullet>s)[c::=t2]" using i by simp
    have    "?LHS = Lam [b].(s[a::=t2])" using b c by simp
    also have "\<dots> = Lam [b].(([(c,a)]\<bullet>s)[c::=t2])" using d by simp
    also have "\<dots> = (Lam [b].([(c,a)]\<bullet>s))[c::=t2]" using a c by simp
    also have "\<dots> = ?RHS" using a b by (force simp add: calc_atm)
    finally show "?LHS = ?RHS" by simp
  qed
qed

lemma subst_rename[rule_format]: 
  fixes  c  :: "name"
  and    a  :: "name"
  and    t1 :: "lam"
  and    t2 :: "lam"
  shows "c\<sharp>t1 \<longrightarrow> (t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2])"
apply(nominal_induct t1 rule: lam_induct)
apply(auto simp add: calc_atm fresh_atm fresh_prod abs_fresh)
done

section {* Beta Reduction *}

consts
  Beta :: "(lam\<times>lam) set"
syntax 
  "_Beta"       :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>\<beta> _" [80,80] 80)
  "_Beta_star"  :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>\<beta>\<^sup>* _" [80,80] 80)
translations 
  "t1 \<longrightarrow>\<^isub>\<beta> t2" \<rightleftharpoons> "(t1,t2) \<in> Beta"
  "t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* t2" \<rightleftharpoons> "(t1,t2) \<in> Beta\<^sup>*"
inductive Beta
  intros
  b1[intro!]: "s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (App s1 t)\<longrightarrow>\<^isub>\<beta>(App s2 t)"
  b2[intro!]: "s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (App t s1)\<longrightarrow>\<^isub>\<beta>(App t s2)"
  b3[intro!]: "s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (Lam [a].s1)\<longrightarrow>\<^isub>\<beta> (Lam [(a::name)].s2)"
  b4[intro!]: "(App (Lam [(a::name)].s1) s2)\<longrightarrow>\<^isub>\<beta>(s1[a::=s2])"

lemma eqvt_beta: 
  fixes pi :: "name prm"
  and   t  :: "lam"
  and   s  :: "lam"
  shows "t\<longrightarrow>\<^isub>\<beta>s \<Longrightarrow> (pi\<bullet>t)\<longrightarrow>\<^isub>\<beta>(pi\<bullet>s)"
  apply(erule Beta.induct)
  apply(auto)
  done

lemma beta_induct_aux[rule_format]:
  fixes  P :: "lam \<Rightarrow> lam \<Rightarrow>'a::fs_name\<Rightarrow>bool"
  and    t :: "lam"
  and    s :: "lam"
  assumes a: "t\<longrightarrow>\<^isub>\<beta>s"
  and a1:    "\<And>x t s1 s2. 
              s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (\<forall>z. P s1 s2 z) \<Longrightarrow> P (App s1 t) (App s2 t) x"
  and a2:    "\<And>x t s1 s2. 
              s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (\<forall>z. P s1 s2 z) \<Longrightarrow> P (App t s1) (App t s2) x"
  and a3:    "\<And>x (a::name) s1 s2. 
              a\<sharp>x \<Longrightarrow> s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (\<forall>z. P s1 s2 z) \<Longrightarrow> P (Lam [a].s1) (Lam [a].s2) x"
  and a4:    "\<And>x (a::name) t1 s1. a\<sharp>(s1,x) \<Longrightarrow> P (App (Lam [a].t1) s1) (t1[a::=s1]) x"
  shows "\<forall>x (pi::name prm). P (pi\<bullet>t) (pi\<bullet>s) x"
using a
proof (induct)
  case b1 thus ?case using a1 by (simp, blast intro: eqvt_beta)
next
  case b2 thus ?case using a2 by (simp, blast intro: eqvt_beta)
next
  case (b3 a s1 s2)
  assume j1: "s1 \<longrightarrow>\<^isub>\<beta> s2"
  assume j2: "\<forall>x (pi::name prm). P (pi\<bullet>s1) (pi\<bullet>s2) x"
  show ?case 
  proof (simp, intro strip)
    fix pi::"name prm" and x::"'a::fs_name"
     have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>s1,pi\<bullet>s2,x)"
      by (rule at_exists_fresh[OF at_name_inst], simp add: fs_name1)
    then obtain c::"name" 
      where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>x" and f3: "c\<sharp>(pi\<bullet>s1)" and f4: "c\<sharp>(pi\<bullet>s2)"
      by (force simp add: fresh_prod fresh_atm)
    have x: "P (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>s1)) (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>s2)) x"
      using a3 f2 j1 j2 by (simp, blast intro: eqvt_beta)
    have alpha1: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>s1))) = (Lam [(pi\<bullet>a)].(pi\<bullet>s1))" using f1 f3
      by (simp add: lam.inject alpha)
    have alpha2: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>s2))) = (Lam [(pi\<bullet>a)].(pi\<bullet>s2))" using f1 f3
      by (simp add: lam.inject alpha)
    show " P (Lam [(pi\<bullet>a)].(pi\<bullet>s1)) (Lam [(pi\<bullet>a)].(pi\<bullet>s2)) x"
      using x alpha1 alpha2 by (simp only: pt_name2)
  qed
next
  case (b4 a s1 s2)
  show ?case
  proof (simp add: subst_eqvt, intro strip)
    fix pi::"name prm" and x::"'a::fs_name" 
    have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>s1,pi\<bullet>s2,x)"
      by (rule at_exists_fresh[OF at_name_inst], simp add: fs_name1)
    then obtain c::"name" 
      where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>(pi\<bullet>s2,x)" and f3: "c\<sharp>(pi\<bullet>s1)" and f4: "c\<sharp>(pi\<bullet>s2)"
      by (force simp add: fresh_prod fresh_atm)
    have x: "P (App (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>s1)) (pi\<bullet>s2)) ((([(c,pi\<bullet>a)]@pi)\<bullet>s1)[c::=(pi\<bullet>s2)]) x"
      using a4 f2 by (blast intro!: eqvt_beta)
    have alpha1: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>s1))) = (Lam [(pi\<bullet>a)].(pi\<bullet>s1))" using f1 f3
      by (simp add: lam.inject alpha)
    have alpha2: "(([(c,pi\<bullet>a)]@pi)\<bullet>s1)[c::=(pi\<bullet>s2)] = (pi\<bullet>s1)[(pi\<bullet>a)::=(pi\<bullet>s2)]"
      using f3 by (simp only: subst_rename[symmetric] pt_name2)
    show "P (App (Lam [(pi\<bullet>a)].(pi\<bullet>s1)) (pi\<bullet>s2)) ((pi\<bullet>s1)[(pi\<bullet>a)::=(pi\<bullet>s2)]) x"
      using x alpha1 alpha2 by (simp only: pt_name2)
  qed
qed


lemma beta_induct[case_names b1 b2 b3 b4]:
  fixes  P :: "lam \<Rightarrow> lam \<Rightarrow>'a::fs_name\<Rightarrow>bool"
  and    t :: "lam"
  and    s :: "lam"
  and    x :: "'a::fs_name"
  assumes a: "t\<longrightarrow>\<^isub>\<beta>s"
  and a1:    "\<And>x t s1 s2. 
              s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (\<forall>z. P s1 s2 z) \<Longrightarrow> P (App s1 t) (App s2 t) x"
  and a2:    "\<And>x t s1 s2. 
              s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (\<forall>z. P s1 s2 z) \<Longrightarrow> P (App t s1) (App t s2) x"
  and a3:    "\<And>x (a::name) s1 s2. 
              a\<sharp>x \<Longrightarrow> s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (\<forall>z. P s1 s2 z) \<Longrightarrow> P (Lam [a].s1) (Lam [a].s2) x"
  and a4:    "\<And>x (a::name) t1 s1. 
              a\<sharp>(s1,x) \<Longrightarrow> P (App (Lam [a].t1) s1) (t1[a::=s1]) x"
  shows "P t s x"
using a a1 a2 a3 a4
by (auto intro!: beta_induct_aux[of "t" "s" "P" "[]" "x", simplified])

section {* One-Reduction *}

consts
  One :: "(lam\<times>lam) set"
syntax 
  "_One"       :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>1 _" [80,80] 80)
  "_One_star"  :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>1\<^sup>* _" [80,80] 80)
translations 
  "t1 \<longrightarrow>\<^isub>1 t2" \<rightleftharpoons> "(t1,t2) \<in> One"
  "t1 \<longrightarrow>\<^isub>1\<^sup>* t2" \<rightleftharpoons> "(t1,t2) \<in> One\<^sup>*"
inductive One
  intros
  o1[intro!]:      "M\<longrightarrow>\<^isub>1M"
  o2[simp,intro!]: "\<lbrakk>t1\<longrightarrow>\<^isub>1t2;s1\<longrightarrow>\<^isub>1s2\<rbrakk> \<Longrightarrow> (App t1 s1)\<longrightarrow>\<^isub>1(App t2 s2)"
  o3[simp,intro!]: "s1\<longrightarrow>\<^isub>1s2 \<Longrightarrow> (Lam [(a::name)].s1)\<longrightarrow>\<^isub>1(Lam [a].s2)"
  o4[simp,intro!]: "\<lbrakk>s1\<longrightarrow>\<^isub>1s2;t1\<longrightarrow>\<^isub>1t2\<rbrakk> \<Longrightarrow> (App (Lam [(a::name)].t1) s1)\<longrightarrow>\<^isub>1(t2[a::=s2])"

lemma eqvt_one: 
  fixes pi :: "name prm"
  and   t  :: "lam"
  and   s  :: "lam"
  shows "t\<longrightarrow>\<^isub>1s \<Longrightarrow> (pi\<bullet>t)\<longrightarrow>\<^isub>1(pi\<bullet>s)"
  apply(erule One.induct)
  apply(auto)
  done

lemma one_induct_aux[rule_format]:
  fixes  P :: "lam \<Rightarrow> lam \<Rightarrow>'a::fs_name\<Rightarrow>bool"
  and    t :: "lam"
  and    s :: "lam"
  assumes a: "t\<longrightarrow>\<^isub>1s"
  and a1:    "\<forall>x t. P t t x"
  and a2:    "\<forall>x t1 t2 s1 s2. 
              (t1\<longrightarrow>\<^isub>1t2 \<and> (\<forall>z. P t1 t2 z) \<and> s1\<longrightarrow>\<^isub>1s2 \<and> (\<forall>z. P s1 s2 z)) 
              \<longrightarrow> P (App t1 s1) (App t2 s2) x"
  and a3:    "\<forall>x (a::name) s1 s2. (a\<sharp>x \<and> s1\<longrightarrow>\<^isub>1s2 \<and> (\<forall>z. P s1 s2 z)) 
             \<longrightarrow>  P (Lam [a].s1) (Lam [a].s2) x"
  and a4:    "\<forall>x (a::name) t1 t2 s1 s2. 
              (a\<sharp>(s1,s2,x) \<and> t1\<longrightarrow>\<^isub>1t2 \<and> (\<forall>z. P t1 t2 z) \<and> s1\<longrightarrow>\<^isub>1s2 \<and> (\<forall>z. P s1 s2 z)) 
              \<longrightarrow> P (App (Lam [a].t1) s1) (t2[a::=s2]) x"
  shows "\<forall>x (pi::name prm). P (pi\<bullet>t) (pi\<bullet>s) x"
using a
proof (induct)
  case o1 show ?case using a1 by force
next
  case (o2 s1 s2 t1 t2) 
  thus ?case using a2 by (simp, blast intro: eqvt_one)
next
  case (o3 a t1 t2)
  assume j1: "t1 \<longrightarrow>\<^isub>1 t2"
  assume j2: "\<forall>x (pi::name prm). P (pi\<bullet>t1) (pi\<bullet>t2) x"
  show ?case 
  proof (simp, intro strip)
    fix pi::"name prm" and x::"'a::fs_name"
     have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>t1,pi\<bullet>t2,x)"
      by (rule at_exists_fresh[OF at_name_inst], simp add: fs_name1)
    then obtain c::"name" 
      where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>x" and f3: "c\<sharp>(pi\<bullet>t1)" and f4: "c\<sharp>(pi\<bullet>t2)"
      by (force simp add: fresh_prod fresh_atm)
    have x: "P (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>t1)) (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>t2)) x"
      using a3 f2 j1 j2 by (simp, blast intro: eqvt_one)
    have alpha1: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>t1))) = (Lam [(pi\<bullet>a)].(pi\<bullet>t1))" using f1 f3
      by (simp add: lam.inject alpha)
    have alpha2: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>t2))) = (Lam [(pi\<bullet>a)].(pi\<bullet>t2))" using f1 f3
      by (simp add: lam.inject alpha)
    show " P (Lam [(pi\<bullet>a)].(pi\<bullet>t1)) (Lam [(pi\<bullet>a)].(pi\<bullet>t2)) x"
      using x alpha1 alpha2 by (simp only: pt_name2)
  qed
next
case (o4 a s1 s2 t1 t2)
  assume j0: "t1 \<longrightarrow>\<^isub>1 t2"
  assume j1: "s1 \<longrightarrow>\<^isub>1 s2"
  assume j2: "\<forall>x (pi::name prm). P (pi\<bullet>t1) (pi\<bullet>t2) x"
  assume j3: "\<forall>x (pi::name prm). P (pi\<bullet>s1) (pi\<bullet>s2) x"
  show ?case
  proof (simp, intro strip)
    fix pi::"name prm" and x::"'a::fs_name" 
    have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>t1,pi\<bullet>t2,pi\<bullet>s1,pi\<bullet>s2,x)"
      by (rule at_exists_fresh[OF at_name_inst], simp add: fs_name1)
    then obtain c::"name" 
      where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>(pi\<bullet>s1,pi\<bullet>s2,x)" and f3: "c\<sharp>(pi\<bullet>t1)" and f4: "c\<sharp>(pi\<bullet>t2)"
      by (force simp add: fresh_prod at_fresh[OF at_name_inst])
    have x: "P (App (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>t1)) (pi\<bullet>s1)) ((([(c,pi\<bullet>a)]@pi)\<bullet>t2)[c::=(pi\<bullet>s2)]) x"
      using a4 f2 j0 j1 j2 j3 by (simp, blast intro!: eqvt_one)
    have alpha1: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>t1))) = (Lam [(pi\<bullet>a)].(pi\<bullet>t1))" using f1 f3
      by (simp add: lam.inject alpha)
    have alpha2: "(([(c,pi\<bullet>a)]@pi)\<bullet>t2)[c::=(pi\<bullet>s2)] = (pi\<bullet>t2)[(pi\<bullet>a)::=(pi\<bullet>s2)]"
      using f4 by (simp only: subst_rename[symmetric] pt_name2)
    show "P (App (Lam [(pi\<bullet>a)].(pi\<bullet>t1)) (pi\<bullet>s1)) ((pi\<bullet>t2)[(pi\<bullet>a)::=(pi\<bullet>s2)]) x"
      using x alpha1 alpha2 by (simp only: pt_name2)
  qed
qed

lemma one_induct[rule_format, case_names o1 o2 o3 o4]:
  fixes  P :: "lam \<Rightarrow> lam \<Rightarrow>'a::fs_name\<Rightarrow>bool"
  and    t :: "lam"
  and    s :: "lam"
  and    x :: "'a::fs_name"
  assumes a: "t\<longrightarrow>\<^isub>1s"
  and a1:    "\<And>x t. P t t x"
  and a2:    "\<And>x t1 t2 s1 s2. 
              t1\<longrightarrow>\<^isub>1t2 \<Longrightarrow> (\<And>z. P t1 t2 z) \<Longrightarrow> s1\<longrightarrow>\<^isub>1s2 \<Longrightarrow> (\<And>z. P s1 s2 z) \<Longrightarrow> 
              P (App t1 s1) (App t2 s2) x"
  and a3:    "\<And>x (a::name) s1 s2. a\<sharp>x \<Longrightarrow> s1\<longrightarrow>\<^isub>1s2 \<Longrightarrow> (\<And>z. P s1 s2 z) 
              \<Longrightarrow> P (Lam [a].s1) (Lam [a].s2) x"
  and a4:    "\<And>x (a::name) t1 t2 s1 s2. 
              a\<sharp>(s1,s2,x) \<Longrightarrow> t1\<longrightarrow>\<^isub>1t2 \<Longrightarrow> (\<And>z. P t1 t2 z) \<Longrightarrow> s1\<longrightarrow>\<^isub>1s2 \<Longrightarrow> (\<And>z. P s1 s2 z) 
              \<Longrightarrow> P (App (Lam [a].t1) s1) (t2[a::=s2]) x"
  shows "P t s x"
using a a1 a2 a3 a4
by (auto intro!: one_induct_aux[of "t" "s" "P" "[]" "x", simplified])

lemma fresh_fact'[rule_format]:  
  shows "a\<sharp>t2 \<longrightarrow> a\<sharp>(t1[a::=t2])" 
proof (nominal_induct t1 rule: lam_induct)
  case (Var a t2 b) 
  show ?case by (cases "b=a") (force simp add: at_fresh[OF at_name_inst])+ 
next
  case App
  thus ?case by (simp add: fresh_prod)
next
  case (Lam a t2 c t) 
  from Lam(1) have "c\<noteq>a \<and> c\<sharp>t2" by (simp add: fresh_prod fresh_atm) 
  thus ?case using Lam(2) by (force simp add: abs_fresh)
qed

lemma one_fresh_preserv[rule_format]:
  fixes    t :: "lam"
  and      s :: "lam"
  and      a :: "name"
  assumes a: "t\<longrightarrow>\<^isub>1s"
  shows "a\<sharp>t \<longrightarrow> a\<sharp>s"
using a
proof (induct)
  case o1 show ?case by simp
next
  case o2 thus ?case by (simp add: fresh_prod)
next
  case (o3 c s1 s2)
  assume i: "a\<sharp>s1 \<longrightarrow>  a\<sharp>s2"
  show ?case
  proof (intro strip, cases "a=c")
    assume "a=c" 
    thus "a\<sharp>Lam [c].s2" by (simp add: abs_fresh)
  next
    assume b: "a\<noteq>c" and "a\<sharp>Lam [c].s1"
    hence "a\<sharp>s1" by (simp add: abs_fresh)
    hence "a\<sharp>s2" using i by simp
    thus "a\<sharp>Lam [c].s2" using b by (simp add: abs_fresh) 
  qed
next 
  case (o4 c t1 t2 s1 s2)
  assume i1: "a\<sharp>t1 \<longrightarrow> a\<sharp>t2"
     and i2: "a\<sharp>s1 \<longrightarrow> a\<sharp>s2"
  show "a\<sharp>App (Lam [c].s1) t1 \<longrightarrow> a\<sharp>s2[c::=t2]"
  proof
    assume "a\<sharp>App (Lam [c].s1) t1"
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
qed

lemma one_abs: 
  fixes    t :: "lam"
  and      t':: "lam"
  and      a :: "name"
  shows "(Lam [a].t)\<longrightarrow>\<^isub>1t'\<Longrightarrow>\<exists>t''. t'=Lam [a].t'' \<and> t\<longrightarrow>\<^isub>1t''"
  apply(ind_cases "(Lam [a].t)\<longrightarrow>\<^isub>1t'")
  apply(auto simp add: lam.distinct lam.inject alpha)
  apply(rule_tac x="[(a,aa)]\<bullet>s2" in exI)
  apply(rule conjI)
  apply(rule pt_bij2[OF pt_name_inst, OF at_name_inst, symmetric])
  apply(simp)
  apply(rule pt_name3)
  apply(rule at_ds5[OF at_name_inst])
  apply(frule_tac a="a" in one_fresh_preserv)
  apply(assumption)
  apply(rule conjI)
  apply(simp add: pt_fresh_left[OF pt_name_inst, OF at_name_inst])
  apply(simp add: calc_atm)
  apply(force intro!: eqvt_one)
  done

lemma one_app: 
  "App t1 t2 \<longrightarrow>\<^isub>1 t' \<Longrightarrow> 
  (\<exists>s1 s2. t' = App s1 s2 \<and> t1 \<longrightarrow>\<^isub>1 s1 \<and> t2 \<longrightarrow>\<^isub>1 s2) \<or> 
  (\<exists>a s s1 s2. t1 = Lam [a].s \<and> t' = s1[a::=s2] \<and> s \<longrightarrow>\<^isub>1 s1 \<and> t2 \<longrightarrow>\<^isub>1 s2)" 
  apply(ind_cases "App t1 s1 \<longrightarrow>\<^isub>1 t'")
  apply(auto simp add: lam.distinct lam.inject)
  done

lemma one_red: 
  "App (Lam [a].t1) t2 \<longrightarrow>\<^isub>1 M \<Longrightarrow>
  (\<exists>s1 s2. M = App (Lam [a].s1) s2 \<and> t1 \<longrightarrow>\<^isub>1 s1 \<and> t2 \<longrightarrow>\<^isub>1 s2) \<or> 
  (\<exists>s1 s2. M = s1[a::=s2] \<and> t1 \<longrightarrow>\<^isub>1 s1 \<and> t2 \<longrightarrow>\<^isub>1 s2)" 
  apply(ind_cases "App (Lam [a].t1) s1 \<longrightarrow>\<^isub>1 M")
  apply(simp_all add: lam.inject)
  apply(force)
  apply(erule conjE)
  apply(drule sym[of "Lam [a].t1"])
  apply(simp)
  apply(drule one_abs)
  apply(erule exE)
  apply(simp)
  apply(force simp add: alpha)
  apply(erule conjE)
  apply(simp add: lam.inject alpha)
  apply(erule disjE)
  apply(simp)
  apply(force)
  apply(simp)
  apply(rule disjI2)
  apply(rule_tac x="[(a,aa)]\<bullet>t2a" in exI)
  apply(rule_tac x="s2" in exI)
  apply(auto)
  apply(subgoal_tac "a\<sharp>t2a")(*A*)
  apply(simp add: subst_rename)
  (*A*)
  apply(force intro: one_fresh_preserv)
  apply(force intro: eqvt_one)
  done

(* first case in Lemma 3.2.4*)

lemma one_subst_aux[rule_format]:
  fixes    M :: "lam"
  and      N :: "lam"
  and      N':: "lam"
  and      x :: "name"
  shows "N\<longrightarrow>\<^isub>1N'\<longrightarrow>M[x::=N] \<longrightarrow>\<^isub>1 M[x::=N']"
proof (nominal_induct M rule: lam_induct)
  case (Var N N' x y) 
  show "N\<longrightarrow>\<^isub>1N' \<longrightarrow> Var y[x::=N] \<longrightarrow>\<^isub>1 Var y[x::=N']" by (cases "x=y", auto)
next
  case (App N N' x P Q) (* application case - third line *)
  thus "N\<longrightarrow>\<^isub>1N' \<longrightarrow> (App P Q)[x::=N] \<longrightarrow>\<^isub>1  (App P Q)[x::=N']" using o2 by simp
next 
  case (Lam N N' x y P) (* abstraction case - fourth line *)
  thus "N\<longrightarrow>\<^isub>1N' \<longrightarrow> (Lam [y].P)[x::=N] \<longrightarrow>\<^isub>1 (Lam [y].P)[x::=N']" using o3 
    by (simp add: fresh_prod fresh_atm)
qed

lemma one_subst_aux[rule_format]:
  fixes    M :: "lam"
  and      N :: "lam"
  and      N':: "lam"
  and      x :: "name"
  shows "N\<longrightarrow>\<^isub>1N'\<longrightarrow>M[x::=N] \<longrightarrow>\<^isub>1 M[x::=N']"
apply(nominal_induct M rule: lam_induct)
apply(auto simp add: fresh_prod fresh_atm)
done

lemma one_subst[rule_format]: 
  fixes    M :: "lam"
  and      M':: "lam"
  and      N :: "lam"
  and      N':: "lam"
  and      x :: "name"
  assumes a: "M\<longrightarrow>\<^isub>1M'" 
  shows "N\<longrightarrow>\<^isub>1N' \<longrightarrow> M[x::=N]\<longrightarrow>\<^isub>1M'[x::=N']" 
using a
proof (nominal_induct M M' rule: one_induct)
  case (o1 x N N' M)
  show ?case by (simp add: one_subst_aux)
next
  case (o2 x N N' M1 M2 N1 N2)
  thus ?case by simp
next
  case (o3 x N N' a M1 M2)
  thus ?case by (simp add: fresh_prod fresh_atm)
next
  case (o4 N N' x a M1 M2 N1 N2)
  assume e3: "a\<sharp>(N1,N2,N,N',x)"
  show ?case
  proof  
    assume a1: "N\<longrightarrow>\<^isub>1N'"
    have "(App (Lam [a].M1) N1)[x::=N] = App (Lam [a].(M1[x::=N])) (N1[x::=N])" 
      using e3 by (simp add: fresh_prod fresh_atm)
    also have "App (Lam [a].(M1[x::=N])) (N1[x::=N]) \<longrightarrow>\<^isub>1 M2[x::=N'][a::=N2[x::=N']]" 
      using  o4 a1 by force
    also have "M2[x::=N'][a::=N2[x::=N']] = M2[a::=N2][x::=N']" 
      using e3 by (simp add: subs_lemma fresh_prod fresh_atm)
    ultimately show "(App (Lam [a].M1) N1)[x::=N] \<longrightarrow>\<^isub>1 M2[a::=N2][x::=N']" by simp
  qed
qed

lemma one_subst[rule_format]: 
  assumes a: "M\<longrightarrow>\<^isub>1M'" 
  shows "N\<longrightarrow>\<^isub>1N' \<longrightarrow> M[x::=N]\<longrightarrow>\<^isub>1M'[x::=N']" 
using a
apply(nominal_induct M M' rule: one_induct)
apply(auto simp add: one_subst_aux subs_lemma fresh_prod fresh_atm)
done

lemma diamond[rule_format]:
  fixes    M :: "lam"
  and      M1:: "lam"
  assumes a: "M\<longrightarrow>\<^isub>1M1" 
  shows "\<forall>M2. (M\<longrightarrow>\<^isub>1M2) \<longrightarrow> (\<exists>M3. M1\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)"
  using a
proof (induct)
  case (o1 M) (* case 1 --- M1 = M *)
  show "\<forall>M2. M\<longrightarrow>\<^isub>1M2 \<longrightarrow> (\<exists>M3. M\<longrightarrow>\<^isub>1M3 \<and>  M2\<longrightarrow>\<^isub>1M3)" by force
next
  case (o4 x Q Q' P P') (* case 2 --- a beta-reduction occurs*)
  assume i1: "\<forall>M2. Q \<longrightarrow>\<^isub>1M2 \<longrightarrow> (\<exists>M3. Q'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)"
  assume i2: "\<forall>M2. P \<longrightarrow>\<^isub>1M2 \<longrightarrow> (\<exists>M3. P'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)"
  show "\<forall>M2. App (Lam [x].P) Q\<longrightarrow>\<^isub>1M2 \<longrightarrow> (\<exists>M3. P'[x::=Q']\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)"
  proof (intro strip)
    fix M2
    assume "App (Lam [x].P) Q \<longrightarrow>\<^isub>1 M2"
    hence "(\<exists>P' Q'. M2 = App (Lam [x].P') Q' \<and> P\<longrightarrow>\<^isub>1P' \<and> Q\<longrightarrow>\<^isub>1Q') \<or> 
           (\<exists>P' Q'. M2 = P'[x::=Q'] \<and> P\<longrightarrow>\<^isub>1P' \<and> Q\<longrightarrow>\<^isub>1Q')" by (simp add: one_red)
    moreover (* subcase 2.1 *)
    { assume "\<exists>P' Q'. M2 = App (Lam [x].P') Q' \<and> P\<longrightarrow>\<^isub>1P' \<and> Q\<longrightarrow>\<^isub>1Q'"
      then obtain P'' and Q'' where 
	b1: "M2=App (Lam [x].P'') Q''" and b2: "P\<longrightarrow>\<^isub>1P''" and b3: "Q\<longrightarrow>\<^isub>1Q''" by force
      from b2 i2 have "(\<exists>M3. P'\<longrightarrow>\<^isub>1M3 \<and> P''\<longrightarrow>\<^isub>1M3)" by simp
      then obtain P''' where
	c1: "P'\<longrightarrow>\<^isub>1P'''" and c2: "P''\<longrightarrow>\<^isub>1P'''" by force
      from b3 i1 have "(\<exists>M3. Q'\<longrightarrow>\<^isub>1M3 \<and> Q''\<longrightarrow>\<^isub>1M3)" by simp
      then obtain Q''' where
	d1: "Q'\<longrightarrow>\<^isub>1Q'''" and d2: "Q''\<longrightarrow>\<^isub>1Q'''" by force
      from c1 c2 d1 d2 
      have "P'[x::=Q']\<longrightarrow>\<^isub>1P'''[x::=Q'''] \<and> App (Lam [x].P'') Q'' \<longrightarrow>\<^isub>1 P'''[x::=Q''']" 
	by (force simp add: one_subst)
      hence "\<exists>M3. P'[x::=Q']\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" using b1 by force
    }
    moreover (* subcase 2.2 *)
    { assume "\<exists>P' Q'. M2 = P'[x::=Q'] \<and> P\<longrightarrow>\<^isub>1P' \<and> Q\<longrightarrow>\<^isub>1Q'"
      then obtain P'' Q'' where
	b1: "M2=P''[x::=Q'']" and b2: "P\<longrightarrow>\<^isub>1P''" and  b3: "Q\<longrightarrow>\<^isub>1Q''" by force
      from b2 i2 have "(\<exists>M3. P'\<longrightarrow>\<^isub>1M3 \<and> P''\<longrightarrow>\<^isub>1M3)" by simp
      then obtain P''' where
	c1: "P'\<longrightarrow>\<^isub>1P'''" and c2: "P''\<longrightarrow>\<^isub>1P'''" by force
      from b3 i1 have "(\<exists>M3. Q'\<longrightarrow>\<^isub>1M3 \<and> Q''\<longrightarrow>\<^isub>1M3)" by simp
      then obtain Q''' where
	d1: "Q'\<longrightarrow>\<^isub>1Q'''" and d2: "Q''\<longrightarrow>\<^isub>1Q'''" by force
      from c1 c2 d1 d2 
      have "P'[x::=Q']\<longrightarrow>\<^isub>1P'''[x::=Q'''] \<and> P''[x::=Q'']\<longrightarrow>\<^isub>1P'''[x::=Q''']" 
	by (force simp add: one_subst)
      hence "\<exists>M3. P'[x::=Q']\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" using b1 by force
    }
    ultimately show "\<exists>M3. P'[x::=Q']\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" by blast
  qed
next
  case (o2 Q Q' P P') (* case 3 *)
  assume i0: "P\<longrightarrow>\<^isub>1P'"
  assume i1: "\<forall>M2. Q \<longrightarrow>\<^isub>1M2 \<longrightarrow> (\<exists>M3. Q'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)"
  assume i2: "\<forall>M2. P \<longrightarrow>\<^isub>1M2 \<longrightarrow> (\<exists>M3. P'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)"
  show "\<forall>M2. App P Q\<longrightarrow>\<^isub>1M2 \<longrightarrow> (\<exists>M3. App P' Q'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)"
  proof (intro strip)
    fix M2
    assume "App P Q \<longrightarrow>\<^isub>1 M2"
    hence "(\<exists>P'' Q''. M2 = App P'' Q'' \<and> P\<longrightarrow>\<^isub>1P'' \<and> Q\<longrightarrow>\<^isub>1Q'') \<or> 
           (\<exists>x P' P'' Q'. P = Lam [x].P' \<and> M2 = P''[x::=Q'] \<and> P'\<longrightarrow>\<^isub>1 P'' \<and> Q\<longrightarrow>\<^isub>1Q')" 
      by (simp add: one_app[simplified])
    moreover (* subcase 3.1 *)
    { assume "\<exists>P'' Q''. M2 = App P'' Q'' \<and> P\<longrightarrow>\<^isub>1P'' \<and> Q\<longrightarrow>\<^isub>1Q''"
      then obtain P'' and Q'' where 
	b1: "M2=App P'' Q''" and b2: "P\<longrightarrow>\<^isub>1P''" and b3: "Q\<longrightarrow>\<^isub>1Q''" by force
      from b2 i2 have "(\<exists>M3. P'\<longrightarrow>\<^isub>1M3 \<and> P''\<longrightarrow>\<^isub>1M3)" by simp
      then obtain P''' where
	c1: "P'\<longrightarrow>\<^isub>1P'''" and c2: "P''\<longrightarrow>\<^isub>1P'''" by force
      from b3 i1 have "(\<exists>M3. Q'\<longrightarrow>\<^isub>1M3 \<and> Q''\<longrightarrow>\<^isub>1M3)" by simp
      then obtain Q''' where
	d1: "Q'\<longrightarrow>\<^isub>1Q'''" and d2: "Q''\<longrightarrow>\<^isub>1Q'''" by force
      from c1 c2 d1 d2 
      have "App P' Q'\<longrightarrow>\<^isub>1App P''' Q''' \<and> App P'' Q'' \<longrightarrow>\<^isub>1 App P''' Q'''" by force
      hence "\<exists>M3. App P' Q'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" using b1 by force
    }
    moreover (* subcase 3.2 *)
    { assume "\<exists>x P1 P'' Q''. P = Lam [x].P1 \<and> M2 = P''[x::=Q''] \<and> P1\<longrightarrow>\<^isub>1 P'' \<and> Q\<longrightarrow>\<^isub>1Q''"
      then obtain x P1 P1'' Q'' where
	b0: "P=Lam [x].P1" and b1: "M2=P1''[x::=Q'']" and 
        b2: "P1\<longrightarrow>\<^isub>1P1''" and  b3: "Q\<longrightarrow>\<^isub>1Q''" by force
      from b0 i0 have "\<exists>P1'. P'=Lam [x].P1' \<and> P1\<longrightarrow>\<^isub>1P1'" by (simp add: one_abs)
      then obtain P1' where g1: "P'=Lam [x].P1'" and g2: "P1\<longrightarrow>\<^isub>1P1'" by force 
      from g1 b0 b2 i2 have "(\<exists>M3. (Lam [x].P1')\<longrightarrow>\<^isub>1M3 \<and> (Lam [x].P1'')\<longrightarrow>\<^isub>1M3)" by simp
      then obtain P1''' where
	c1: "(Lam [x].P1')\<longrightarrow>\<^isub>1P1'''" and c2: "(Lam [x].P1'')\<longrightarrow>\<^isub>1P1'''" by force
      from c1 have "\<exists>R1. P1'''=Lam [x].R1 \<and> P1'\<longrightarrow>\<^isub>1R1" by (simp add: one_abs)
      then obtain R1 where r1: "P1'''=Lam [x].R1" and r2: "P1'\<longrightarrow>\<^isub>1R1" by force
      from c2 have "\<exists>R2. P1'''=Lam [x].R2 \<and> P1''\<longrightarrow>\<^isub>1R2" by (simp add: one_abs)
      then obtain R2 where r3: "P1'''=Lam [x].R2" and r4: "P1''\<longrightarrow>\<^isub>1R2" by force
      from r1 r3 have r5: "R1=R2" 
	by (simp add: lam.inject alpha)
      from b3 i1 have "(\<exists>M3. Q'\<longrightarrow>\<^isub>1M3 \<and> Q''\<longrightarrow>\<^isub>1M3)" by simp
      then obtain Q''' where
	d1: "Q'\<longrightarrow>\<^isub>1Q'''" and d2: "Q''\<longrightarrow>\<^isub>1Q'''" by force
      from g1 r2 d1 r4 r5 d2 
      have "App P' Q'\<longrightarrow>\<^isub>1R1[x::=Q'''] \<and> P1''[x::=Q'']\<longrightarrow>\<^isub>1R1[x::=Q''']" by (simp add: one_subst)
      hence "\<exists>M3. App P' Q'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" using b1 by force
    }
    ultimately show "\<exists>M3. App P' Q'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" by blast
  qed
next
  case (o3 x P P') (* case 4 *)
  assume i1: "P\<longrightarrow>\<^isub>1P'"
  assume i2: "\<forall>M2. P \<longrightarrow>\<^isub>1M2 \<longrightarrow> (\<exists>M3. P'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)"
  show "\<forall>M2. (Lam [x].P)\<longrightarrow>\<^isub>1M2 \<longrightarrow> (\<exists>M3. (Lam [x].P')\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)"
  proof (intro strip)
    fix M2
    assume "(Lam [x].P)\<longrightarrow>\<^isub>1 M2"
    hence "\<exists>P''. M2=Lam [x].P'' \<and> P\<longrightarrow>\<^isub>1P''" by (simp add: one_abs)
    then obtain P'' where b1: "M2=Lam [x].P''" and b2: "P\<longrightarrow>\<^isub>1P''" by force
    from i2 b1 b2 have "\<exists>M3. (Lam [x].P')\<longrightarrow>\<^isub>1M3 \<and> (Lam [x].P'')\<longrightarrow>\<^isub>1M3" by force
    then obtain M3 where c1: "(Lam [x].P')\<longrightarrow>\<^isub>1M3" and c2: "(Lam [x].P'')\<longrightarrow>\<^isub>1M3" by force
    from c1 have "\<exists>R1. M3=Lam [x].R1 \<and> P'\<longrightarrow>\<^isub>1R1" by (simp add: one_abs)
    then obtain R1 where r1: "M3=Lam [x].R1" and r2: "P'\<longrightarrow>\<^isub>1R1" by force
    from c2 have "\<exists>R2. M3=Lam [x].R2 \<and> P''\<longrightarrow>\<^isub>1R2" by (simp add: one_abs)
    then obtain R2 where r3: "M3=Lam [x].R2" and r4: "P''\<longrightarrow>\<^isub>1R2" by force
    from r1 r3 have r5: "R1=R2" 
      by (simp add: lam.inject alpha)
    from r2 r4 have "(Lam [x].P')\<longrightarrow>\<^isub>1(Lam [x].R1) \<and> (Lam [x].P'')\<longrightarrow>\<^isub>1(Lam [x].R2)" 
      by (simp add: one_subst)
    thus "\<exists>M3. (Lam [x].P')\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" using b1 r5 by force
  qed
qed

lemma one_abs_cong: 
  fixes a :: "name"
  assumes a: "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2" 
  shows "(Lam [a].t1)\<longrightarrow>\<^isub>\<beta>\<^sup>*(Lam [a].t2)"
  using a
proof induct
  case 1 thus ?case by force
next
  case (2 y z) 
  thus ?case by (force dest: b3 intro: rtrancl_trans)
qed

lemma one_pr_congL: 
  assumes a: "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2" 
  shows "App t1 s\<longrightarrow>\<^isub>\<beta>\<^sup>* App t2 s"
  using a
proof induct
  case 1 thus ?case by (force)
next
  case 2 thus ?case by (force dest: b1 intro: rtrancl_trans)
qed
  
lemma one_pr_congR: 
  assumes a: "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2" 
  shows "App s t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* App s t2"
using a
proof induct
  case 1 thus ?case by (force)
next 
  case 2 thus ?case by (force dest: b2 intro: rtrancl_trans)
qed

lemma one_pr_cong: 
  assumes a1: "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2" 
  and a2: "s1\<longrightarrow>\<^isub>\<beta>\<^sup>*s2" 
  shows "App t1 s1\<longrightarrow>\<^isub>\<beta>\<^sup>* App t2 s2"
proof -
  have b1: "App t1 s1 \<longrightarrow>\<^isub>\<beta>\<^sup>* App t2 s1" using a1 by (rule one_pr_congL)
  have b2: "App t2 s1 \<longrightarrow>\<^isub>\<beta>\<^sup>* App t2 s2" using a2 by (rule one_pr_congR)
  show ?thesis using b1 and b2 by (force intro: rtrancl_trans)
qed

lemma one_beta_star: 
  assumes a: "(t1\<longrightarrow>\<^isub>1t2)" 
  shows "(t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2)"
  using a
proof induct
  case o1 thus ?case by (force)
next
  case o2 thus ?case by (force intro!: one_pr_cong)
next
  case o3 thus ?case by (force intro!: one_abs_cong)
next 
  case (o4 a s1 s2 t1 t2)
  have a1: "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2" and a2: "s1\<longrightarrow>\<^isub>\<beta>\<^sup>*s2" .
  have c1: "(App (Lam [a].t2) s2) \<longrightarrow>\<^isub>\<beta> (t2 [a::= s2])" by (rule b4)
  from a1 a2 have c2: "App (Lam [a].t1 ) s1 \<longrightarrow>\<^isub>\<beta>\<^sup>* App (Lam [a].t2 ) s2" 
    by (force intro!: one_pr_cong one_abs_cong)
  show ?case using c1 c2 by (force intro: rtrancl_trans)
qed
 
lemma one_star_abs_cong: 
  fixes a :: "name"
  assumes a: "t1\<longrightarrow>\<^isub>1\<^sup>*t2" 
  shows "(Lam  [a].t1)\<longrightarrow>\<^isub>1\<^sup>* (Lam [a].t2)"
  using a
proof induct
  case 1 thus ?case by (force)
next
  case 2 thus ?case by (force intro: rtrancl_trans)
qed

lemma one_star_pr_congL: 
  assumes a: "t1\<longrightarrow>\<^isub>1\<^sup>*t2" 
  shows "App t1 s\<longrightarrow>\<^isub>1\<^sup>* App t2 s"
  using a
proof induct
  case 1 thus ?case by (force)
next
  case 2 thus ?case by (force intro: rtrancl_trans)
qed

lemma one_star_pr_congR: 
  assumes a: "t1\<longrightarrow>\<^isub>1\<^sup>*t2" 
  shows "App s t1 \<longrightarrow>\<^isub>1\<^sup>* App s t2"
  using a
proof induct
  case 1 thus ?case by (force)
next
  case 2 thus ?case by (force intro: rtrancl_trans)
qed

lemma beta_one_star: 
  assumes a: "t1\<longrightarrow>\<^isub>\<beta>t2" 
  shows "t1\<longrightarrow>\<^isub>1\<^sup>*t2"
  using a
proof induct
  case b1 thus ?case by (force intro!: one_star_pr_congL)
next
  case b2 thus ?case by (force intro!: one_star_pr_congR)
next
  case b3 thus ?case by (force intro!: one_star_abs_cong)
next
  case b4 thus ?case by (force)
qed

lemma trans_closure: 
  shows "(t1\<longrightarrow>\<^isub>1\<^sup>*t2) = (t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2)"
proof
  assume "t1 \<longrightarrow>\<^isub>1\<^sup>* t2"
  thus "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2"
  proof induct
    case 1 thus ?case by (force)
  next
    case 2 thus ?case by (force intro: rtrancl_trans simp add: one_beta_star)
  qed
next
  assume "t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* t2" 
  thus "t1\<longrightarrow>\<^isub>1\<^sup>*t2"
  proof induct
    case 1 thus ?case by (force)
  next
    case 2 thus ?case by (force intro: rtrancl_trans simp add: beta_one_star)
  qed
qed

lemma cr_one:
  assumes a: "t\<longrightarrow>\<^isub>1\<^sup>*t1" 
  and b: "t\<longrightarrow>\<^isub>1t2"
  shows "\<exists>t3. t1\<longrightarrow>\<^isub>1t3 \<and> t2\<longrightarrow>\<^isub>1\<^sup>*t3"
proof -
  have stronger: "\<forall>t2. t\<longrightarrow>\<^isub>1t2\<longrightarrow>(\<exists>t3. t1\<longrightarrow>\<^isub>1t3\<and>t2\<longrightarrow>\<^isub>1\<^sup>*t3)"
    using a 
  proof induct
    case 1 show ?case by (force)
  next
    case (2 s1 s2)
    assume b: "s1 \<longrightarrow>\<^isub>1 s2"
    assume h: "\<forall>t2. t \<longrightarrow>\<^isub>1 t2 \<longrightarrow> (\<exists>t3. s1 \<longrightarrow>\<^isub>1 t3 \<and> t2 \<longrightarrow>\<^isub>1\<^sup>* t3)"
    show ?case
    proof (rule allI, rule impI)
      fix t2
      assume  c: "t \<longrightarrow>\<^isub>1 t2"
      show "(\<exists>t3.  s2 \<longrightarrow>\<^isub>1 t3 \<and>  t2 \<longrightarrow>\<^isub>1\<^sup>* t3)" 
      proof -
	from c h have "(\<exists>t3. s1 \<longrightarrow>\<^isub>1 t3 \<and> t2 \<longrightarrow>\<^isub>1\<^sup>* t3)" by force
	then obtain t3 where c1: "s1 \<longrightarrow>\<^isub>1 t3"
                         and c2: "t2 \<longrightarrow>\<^isub>1\<^sup>* t3" by (force)
	have "(\<exists>t4. s2 \<longrightarrow>\<^isub>1 t4 \<and> t3 \<longrightarrow>\<^isub>1 t4)" using b c1 by (force intro: diamond)
	thus ?thesis using c2 by (force intro: rtrancl_trans)
      qed
    qed
  qed
  from a b stronger show ?thesis by force
qed


lemma cr_one_star: 
  assumes a: "t\<longrightarrow>\<^isub>1\<^sup>*t2"
      and b: "t\<longrightarrow>\<^isub>1\<^sup>*t1"
    shows "(\<exists>t3. t1\<longrightarrow>\<^isub>1\<^sup>*t3\<and>t2\<longrightarrow>\<^isub>1\<^sup>*t3)"
using a
proof induct
  case 1
  show ?case using b by force
next 
  case (2 s1 s2)
  assume d: "s1 \<longrightarrow>\<^isub>1 s2"
  assume "\<exists>t3.  t1 \<longrightarrow>\<^isub>1\<^sup>* t3 \<and>  s1 \<longrightarrow>\<^isub>1\<^sup>* t3"
  then obtain t3 where f1: "t1 \<longrightarrow>\<^isub>1\<^sup>* t3"
                   and f2: "s1 \<longrightarrow>\<^isub>1\<^sup>* t3" by force
  from cr_one d f2 have "\<exists>t4. t3\<longrightarrow>\<^isub>1t4 \<and> s2\<longrightarrow>\<^isub>1\<^sup>*t4" by force
  then obtain t4 where g1: "t3\<longrightarrow>\<^isub>1t4"
                   and g2: "s2\<longrightarrow>\<^isub>1\<^sup>*t4" by force
  have "t1\<longrightarrow>\<^isub>1\<^sup>*t4" using f1 g1 by (force intro: rtrancl_trans)
  thus ?case using g2 by (force)
qed
  
lemma cr_beta_star: 
  assumes a1: "t\<longrightarrow>\<^isub>\<beta>\<^sup>*t1" 
  and a2: "t\<longrightarrow>\<^isub>\<beta>\<^sup>*t2" 
  shows "(\<exists>t3. t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t3\<and>t2\<longrightarrow>\<^isub>\<beta>\<^sup>*t3)"
proof -
  from a1 have b1: "t\<longrightarrow>\<^isub>1\<^sup>*t1" by (simp add: trans_closure[symmetric])
  from a2 have b2: "t\<longrightarrow>\<^isub>1\<^sup>*t2" by (simp add: trans_closure[symmetric])
  from b1 and b2 have c: "\<exists>t3. (t1\<longrightarrow>\<^isub>1\<^sup>*t3 \<and> t2\<longrightarrow>\<^isub>1\<^sup>*t3)" by (force intro!: cr_one_star) 
  from c obtain t3 where d1: "t1\<longrightarrow>\<^isub>1\<^sup>*t3" and d2: "t2\<longrightarrow>\<^isub>1\<^sup>*t3" by force
  from d1 have e1: "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t3" by (simp add: trans_closure)
  from d2 have e2: "t2\<longrightarrow>\<^isub>\<beta>\<^sup>*t3" by (simp add: trans_closure)
  show ?thesis using e1 and e2 by (force)
qed

end

