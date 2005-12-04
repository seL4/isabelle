(* $Id$ *)

theory cr
imports lam_substs
begin

text {* The Church-Rosser proof from Barendregt's book *}

lemma forget: 
  assumes a: "a\<sharp>t1"
  shows "t1[a::=t2] = t1"
using a
proof (nominal_induct t1 avoiding: a t2 rule: lam_induct)
  case (Var b) 
  thus ?case by (simp add: fresh_atm)
next 
  case App
  thus ?case by simp
next
  case (Lam c t)
  have ih: "\<And>c t2. c\<sharp>t \<Longrightarrow>  t[c::=t2] = t" by fact
  have a: "c\<sharp>t2" by fact
  have "c\<sharp>a" by fact
  hence b: "a\<noteq>c" by (simp add: fresh_atm)
  have "a\<sharp>Lam [c].t" by fact 
  hence "a\<sharp>t" using b by (simp add: abs_fresh)
  hence "t[a::=t2] = t" using ih by simp
  thus "(Lam [c].t)[a::=t2] = Lam [c].t" using a b by simp
qed

lemma forget: 
  assumes a: "a\<sharp>t1"
  shows "t1[a::=t2] = t1"
  using a
  by (nominal_induct t1 avoiding: a t2 rule: lam_induct)
     (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact: 
  fixes   b :: "name"
  and    a  :: "name"
  and    t1 :: "lam"
  and    t2 :: "lam"
  assumes a: "a\<sharp>t1"
  and     b: "a\<sharp>t2"
  shows "a\<sharp>(t1[b::=t2])"
using a b
proof (nominal_induct t1 avoiding: a b t2 rule: lam_induct)
  case (Var c) 
  thus ?case by simp
next
  case App thus ?case by simp 
next
  case (Lam c t)
  have ih: "\<And>(a::name) b t2. a\<sharp>t \<Longrightarrow> a\<sharp>t2 \<Longrightarrow> a\<sharp>(t[b::=t2])" by fact
  have fr: "c\<sharp>a" "c\<sharp>b" "c\<sharp>t2" by fact+
  hence fr': "c\<noteq>a" by (simp add: fresh_atm) 
  have a1: "a\<sharp>t2" by fact
  have a2: "a\<sharp>Lam [c].t" by fact
  hence "a\<sharp>t" using fr' by (simp add: abs_fresh)
  hence "a\<sharp>t[b::=t2]" using a1 ih by simp
  thus "a\<sharp>(Lam [c].t)[b::=t2]" using fr  by (simp add: abs_fresh)
qed

lemma fresh_fact: 
  fixes a::"name"
  assumes a: "a\<sharp>t1"
  and     b: "a\<sharp>t2"
  shows "a\<sharp>(t1[b::=t2])"
using a b
by (nominal_induct t1 avoiding: a b t2 rule: lam_induct)
   (auto simp add: abs_fresh fresh_atm)


lemma subs_lemma:  
  fixes x::"name"
  and   y::"name"
  and   L::"lam"
  and   M::"lam"
  and   N::"lam"
  assumes a: "x\<noteq>y"
  and     b: "x\<sharp>L"
  shows "M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
using a b
proof (nominal_induct M avoiding: x y N L rule: lam_induct)
  case (Var z) (* case 1: Variables*)
  have "x\<noteq>y" by fact
  have "x\<sharp>L" by fact
  show "Var z[x::=N][y::=L] = Var z[y::=L][x::=N[y::=L]]" (is "?LHS = ?RHS")
  proof -
    { (*Case 1.1*)
      assume  "z=x"
      have "(1)": "?LHS = N[y::=L]" using `z=x` by simp
      have "(2)": "?RHS = N[y::=L]" using `z=x` `x\<noteq>y` by simp
      from "(1)" "(2)" have "?LHS = ?RHS"  by simp
    }
    moreover 
    { (*Case 1.2*)
      assume "z\<noteq>x" and "z=y"
      have "(1)": "?LHS = L"               using `z\<noteq>x` `z=y` by force
      have "(2)": "?RHS = L[x::=N[y::=L]]" using `z=y` by force
      have "(3)": "L[x::=N[y::=L]] = L"    using `x\<sharp>L` by (simp add: forget)
      from "(1)" "(2)" "(3)" have "?LHS = ?RHS" by simp
    }
    moreover 
    { (*Case 1.3*)
      assume "z\<noteq>x" and "z\<noteq>y"
      have "(1)": "?LHS = Var z" using `z\<noteq>x` `z\<noteq>y` by force
      have "(2)": "?RHS = Var z" using `z\<noteq>x` `z\<noteq>y` by force
      from "(1)" "(2)" have "?LHS = ?RHS" by simp
    }
    ultimately show "?LHS = ?RHS" by blast
  qed
next
  case (Lam z M1) (* case 2: lambdas *)
  have ih: "\<And>x y N L. x\<noteq>y \<Longrightarrow> x\<sharp>L \<Longrightarrow> M1[x::=N][y::=L] = M1[y::=L][x::=N[y::=L]]" by fact
  have "x\<noteq>y" by fact
  have "x\<sharp>L" by fact
  have "z\<sharp>x" "z\<sharp>y" "z\<sharp>N" "z\<sharp>L" by fact
  hence "z\<sharp>N[y::=L]" by (simp add: fresh_fact)
  show "(Lam [z].M1)[x::=N][y::=L] = (Lam [z].M1)[y::=L][x::=N[y::=L]]" (is "?LHS=?RHS") 
  proof -
    have "?LHS = Lam [z].(M1[x::=N][y::=L])" using `z\<sharp>x` `z\<sharp>y` `z\<sharp>N` `z\<sharp>L` by simp
    also from ih have "\<dots> = Lam [z].(M1[y::=L][x::=N[y::=L]])" using `x\<noteq>y` `x\<sharp>L` by simp
    also have "\<dots> = (Lam [z].(M1[y::=L]))[x::=N[y::=L]]" using `z\<sharp>x` `z\<sharp>N[y::=L]` by simp
    also have "\<dots> = ?RHS" using  `z\<sharp>y` `z\<sharp>L` by simp
    finally show "?LHS = ?RHS" .
  qed
next
  case (App M1 M2) (* case 3: applications *)
  thus ?case by simp
qed

lemma subs_lemma:  
  fixes x::"name"
  and   y::"name"
  and   L::"lam"
  and   M::"lam"
  and   N::"lam"
  assumes a: "x\<noteq>y"
  and     b: "x\<sharp>L"
  shows "M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
using a b
by (nominal_induct M avoiding: x y N L rule: lam_induct)
   (auto simp add: fresh_fact forget)

lemma subst_rename: 
  fixes  c  :: "name"
  and    a  :: "name"
  and    t1 :: "lam"
  and    t2 :: "lam"
  assumes a: "c\<sharp>t1"
  shows "t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2]"
using a
proof (nominal_induct t1 avoiding: a c t2 rule: lam_induct)
  case (Var b)
  thus "(Var b)[a::=t2] = ([(c,a)]\<bullet>(Var b))[c::=t2]" by (simp add: calc_atm fresh_atm)
next
  case App thus ?case by force
next
  case (Lam b s)
  have i: "\<And>a c t2. c\<sharp>s \<Longrightarrow> (s[a::=t2] = ([(c,a)]\<bullet>s)[c::=t2])" by fact
  have f: "b\<sharp>a" "b\<sharp>c" "b\<sharp>t2" by fact
  from f have a:"b\<noteq>c" and b: "b\<noteq>a" and c: "b\<sharp>t2" by (simp add: fresh_atm)+
  have "c\<sharp>Lam [b].s" by fact
  hence "c\<sharp>s" using a by (simp add: abs_fresh)
  hence d: "s[a::=t2] = ([(c,a)]\<bullet>s)[c::=t2]" using i by simp
  show "(Lam [b].s)[a::=t2] = ([(c,a)]\<bullet>(Lam [b].s))[c::=t2]" (is "?LHS = ?RHS")
  proof -
    have    "?LHS = Lam [b].(s[a::=t2])" using b c by simp
    also have "\<dots> = Lam [b].(([(c,a)]\<bullet>s)[c::=t2])" using d by simp
    also have "\<dots> = (Lam [b].([(c,a)]\<bullet>s))[c::=t2]" using a c by simp
    also have "\<dots> = ?RHS" using a b by (simp add: calc_atm)
    finally show "?LHS = ?RHS" by simp
  qed
qed

lemma subst_rename: 
  fixes  c  :: "name"
  and    a  :: "name"
  and    t1 :: "lam"
  and    t2 :: "lam"
  assumes a: "c\<sharp>t1"
  shows "t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2]"
using a
apply(nominal_induct t1 avoiding: a c t2 rule: lam_induct)
apply(auto simp add: calc_atm fresh_atm abs_fresh)
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
  assumes a: "t\<longrightarrow>\<^isub>\<beta>s"
  shows "(pi\<bullet>t)\<longrightarrow>\<^isub>\<beta>(pi\<bullet>s)"
  using a by (induct, auto)

lemma beta_induct[consumes 1, case_names b1 b2 b3 b4]:
  fixes  P :: "'a::fs_name\<Rightarrow>lam \<Rightarrow> lam \<Rightarrow>bool"
  and    t :: "lam"
  and    s :: "lam"
  and    x :: "'a::fs_name"
  assumes a: "t\<longrightarrow>\<^isub>\<beta>s"
  and a1:    "\<And>t s1 s2 x. s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (\<And>z. P z s1 s2) \<Longrightarrow> P x (App s1 t) (App s2 t)"
  and a2:    "\<And>t s1 s2 x. s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (\<And>z. P z s1 s2) \<Longrightarrow> P x (App t s1) (App t s2)"
  and a3:    "\<And>a s1 s2 x. a\<sharp>x \<Longrightarrow> s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (\<And>z. P z s1 s2) \<Longrightarrow> P x (Lam [a].s1) (Lam [a].s2)"
  and a4:    "\<And>a t1 s1 x. a\<sharp>(s1,x) \<Longrightarrow> P x (App (Lam [a].t1) s1) (t1[a::=s1])"
  shows "P x t s"
proof -
  from a have "\<And>(pi::name prm) x. P x (pi\<bullet>t) (pi\<bullet>s)"
  proof (induct)
    case b1 thus ?case using a1 by (simp, blast intro: eqvt_beta)
  next
    case b2 thus ?case using a2 by (simp, blast intro: eqvt_beta)
  next
    case (b3 a s1 s2)
    have j1: "s1 \<longrightarrow>\<^isub>\<beta> s2" by fact
    have j2: "\<And>x (pi::name prm). P x (pi\<bullet>s1) (pi\<bullet>s2)" by fact
    show ?case 
    proof (simp)
      have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>s1,pi\<bullet>s2,x)"
	by (rule at_exists_fresh[OF at_name_inst], simp add: fs_name1)
      then obtain c::"name" 
	where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>x" and f3: "c\<sharp>(pi\<bullet>s1)" and f4: "c\<sharp>(pi\<bullet>s2)"
	by (force simp add: fresh_prod fresh_atm)
      have x: "P x (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>s1)) (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>s2))"
	using a3 f2 j1 j2 by (simp, blast intro: eqvt_beta)
      have alpha1: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>s1))) = (Lam [(pi\<bullet>a)].(pi\<bullet>s1))" using f1 f3
	by (simp add: lam.inject alpha)
      have alpha2: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>s2))) = (Lam [(pi\<bullet>a)].(pi\<bullet>s2))" using f1 f3
	by (simp add: lam.inject alpha)
      show " P x (Lam [(pi\<bullet>a)].(pi\<bullet>s1)) (Lam [(pi\<bullet>a)].(pi\<bullet>s2))"
	using x alpha1 alpha2 by (simp only: pt_name2)
    qed
  next
    case (b4 a s1 s2)
    show ?case
    proof (simp add: subst_eqvt)
      have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>s1,pi\<bullet>s2,x)"
	by (rule at_exists_fresh[OF at_name_inst], simp add: fs_name1)
      then obtain c::"name" 
	where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>(pi\<bullet>s2,x)" and f3: "c\<sharp>(pi\<bullet>s1)" and f4: "c\<sharp>(pi\<bullet>s2)"
	by (force simp add: fresh_prod fresh_atm)
      have x: "P x (App (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>s1)) (pi\<bullet>s2)) ((([(c,pi\<bullet>a)]@pi)\<bullet>s1)[c::=(pi\<bullet>s2)])"
	using a4 f2 by (blast intro!: eqvt_beta)
      have alpha1: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>s1))) = (Lam [(pi\<bullet>a)].(pi\<bullet>s1))" using f1 f3
	by (simp add: lam.inject alpha)
      have alpha2: "(([(c,pi\<bullet>a)]@pi)\<bullet>s1)[c::=(pi\<bullet>s2)] = (pi\<bullet>s1)[(pi\<bullet>a)::=(pi\<bullet>s2)]"
	using f3 by (simp only: subst_rename[symmetric] pt_name2)
      show "P x (App (Lam [(pi\<bullet>a)].(pi\<bullet>s1)) (pi\<bullet>s2)) ((pi\<bullet>s1)[(pi\<bullet>a)::=(pi\<bullet>s2)])"
	using x alpha1 alpha2 by (simp only: pt_name2)
    qed
  qed
  hence "P x (([]::name prm)\<bullet>t) (([]::name prm)\<bullet>s)" by blast 
  thus ?thesis by simp
qed

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
  assumes a: "t\<longrightarrow>\<^isub>1s"
  shows "(pi\<bullet>t)\<longrightarrow>\<^isub>1(pi\<bullet>s)"
  using a by (induct, auto)

lemma one_induct[consumes 1, case_names o1 o2 o3 o4]:
  fixes  P :: "'a::fs_name\<Rightarrow>lam \<Rightarrow> lam \<Rightarrow>bool"
  and    t :: "lam"
  and    s :: "lam"
  and    x :: "'a::fs_name"
  assumes a: "t\<longrightarrow>\<^isub>1s"
  and a1:    "\<And>t x. P x t t"
  and a2:    "\<And>t1 t2 s1 s2 x. t1\<longrightarrow>\<^isub>1t2 \<Longrightarrow> (\<And>z. P z t1 t2) \<Longrightarrow> s1\<longrightarrow>\<^isub>1s2 \<Longrightarrow> (\<And>z. P z s1 s2) \<Longrightarrow> 
              P x (App t1 s1) (App t2 s2)"
  and a3:    "\<And>a s1 s2 x. a\<sharp>x \<Longrightarrow> s1\<longrightarrow>\<^isub>1s2 \<Longrightarrow> (\<And>z. P z s1 s2) \<Longrightarrow> P x (Lam [a].s1) (Lam [a].s2)"
  and a4:    "\<And>a t1 t2 s1 s2 x. 
              a\<sharp>(s1,s2,x) \<Longrightarrow> t1\<longrightarrow>\<^isub>1t2 \<Longrightarrow> (\<And>z. P z t1 t2) \<Longrightarrow> s1\<longrightarrow>\<^isub>1s2 \<Longrightarrow> (\<And>z. P z s1 s2) 
              \<Longrightarrow> P x (App (Lam [a].t1) s1) (t2[a::=s2])"
  shows "P x t s"
proof -
  from a have "\<And>(pi::name prm) x. P x (pi\<bullet>t) (pi\<bullet>s)"
  proof (induct)
    case o1 show ?case using a1 by force
  next
    case (o2 s1 s2 t1 t2) 
    thus ?case using a2 by (simp, blast intro: eqvt_one)
  next
    case (o3 a t1 t2)
    have j1: "t1 \<longrightarrow>\<^isub>1 t2" by fact
    have j2: "\<And>(pi::name prm) x. P x (pi\<bullet>t1) (pi\<bullet>t2)" by fact
    show ?case 
    proof (simp)
      have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>t1,pi\<bullet>t2,x)"
	by (rule at_exists_fresh[OF at_name_inst], simp add: fs_name1)
      then obtain c::"name" 
	where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>x" and f3: "c\<sharp>(pi\<bullet>t1)" and f4: "c\<sharp>(pi\<bullet>t2)"
	by (force simp add: fresh_prod fresh_atm)
      have x: "P x (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>t1)) (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>t2))"
	using a3 f2 j1 j2 by (simp, blast intro: eqvt_one)
      have alpha1: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>t1))) = (Lam [(pi\<bullet>a)].(pi\<bullet>t1))" using f1 f3
	by (simp add: lam.inject alpha)
      have alpha2: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>t2))) = (Lam [(pi\<bullet>a)].(pi\<bullet>t2))" using f1 f3
	by (simp add: lam.inject alpha)
      show " P x (Lam [(pi\<bullet>a)].(pi\<bullet>t1)) (Lam [(pi\<bullet>a)].(pi\<bullet>t2))"
	using x alpha1 alpha2 by (simp only: pt_name2)
    qed
  next
    case (o4 a s1 s2 t1 t2)
    have j0: "t1 \<longrightarrow>\<^isub>1 t2" by fact
    have j1: "s1 \<longrightarrow>\<^isub>1 s2" by fact
    have j2: "\<And>(pi::name prm) x. P x (pi\<bullet>t1) (pi\<bullet>t2)" by fact
    have j3: "\<And>(pi::name prm) x. P x (pi\<bullet>s1) (pi\<bullet>s2)" by fact
    show ?case
    proof (simp)
      have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>t1,pi\<bullet>t2,pi\<bullet>s1,pi\<bullet>s2,x)"
	by (rule at_exists_fresh[OF at_name_inst], simp add: fs_name1)
      then obtain c::"name" 
	where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>(pi\<bullet>s1,pi\<bullet>s2,x)" and f3: "c\<sharp>(pi\<bullet>t1)" and f4: "c\<sharp>(pi\<bullet>t2)"
	by (force simp add: fresh_prod at_fresh[OF at_name_inst])
      have x: "P x (App (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>t1)) (pi\<bullet>s1)) ((([(c,pi\<bullet>a)]@pi)\<bullet>t2)[c::=(pi\<bullet>s2)])"
	using a4 f2 j0 j1 j2 j3 by (simp, blast intro!: eqvt_one)
      have alpha1: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>t1))) = (Lam [(pi\<bullet>a)].(pi\<bullet>t1))" using f1 f3
	by (simp add: lam.inject alpha)
      have alpha2: "(([(c,pi\<bullet>a)]@pi)\<bullet>t2)[c::=(pi\<bullet>s2)] = (pi\<bullet>t2)[(pi\<bullet>a)::=(pi\<bullet>s2)]"
	using f4 by (simp only: subst_rename[symmetric] pt_name2)
      show "P x (App (Lam [(pi\<bullet>a)].(pi\<bullet>t1)) (pi\<bullet>s1)) ((pi\<bullet>t2)[(pi\<bullet>a)::=(pi\<bullet>s2)])"
	using x alpha1 alpha2 by (simp only: pt_name2)
    qed
  qed
  hence "P x (([]::name prm)\<bullet>t) (([]::name prm)\<bullet>s)" by blast
  thus ?thesis by simp
qed

lemma fresh_fact':  
  assumes a: "a\<sharp>t2" 
  shows "a\<sharp>(t1[a::=t2])"
using a 
proof (nominal_induct t1 avoiding: a t2 rule: lam_induct)
  case (Var b) 
  thus ?case by (simp add: fresh_atm)
next
  case App thus ?case by simp
next
  case (Lam c t)
  have "a\<sharp>t2" "c\<sharp>a" "c\<sharp>t2" by fact
  moreover
  have ih: "\<And>a t2. a\<sharp>t2 \<Longrightarrow> a\<sharp>(t[a::=t2])" by fact
  ultimately show ?case by (simp add: abs_fresh)
qed

lemma one_fresh_preserv:
  fixes    t :: "lam"
  and      s :: "lam"
  and      a :: "name"
  assumes a: "t\<longrightarrow>\<^isub>1s"
  and     b: "a\<sharp>t"
  shows "a\<sharp>s"
using a b
proof (induct)
  case o1 thus ?case by simp
next
  case o2 thus ?case by simp
next
  case (o3 c s1 s2)
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

text {* first case in Lemma 3.2.4*}

lemma one_subst_aux:
  fixes    M :: "lam"
  and      N :: "lam"
  and      N':: "lam"
  and      x :: "name"
  assumes a: "N\<longrightarrow>\<^isub>1N'"
  shows "M[x::=N] \<longrightarrow>\<^isub>1 M[x::=N']"
using a
proof (nominal_induct M avoiding: x N N' rule: lam_induct)
  case (Var y) 
  show "Var y[x::=N] \<longrightarrow>\<^isub>1 Var y[x::=N']" by (cases "x=y", auto)
next
  case (App P Q) (* application case - third line *)
  thus "(App P Q)[x::=N] \<longrightarrow>\<^isub>1  (App P Q)[x::=N']" using o2 by simp
next 
  case (Lam y P) (* abstraction case - fourth line *)
  thus "(Lam [y].P)[x::=N] \<longrightarrow>\<^isub>1 (Lam [y].P)[x::=N']" using o3 by simp
qed

lemma one_subst_aux:
  fixes    M :: "lam"
  and      N :: "lam"
  and      N':: "lam"
  and      x :: "name"
  assumes a: "N\<longrightarrow>\<^isub>1N'"
  shows "M[x::=N] \<longrightarrow>\<^isub>1 M[x::=N']"
using a
apply(nominal_induct M avoiding: x N N' rule: lam_induct)
apply(auto simp add: fresh_prod fresh_atm)
done

lemma one_subst: 
  fixes    M :: "lam"
  and      M':: "lam"
  and      N :: "lam"
  and      N':: "lam"
  and      x :: "name"
  assumes a: "M\<longrightarrow>\<^isub>1M'"
  and     b: "N\<longrightarrow>\<^isub>1N'"
  shows "M[x::=N]\<longrightarrow>\<^isub>1M'[x::=N']" 
using prems
proof (nominal_induct M M' avoiding: N N' x rule: one_induct)
  case (o1 M)
  thus ?case by (simp add: one_subst_aux)
next
  case (o2 M1 M2 N1 N2)
  thus ?case by simp
next
  case (o3 a M1 M2)
  thus ?case by simp
next
  case (o4 a M1 M2 N1 N2)
  have e3: "a\<sharp>N1" "a\<sharp>N2" "a\<sharp>N" "a\<sharp>N'" "a\<sharp>x" by fact
  show ?case
  proof -
    have "(App (Lam [a].M1) N1)[x::=N] = App (Lam [a].(M1[x::=N])) (N1[x::=N])" using e3 by simp
    also have "App (Lam [a].(M1[x::=N])) (N1[x::=N]) \<longrightarrow>\<^isub>1 M2[x::=N'][a::=N2[x::=N']]" 
      using  o4 b by force
    also have "M2[x::=N'][a::=N2[x::=N']] = M2[a::=N2][x::=N']" 
      using e3 by (simp add: subs_lemma fresh_atm)
    ultimately show "(App (Lam [a].M1) N1)[x::=N] \<longrightarrow>\<^isub>1 M2[a::=N2][x::=N']" by simp
  qed
qed

lemma one_subst: 
  assumes a: "M\<longrightarrow>\<^isub>1M'" 
  and     b: "N\<longrightarrow>\<^isub>1N'"
  shows "M[x::=N]\<longrightarrow>\<^isub>1M'[x::=N']" 
using a b
apply(nominal_induct M M' avoiding: N N' x rule: one_induct)
apply(auto simp add: one_subst_aux subs_lemma fresh_atm)
done

lemma diamond[rule_format]:
  fixes    M :: "lam"
  and      M1:: "lam"
  assumes a: "M\<longrightarrow>\<^isub>1M1" 
  and     b: "M\<longrightarrow>\<^isub>1M2"
  shows "\<exists>M3. M1\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3"
  using a b
proof (induct fixing: M2)
  case (o1 M) (* case 1 --- M1 = M *)
  thus "\<exists>M3. M\<longrightarrow>\<^isub>1M3 \<and>  M2\<longrightarrow>\<^isub>1M3" by blast
next
  case (o4 x Q Q' P P') (* case 2 --- a beta-reduction occurs*)
  have i1: "\<And>M2. Q \<longrightarrow>\<^isub>1M2 \<Longrightarrow> (\<exists>M3. Q'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)" by fact
  have i2: "\<And>M2. P \<longrightarrow>\<^isub>1M2 \<Longrightarrow> (\<exists>M3. P'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)" by fact
  have "App (Lam [x].P) Q \<longrightarrow>\<^isub>1 M2" by fact
  hence "(\<exists>P' Q'. M2 = App (Lam [x].P') Q' \<and> P\<longrightarrow>\<^isub>1P' \<and> Q\<longrightarrow>\<^isub>1Q') \<or> 
         (\<exists>P' Q'. M2 = P'[x::=Q'] \<and> P\<longrightarrow>\<^isub>1P' \<and> Q\<longrightarrow>\<^isub>1Q')" by (simp add: one_red)
  moreover (* subcase 2.1 *)
  { assume "\<exists>P' Q'. M2 = App (Lam [x].P') Q' \<and> P\<longrightarrow>\<^isub>1P' \<and> Q\<longrightarrow>\<^isub>1Q'"
    then obtain P'' and Q'' where 
      b1: "M2=App (Lam [x].P'') Q''" and b2: "P\<longrightarrow>\<^isub>1P''" and b3: "Q\<longrightarrow>\<^isub>1Q''" by blast
    from b2 i2 have "(\<exists>M3. P'\<longrightarrow>\<^isub>1M3 \<and> P''\<longrightarrow>\<^isub>1M3)" by simp
    then obtain P''' where
      c1: "P'\<longrightarrow>\<^isub>1P'''" and c2: "P''\<longrightarrow>\<^isub>1P'''" by force
    from b3 i1 have "(\<exists>M3. Q'\<longrightarrow>\<^isub>1M3 \<and> Q''\<longrightarrow>\<^isub>1M3)" by simp
    then obtain Q''' where
      d1: "Q'\<longrightarrow>\<^isub>1Q'''" and d2: "Q''\<longrightarrow>\<^isub>1Q'''" by force
    from c1 c2 d1 d2 
    have "P'[x::=Q']\<longrightarrow>\<^isub>1P'''[x::=Q'''] \<and> App (Lam [x].P'') Q'' \<longrightarrow>\<^isub>1 P'''[x::=Q''']" 
      by (force simp add: one_subst)
    hence "\<exists>M3. P'[x::=Q']\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" using b1 by blast
  }
  moreover (* subcase 2.2 *)
  { assume "\<exists>P' Q'. M2 = P'[x::=Q'] \<and> P\<longrightarrow>\<^isub>1P' \<and> Q\<longrightarrow>\<^isub>1Q'"
    then obtain P'' Q'' where
      b1: "M2=P''[x::=Q'']" and b2: "P\<longrightarrow>\<^isub>1P''" and  b3: "Q\<longrightarrow>\<^isub>1Q''" by blast
    from b2 i2 have "(\<exists>M3. P'\<longrightarrow>\<^isub>1M3 \<and> P''\<longrightarrow>\<^isub>1M3)" by simp
    then obtain P''' where
      c1: "P'\<longrightarrow>\<^isub>1P'''" and c2: "P''\<longrightarrow>\<^isub>1P'''" by blast
    from b3 i1 have "(\<exists>M3. Q'\<longrightarrow>\<^isub>1M3 \<and> Q''\<longrightarrow>\<^isub>1M3)" by simp
    then obtain Q''' where
      d1: "Q'\<longrightarrow>\<^isub>1Q'''" and d2: "Q''\<longrightarrow>\<^isub>1Q'''" by blast
    from c1 c2 d1 d2 
    have "P'[x::=Q']\<longrightarrow>\<^isub>1P'''[x::=Q'''] \<and> P''[x::=Q'']\<longrightarrow>\<^isub>1P'''[x::=Q''']" 
      by (force simp add: one_subst)
    hence "\<exists>M3. P'[x::=Q']\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" using b1 by blast
  }
  ultimately show "\<exists>M3. P'[x::=Q']\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" by blast
next
  case (o2 Q Q' P P') (* case 3 *)
  have i0: "P\<longrightarrow>\<^isub>1P'" by fact
  have i1: "\<And>M2. Q \<longrightarrow>\<^isub>1M2 \<Longrightarrow> (\<exists>M3. Q'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)" by fact
  have i2: "\<And>M2. P \<longrightarrow>\<^isub>1M2 \<Longrightarrow> (\<exists>M3. P'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)" by fact
  assume "App P Q \<longrightarrow>\<^isub>1 M2"
  hence "(\<exists>P'' Q''. M2 = App P'' Q'' \<and> P\<longrightarrow>\<^isub>1P'' \<and> Q\<longrightarrow>\<^isub>1Q'') \<or> 
         (\<exists>x P' P'' Q'. P = Lam [x].P' \<and> M2 = P''[x::=Q'] \<and> P'\<longrightarrow>\<^isub>1 P'' \<and> Q\<longrightarrow>\<^isub>1Q')" 
    by (simp add: one_app[simplified])
  moreover (* subcase 3.1 *)
  { assume "\<exists>P'' Q''. M2 = App P'' Q'' \<and> P\<longrightarrow>\<^isub>1P'' \<and> Q\<longrightarrow>\<^isub>1Q''"
    then obtain P'' and Q'' where 
      b1: "M2=App P'' Q''" and b2: "P\<longrightarrow>\<^isub>1P''" and b3: "Q\<longrightarrow>\<^isub>1Q''" by blast
    from b2 i2 have "(\<exists>M3. P'\<longrightarrow>\<^isub>1M3 \<and> P''\<longrightarrow>\<^isub>1M3)" by simp
    then obtain P''' where
      c1: "P'\<longrightarrow>\<^isub>1P'''" and c2: "P''\<longrightarrow>\<^isub>1P'''" by blast
    from b3 i1 have "\<exists>M3. Q'\<longrightarrow>\<^isub>1M3 \<and> Q''\<longrightarrow>\<^isub>1M3" by simp
    then obtain Q''' where
      d1: "Q'\<longrightarrow>\<^isub>1Q'''" and d2: "Q''\<longrightarrow>\<^isub>1Q'''" by blast
    from c1 c2 d1 d2 
    have "App P' Q'\<longrightarrow>\<^isub>1App P''' Q''' \<and> App P'' Q'' \<longrightarrow>\<^isub>1 App P''' Q'''" by blast
    hence "\<exists>M3. App P' Q'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" using b1 by blast
  }
  moreover (* subcase 3.2 *)
  { assume "\<exists>x P1 P'' Q''. P = Lam [x].P1 \<and> M2 = P''[x::=Q''] \<and> P1\<longrightarrow>\<^isub>1 P'' \<and> Q\<longrightarrow>\<^isub>1Q''"
    then obtain x P1 P1'' Q'' where
      b0: "P=Lam [x].P1" and b1: "M2=P1''[x::=Q'']" and 
      b2: "P1\<longrightarrow>\<^isub>1P1''" and  b3: "Q\<longrightarrow>\<^isub>1Q''" by blast
    from b0 i0 have "\<exists>P1'. P'=Lam [x].P1' \<and> P1\<longrightarrow>\<^isub>1P1'" by (simp add: one_abs)
    then obtain P1' where g1: "P'=Lam [x].P1'" and g2: "P1\<longrightarrow>\<^isub>1P1'" by blast 
    from g1 b0 b2 i2 have "(\<exists>M3. (Lam [x].P1')\<longrightarrow>\<^isub>1M3 \<and> (Lam [x].P1'')\<longrightarrow>\<^isub>1M3)" by simp
    then obtain P1''' where
      c1: "(Lam [x].P1')\<longrightarrow>\<^isub>1P1'''" and c2: "(Lam [x].P1'')\<longrightarrow>\<^isub>1P1'''" by blast
    from c1 have "\<exists>R1. P1'''=Lam [x].R1 \<and> P1'\<longrightarrow>\<^isub>1R1" by (simp add: one_abs)
    then obtain R1 where r1: "P1'''=Lam [x].R1" and r2: "P1'\<longrightarrow>\<^isub>1R1" by blast
    from c2 have "\<exists>R2. P1'''=Lam [x].R2 \<and> P1''\<longrightarrow>\<^isub>1R2" by (simp add: one_abs)
    then obtain R2 where r3: "P1'''=Lam [x].R2" and r4: "P1''\<longrightarrow>\<^isub>1R2" by blast
    from r1 r3 have r5: "R1=R2" by (simp add: lam.inject alpha)
    from b3 i1 have "(\<exists>M3. Q'\<longrightarrow>\<^isub>1M3 \<and> Q''\<longrightarrow>\<^isub>1M3)" by simp
    then obtain Q''' where
      d1: "Q'\<longrightarrow>\<^isub>1Q'''" and d2: "Q''\<longrightarrow>\<^isub>1Q'''" by blast
    from g1 r2 d1 r4 r5 d2 
    have "App P' Q'\<longrightarrow>\<^isub>1R1[x::=Q'''] \<and> P1''[x::=Q'']\<longrightarrow>\<^isub>1R1[x::=Q''']" by (simp add: one_subst)
    hence "\<exists>M3. App P' Q'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" using b1 by blast
  }
  ultimately show "\<exists>M3. App P' Q'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" by blast
next
  case (o3 x P P') (* case 4 *)
  have i1: "P\<longrightarrow>\<^isub>1P'" by fact
  have i2: "\<And>M2. P \<longrightarrow>\<^isub>1M2 \<Longrightarrow> (\<exists>M3. P'\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3)" by fact
  have "(Lam [x].P)\<longrightarrow>\<^isub>1 M2" by fact
  hence "\<exists>P''. M2=Lam [x].P'' \<and> P\<longrightarrow>\<^isub>1P''" by (simp add: one_abs)
  then obtain P'' where b1: "M2=Lam [x].P''" and b2: "P\<longrightarrow>\<^isub>1P''" by blast
  from i2 b1 b2 have "\<exists>M3. (Lam [x].P')\<longrightarrow>\<^isub>1M3 \<and> (Lam [x].P'')\<longrightarrow>\<^isub>1M3" by blast
  then obtain M3 where c1: "(Lam [x].P')\<longrightarrow>\<^isub>1M3" and c2: "(Lam [x].P'')\<longrightarrow>\<^isub>1M3" by blast
  from c1 have "\<exists>R1. M3=Lam [x].R1 \<and> P'\<longrightarrow>\<^isub>1R1" by (simp add: one_abs)
  then obtain R1 where r1: "M3=Lam [x].R1" and r2: "P'\<longrightarrow>\<^isub>1R1" by blast
  from c2 have "\<exists>R2. M3=Lam [x].R2 \<and> P''\<longrightarrow>\<^isub>1R2" by (simp add: one_abs)
  then obtain R2 where r3: "M3=Lam [x].R2" and r4: "P''\<longrightarrow>\<^isub>1R2" by blast
  from r1 r3 have r5: "R1=R2" by (simp add: lam.inject alpha)
  from r2 r4 have "(Lam [x].P')\<longrightarrow>\<^isub>1(Lam [x].R1) \<and> (Lam [x].P'')\<longrightarrow>\<^isub>1(Lam [x].R2)" 
    by (simp add: one_subst)
  thus "\<exists>M3. (Lam [x].P')\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1M3" using b1 r5 by blast
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
  show ?thesis using b1 b2 by (force intro: rtrancl_trans)
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
  and     b: "t\<longrightarrow>\<^isub>1t2"
  shows "\<exists>t3. t1\<longrightarrow>\<^isub>1t3 \<and> t2\<longrightarrow>\<^isub>1\<^sup>*t3"
  using a b
proof (induct fixing: t2)
  case 1 thus ?case by force
next
  case (2 s1 s2)
  have b: "s1 \<longrightarrow>\<^isub>1 s2" by fact
  have h: "\<And>t2. t \<longrightarrow>\<^isub>1 t2 \<Longrightarrow> (\<exists>t3. s1 \<longrightarrow>\<^isub>1 t3 \<and> t2 \<longrightarrow>\<^isub>1\<^sup>* t3)" by fact
  have c: "t \<longrightarrow>\<^isub>1 t2" by fact
  show "(\<exists>t3.  s2 \<longrightarrow>\<^isub>1 t3 \<and>  t2 \<longrightarrow>\<^isub>1\<^sup>* t3)" 
  proof -
    from c h have "(\<exists>t3. s1 \<longrightarrow>\<^isub>1 t3 \<and> t2 \<longrightarrow>\<^isub>1\<^sup>* t3)" by force
    then obtain t3 where c1: "s1 \<longrightarrow>\<^isub>1 t3" and c2: "t2 \<longrightarrow>\<^isub>1\<^sup>* t3" by (force)
    have "(\<exists>t4. s2 \<longrightarrow>\<^isub>1 t4 \<and> t3 \<longrightarrow>\<^isub>1 t4)" using b c1 by (force intro: diamond)
    thus ?thesis using c2 by (force intro: rtrancl_trans)
  qed
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

