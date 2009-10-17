theory Weakening 
  imports "../Nominal" 
begin

text {* 
  A simple proof of the Weakening Property in the simply-typed 
  lambda-calculus. The proof is simple, because we can make use
  of the variable convention. *}

atom_decl name 

text {* Terms and Types *}

nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

nominal_datatype ty =
    TVar "string"
  | TArr "ty" "ty" ("_ \<rightarrow> _" [100,100] 100)

lemma ty_fresh:
  fixes x::"name"
  and   T::"ty"
  shows "x\<sharp>T"
by (nominal_induct T rule: ty.strong_induct)
   (auto simp add: fresh_string)

text {* 
  Valid contexts (at the moment we have no type for finite 
  sets yet, therefore typing-contexts are lists). *}

inductive
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
where
    v1[intro]: "valid []"
  | v2[intro]: "\<lbrakk>valid \<Gamma>;x\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((x,T)#\<Gamma>)"

equivariance valid

text{* Typing judgements *}

inductive
  typing :: "(name\<times>ty) list\<Rightarrow>lam\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ : _" [60,60,60] 60) 
where
    t_Var[intro]: "\<lbrakk>valid \<Gamma>; (x,T)\<in>set \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
  | t_App[intro]: "\<lbrakk>\<Gamma> \<turnstile> t1 : T1\<rightarrow>T2; \<Gamma> \<turnstile> t2 : T1\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App t1 t2 : T2"
  | t_Lam[intro]: "\<lbrakk>x\<sharp>\<Gamma>;(x,T1)#\<Gamma> \<turnstile> t : T2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].t : T1\<rightarrow>T2"

text {* 
  We derive the strong induction principle for the typing 
  relation (this induction principle has the variable convention 
  already built-in). *}

equivariance typing
nominal_inductive typing
  by (simp_all add: abs_fresh ty_fresh)

text {* Abbreviation for the notion of subcontexts. *}

abbreviation
  "sub_context" :: "(name\<times>ty) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" ("_ \<subseteq> _" [60,60] 60) 
where
  "\<Gamma>1 \<subseteq> \<Gamma>2 \<equiv> \<forall>x T. (x,T)\<in>set \<Gamma>1 \<longrightarrow> (x,T)\<in>set \<Gamma>2"

text {* Now it comes: The Weakening Lemma *}

text {*
  The first version is, after setting up the induction, 
  completely automatic except for use of atomize. *}

lemma weakening_version1: 
  fixes \<Gamma>1 \<Gamma>2::"(name\<times>ty) list"
  assumes a: "\<Gamma>1 \<turnstile> t : T" 
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<subseteq> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
by (nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing.strong_induct)
   (auto | atomize)+

text {* 
  The second version gives the details for the variable
  and lambda case. *}

lemma weakening_version2: 
  fixes \<Gamma>1 \<Gamma>2::"(name\<times>ty) list"
  and   t ::"lam"
  and   \<tau> ::"ty"
  assumes a: "\<Gamma>1 \<turnstile> t : T"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<subseteq> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
proof (nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing.strong_induct)
  case (t_Var \<Gamma>1 x T)  (* variable case *)
  have "\<Gamma>1 \<subseteq> \<Gamma>2" by fact 
  moreover  
  have "valid \<Gamma>2" by fact 
  moreover 
  have "(x,T)\<in> set \<Gamma>1" by fact
  ultimately show "\<Gamma>2 \<turnstile> Var x : T" by auto
next
  case (t_Lam x \<Gamma>1 T1 t T2) (* lambda case *)
  have vc: "x\<sharp>\<Gamma>2" by fact   (* variable convention *)
  have ih: "\<lbrakk>valid ((x,T1)#\<Gamma>2); (x,T1)#\<Gamma>1 \<subseteq> (x,T1)#\<Gamma>2\<rbrakk> \<Longrightarrow> (x,T1)#\<Gamma>2 \<turnstile> t:T2" by fact
  have "\<Gamma>1 \<subseteq> \<Gamma>2" by fact
  then have "(x,T1)#\<Gamma>1 \<subseteq> (x,T1)#\<Gamma>2" by simp
  moreover
  have "valid \<Gamma>2" by fact
  then have "valid ((x,T1)#\<Gamma>2)" using vc by (simp add: v2)
  ultimately have "(x,T1)#\<Gamma>2 \<turnstile> t : T2" using ih by simp
  with vc show "\<Gamma>2 \<turnstile> Lam [x].t : T1\<rightarrow>T2" by auto
qed (auto) (* app case *)

text{* 
  The original induction principle for the typing relation
  is not strong enough - even this simple lemma fails to be 
  simple ;o) *}

lemma weakening_not_straigh_forward: 
  fixes \<Gamma>1 \<Gamma>2::"(name\<times>ty) list"
  assumes a: "\<Gamma>1 \<turnstile> t : T"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<subseteq> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
proof (induct arbitrary: \<Gamma>2)
  case (t_Var \<Gamma>1 x T) (* variable case still works *)
  have "\<Gamma>1 \<subseteq> \<Gamma>2" by fact
  moreover
  have "valid \<Gamma>2" by fact
  moreover
  have "(x,T) \<in> (set \<Gamma>1)" by fact 
  ultimately show "\<Gamma>2 \<turnstile> Var x : T" by auto
next
  case (t_Lam x \<Gamma>1 T1 t T2) (* lambda case *)
  (* These are all assumptions available in this case*)
  have a0: "x\<sharp>\<Gamma>1" by fact
  have a1: "(x,T1)#\<Gamma>1 \<turnstile> t : T2" by fact
  have a2: "\<Gamma>1 \<subseteq> \<Gamma>2" by fact
  have a3: "valid \<Gamma>2" by fact
  have ih: "\<And>\<Gamma>3. \<lbrakk>valid \<Gamma>3; (x,T1)#\<Gamma>1 \<subseteq> \<Gamma>3\<rbrakk> \<Longrightarrow> \<Gamma>3 \<turnstile> t : T2" by fact
  have "(x,T1)#\<Gamma>1 \<subseteq> (x,T1)#\<Gamma>2" using a2 by simp
  moreover
  have "valid ((x,T1)#\<Gamma>2)" using v2 (* fails *) 
    oops
  
text{* 
  To show that the proof with explicit renaming is not simple, 
  here is the proof without using the variable convention. It
  crucially depends on the equivariance property of the typing
  relation.

*}

lemma weakening_with_explicit_renaming: 
  fixes \<Gamma>1 \<Gamma>2::"(name\<times>ty) list"
  assumes a: "\<Gamma>1 \<turnstile> t : T"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<subseteq> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
proof (induct arbitrary: \<Gamma>2)
  case (t_Lam x \<Gamma>1 T1 t T2) (* lambda case *)
  have fc0: "x\<sharp>\<Gamma>1" by fact
  have ih: "\<And>\<Gamma>3. \<lbrakk>valid \<Gamma>3; (x,T1)#\<Gamma>1 \<subseteq> \<Gamma>3\<rbrakk> \<Longrightarrow> \<Gamma>3 \<turnstile> t : T2" by fact
  obtain c::"name" where fc1: "c\<sharp>(x,t,\<Gamma>1,\<Gamma>2)"  (* we obtain a fresh name *)
    by (rule exists_fresh) (auto simp add: fs_name1)
  have "Lam [c].([(c,x)]\<bullet>t) = Lam [x].t" using fc1 (* we then alpha-rename the lambda-abstraction *)
    by (auto simp add: lam.inject alpha fresh_prod fresh_atm)
  moreover
  have "\<Gamma>2 \<turnstile> Lam [c].([(c,x)]\<bullet>t) : T1 \<rightarrow> T2" (* we can then alpha-rename our original goal *)
  proof - 
    (* we establish (x,T1)#\<Gamma>1 \<subseteq> (x,T1)#([(c,x)]\<bullet>\<Gamma>2) and valid ((x,T1)#([(c,x)]\<bullet>\<Gamma>2)) *)
    have "(x,T1)#\<Gamma>1 \<subseteq> (x,T1)#([(c,x)]\<bullet>\<Gamma>2)" 
    proof -
      have "\<Gamma>1 \<subseteq> \<Gamma>2" by fact
      then have "[(c,x)]\<bullet>((x,T1)#\<Gamma>1 \<subseteq> (x,T1)#([(c,x)]\<bullet>\<Gamma>2))" using fc0 fc1 
        by (perm_simp add: eqvts calc_atm perm_fresh_fresh ty_fresh)
      then show "(x,T1)#\<Gamma>1 \<subseteq> (x,T1)#([(c,x)]\<bullet>\<Gamma>2)" by (rule perm_boolE)
    qed
    moreover 
    have "valid ((x,T1)#([(c,x)]\<bullet>\<Gamma>2))" 
    proof -
      have "valid \<Gamma>2" by fact
      then show "valid ((x,T1)#([(c,x)]\<bullet>\<Gamma>2))" using fc1
        by (auto intro!: v2 simp add: fresh_left calc_atm eqvts)
    qed
    (* these two facts give us by induction hypothesis the following *)
    ultimately have "(x,T1)#([(c,x)]\<bullet>\<Gamma>2) \<turnstile> t : T2" using ih by simp 
    (* we now apply renamings to get to our goal *)
    then have "[(c,x)]\<bullet>((x,T1)#([(c,x)]\<bullet>\<Gamma>2) \<turnstile> t : T2)" by (rule perm_boolI)
    then have "(c,T1)#\<Gamma>2 \<turnstile> ([(c,x)]\<bullet>t) : T2" using fc1 
      by (perm_simp add: eqvts calc_atm perm_fresh_fresh ty_fresh)
    then show "\<Gamma>2 \<turnstile> Lam [c].([(c,x)]\<bullet>t) : T1 \<rightarrow> T2" using fc1 by auto
  qed
  ultimately show "\<Gamma>2 \<turnstile> Lam [x].t : T1 \<rightarrow> T2" by simp
qed (auto) (* var and app cases *)

text {*
  Moral: compare the proof with explicit renamings to weakening_version1 
  and weakening_version2, and imagine you are proving something more substantial 
  than the weakening lemma. *}

end