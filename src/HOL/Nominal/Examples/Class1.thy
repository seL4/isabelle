theory Class1
imports "HOL-Nominal.Nominal"
begin

section \<open>Term-Calculus from Urban's PhD\<close>

atom_decl name coname

text \<open>types\<close>

unbundle no bit_operations_syntax

nominal_datatype ty =
    PR "string"
  | NOT  "ty"
  | AND  "ty" "ty"   (\<open>_ AND _\<close> [100,100] 100)
  | OR   "ty" "ty"   (\<open>_ OR _\<close>  [100,100] 100)
  | IMP  "ty" "ty"   (\<open>_ IMP _\<close> [100,100] 100)

instantiation ty :: size
begin

nominal_primrec size_ty
where
  "size (PR s)     = (1::nat)"
| "size (NOT T)     = 1 + size T"
| "size (T1 AND T2) = 1 + size T1 + size T2"
| "size (T1 OR T2)  = 1 + size T1 + size T2"
| "size (T1 IMP T2) = 1 + size T1 + size T2"
by (rule TrueI)+

instance ..

end

lemma ty_cases:
  fixes T::ty
  shows "(\<exists>s. T=PR s) \<or> (\<exists>T'. T=NOT T') \<or> (\<exists>S U. T=S OR U) \<or> (\<exists>S U. T=S AND U) \<or> (\<exists>S U. T=S IMP U)"
by (induct T rule:ty.induct) (auto)

lemma fresh_ty:
  fixes a::"coname"
  and   x::"name"
  and   T::"ty"
  shows "a\<sharp>T" and "x\<sharp>T"
by (nominal_induct T rule: ty.strong_induct)
   (auto simp: fresh_string)

text \<open>terms\<close>                               

nominal_datatype trm = 
    Ax   "name" "coname"
  | Cut  "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm"            (\<open>Cut <_>._ ('(_'))._\<close> [0,0,0,100] 101)
  | NotR "\<guillemotleft>name\<guillemotright>trm" "coname"                 (\<open>NotR ('(_'))._ _\<close> [0,100,100] 101)
  | NotL "\<guillemotleft>coname\<guillemotright>trm" "name"                 (\<open>NotL <_>._ _\<close> [0,100,100] 101)
  | AndR "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>coname\<guillemotright>trm" "coname" (\<open>AndR <_>._ <_>._ _\<close> [0,100,0,100,100] 101)
  | AndL1 "\<guillemotleft>name\<guillemotright>trm" "name"                  (\<open>AndL1 (_)._ _\<close> [100,100,100] 101)
  | AndL2 "\<guillemotleft>name\<guillemotright>trm" "name"                  (\<open>AndL2 (_)._ _\<close> [100,100,100] 101)
  | OrR1 "\<guillemotleft>coname\<guillemotright>trm" "coname"               (\<open>OrR1 <_>._ _\<close> [100,100,100] 101)
  | OrR2 "\<guillemotleft>coname\<guillemotright>trm" "coname"               (\<open>OrR2 <_>._ _\<close> [100,100,100] 101)
  | OrL "\<guillemotleft>name\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"        (\<open>OrL (_)._ (_)._ _\<close> [100,100,100,100,100] 101)
  | ImpR "\<guillemotleft>name\<guillemotright>(\<guillemotleft>coname\<guillemotright>trm)" "coname"       (\<open>ImpR (_).<_>._ _\<close> [100,100,100,100] 101)
  | ImpL "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"     (\<open>ImpL <_>._ (_)._ _\<close> [100,100,100,100,100] 101)

text \<open>named terms\<close>

nominal_datatype ntrm = Na "\<guillemotleft>name\<guillemotright>trm" (\<open>((_):_)\<close> [100,100] 100)

text \<open>conamed terms\<close>

nominal_datatype ctrm = Co "\<guillemotleft>coname\<guillemotright>trm" (\<open>(<_>:_)\<close> [100,100] 100)

text \<open>renaming functions\<close>

nominal_primrec (freshness_context: "(d::coname,e::coname)") 
  crename :: "trm \<Rightarrow> coname \<Rightarrow> coname \<Rightarrow> trm"  (\<open>_[_\<turnstile>c>_]\<close> [100,0,0] 100) 
where
  "(Ax x a)[d\<turnstile>c>e] = (if a=d then Ax x e else Ax x a)" 
| "\<lbrakk>a\<sharp>(d,e,N);x\<sharp>M\<rbrakk> \<Longrightarrow> (Cut <a>.M (x).N)[d\<turnstile>c>e] = Cut <a>.(M[d\<turnstile>c>e]) (x).(N[d\<turnstile>c>e])" 
| "(NotR (x).M a)[d\<turnstile>c>e] = (if a=d then NotR (x).(M[d\<turnstile>c>e]) e else NotR (x).(M[d\<turnstile>c>e]) a)" 
| "a\<sharp>(d,e) \<Longrightarrow> (NotL <a>.M x)[d\<turnstile>c>e] = (NotL <a>.(M[d\<turnstile>c>e]) x)" 
| "\<lbrakk>a\<sharp>(d,e,N,c);b\<sharp>(d,e,M,c);b\<noteq>a\<rbrakk> \<Longrightarrow> (AndR <a>.M <b>.N c)[d\<turnstile>c>e] = 
          (if c=d then AndR <a>.(M[d\<turnstile>c>e]) <b>.(N[d \<turnstile>c>e]) e else AndR <a>.(M[d\<turnstile>c>e]) <b>.(N[d\<turnstile>c>e]) c)" 
| "x\<sharp>y \<Longrightarrow> (AndL1 (x).M y)[d\<turnstile>c>e] = AndL1 (x).(M[d\<turnstile>c>e]) y"
| "x\<sharp>y \<Longrightarrow> (AndL2 (x).M y)[d\<turnstile>c>e] = AndL2 (x).(M[d\<turnstile>c>e]) y"
| "a\<sharp>(d,e,b) \<Longrightarrow> (OrR1 <a>.M b)[d\<turnstile>c>e] = (if b=d then OrR1 <a>.(M[d\<turnstile>c>e]) e else OrR1 <a>.(M[d\<turnstile>c>e]) b)"
| "a\<sharp>(d,e,b) \<Longrightarrow> (OrR2 <a>.M b)[d\<turnstile>c>e] = (if b=d then OrR2 <a>.(M[d\<turnstile>c>e]) e else OrR2 <a>.(M[d\<turnstile>c>e]) b)"
| "\<lbrakk>x\<sharp>(N,z);y\<sharp>(M,z);y\<noteq>x\<rbrakk> \<Longrightarrow> (OrL (x).M (y).N z)[d\<turnstile>c>e] = OrL (x).(M[d\<turnstile>c>e]) (y).(N[d\<turnstile>c>e]) z"
| "a\<sharp>(d,e,b) \<Longrightarrow> (ImpR (x).<a>.M b)[d\<turnstile>c>e] = 
       (if b=d then ImpR (x).<a>.(M[d\<turnstile>c>e]) e else ImpR (x).<a>.(M[d\<turnstile>c>e]) b)"
| "\<lbrakk>a\<sharp>(d,e,N);x\<sharp>(M,y)\<rbrakk> \<Longrightarrow> (ImpL <a>.M (x).N y)[d\<turnstile>c>e] = ImpL <a>.(M[d\<turnstile>c>e]) (x).(N[d\<turnstile>c>e]) y"
  by(finite_guess | simp add: abs_fresh abs_supp fin_supp | fresh_guess)+

nominal_primrec (freshness_context: "(u::name,v::name)") 
  nrename :: "trm \<Rightarrow> name \<Rightarrow> name \<Rightarrow> trm"      (\<open>_[_\<turnstile>n>_]\<close> [100,0,0] 100) 
where
  "(Ax x a)[u\<turnstile>n>v] = (if x=u then Ax v a else Ax x a)" 
| "\<lbrakk>a\<sharp>N;x\<sharp>(u,v,M)\<rbrakk> \<Longrightarrow> (Cut <a>.M (x).N)[u\<turnstile>n>v] = Cut <a>.(M[u\<turnstile>n>v]) (x).(N[u\<turnstile>n>v])" 
| "x\<sharp>(u,v) \<Longrightarrow> (NotR (x).M a)[u\<turnstile>n>v] = NotR (x).(M[u\<turnstile>n>v]) a" 
| "(NotL <a>.M x)[u\<turnstile>n>v] = (if x=u then NotL <a>.(M[u\<turnstile>n>v]) v else NotL <a>.(M[u\<turnstile>n>v]) x)" 
| "\<lbrakk>a\<sharp>(N,c);b\<sharp>(M,c);b\<noteq>a\<rbrakk> \<Longrightarrow> (AndR <a>.M <b>.N c)[u\<turnstile>n>v] = AndR <a>.(M[u\<turnstile>n>v]) <b>.(N[u\<turnstile>n>v]) c" 
| "x\<sharp>(u,v,y) \<Longrightarrow> (AndL1 (x).M y)[u\<turnstile>n>v] = (if y=u then AndL1 (x).(M[u\<turnstile>n>v]) v else AndL1 (x).(M[u\<turnstile>n>v]) y)"
| "x\<sharp>(u,v,y) \<Longrightarrow> (AndL2 (x).M y)[u\<turnstile>n>v] = (if y=u then AndL2 (x).(M[u\<turnstile>n>v]) v else AndL2 (x).(M[u\<turnstile>n>v]) y)"
| "a\<sharp>b \<Longrightarrow> (OrR1 <a>.M b)[u\<turnstile>n>v] = OrR1 <a>.(M[u\<turnstile>n>v]) b"
| "a\<sharp>b \<Longrightarrow> (OrR2 <a>.M b)[u\<turnstile>n>v] = OrR2 <a>.(M[u\<turnstile>n>v]) b"
| "\<lbrakk>x\<sharp>(u,v,N,z);y\<sharp>(u,v,M,z);y\<noteq>x\<rbrakk> \<Longrightarrow> (OrL (x).M (y).N z)[u\<turnstile>n>v] = 
        (if z=u then OrL (x).(M[u\<turnstile>n>v]) (y).(N[u\<turnstile>n>v]) v else OrL (x).(M[u\<turnstile>n>v]) (y).(N[u\<turnstile>n>v]) z)"
| "\<lbrakk>a\<sharp>b; x\<sharp>(u,v)\<rbrakk> \<Longrightarrow> (ImpR (x).<a>.M b)[u\<turnstile>n>v] = ImpR (x).<a>.(M[u\<turnstile>n>v]) b"
| "\<lbrakk>a\<sharp>N;x\<sharp>(u,v,M,y)\<rbrakk> \<Longrightarrow> (ImpL <a>.M (x).N y)[u\<turnstile>n>v] = 
        (if y=u then ImpL <a>.(M[u\<turnstile>n>v]) (x).(N[u\<turnstile>n>v]) v else ImpL <a>.(M[u\<turnstile>n>v]) (x).(N[u\<turnstile>n>v]) y)"
  by(finite_guess | simp add: abs_fresh abs_supp fin_supp | fresh_guess)+

lemmas eq_bij = pt_bij[OF pt_name_inst, OF at_name_inst] pt_bij[OF pt_coname_inst, OF at_coname_inst]

lemma crename_name_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(M[d\<turnstile>c>e]) = (pi\<bullet>M)[(pi\<bullet>d)\<turnstile>c>(pi\<bullet>e)]"
  by (nominal_induct M avoiding: d e rule: trm.strong_induct) (auto simp: fresh_bij eq_bij)

lemma crename_coname_eqvt[eqvt]:
  fixes pi::"coname prm"
  shows "pi\<bullet>(M[d\<turnstile>c>e]) = (pi\<bullet>M)[(pi\<bullet>d)\<turnstile>c>(pi\<bullet>e)]"
  by (nominal_induct M avoiding: d e rule: trm.strong_induct)(auto simp: fresh_bij eq_bij)

lemma nrename_name_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(M[x\<turnstile>n>y]) = (pi\<bullet>M)[(pi\<bullet>x)\<turnstile>n>(pi\<bullet>y)]"
  by(nominal_induct M avoiding: x y rule: trm.strong_induct) (auto simp: fresh_bij eq_bij)

lemma nrename_coname_eqvt[eqvt]:
  fixes pi::"coname prm"
  shows "pi\<bullet>(M[x\<turnstile>n>y]) = (pi\<bullet>M)[(pi\<bullet>x)\<turnstile>n>(pi\<bullet>y)]"
  by(nominal_induct M avoiding: x y rule: trm.strong_induct)(auto simp: fresh_bij eq_bij)

lemmas rename_eqvts = crename_name_eqvt crename_coname_eqvt
                      nrename_name_eqvt nrename_coname_eqvt
lemma nrename_fresh:
  assumes a: "x\<sharp>M"
  shows "M[x\<turnstile>n>y] = M"
using a
by (nominal_induct M avoiding: x y rule: trm.strong_induct)
   (auto simp: trm.inject fresh_atm abs_fresh fin_supp abs_supp)

lemma crename_fresh:
  assumes a: "a\<sharp>M"
  shows "M[a\<turnstile>c>b] = M"
using a
by (nominal_induct M avoiding: a b rule: trm.strong_induct)
   (auto simp: trm.inject fresh_atm abs_fresh)

lemma nrename_nfresh:
  fixes x::"name"
  shows "x\<sharp>y\<Longrightarrow>x\<sharp>M[x\<turnstile>n>y]"
by (nominal_induct M avoiding: x y rule: trm.strong_induct)
   (auto simp: fresh_atm abs_fresh abs_supp fin_supp)

 lemma crename_nfresh:
  fixes x::"name"
  shows "x\<sharp>M\<Longrightarrow>x\<sharp>M[a\<turnstile>c>b]"
by (nominal_induct M avoiding: a b rule: trm.strong_induct)
   (auto simp: fresh_atm abs_fresh abs_supp fin_supp)

lemma crename_cfresh:
  fixes a::"coname"
  shows "a\<sharp>b\<Longrightarrow>a\<sharp>M[a\<turnstile>c>b]"
by (nominal_induct M avoiding: a b rule: trm.strong_induct)
   (auto simp: fresh_atm abs_fresh abs_supp fin_supp)

lemma nrename_cfresh:
  fixes c::"coname"
  shows "c\<sharp>M\<Longrightarrow>c\<sharp>M[x\<turnstile>n>y]"
by (nominal_induct M avoiding: x y rule: trm.strong_induct)
   (auto simp: fresh_atm abs_fresh abs_supp fin_supp)

lemma nrename_nfresh':
  fixes x::"name"
  shows "x\<sharp>(M,z,y)\<Longrightarrow>x\<sharp>M[z\<turnstile>n>y]"
by (nominal_induct M avoiding: x z y rule: trm.strong_induct)
   (auto simp: fresh_prod fresh_atm abs_fresh abs_supp fin_supp)

lemma crename_cfresh':
  fixes a::"coname"
  shows "a\<sharp>(M,b,c)\<Longrightarrow>a\<sharp>M[b\<turnstile>c>c]"
by (nominal_induct M avoiding: a b c rule: trm.strong_induct)
   (auto simp: fresh_prod fresh_atm abs_fresh abs_supp fin_supp)

lemma nrename_rename:
  assumes a: "x'\<sharp>M"
  shows "([(x',x)]\<bullet>M)[x'\<turnstile>n>y]= M[x\<turnstile>n>y]"
using a
proof (nominal_induct M avoiding: x x' y rule: trm.strong_induct)
qed (auto simp: abs_fresh abs_supp fin_supp fresh_left calc_atm fresh_atm)

lemma crename_rename:
  assumes a: "a'\<sharp>M"
  shows "([(a',a)]\<bullet>M)[a'\<turnstile>c>b]= M[a\<turnstile>c>b]"
using a
proof (nominal_induct M avoiding: a a' b rule: trm.strong_induct)
qed (auto simp: abs_fresh abs_supp fin_supp fresh_left calc_atm fresh_atm)

lemmas rename_fresh = nrename_fresh crename_fresh 
                      nrename_nfresh crename_nfresh crename_cfresh nrename_cfresh
                      nrename_nfresh' crename_cfresh'
                      nrename_rename crename_rename

lemma better_nrename_Cut:
  assumes a: "x\<sharp>(u,v)"
  shows "(Cut <a>.M (x).N)[u\<turnstile>n>v] = Cut <a>.(M[u\<turnstile>n>v]) (x).(N[u\<turnstile>n>v])"
proof -
  obtain x'::"name"   where fs1: "x'\<sharp>(M,N,a,x,u,v)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a,x,u,v)" by (rule exists_fresh(2), rule fin_supp, blast)
  have eq1: "(Cut <a>.M (x).N) = (Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N))"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  have "(Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N))[u\<turnstile>n>v] = 
                        Cut <a'>.(([(a',a)]\<bullet>M)[u\<turnstile>n>v]) (x').(([(x',x)]\<bullet>N)[u\<turnstile>n>v])"
    using fs1 fs2
    by (intro nrename.simps; simp add: fresh_left calc_atm)
  also have "\<dots> = Cut <a>.(M[u\<turnstile>n>v]) (x).(N[u\<turnstile>n>v])" using fs1 fs2 a
    by(simp add: trm.inject alpha fresh_prod rename_eqvts calc_atm rename_fresh fresh_atm)
  finally show "(Cut <a>.M (x).N)[u\<turnstile>n>v] = Cut <a>.(M[u\<turnstile>n>v]) (x).(N[u\<turnstile>n>v])" using eq1
    by simp
qed

lemma better_crename_Cut:
  assumes a: "a\<sharp>(b,c)"
  shows "(Cut <a>.M (x).N)[b\<turnstile>c>c] = Cut <a>.(M[b\<turnstile>c>c]) (x).(N[b\<turnstile>c>c])"
proof -
  obtain x'::"name"   where fs1: "x'\<sharp>(M,N,a,x,b,c)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a,x,b,c)" by (rule exists_fresh(2), rule fin_supp, blast)
  have eq1: "(Cut <a>.M (x).N) = (Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N))"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  have "(Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N))[b\<turnstile>c>c] = 
                        Cut <a'>.(([(a',a)]\<bullet>M)[b\<turnstile>c>c]) (x').(([(x',x)]\<bullet>N)[b\<turnstile>c>c])"
    using fs1 fs2
    by (intro crename.simps; simp add: fresh_left calc_atm)
  also have "\<dots> = Cut <a>.(M[b\<turnstile>c>c]) (x).(N[b\<turnstile>c>c])" using fs1 fs2 a
    by(simp add: trm.inject alpha calc_atm rename_fresh fresh_atm fresh_prod rename_eqvts)
  finally show "(Cut <a>.M (x).N)[b\<turnstile>c>c] = Cut <a>.(M[b\<turnstile>c>c]) (x).(N[b\<turnstile>c>c])" using eq1
    by simp
qed

lemma crename_id:
  shows "M[a\<turnstile>c>a] = M"
by (nominal_induct M avoiding: a rule: trm.strong_induct) (auto)

lemma nrename_id:
  shows "M[x\<turnstile>n>x] = M"
by (nominal_induct M avoiding: x rule: trm.strong_induct) (auto)

lemma nrename_swap:
  shows "x\<sharp>M \<Longrightarrow> [(x,y)]\<bullet>M = M[y\<turnstile>n>x]"
by (nominal_induct M avoiding: x y rule: trm.strong_induct) 
   (auto simp: abs_fresh abs_supp fin_supp fresh_left calc_atm fresh_atm)


lemma crename_swap:
  shows "a\<sharp>M \<Longrightarrow> [(a,b)]\<bullet>M = M[b\<turnstile>c>a]"
by (nominal_induct M avoiding: a b rule: trm.strong_induct) 
   (auto simp: abs_fresh abs_supp fin_supp fresh_left calc_atm fresh_atm)


lemma crename_ax:
  assumes a: "M[a\<turnstile>c>b] = Ax x c" "c\<noteq>a" "c\<noteq>b"
  shows "M = Ax x c"
using a
proof (nominal_induct M avoiding: a b x c rule: trm.strong_induct)
qed (simp_all add: trm.inject split: if_splits)

lemma nrename_ax:
  assumes a: "M[x\<turnstile>n>y] = Ax z a" "z\<noteq>x" "z\<noteq>y"
  shows "M = Ax z a"
using a
proof (nominal_induct M avoiding: x y z a rule: trm.strong_induct)
qed (simp_all add: trm.inject split: if_splits)

text \<open>substitution functions\<close>

lemma fresh_perm_coname:
  fixes c::"coname"
  and   pi::"coname prm"
  and   M::"trm"
  assumes a: "c\<sharp>pi" "c\<sharp>M"
  shows "c\<sharp>(pi\<bullet>M)"
  by (simp add: assms fresh_perm_app)

lemma fresh_perm_name:
  fixes x::"name"
  and   pi::"name prm"
  and   M::"trm"
  assumes a: "x\<sharp>pi" "x\<sharp>M"
  shows "x\<sharp>(pi\<bullet>M)"
  by (simp add: assms fresh_perm_app)

lemma fresh_fun_simp_NotL:
  assumes a: "x'\<sharp>P" "x'\<sharp>M"
  shows "fresh_fun (\<lambda>x'. Cut <c>.P (x').NotL <a>.M x') = Cut <c>.P (x').NotL <a>.M x'"
proof (rule fresh_fun_app)
  show "pt (TYPE(trm)::trm itself) (TYPE(name)::name itself)"
    by(rule pt_name_inst)
  show "at (TYPE(name)::name itself)"
    by(rule at_name_inst)
  show "finite (supp (\<lambda>x'. Cut <c>.P (x').NotL <a>.M x')::name set)"
    using a by(finite_guess)
  obtain n::name where n: "n\<sharp>(c,P,a,M)"
    by (metis assms fresh_atm(3) fresh_prod)
  with assms have "n \<sharp> (\<lambda>x'. Cut <c>.P (x').NotL <a>.M x')"
    by (fresh_guess)
  then show "\<exists>b. b \<sharp> (\<lambda>x'. Cut <c>.P (x').NotL <a>.M x', Cut <c>.P (b).NotL <a>.M b)"
    by (metis abs_fresh(1) abs_fresh(5) fresh_prod n trm.fresh(3))
  show "x' \<sharp> (\<lambda>x'. Cut <c>.P (x').NotL <a>.M x')"
    using assms by(fresh_guess)
qed

lemma fresh_fun_NotL[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>x'. Cut <c>.P (x').NotL <a>.M x')=
             fresh_fun (pi1\<bullet>(\<lambda>x'. Cut <c>.P (x').NotL <a>.M x'))"
  and   "pi2\<bullet>fresh_fun (\<lambda>x'. Cut <c>.P (x').NotL <a>.M x')=
             fresh_fun (pi2\<bullet>(\<lambda>x'. Cut <c>.P (x').NotL <a>.M x'))"
   apply(perm_simp)
   apply(generate_fresh "name")
   apply(auto simp: fresh_prod fresh_fun_simp_NotL)
  apply (metis fresh_bij(1) fresh_fun_simp_NotL name_prm_coname_def)
  apply(perm_simp)
  apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,pi2\<bullet>P,pi2\<bullet>M,pi2)")
   apply (metis fresh_fun_simp_NotL fresh_prodD swap_simps(8) trm.perm(14) trm.perm(16))
  by (meson exists_fresh(1) fs_name1)

lemma fresh_fun_simp_AndL1:
  assumes a: "z'\<sharp>P" "z'\<sharp>M" "z'\<sharp>x"
  shows "fresh_fun (\<lambda>z'. Cut <c>.P(z').AndL1 (x).M z') = Cut <c>.P (z').AndL1 (x).M z'"
proof (rule fresh_fun_app [OF pt_name_inst at_name_inst])
  obtain n::name where "n\<sharp>(c,P,x,M)"
    by (meson exists_fresh(1) fs_name1)
  then show "\<exists>a. a \<sharp> (\<lambda>z'. Cut <c>.P(z').AndL1 x. M z', Cut <c>.P(a).AndL1 x. M a)"
    apply(intro exI [where x="n"])
    apply(simp add: fresh_prod abs_fresh)
    apply(fresh_guess)
    done
next
  show "z' \<sharp> (\<lambda>z'. Cut <c>.P(z').AndL1 x. M z')"
    using a by(fresh_guess)
qed finite_guess

lemma fresh_fun_AndL1[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL1 (x).M z')=
             fresh_fun (pi1\<bullet>(\<lambda>z'. Cut <c>.P (z').AndL1 (x).M z'))"
  and   "pi2\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL1 (x).M z')=
             fresh_fun (pi2\<bullet>(\<lambda>z'. Cut <c>.P (z').AndL1 (x).M z'))"
apply(perm_simp)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,x,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>x,pi1)")
apply(force simp add: fresh_prod fresh_fun_simp_AndL1 at_prm_fresh[OF at_name_inst] swap_simps)
  apply (meson exists_fresh(1) fs_name1)
apply(perm_simp)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,x,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>x,pi2)")
apply(force simp add: fresh_prod fresh_fun_simp_AndL1 calc_atm)
  by (meson exists_fresh'(1) fs_name1)

lemma fresh_fun_simp_AndL2:
  assumes a: "z'\<sharp>P" "z'\<sharp>M" "z'\<sharp>x"
  shows "fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL2 (x).M z') = Cut <c>.P (z').AndL2 (x).M z'"
proof (rule fresh_fun_app [OF pt_name_inst at_name_inst])
  obtain n::name where "n\<sharp>(c,P,x,M)"
    by (meson exists_fresh(1) fs_name1)
  then show "\<exists>a. a \<sharp> (\<lambda>z'. Cut <c>.P(z').AndL2 x. M z', Cut <c>.P(a).AndL2 x. M a)"
    apply(intro exI [where x="n"])
    apply(simp add: fresh_prod abs_fresh)
    apply(fresh_guess)
    done
next
  show "z' \<sharp> (\<lambda>z'. Cut <c>.P(z').AndL2 x. M z')"
    using a by(fresh_guess)           
qed finite_guess

lemma fresh_fun_AndL2[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL2 (x).M z')=
             fresh_fun (pi1\<bullet>(\<lambda>z'. Cut <c>.P (z').AndL2 (x).M z'))"
  and   "pi2\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL2 (x).M z')=
             fresh_fun (pi2\<bullet>(\<lambda>z'. Cut <c>.P (z').AndL2 (x).M z'))"
   apply(perm_simp)
   apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,x,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>x,pi1)")
    apply(force simp add: fresh_prod fresh_fun_simp_AndL2 at_prm_fresh[OF at_name_inst] swap_simps)
   apply (meson exists_fresh(1) fs_name1)
  apply(perm_simp)
  apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,x,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>x,pi2)")
   apply(force simp add: fresh_prod fresh_fun_simp_AndL2 calc_atm)
  by (meson exists_fresh(1) fs_name1)

lemma fresh_fun_simp_OrL:
  assumes a: "z'\<sharp>P" "z'\<sharp>M" "z'\<sharp>N" "z'\<sharp>u" "z'\<sharp>x"
  shows "fresh_fun (\<lambda>z'. Cut <c>.P(z').OrL(x).M(u).N z') = Cut <c>.P (z').OrL (x).M (u).N z'"
proof (rule fresh_fun_app [OF pt_name_inst at_name_inst])
  obtain n::name where "n\<sharp>(c,P,x,M,u,N)"
    by (meson exists_fresh(1) fs_name1)
  then show "\<exists>a. a \<sharp> (\<lambda>z'. Cut <c>.P(z').OrL(x).M(u).N(z'), Cut <c>.P(a).OrL(x).M(u).N(a))"
    apply(intro exI [where x="n"])
    apply(simp add: fresh_prod abs_fresh)
    apply(fresh_guess)
    done
next
  show "z' \<sharp> (\<lambda>z'. Cut <c>.P(z').OrL(x).M(u).N(z'))"
    using a by(fresh_guess) 
qed finite_guess

lemma fresh_fun_OrL[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P(z').OrL (x).M(u).N z')=
             fresh_fun (pi1\<bullet>(\<lambda>z'. Cut <c>.P (z').OrL(x).M (u).N z'))"
  and   "pi2\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P(z').OrL (x).M(u).N z')=
             fresh_fun (pi2\<bullet>(\<lambda>z'. Cut <c>.P(z').OrL(x).M(u).N z'))"
   apply(perm_simp)
   apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,N,x,u,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>N,pi1\<bullet>x,pi1\<bullet>u,pi1)")
    apply(force simp add: fresh_prod fresh_fun_simp_OrL at_prm_fresh[OF at_name_inst] swap_simps)
   apply (meson exists_fresh(1) fs_name1)
  apply(perm_simp)
  apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,N,x,u,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>N,pi2\<bullet>x,pi2\<bullet>u,pi2)")
   apply(force simp add: fresh_prod fresh_fun_simp_OrL calc_atm)
  by (meson exists_fresh(1) fs_name1)

lemma fresh_fun_simp_ImpL:
  assumes a: "z'\<sharp>P" "z'\<sharp>M" "z'\<sharp>N" "z'\<sharp>x"
  shows "fresh_fun (\<lambda>z'. Cut <c>.P (z').ImpL <a>.M (x).N z') = Cut <c>.P (z').ImpL <a>.M (x).N z'"
proof (rule fresh_fun_app [OF pt_name_inst at_name_inst])
  obtain n::name where "n\<sharp>(c,P,x,M,N)"
    by (meson exists_fresh(1) fs_name1)
  then show "\<exists>aa. aa \<sharp> (\<lambda>z'. Cut <c>.P(z').ImpL <a>.M(x).N z', Cut <c>.P(aa).ImpL <a>.M(x).N aa)"
    apply(intro exI [where x="n"])
    apply(simp add: fresh_prod abs_fresh)
    apply(fresh_guess)
    done
next
  show "z' \<sharp> (\<lambda>z'. Cut <c>.P(z').ImpL <a>.M(x).N z')"
    using a by(fresh_guess) 
qed finite_guess

lemma fresh_fun_ImpL[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').ImpL <a>.M (x).N z')=
             fresh_fun (pi1\<bullet>(\<lambda>z'. Cut <c>.P (z').ImpL <a>.M (x).N z'))"
  and   "pi2\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').ImpL <a>.M (x).N z')=
             fresh_fun (pi2\<bullet>(\<lambda>z'. Cut <c>.P (z').ImpL <a>.M (x).N z'))"
   apply(perm_simp)
   apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,N,x,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>N,pi1\<bullet>x,pi1)")
    apply(force simp add: fresh_prod fresh_fun_simp_ImpL at_prm_fresh[OF at_name_inst] swap_simps)
   apply (meson exists_fresh(1) fs_name1)
  apply(perm_simp)
  apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,N,x,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>N,pi2\<bullet>x,pi2)")
   apply(force simp add: fresh_prod fresh_fun_simp_ImpL calc_atm)
  by (meson exists_fresh(1) fs_name1)

lemma fresh_fun_simp_NotR:
  assumes a: "a'\<sharp>P" "a'\<sharp>M"
  shows "fresh_fun (\<lambda>a'. Cut <a'>.(NotR (y).M a') (x).P) = Cut <a'>.(NotR (y).M a') (x).P"
proof (rule fresh_fun_app [OF pt_coname_inst at_coname_inst])
  obtain n::coname where "n\<sharp>(x,P,y,M)"
    by (metis assms(1) assms(2) fresh_atm(4) fresh_prod)
  then show "\<exists>a. a \<sharp> (\<lambda>a'. Cut <a'>.(NotR (y).M a') (x).P, Cut <a>.NotR(y).M(a) (x).P)"
    apply(intro exI [where x="n"])
    apply(simp add: fresh_prod abs_fresh)
    apply(fresh_guess)
    done
qed (use a in \<open>fresh_guess|finite_guess\<close>)+

lemma fresh_fun_NotR[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(NotR (y).M a') (x).P)=
             fresh_fun (pi1\<bullet>(\<lambda>a'. Cut <a'>.(NotR (y).M a') (x).P))"
  and   "pi2\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(NotR (y).M a') (x).P)=
             fresh_fun (pi2\<bullet>(\<lambda>a'. Cut <a'>.(NotR (y).M a') (x).P))"
   apply(perm_simp)
   apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,pi1\<bullet>P,pi1\<bullet>M,pi1)")
    apply(force simp add: fresh_prod fresh_fun_simp_NotR calc_atm)
   apply (meson exists_fresh(2) fs_coname1)
  apply(perm_simp)
  apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,pi2\<bullet>P,pi2\<bullet>M,pi2)")
   apply(force simp: fresh_prod fresh_fun_simp_NotR at_prm_fresh[OF at_coname_inst] swap_simps)
  by (meson exists_fresh(2) fs_coname1)

lemma fresh_fun_simp_AndR:
  assumes a: "a'\<sharp>P" "a'\<sharp>M" "a'\<sharp>N" "a'\<sharp>b" "a'\<sharp>c"
  shows "fresh_fun (\<lambda>a'. Cut <a'>.(AndR <b>.M <c>.N a') (x).P) = Cut <a'>.(AndR <b>.M <c>.N a') (x).P"
proof (rule fresh_fun_app [OF pt_coname_inst at_coname_inst])
  obtain n::coname where "n\<sharp>(x,P,b,M,c,N)"
    by (meson exists_fresh(2) fs_coname1)
  then show "\<exists>a. a \<sharp> (\<lambda>a'. Cut <a'>.AndR <b>.M <c>.N(a') (x).P, Cut <a>.AndR <b>.M <c>.N(a) (x).P)"
    apply(intro exI [where x="n"])
    apply(simp add: fresh_prod abs_fresh)
    apply(fresh_guess)
    done
qed (use a in \<open>fresh_guess|finite_guess\<close>)+

lemma fresh_fun_AndR[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(AndR <b>.M <c>.N a') (x).P)=
             fresh_fun (pi1\<bullet>(\<lambda>a'. Cut <a'>.(AndR <b>.M <c>.N a') (x).P))"
  and   "pi2\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(AndR <b>.M <c>.N a') (x).P)=
             fresh_fun (pi2\<bullet>(\<lambda>a'. Cut <a'>.(AndR <b>.M <c>.N a') (x).P))"
   apply(perm_simp)
   apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,N,b,c,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>N,pi1\<bullet>b,pi1\<bullet>c,pi1)")
    apply(force simp add: fresh_prod fresh_fun_simp_AndR calc_atm)
   apply (meson exists_fresh(2) fs_coname1)
  apply(perm_simp)
  apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,N,b,c,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>N,pi2\<bullet>b,pi2\<bullet>c,pi2)")
   apply(force simp add: fresh_prod fresh_fun_simp_AndR at_prm_fresh[OF at_coname_inst] swap_simps)
  by (meson exists_fresh(2) fs_coname1)

lemma fresh_fun_simp_OrR1:
  assumes a: "a'\<sharp>P" "a'\<sharp>M" "a'\<sharp>b" 
  shows "fresh_fun (\<lambda>a'. Cut <a'>.(OrR1 <b>.M a') (x).P) = Cut <a'>.(OrR1 <b>.M a') (x).P"
proof (rule fresh_fun_app [OF pt_coname_inst at_coname_inst])
  obtain n::coname where "n\<sharp>(x,P,b,M)"
    by (meson exists_fresh(2) fs_coname1)
  then show "\<exists>a. a \<sharp> (\<lambda>a'. Cut <a'>.OrR1 <b>.M(a') (x).P, Cut <a>.OrR1 <b>.M(a) (x).P)"
    apply(intro exI [where x="n"])
    apply(simp add: fresh_prod abs_fresh)
    apply(fresh_guess)
    done
qed (use a in \<open>fresh_guess|finite_guess\<close>)+

lemma fresh_fun_OrR1[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(OrR1 <b>.M a') (x).P) =
             fresh_fun (pi1\<bullet>(\<lambda>a'. Cut <a'>.(OrR1 <b>.M  a') (x).P))" (is "?t1")
  and   "pi2\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(OrR1 <b>.M a') (x).P) =
             fresh_fun (pi2\<bullet>(\<lambda>a'. Cut <a'>.(OrR1 <b>.M a') (x).P))"  (is "?t2")
proof -
  obtain n::coname where "n\<sharp>(P,M,b,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>b,pi1)"
    by (meson exists_fresh(2) fs_coname1)
  then show ?t1
    by perm_simp (force simp add: fresh_prod fresh_fun_simp_OrR1 calc_atm)
  obtain n::coname where "n\<sharp>(P,M,b,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>b,pi2)"
    by (meson exists_fresh(2) fs_coname1)
  then show ?t2
    by perm_simp
      (force simp add: fresh_prod fresh_fun_simp_OrR1 at_prm_fresh[OF at_coname_inst] swap_simps)
qed

lemma fresh_fun_simp_OrR2:
  assumes "a'\<sharp>P" "a'\<sharp>M" "a'\<sharp>b" 
  shows "fresh_fun (\<lambda>a'. Cut <a'>.(OrR2 <b>.M a') (x).P) = Cut <a'>.(OrR2 <b>.M a') (x).P"
proof (rule fresh_fun_app [OF pt_coname_inst at_coname_inst])
  obtain n::coname where "n\<sharp>(x,P,b,M)"
    by (meson exists_fresh(2) fs_coname1)
  then show "\<exists>a. a \<sharp> (\<lambda>a'. Cut <a'>.OrR2 <b>.M(a') (x).P, Cut <a>.OrR2 <b>.M(a) (x).P)"
    apply(intro exI [where x="n"])
    apply(simp add: fresh_prod abs_fresh)
    apply(fresh_guess)
    done
qed (use assms in \<open>fresh_guess|finite_guess\<close>)+

lemma fresh_fun_OrR2[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(OrR2 <b>.M a') (x).P) =
             fresh_fun (pi1\<bullet>(\<lambda>a'. Cut <a'>.(OrR2 <b>.M  a') (x).P))" (is "?t1")
  and   "pi2\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(OrR2 <b>.M a') (x).P) =
             fresh_fun (pi2\<bullet>(\<lambda>a'. Cut <a'>.(OrR2 <b>.M a') (x).P))"  (is "?t2")
proof -
  obtain n::coname where "n\<sharp>(P,M,b,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>b,pi1)"
    by (meson exists_fresh(2) fs_coname1)
  then show ?t1
    by perm_simp (force simp add: fresh_prod fresh_fun_simp_OrR2 calc_atm)
  obtain n::coname where "n\<sharp>(P,M,b,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>b,pi2)"
    by (meson exists_fresh(2) fs_coname1)
  then show ?t2
    by perm_simp
      (force simp add: fresh_prod fresh_fun_simp_OrR2 at_prm_fresh[OF at_coname_inst] swap_simps)
qed

lemma fresh_fun_simp_ImpR:
  assumes a: "a'\<sharp>P" "a'\<sharp>M" "a'\<sharp>b" 
  shows "fresh_fun (\<lambda>a'. Cut <a'>.(ImpR (y).<b>.M a') (x).P) = Cut <a'>.(ImpR (y).<b>.M a') (x).P"
proof (rule fresh_fun_app [OF pt_coname_inst at_coname_inst])
  obtain n::coname where "n\<sharp>(x,P,y,b,M)"
    by (meson exists_fresh(2) fs_coname1)
  then show "\<exists>a. a \<sharp> (\<lambda>a'. Cut <a'>.(ImpR (y).<b>.M a') (x).P, Cut <a>.(ImpR (y).<b>.M a) (x).P)"
    apply(intro exI [where x="n"])
    apply(simp add: fresh_prod abs_fresh)
    apply(fresh_guess)
    done
qed (use a in \<open>fresh_guess|finite_guess\<close>)+

lemma fresh_fun_ImpR[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(ImpR (y).<b>.M a') (x).P) =
             fresh_fun (pi1\<bullet>(\<lambda>a'. Cut <a'>.(ImpR (y).<b>.M  a') (x).P))" (is "?t1")
  and   "pi2\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(ImpR (y).<b>.M a') (x).P)=
             fresh_fun (pi2\<bullet>(\<lambda>a'. Cut <a'>.(ImpR (y).<b>.M a') (x).P))"  (is "?t2")
proof -
  obtain n::coname where "n\<sharp>(P,M,b,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>b,pi1)"
    by (meson exists_fresh(2) fs_coname1)
  then show ?t1
    by perm_simp (force simp add: fresh_prod fresh_fun_simp_ImpR calc_atm)
  obtain n::coname where "n\<sharp>(P,M,b,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>b,pi2)"
    by (meson exists_fresh(2) fs_coname1)
  then show ?t2
    by perm_simp
      (force simp add: fresh_prod fresh_fun_simp_ImpR at_prm_fresh[OF at_coname_inst] swap_simps)
qed

nominal_primrec (freshness_context: "(y::name,c::coname,P::trm)")
  substn :: "trm \<Rightarrow> name   \<Rightarrow> coname \<Rightarrow> trm \<Rightarrow> trm" (\<open>_{_:=<_>._}\<close> [100,100,100,100] 100) 
where
  "(Ax x a){y:=<c>.P} = (if x=y then Cut <c>.P (y).Ax y a else Ax x a)" 
| "\<lbrakk>a\<sharp>(c,P,N);x\<sharp>(y,P,M)\<rbrakk> \<Longrightarrow> (Cut <a>.M (x).N){y:=<c>.P} = 
  (if M=Ax y a then Cut <c>.P (x).(N{y:=<c>.P}) else Cut <a>.(M{y:=<c>.P}) (x).(N{y:=<c>.P}))" 
| "x\<sharp>(y,P) \<Longrightarrow> (NotR (x).M a){y:=<c>.P} = NotR (x).(M{y:=<c>.P}) a" 
| "a\<sharp>(c,P) \<Longrightarrow> (NotL <a>.M x){y:=<c>.P} = 
  (if x=y then fresh_fun (\<lambda>x'. Cut <c>.P (x').NotL <a>.(M{y:=<c>.P}) x') else NotL <a>.(M{y:=<c>.P}) x)"
| "\<lbrakk>a\<sharp>(c,P,N,d);b\<sharp>(c,P,M,d);b\<noteq>a\<rbrakk> \<Longrightarrow> 
  (AndR <a>.M <b>.N d){y:=<c>.P} = AndR <a>.(M{y:=<c>.P}) <b>.(N{y:=<c>.P}) d" 
| "x\<sharp>(y,P,z) \<Longrightarrow> (AndL1 (x).M z){y:=<c>.P} = 
  (if z=y then fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL1 (x).(M{y:=<c>.P}) z') 
   else AndL1 (x).(M{y:=<c>.P}) z)"
| "x\<sharp>(y,P,z) \<Longrightarrow> (AndL2 (x).M z){y:=<c>.P} = 
  (if z=y then fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL2 (x).(M{y:=<c>.P}) z') 
   else AndL2 (x).(M{y:=<c>.P}) z)"
| "a\<sharp>(c,P,b) \<Longrightarrow> (OrR1 <a>.M b){y:=<c>.P} = OrR1 <a>.(M{y:=<c>.P}) b"
| "a\<sharp>(c,P,b) \<Longrightarrow> (OrR2 <a>.M b){y:=<c>.P} = OrR2 <a>.(M{y:=<c>.P}) b"
| "\<lbrakk>x\<sharp>(y,N,P,z);u\<sharp>(y,M,P,z);x\<noteq>u\<rbrakk> \<Longrightarrow> (OrL (x).M (u).N z){y:=<c>.P} = 
  (if z=y then fresh_fun (\<lambda>z'. Cut <c>.P (z').OrL (x).(M{y:=<c>.P}) (u).(N{y:=<c>.P}) z') 
   else OrL (x).(M{y:=<c>.P}) (u).(N{y:=<c>.P}) z)"
| "\<lbrakk>a\<sharp>(b,c,P); x\<sharp>(y,P)\<rbrakk> \<Longrightarrow> (ImpR (x).<a>.M b){y:=<c>.P} = ImpR (x).<a>.(M{y:=<c>.P}) b"
| "\<lbrakk>a\<sharp>(N,c,P);x\<sharp>(y,P,M,z)\<rbrakk> \<Longrightarrow> (ImpL <a>.M (x).N z){y:=<c>.P} = 
  (if y=z then fresh_fun (\<lambda>z'. Cut <c>.P (z').ImpL <a>.(M{y:=<c>.P}) (x).(N{y:=<c>.P}) z') 
   else ImpL <a>.(M{y:=<c>.P}) (x).(N{y:=<c>.P}) z)"
apply(finite_guess | simp add: abs_fresh abs_supp fin_supp | fresh_guess | rule strip)+
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x1,P,y1)")
apply(force simp add: fresh_prod fresh_fun_simp_NotL abs_fresh fresh_atm)
apply (meson exists_fresh(1) fs_name1)

apply(simp add: abs_fresh abs_supp fin_supp | rule strip)+
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x1,P,y1)")
apply(force simp add: fresh_prod fresh_fun_simp_AndL1 abs_fresh fresh_atm)
apply (meson exists_fresh(1) fs_name1)

apply(simp add: abs_fresh abs_supp fin_supp | rule strip)+
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x1,P,y1)")
apply(force simp add: fresh_prod fresh_fun_simp_AndL2 abs_fresh fresh_atm)
apply (meson exists_fresh(1) fs_name1)

apply(simp add: abs_fresh abs_supp fin_supp | rule strip)+
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x1,P,y1,x3,y2)")
apply(force simp add: fresh_prod fresh_fun_simp_OrL abs_fresh fresh_atm)
apply (meson exists_fresh(1) fs_name1)

apply(simp add: abs_fresh abs_supp fin_supp | rule strip)+
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x1,P,y1,x3,y2)")
apply(force simp add: fresh_prod fresh_fun_simp_OrL abs_fresh fresh_atm)
apply (meson exists_fresh(1) fs_name1)

apply(simp add: abs_fresh abs_supp fin_supp | rule strip)+
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x3,P,y1,y2)")
apply(force simp add: fresh_prod fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply (meson exists_fresh(1) fs_name1)

apply(simp add: abs_fresh abs_supp fin_supp | rule strip)+
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x3,P,y1,y2)")
apply(force simp add: fresh_prod fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply (meson exists_fresh(1) fs_name1)
apply(fresh_guess)+
done

nominal_primrec (freshness_context: "(d::name,z::coname,P::trm)")
  substc :: "trm \<Rightarrow> coname \<Rightarrow> name   \<Rightarrow> trm \<Rightarrow> trm" (\<open>_{_:=('(_'))._}\<close> [100,0,0,100] 100)
where
  "(Ax x a){d:=(z).P} = (if d=a then Cut <a>.(Ax x a) (z).P else Ax x a)" 
| "\<lbrakk>a\<sharp>(d,P,N);x\<sharp>(z,P,M)\<rbrakk> \<Longrightarrow> (Cut <a>.M (x).N){d:=(z).P} = 
  (if N=Ax x d then Cut <a>.(M{d:=(z).P}) (z).P else Cut <a>.(M{d:=(z).P}) (x).(N{d:=(z).P}))" 
| "x\<sharp>(z,P) \<Longrightarrow> (NotR (x).M a){d:=(z).P} = 
  (if d=a then fresh_fun (\<lambda>a'. Cut <a'>.NotR (x).(M{d:=(z).P}) a' (z).P) else NotR (x).(M{d:=(z).P}) a)" 
| "a\<sharp>(d,P) \<Longrightarrow> (NotL <a>.M x){d:=(z).P} = NotL <a>.(M{d:=(z).P}) x" 
| "\<lbrakk>a\<sharp>(P,c,N,d);b\<sharp>(P,c,M,d);b\<noteq>a\<rbrakk> \<Longrightarrow> (AndR <a>.M <b>.N c){d:=(z).P} = 
  (if d=c then fresh_fun (\<lambda>a'. Cut <a'>.(AndR <a>.(M{d:=(z).P}) <b>.(N{d:=(z).P}) a') (z).P)
   else AndR <a>.(M{d:=(z).P}) <b>.(N{d:=(z).P}) c)" 
| "x\<sharp>(y,z,P) \<Longrightarrow> (AndL1 (x).M y){d:=(z).P} = AndL1 (x).(M{d:=(z).P}) y"
| "x\<sharp>(y,P,z) \<Longrightarrow> (AndL2 (x).M y){d:=(z).P} = AndL2 (x).(M{d:=(z).P}) y"
| "a\<sharp>(d,P,b) \<Longrightarrow> (OrR1 <a>.M b){d:=(z).P} = 
  (if d=b then fresh_fun (\<lambda>a'. Cut <a'>.OrR1 <a>.(M{d:=(z).P}) a' (z).P) else OrR1 <a>.(M{d:=(z).P}) b)"
| "a\<sharp>(d,P,b) \<Longrightarrow> (OrR2 <a>.M b){d:=(z).P} = 
  (if d=b then fresh_fun (\<lambda>a'. Cut <a'>.OrR2 <a>.(M{d:=(z).P}) a' (z).P) else OrR2 <a>.(M{d:=(z).P}) b)"
| "\<lbrakk>x\<sharp>(N,z,P,u);y\<sharp>(M,z,P,u);x\<noteq>y\<rbrakk> \<Longrightarrow> (OrL (x).M (y).N u){d:=(z).P} = 
  OrL (x).(M{d:=(z).P}) (y).(N{d:=(z).P}) u" 
| "\<lbrakk>a\<sharp>(b,d,P); x\<sharp>(z,P)\<rbrakk> \<Longrightarrow> (ImpR (x).<a>.M b){d:=(z).P} = 
  (if d=b then fresh_fun (\<lambda>a'. Cut <a'>.ImpR (x).<a>.(M{d:=(z).P}) a' (z).P) 
   else ImpR (x).<a>.(M{d:=(z).P}) b)"
| "\<lbrakk>a\<sharp>(N,d,P);x\<sharp>(y,z,P,M)\<rbrakk> \<Longrightarrow> (ImpL <a>.M (x).N y){d:=(z).P} = 
  ImpL <a>.(M{d:=(z).P}) (x).(N{d:=(z).P}) y"
apply(finite_guess | simp add: abs_fresh abs_supp fs_name1 fs_coname1 | rule strip)+
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,y1)")
apply(force simp add: fresh_prod fresh_fun_simp_NotR abs_fresh fresh_atm)
apply(meson exists_fresh' fin_supp)

apply(simp add: abs_fresh abs_supp fs_name1 fs_coname1 | rule strip)+
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,y1,x3,y2)")
apply(force simp add: fresh_prod fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(meson exists_fresh' fin_supp)

apply(simp add: abs_fresh abs_supp fs_name1 fs_coname1 | rule strip)+
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,y1,x3,y2)")
apply(force simp add: fresh_prod fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(meson exists_fresh' fin_supp)

apply(simp add: abs_fresh abs_supp fs_name1 fs_coname1 | rule strip)+
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,y1)")
apply(force simp add: fresh_prod fresh_fun_simp_OrR1 abs_fresh fresh_atm)
apply(meson exists_fresh' fin_supp)

apply(simp add: abs_fresh abs_supp fs_name1 fs_coname1 | rule strip)+
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,y1)")
apply(force simp add: fresh_prod fresh_fun_simp_OrR2 abs_fresh fresh_atm)
apply(meson exists_fresh' fin_supp)

apply(simp add: abs_fresh abs_supp | rule strip)+
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,x2,y1)")
apply(force simp add: fresh_prod fresh_fun_simp_ImpR abs_fresh fresh_atm abs_supp)
apply(meson exists_fresh' fin_supp)

apply(simp add: abs_fresh abs_supp | rule strip)+
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,x2,y1)")
apply(force simp add: fresh_prod fresh_fun_simp_ImpR abs_fresh fresh_atm)
apply(meson exists_fresh' fin_supp)

apply(simp add: abs_fresh | fresh_guess add: abs_fresh)+
done


lemma csubst_eqvt[eqvt]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>(M{c:=(x).N}) = (pi1\<bullet>M){(pi1\<bullet>c):=(pi1\<bullet>x).(pi1\<bullet>N)}"
  and   "pi2\<bullet>(M{c:=(x).N}) = (pi2\<bullet>M){(pi2\<bullet>c):=(pi2\<bullet>x).(pi2\<bullet>N)}"
by (nominal_induct M avoiding: c x N rule: trm.strong_induct)
   (auto simp: eq_bij fresh_bij eqvts; perm_simp)+

lemma nsubst_eqvt[eqvt]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>(M{x:=<c>.N}) = (pi1\<bullet>M){(pi1\<bullet>x):=<(pi1\<bullet>c)>.(pi1\<bullet>N)}"
  and   "pi2\<bullet>(M{x:=<c>.N}) = (pi2\<bullet>M){(pi2\<bullet>x):=<(pi2\<bullet>c)>.(pi2\<bullet>N)}"
by (nominal_induct M avoiding: c x N rule: trm.strong_induct)
   (auto simp: eq_bij fresh_bij eqvts; perm_simp)+

lemma supp_subst1:
  shows "supp (M{y:=<c>.P}) \<subseteq> ((supp M) - {y}) \<union> (supp P)"
proof (nominal_induct M avoiding: y P c rule: trm.strong_induct)
  case (NotL coname trm name)
  obtain x'::name where "x'\<sharp>(trm{y:=<c>.P},P)"
    by (meson exists_fresh(1) fs_name1)
  with NotL
   show ?case 
     by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_NotL; blast)
next
  case (AndL1 name1 trm name2)
  obtain x'::name where "x'\<sharp>(trm{y:=<c>.P},P,name1)"
    by (meson exists_fresh(1) fs_name1)
  with AndL1 show ?case
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_AndL1 fresh_atm; blast)
next
  case (AndL2 name1 trm name2)
  obtain x'::name where "x'\<sharp>(trm{y:=<c>.P},P,name1)"
    by (meson exists_fresh(1) fs_name1)
  with AndL2 show ?case
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_AndL2 fresh_atm; blast)
next
  case (OrL name1 trm1 name2 trm2 name3)
  obtain x'::name where "x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)"
    by (meson exists_fresh(1) fs_name1)
  with OrL show ?case 
    by (auto simp: fs_name1 fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_OrL fresh_atm; blast)
next
  case (ImpL coname trm1 name1 trm2 name2)
  obtain x'::name where "x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})"
    by (meson exists_fresh(1) fs_name1)
  with ImpL show ?case 
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_ImpL fresh_atm; blast)
qed (simp add: abs_supp supp_atm trm.supp fs_name1; blast)+

text \<open>Identical to the previous proof\<close>
lemma supp_subst2:
  shows "supp (M{y:=<c>.P}) \<subseteq> supp (M) \<union> ((supp P) - {c})"
proof (nominal_induct M avoiding: y P c rule: trm.strong_induct)
  case (NotL coname trm name)
  obtain x'::name where "x'\<sharp>(trm{y:=<c>.P},P)"
    by (meson exists_fresh(1) fs_name1)
  with NotL
   show ?case 
     by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_NotL; blast)
next
  case (AndL1 name1 trm name2)
  obtain x'::name where "x'\<sharp>(trm{y:=<c>.P},P,name1)"
    by (meson exists_fresh(1) fs_name1)
  with AndL1 show ?case
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_AndL1 fresh_atm; blast)
next
  case (AndL2 name1 trm name2)
  obtain x'::name where "x'\<sharp>(trm{y:=<c>.P},P,name1)"
    by (meson exists_fresh(1) fs_name1)
  with AndL2 show ?case
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_AndL2 fresh_atm; blast)
next
  case (OrL name1 trm1 name2 trm2 name3)
  obtain x'::name where "x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)"
    by (meson exists_fresh(1) fs_name1)
  with OrL show ?case 
    by (auto simp: fs_name1 fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_OrL fresh_atm; blast)
next
  case (ImpL coname trm1 name1 trm2 name2)
  obtain x'::name where "x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})"
    by (meson exists_fresh(1) fs_name1)
  with ImpL show ?case 
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_ImpL fresh_atm; blast)
qed (simp add: abs_supp supp_atm trm.supp fs_name1; blast)+

lemma supp_subst3:
  shows "supp (M{c:=(x).P}) \<subseteq> ((supp M) - {c}) \<union> (supp P)"
proof (nominal_induct M avoiding: x P c rule: trm.strong_induct)
  case (NotR name trm coname)
  obtain x'::coname where "x'\<sharp>(trm{coname:=(x).P},P)"
    by (meson exists_fresh'(2) fs_coname1)
  with NotR show ?case
     by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_NotR; blast)
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  obtain x'::coname where x': "x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)"
    by (meson exists_fresh'(2) fs_coname1)
  with AndR show ?case 
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_AndR; blast)
next
  case (OrR1 coname1 trm coname2)
  obtain x'::coname where x': "x'\<sharp>(trm{coname2:=(x).P},P,coname1)"
    by (meson exists_fresh'(2) fs_coname1)
  with OrR1 show ?case 
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_OrR1; blast)
next
  case (OrR2 coname1 trm coname2)
  obtain x'::coname where x': "x'\<sharp>(trm{coname2:=(x).P},P,coname1)"
    by (meson exists_fresh'(2) fs_coname1)
  with OrR2 show ?case 
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_OrR2; blast)  
next
  case (ImpR name coname1 trm coname2)
  obtain x'::coname where x': "x'\<sharp>(trm{coname2:=(x).P},P,coname1)"
    by (meson exists_fresh'(2) fs_coname1)
  with ImpR show ?case 
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_ImpR; blast)
qed (simp add: abs_supp supp_atm trm.supp fs_name1; blast)+


lemma supp_subst4:
  shows "supp (M{c:=(x).P}) \<subseteq> (supp M) \<union> ((supp P) - {x})"
proof (nominal_induct M avoiding: x P c rule: trm.strong_induct)
  case (NotR name trm coname)
  obtain x'::coname where "x'\<sharp>(trm{coname:=(x).P},P)"
    by (meson exists_fresh'(2) fs_coname1)
  with NotR show ?case
     by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_NotR; blast)
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  obtain x'::coname where x': "x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)"
    by (meson exists_fresh'(2) fs_coname1)
  with AndR show ?case 
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_AndR; blast)
next
  case (OrR1 coname1 trm coname2)
  obtain x'::coname where x': "x'\<sharp>(trm{coname2:=(x).P},P,coname1)"
    by (meson exists_fresh'(2) fs_coname1)
  with OrR1 show ?case 
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_OrR1; blast)
next
  case (OrR2 coname1 trm coname2)
  obtain x'::coname where x': "x'\<sharp>(trm{coname2:=(x).P},P,coname1)"
    by (meson exists_fresh'(2) fs_coname1)
  with OrR2 show ?case 
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_OrR2; blast)  
next
  case (ImpR name coname1 trm coname2)
  obtain x'::coname where x': "x'\<sharp>(trm{coname2:=(x).P},P,coname1)"
    by (meson exists_fresh'(2) fs_coname1)
  with ImpR show ?case 
    by (auto simp: fresh_prod abs_supp supp_atm trm.supp fs_name1 fresh_fun_simp_ImpR; blast)
qed (simp add: abs_supp supp_atm trm.supp fs_name1; blast)+

lemma supp_subst5:
  shows "(supp M - {y}) \<subseteq> supp (M{y:=<c>.P})"
proof (nominal_induct M avoiding: y P c rule: trm.strong_induct)
  case (NotL coname trm name)
  obtain x'::name where "x'\<sharp>(trm{y:=<c>.P},P)"
    by (meson exists_fresh(1) fs_name1)
  with NotL
  show ?case 
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_NotL)
     apply (auto simp: fresh_def)
    done
next
  case (AndL1 name1 trm name2)
  obtain x'::name where "x'\<sharp>(trm{y:=<c>.P},P,name1)"
    by (meson exists_fresh(1) fs_name1)
  with AndL1 show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_AndL1)
     apply (auto simp: fresh_def)
    done
next
  case (AndL2 name1 trm name2)
  obtain x'::name where "x'\<sharp>(trm{y:=<c>.P},P,name1)"
    by (meson exists_fresh(1) fs_name1)
  with AndL2 show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_AndL2)
     apply (auto simp: fresh_def)
    done
next
  case (OrL name1 trm1 name2 trm2 name3)
  obtain x'::name where "x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)"
    by (meson exists_fresh(1) fs_name1)
  with OrL show ?case 
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_OrL)
           apply (fastforce simp: fresh_def)+
    done
next
  case (ImpL coname trm1 name1 trm2 name2)
  obtain x'::name where "x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})"
    by (meson exists_fresh(1) fs_name1)
  with ImpL show ?case 
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_ImpL)
           apply (fastforce simp: fresh_def)+
    done
qed (simp add: abs_supp supp_atm trm.supp fs_name1; blast)+

lemma supp_subst6:
  shows "(supp M) \<subseteq> ((supp (M{y:=<c>.P}))::coname set)"
proof (nominal_induct M avoiding: y P c rule: trm.strong_induct)
  case (NotL coname trm name)
  obtain x'::name where "x'\<sharp>(trm{y:=<c>.P},P)"
    by (meson exists_fresh(1) fs_name1)
  with NotL
  show ?case 
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_NotL)
     apply (auto simp: fresh_def)
    done
next
  case (AndL1 name1 trm name2)
  obtain x'::name where "x'\<sharp>(trm{y:=<c>.P},P,name1)"
    by (meson exists_fresh(1) fs_name1)
  with AndL1 show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_AndL1)
     apply (auto simp: fresh_def)
    done
next
  case (AndL2 name1 trm name2)
  obtain x'::name where "x'\<sharp>(trm{y:=<c>.P},P,name1)"
    by (meson exists_fresh(1) fs_name1)
  with AndL2 show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_AndL2)
     apply (auto simp: fresh_def)
    done
next
  case (OrL name1 trm1 name2 trm2 name3)
  obtain x'::name where "x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)"
    by (meson exists_fresh(1) fs_name1)
  with OrL show ?case 
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_OrL)
           apply (fastforce simp: fresh_def)+
    done
next
  case (ImpL coname trm1 name1 trm2 name2)
  obtain x'::name where "x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})"
    by (meson exists_fresh(1) fs_name1)
  with ImpL show ?case 
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_ImpL)
           apply (fastforce simp: fresh_def)+
    done
qed (simp add: abs_supp supp_atm trm.supp fs_name1; blast)+

lemma supp_subst7:
  shows "(supp M - {c}) \<subseteq>  supp (M{c:=(x).P})"
proof (nominal_induct M avoiding: x P c rule: trm.strong_induct)
  case (NotR name trm coname)
  obtain x'::coname where "x'\<sharp>(trm{coname:=(x).P},P)"
    by (meson exists_fresh'(2) fs_coname1)
  with NotR show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_NotR)
     apply (auto simp: fresh_def)
    done
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  obtain x'::coname where "x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)"
    by (meson exists_fresh'(2) fs_coname1)
  with AndR show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_AndR)
     apply (fastforce simp: fresh_def)+
    done
next
  case (OrR1 coname1 trm coname2)
  obtain x'::coname where "x'\<sharp>(trm{coname2:=(x).P},P,coname1)"
    by (meson exists_fresh'(2) fs_coname1)
  with OrR1 show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_OrR1)
     apply (auto simp: fresh_def)
    done
next
  case (OrR2 coname1 trm coname2)
  obtain x'::coname where "x'\<sharp>(trm{coname2:=(x).P},P,coname1)"
    by (meson exists_fresh'(2) fs_coname1)
  with OrR2 show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_OrR2)
     apply (auto simp: fresh_def)
    done
next
  case (ImpR name coname1 trm coname2)
  obtain x'::coname where "x'\<sharp>(trm{coname2:=(x).P},P,coname1)"
    by (meson exists_fresh'(2) fs_coname1)
  with ImpR show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_ImpR)
     apply (auto simp: fresh_def)
    done
qed (simp add: abs_supp supp_atm trm.supp fs_name1; blast)+
  
lemma supp_subst8:
  shows "(supp M) \<subseteq> ((supp (M{c:=(x).P}))::name set)"
proof (nominal_induct M avoiding: x P c rule: trm.strong_induct)
  case (NotR name trm coname)
  obtain x'::coname where "x'\<sharp>(trm{coname:=(x).P},P)"
    by (meson exists_fresh'(2) fs_coname1)
  with NotR show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_NotR)
     apply (auto simp: fresh_def)
    done
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  obtain x'::coname where "x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)"
    by (meson exists_fresh'(2) fs_coname1)
  with AndR show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_AndR)
     apply (fastforce simp: fresh_def)+
    done
next
  case (OrR1 coname1 trm coname2)
  obtain x'::coname where "x'\<sharp>(trm{coname2:=(x).P},P,coname1)"
    by (meson exists_fresh'(2) fs_coname1)
  with OrR1 show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_OrR1)
     apply (auto simp: fresh_def)
    done
next
  case (OrR2 coname1 trm coname2)
  obtain x'::coname where "x'\<sharp>(trm{coname2:=(x).P},P,coname1)"
    by (meson exists_fresh'(2) fs_coname1)
  with OrR2 show ?case
    apply (auto simp: fresh_prod abs_supp supp_atm trm.supp fresh_fun_simp_OrR2)
     apply (auto simp: fresh_def)
    done
next
  case (ImpR name coname1 trm coname2)
  obtain x'::coname where "x'\<sharp>(trm{coname2:=(x).P},P,coname1)"
    by (meson exists_fresh'(2) fs_coname1)
  with ImpR show ?case
    by (force simp: fresh_prod abs_supp fs_name1 supp_atm trm.supp fresh_fun_simp_ImpR)
qed (simp add: abs_supp supp_atm trm.supp fs_name1; blast)+
  
lemmas subst_supp = supp_subst1 supp_subst2 supp_subst3 supp_subst4
                    supp_subst5 supp_subst6 supp_subst7 supp_subst8
lemma subst_fresh:
  fixes x::"name"
  and   c::"coname"
  shows "x\<sharp>P \<Longrightarrow> x\<sharp>M{x:=<c>.P}"   
  and   "b\<sharp>P \<Longrightarrow> b\<sharp>M{b:=(y).P}"
  and   "x\<sharp>(M,P) \<Longrightarrow> x\<sharp>M{y:=<c>.P}"
  and   "x\<sharp>M \<Longrightarrow> x\<sharp>M{c:=(x).P}"
  and   "x\<sharp>(M,P) \<Longrightarrow> x\<sharp>M{c:=(y).P}"
  and   "b\<sharp>(M,P) \<Longrightarrow> b\<sharp>M{c:=(y).P}"
  and   "b\<sharp>M \<Longrightarrow> b\<sharp>M{y:=<b>.P}"
  and   "b\<sharp>(M,P) \<Longrightarrow> b\<sharp>M{y:=<c>.P}"
  using subst_supp
  by(fastforce simp add: fresh_def supp_prod)+

lemma forget:
  shows "x\<sharp>M \<Longrightarrow> M{x:=<c>.P} = M"
  and   "c\<sharp>M \<Longrightarrow> M{c:=(x).P} = M"
  by (nominal_induct M avoiding: x c P rule: trm.strong_induct)
     (auto simp: fresh_atm abs_fresh abs_supp fin_supp)

lemma substc_rename1:
  assumes a: "c\<sharp>(M,a)"
  shows "M{a:=(x).N} = ([(c,a)]\<bullet>M){c:=(x).N}"
using a
proof(nominal_induct M avoiding: c a x N rule: trm.strong_induct)
  case (AndR c1 M c2 M' c3)
  then show ?case
    apply(auto simp: fresh_prod calc_atm fresh_atm abs_fresh fresh_left)
     apply (metis (no_types, lifting))+
    done
next 
  case ImpL
  then show ?case
    by (auto simp: calc_atm alpha fresh_atm abs_fresh fresh_prod fresh_left)
       metis
next
  case (Cut d M y M')
  then show ?case
    by(simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
      (metis crename.simps(1) crename_id crename_rename)
qed (auto simp: calc_atm alpha fresh_atm abs_fresh fresh_prod fresh_left trm.inject)

lemma substc_rename2:
  assumes a: "y\<sharp>(N,x)"
  shows "M{a:=(x).N} = M{a:=(y).([(y,x)]\<bullet>N)}"
using a
proof(nominal_induct M avoiding: a x y N rule: trm.strong_induct)
  case (NotR y M d)
  obtain a::coname where "a\<sharp>(N,M{d:=(y).([(y,x)]\<bullet>N)},[(y,x)]\<bullet>N)"
    by (meson exists_fresh(2) fs_coname1)
  with NotR show ?case
    apply(auto simp: calc_atm alpha fresh_atm fresh_prod fresh_left)
    by (metis (no_types, opaque_lifting) alpha(1) trm.inject(2))
next
  case (AndR c1 M c2 M' c3)
  obtain a'::coname where "a'\<sharp>(N,M{c3:=(y).([(y,x)]\<bullet>N)},M'{c3:=(y).([(y,x)]\<bullet>N)},[(y,x)]\<bullet>N,c1,c2,c3)"
    by (meson exists_fresh(2) fs_coname1)
  with AndR show ?case
    apply(auto simp: calc_atm alpha fresh_atm fresh_prod fresh_left)
    by (metis (no_types, opaque_lifting) alpha(1) trm.inject(2))
next
  case (OrR1 d M e)
  obtain a'::coname where "a'\<sharp>(N,M{e:=(y).([(y,x)]\<bullet>N)},[(y,x)]\<bullet>N,d,e)"
    by (meson exists_fresh(2) fs_coname1)
  with OrR1 show ?case 
    by (auto simp: perm_swap calc_atm trm.inject alpha fresh_atm fresh_prod fresh_left fresh_fun_simp_OrR1)
next
  case (OrR2 d M e)
  obtain a'::coname where "a'\<sharp>(N,M{e:=(y).([(y,x)]\<bullet>N)},[(y,x)]\<bullet>N,d,e)"
    by (meson exists_fresh(2) fs_coname1)
  with OrR2 show ?case 
    by (auto simp: perm_swap calc_atm trm.inject alpha fresh_atm fresh_prod fresh_left fresh_fun_simp_OrR2)
next
  case (ImpR y d M e)
  obtain a'::coname where "a'\<sharp>(N,M{e:=(y).([(y,x)]\<bullet>N)},[(y,x)]\<bullet>N,d,e)"
    by (meson exists_fresh(2) fs_coname1)
  with ImpR show ?case 
    by (auto simp: perm_swap calc_atm trm.inject alpha fresh_atm fresh_prod fresh_left fresh_fun_simp_ImpR) 
qed (auto simp: calc_atm trm.inject alpha fresh_atm fresh_prod fresh_left perm_swap)

lemma substn_rename3:
  assumes a: "y\<sharp>(M,x)"
  shows "M{x:=<a>.N} = ([(y,x)]\<bullet>M){y:=<a>.N}"
using a
proof(nominal_induct M avoiding: a x y N rule: trm.strong_induct)
  case (OrL x1 M x2 M' x3)
  then show ?case
    apply(auto simp add: calc_atm fresh_atm abs_fresh fresh_prod fresh_left)
    by (metis (mono_tags))+
next
  case (ImpL d M v M' u)
  then show ?case
    apply(auto simp add: calc_atm fresh_atm abs_fresh fresh_prod fresh_left)
    by (metis (mono_tags))+
next
  case (Cut d M y M')
  then show ?case
    apply(auto simp: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    by (metis nrename.simps(1) nrename_id nrename_rename)+
qed (auto simp: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_left abs_supp fin_supp fresh_prod)

lemma substn_rename4:
  assumes a: "c\<sharp>(N,a)"
  shows "M{x:=<a>.N} = M{x:=<c>.([(c,a)]\<bullet>N)}"
using a
proof(nominal_induct M avoiding: x c a N rule: trm.strong_induct)
  case (Ax z d)
  then show ?case 
    by (auto simp: fresh_prod fresh_atm calc_atm trm.inject alpha perm_swap fresh_left)
next
  case NotR
  then show ?case 
    by (auto simp: fresh_prod fresh_atm calc_atm trm.inject alpha perm_swap fresh_left)
next
  case (NotL d M y)
  then obtain a'::name where "a'\<sharp>(N, M{x:=<c>.([(c,a)]\<bullet>N)}, [(c,a)]\<bullet>N)"
    by (meson exists_fresh(1) fs_name1)
  with NotL show ?case
    apply(auto simp: calc_atm trm.inject fresh_atm fresh_prod fresh_left)
    by (metis (no_types, opaque_lifting) alpha(2) trm.inject(2))
next
  case (OrL x1 M x2 M' x3)
  then obtain a'::name where "a'\<sharp>(N,M{x:=<c>.([(c,a)]\<bullet>N)},M'{x:=<c>.([(c,a)]\<bullet>N)},[(c,a)]\<bullet>N,x1,x2,x3)"
    by (meson exists_fresh(1) fs_name1)  
  with OrL show ?case
    apply(auto simp: calc_atm trm.inject fresh_atm fresh_prod fresh_left)
    by (metis (no_types) alpha'(2) trm.inject(2))
next
  case (AndL1 u M v)
  then obtain a'::name where "a'\<sharp>(N,M{x:=<c>.([(c,a)]\<bullet>N)},[(c,a)]\<bullet>N,u,v)"
    by (meson exists_fresh(1) fs_name1)  
  with AndL1 show ?case 
    apply(auto simp: calc_atm trm.inject fresh_atm fresh_prod fresh_left)
    by (metis (mono_tags, opaque_lifting) alpha'(2) trm.inject(2))
next
  case (AndL2 u M v)
  then obtain a'::name where "a'\<sharp>(N,M{x:=<c>.([(c,a)]\<bullet>N)},[(c,a)]\<bullet>N,u,v)"
    by (meson exists_fresh(1) fs_name1)  
  with AndL2 show ?case 
    apply(auto simp: calc_atm trm.inject fresh_atm fresh_prod fresh_left)
    by (metis (mono_tags, opaque_lifting) alpha'(2) trm.inject(2))
next
  case (ImpL d M y M' u)
  then obtain a'::name where "a'\<sharp>(N,M{u:=<c>.([(c,a)]\<bullet>N)},M'{u:=<c>.([(c,a)]\<bullet>N)},[(c,a)]\<bullet>N,y,u)"
    by (meson exists_fresh(1) fs_name1)  
  with ImpL show ?case
    apply(auto simp: calc_atm trm.inject fresh_atm fresh_prod fresh_left)
    by (metis (no_types) alpha'(2) trm.inject(2))
next
  case (Cut d M y M')
  then show ?case
    by (auto simp: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left perm_swap)
qed (auto simp: calc_atm fresh_atm fresh_left)

lemma subst_rename5:
  assumes a: "c'\<sharp>(c,N)" "x'\<sharp>(x,M)"
  shows "M{x:=<c>.N} = ([(x',x)]\<bullet>M){x':=<c'>.([(c',c)]\<bullet>N)}"
proof -
  have "M{x:=<c>.N} = ([(x',x)]\<bullet>M){x':=<c>.N}" using a by (simp add: substn_rename3)
  also have "\<dots> = ([(x',x)]\<bullet>M){x':=<c'>.([(c',c)]\<bullet>N)}" using a by (simp add: substn_rename4)
  finally show ?thesis by simp
qed

lemma subst_rename6:
  assumes a: "c'\<sharp>(c,M)" "x'\<sharp>(x,N)"
  shows "M{c:=(x).N} = ([(c',c)]\<bullet>M){c':=(x').([(x',x)]\<bullet>N)}"
proof -
  have "M{c:=(x).N} = ([(c',c)]\<bullet>M){c':=(x).N}" using a by (simp add: substc_rename1)
  also have "\<dots> = ([(c',c)]\<bullet>M){c':=(x').([(x',x)]\<bullet>N)}" using a by (simp add: substc_rename2)
  finally show ?thesis by simp
qed

lemmas subst_rename = substc_rename1 substc_rename2 substn_rename3 substn_rename4 subst_rename5 subst_rename6

lemma better_Cut_substn[simp]:
  assumes a: "a\<sharp>[c].P" "x\<sharp>(y,P)"
  shows "(Cut <a>.M (x).N){y:=<c>.P} = 
  (if M=Ax y a then Cut <c>.P (x).(N{y:=<c>.P}) else Cut <a>.(M{y:=<c>.P}) (x).(N{y:=<c>.P}))"
proof -   
  obtain x'::"name"   where fs1: "x'\<sharp>(M,N,c,P,x,y)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,c,P,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have eq1: "(Cut <a>.M (x).N) = (Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N))"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  have eq2: "(M=Ax y a) = (([(a',a)]\<bullet>M)=Ax y a')"
    by (metis perm_swap(4) swap_simps(4) swap_simps(8) trm.perm(13))
  have "(Cut <a>.M (x).N){y:=<c>.P} = (Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N)){y:=<c>.P}" 
    using eq1 by simp
  also have "\<dots> = (if ([(a',a)]\<bullet>M)=Ax y a' then Cut <c>.P (x').(([(x',x)]\<bullet>N){y:=<c>.P}) 
                              else Cut <a'>.(([(a',a)]\<bullet>M){y:=<c>.P}) (x').(([(x',x)]\<bullet>N){y:=<c>.P}))" 
    using fs1 fs2 by (auto simp: fresh_prod fresh_left calc_atm fresh_atm)
  also have "\<dots> =(if M=Ax y a then Cut <c>.P (x).(N{y:=<c>.P}) else Cut <a>.(M{y:=<c>.P}) (x).(N{y:=<c>.P}))"
    using fs1 fs2 a
    unfolding eq2[symmetric]
    apply(auto simp: trm.inject)
    apply(simp_all add: alpha fresh_atm fresh_prod subst_fresh eqvts perm_fresh_fresh calc_atm)
    apply (simp add: fresh_atm(2) substn_rename4)
    by (metis abs_fresh(2) fresh_atm(2) fresh_prod perm_fresh_fresh(2) substn_rename4)
  finally show ?thesis by simp
qed
    
lemma better_Cut_substc[simp]:
  assumes a: "a\<sharp>(c,P)" "x\<sharp>[y].P"
  shows "(Cut <a>.M (x).N){c:=(y).P} = 
  (if N=Ax x c then Cut <a>.(M{c:=(y).P}) (y).P else Cut <a>.(M{c:=(y).P}) (x).(N{c:=(y).P}))" 
proof -   
  obtain x'::"name"   where fs1: "x'\<sharp>(M,N,c,P,x,y)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,c,P,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have eq1: "(Cut <a>.M (x).N) = (Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N))"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  have eq2: "(N=Ax x c) = (([(x',x)]\<bullet>N)=Ax x' c)"
    by (metis perm_dj(1) perm_swap(1) swap_simps(1) trm.perm(1))
  have "(Cut <a>.M (x).N){c:=(y).P} = (Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N)){c:=(y).P}" 
    using eq1 by simp
  also have "\<dots> = (if ([(x',x)]\<bullet>N)=Ax x' c then  Cut <a'>.(([(a',a)]\<bullet>M){c:=(y).P}) (y).P
                              else Cut <a'>.(([(a',a)]\<bullet>M){c:=(y).P}) (x').(([(x',x)]\<bullet>N){c:=(y).P}))" 
    using fs1 fs2  by (simp add: fresh_prod fresh_left calc_atm fresh_atm trm.inject)
  also have "\<dots> =(if N=Ax x c then Cut <a>.(M{c:=(y).P}) (y).P else Cut <a>.(M{c:=(y).P}) (x).(N{c:=(y).P}))"
    using fs1 fs2 a
    unfolding eq2[symmetric]
    apply(auto simp: trm.inject)
    apply(simp_all add: alpha fresh_atm fresh_prod subst_fresh eqvts perm_fresh_fresh calc_atm)
    by (metis abs_fresh(1) fresh_atm(1) fresh_prod perm_fresh_fresh(1) substc_rename2)
  finally show ?thesis by simp
qed

lemma better_Cut_substn':
  assumes "a\<sharp>[c].P" "y\<sharp>(N,x)" "M\<noteq>Ax y a"
  shows "(Cut <a>.M (x).N){y:=<c>.P} = Cut <a>.(M{y:=<c>.P}) (x).N"
proof -
  obtain d::name where d: "d \<sharp> (M, N, P, a, c, x, y)"
    by (meson exists_fresh(1) fs_name1)
  then have *: "y\<sharp>([(d,x)]\<bullet>N)"
    by (metis assms(2) fresh_atm(1) fresh_list_cons fresh_list_nil fresh_perm_name fresh_prod)
  with d have "Cut <a>.M (x).N = Cut <a>.M (d).([(d,x)]\<bullet>N)"
    by (metis (no_types, lifting) alpha(1) fresh_prodD perm_fresh_fresh(1) trm.inject(2))
  with * d assms show ?thesis
    apply(simp add: fresh_prod)
    by (smt (verit, ccfv_SIG) forget(1) trm.inject(2))
qed

lemma better_NotR_substc:
  assumes a: "d\<sharp>M"
  shows "(NotR (x).M d){d:=(z).P} = fresh_fun (\<lambda>a'. Cut <a'>.NotR (x).M a' (z).P)"
proof -
  obtain c::name where c: "c \<sharp> (M, P, d, x, z)"
    by (meson exists_fresh(1) fs_name1)
  obtain e::coname where e: "e \<sharp> (M, P, d, x, z, c)"
    by (meson exists_fresh'(2) fs_coname1)
  with c have "NotR (x).M d = NotR (c).([(c,x)]\<bullet>M) d"
    by (metis alpha'(1) fresh_prodD(1) nrename_id nrename_swap trm.inject(3))
  with c e assms show ?thesis
    apply(simp add: fresh_prod)
    by (metis forget(2) fresh_perm_app(3) trm.inject(3))
qed

lemma better_NotL_substn:
  assumes a: "y\<sharp>M"
  shows "(NotL <a>.M y){y:=<c>.P} = fresh_fun (\<lambda>x'. Cut <c>.P (x').NotL <a>.M x')"
proof (generate_fresh "coname")
  fix ca :: coname
  assume d: "ca \<sharp> (M, P, a, c, y)"
  then have "NotL <a>.M y = NotL <ca>.([(ca,a)]\<bullet>M) y"
    by (metis alpha(2) fresh_prod perm_fresh_fresh(2) trm.inject(4))
  with a d show ?thesis
    apply(simp add: fresh_left calc_atm forget)
    apply (metis trm.inject(4))
    done
qed

lemma better_AndL1_substn:
  assumes a: "y\<sharp>[x].M"
  shows "(AndL1 (x).M y){y:=<c>.P} = fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL1 (x).M z')"
proof (generate_fresh "name")
  fix d:: name
  assume d: "d \<sharp> (M, P, c, x, y)"
  then have \<section>: "AndL1 (x).M y = AndL1 (d).([(d,x)]\<bullet>M) y"
    by (metis alpha(1) fresh_prodD(1) perm_fresh_fresh(1) trm.inject(6))
  with d have "(\<lambda>z'. Cut <c>.P (z').AndL1 (d).([(d, x)] \<bullet> M){x:=<c>.P} (z')) 
             = (\<lambda>z'. Cut <c>.P (z').AndL1 (x).M (z'))"
    by (metis forget(1) fresh_bij(1) fresh_prodD(1) swap_simps(1) trm.inject(6))
  with d have "(\<lambda>z'. Cut <c>.P (z').AndL1 d.([(d, x)] \<bullet> M){y:=<c>.P} z')
             = (\<lambda>z'. Cut <c>.P (z').AndL1 (x).M (z'))"
    apply(simp add: trm.inject alpha fresh_prod fresh_atm)
    by (metis abs_fresh(1) assms forget(1) fresh_atm(1) fresh_aux(1) nrename_nfresh nrename_swap)
  with d \<section> show ?thesis
    by (simp add: fresh_left calc_atm)
qed

lemma better_AndL2_substn:
  assumes a: "y\<sharp>[x].M"
  shows "(AndL2 (x).M y){y:=<c>.P} = fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL2 (x).M z')"
proof (generate_fresh "name")
  fix d:: name
  assume d: "d \<sharp> (M, P, c, x, y)"
  then have \<section>: "AndL2 (x).M y = AndL2 (d).([(d,x)]\<bullet>M) y"
    by (metis alpha(1) fresh_prodD(1) perm_fresh_fresh(1) trm.inject(7))
  with d have "(\<lambda>z'. Cut <c>.P (z').AndL2 (d).([(d, x)] \<bullet> M){x:=<c>.P} (z')) 
             = (\<lambda>z'. Cut <c>.P (z').AndL2 (x).M (z'))"
    by (metis forget(1) fresh_bij(1) fresh_prodD(1) swap_simps(1) trm.inject(7))
  with d have "(\<lambda>z'. Cut <c>.P (z').AndL2 d.([(d, x)] \<bullet> M){y:=<c>.P} z')
             = (\<lambda>z'. Cut <c>.P (z').AndL2 (x).M (z'))"
    apply(simp add: trm.inject alpha fresh_prod fresh_atm)
    by (metis abs_fresh(1) assms forget(1) fresh_atm(1) fresh_aux(1) nrename_nfresh nrename_swap)
  with d \<section> show ?thesis
    by (simp add: fresh_left calc_atm)
qed

lemma better_AndR_substc:
  assumes "c\<sharp>([a].M,[b].N)"
  shows "(AndR <a>.M <b>.N c){c:=(z).P} = fresh_fun (\<lambda>a'. Cut <a'>.(AndR <a>.M <b>.N a') (z).P)"
proof (generate_fresh "coname" , generate_fresh "coname")
  fix d :: coname
    and e :: coname
  assume d: "d \<sharp> (M, N, P, a, b, c, z)"
    and e: "e \<sharp> (M, N, P, a, b, c, z, d)"
  then have "AndR <a>.M <b>.N c = AndR <d>.([(d,a)]\<bullet>M) <e>.([(e,b)]\<bullet>N) c"
    by (perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm) auto
  with assms d e show ?thesis
    apply (auto simp: fresh_left calc_atm fresh_prod fresh_atm)
    by (metis (no_types, opaque_lifting) abs_fresh(2) forget(2) trm.inject(5))
qed

lemma better_OrL_substn:
  assumes "x\<sharp>([y].M,[z].N)"
  shows "(OrL (y).M (z).N x){x:=<c>.P} = fresh_fun (\<lambda>z'. Cut <c>.P (z').OrL (y).M (z).N z')"
proof (generate_fresh "name" , generate_fresh "name")
  fix d :: name
    and e :: name
  assume d: "d \<sharp> (M, N, P, c, x, y, z)"
    and e: "e \<sharp> (M, N, P, c, x, y, z, d)"
  with assms have "OrL (y).M (z).N x = OrL (d).([(d,y)]\<bullet>M) (e).([(e,z)]\<bullet>N) x"
    by (perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm) auto
  with assms d e show ?thesis
    apply (auto simp: fresh_left calc_atm fresh_prod fresh_atm)
    by (metis (no_types, lifting) abs_fresh(1) forget(1) trm.inject(10))
qed

lemma better_OrR1_substc:
  assumes a: "d\<sharp>[a].M"
  shows "(OrR1 <a>.M d){d:=(z).P} = fresh_fun (\<lambda>a'. Cut <a'>.OrR1 <a>.M a' (z).P)"
proof (generate_fresh "coname")
  fix c :: coname
  assume c: "c \<sharp> (M, P, a, d, z)"
  then have "OrR1 <a>.M d = OrR1 <c>.([(c,a)]\<bullet>M) d"
    by (perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm) auto
  with assms c show ?thesis
    apply (auto simp: fresh_left calc_atm fresh_prod fresh_atm)
    by (metis abs_fresh(2) forget(2) trm.inject(8))
qed

lemma better_OrR2_substc:
  assumes a: "d\<sharp>[a].M"
  shows "(OrR2 <a>.M d){d:=(z).P} = fresh_fun (\<lambda>a'. Cut <a'>.OrR2 <a>.M a' (z).P)"
proof (generate_fresh "coname")
  fix c :: coname
  assume c: "c \<sharp> (M, P, a, d, z)"
  then have "OrR2 <a>.M d = OrR2 <c>.([(c,a)]\<bullet>M) d"
    by (perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm) auto
  with assms c show ?thesis
    apply (auto simp: fresh_left calc_atm fresh_prod fresh_atm)
    by (metis abs_fresh(2) forget(2) trm.inject(9))
qed

lemma better_ImpR_substc:
  assumes "d\<sharp>[a].M"
  shows "(ImpR (x).<a>.M d){d:=(z).P} = fresh_fun (\<lambda>a'. Cut <a'>.ImpR (x).<a>.M a' (z).P)"
proof (generate_fresh "coname" , generate_fresh "name")
  fix c :: coname
    and c' :: name
  assume c: "c \<sharp> (M, P, a, d, x, z)"
    and c': "c' \<sharp> (M, P, a, d, x, z, c)"
  have \<dagger>: "ImpR (x).<a>.M d = ImpR (c').<c>.([(c,a)]\<bullet>[(c',x)]\<bullet>M) d"
    apply (rule sym)
    using c c'
    apply(perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm abs_fresh abs_perm)
    done
  with assms c c' have "fresh_fun
        (\<lambda>a'. Cut <a'>.ImpR (c').<c>.(([(c, a)] \<bullet> [(c', x)] \<bullet> M)){d:=(z).P} a' (z).P)
      = fresh_fun (\<lambda>a'. Cut <a'>.ImpR (x).<a>.M a' (z).P)"
    apply(intro arg_cong [where f="fresh_fun"])
    by(fastforce simp add: trm.inject alpha fresh_prod fresh_atm abs_perm fresh_left calc_atm abs_fresh forget)
  with assms c c' \<dagger> show ?thesis
    by (auto simp: fresh_left calc_atm forget abs_fresh)
qed

lemma better_ImpL_substn:
  assumes "y\<sharp>(M,[x].N)"
  shows "(ImpL <a>.M (x).N y){y:=<c>.P} = fresh_fun (\<lambda>z'. Cut <c>.P (z').ImpL <a>.M (x).N z')"
proof (generate_fresh "coname" , generate_fresh "name")
  fix ca :: coname
    and caa :: name
  assume d: "ca \<sharp> (M, N, P, a, c, x, y)"
    and e: "caa \<sharp> (M, N, P, a, c, x, y, ca)"
  have "ImpL <a>.M (x).N y = ImpL <ca>.([(ca,a)]\<bullet>M) (caa).([(caa,x)]\<bullet>N) y"
    apply(rule sym)
    using d e
    by(perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm abs_fresh abs_perm)
  with d e assms show ?thesis
    apply(simp add: fresh_left calc_atm forget abs_fresh)
    apply(intro arg_cong [where f="fresh_fun"] ext)
    apply(simp add: trm.inject alpha fresh_prod fresh_atm abs_perm abs_fresh fresh_left calc_atm)
    by (metis forget(1) fresh_aux(1) fresh_bij(1) swap_simps(1))
qed

lemma freshn_after_substc:
  fixes x::"name"
  assumes "x\<sharp>M{c:=(y).P}"
  shows "x\<sharp>M"
  by (meson assms fresh_def subsetD supp_subst8)

lemma freshn_after_substn:
  fixes x::"name"
  assumes "x\<sharp>M{y:=<c>.P}" "x\<noteq>y"
  shows "x\<sharp>M"
  by (meson DiffI assms fresh_def singleton_iff subset_eq supp_subst5)

lemma freshc_after_substc:
  fixes a::"coname"
  assumes "a\<sharp>M{c:=(y).P}" "a\<noteq>c"
  shows "a\<sharp>M"
  by (meson Diff_iff assms fresh_def in_mono singleton_iff supp_subst7)

lemma freshc_after_substn:
  fixes a::"coname"
  assumes "a\<sharp>M{y:=<c>.P}" 
  shows "a\<sharp>M"
  by (meson assms fresh_def subset_iff supp_subst6)

lemma substn_crename_comm:
  assumes "c\<noteq>a" "c\<noteq>b"
  shows "M{x:=<c>.P}[a\<turnstile>c>b] = M[a\<turnstile>c>b]{x:=<c>.(P[a\<turnstile>c>b])}"
using assms
proof (nominal_induct M avoiding: x c P a b rule: trm.strong_induct)
  case (Ax name coname)
  then show ?case
    by(auto simp: better_crename_Cut fresh_atm)
next
  case (Cut coname trm1 name trm2)
  then show ?case
    apply(simp add: rename_fresh better_crename_Cut fresh_atm)
    by (meson crename_ax)
next
  case (NotL coname trm name)
  obtain x'::name where "x'\<sharp>(trm{x:=<c>.P},P,P[a\<turnstile>c>b],x,trm[a\<turnstile>c>b]{x:=<c>.P[a\<turnstile>c>b]})"
    by (meson exists_fresh(1) fs_name1)
  with NotL show ?case
    apply (simp add: subst_fresh rename_fresh trm.inject)
    by (force simp: fresh_prod fresh_fun_simp_NotL better_crename_Cut fresh_atm)
next
  case (AndL1 name1 trm name2)
  obtain x'::name where "x'\<sharp>(trm{x:=<c>.P},P,P[a\<turnstile>c>b],name1,trm[a\<turnstile>c>b]{x:=<c>.P[a\<turnstile>c>b]})"
    by (meson exists_fresh(1) fs_name1)
  with AndL1 show ?case
    apply (simp add: subst_fresh rename_fresh trm.inject)
    apply (force simp: fresh_prod fresh_fun_simp_AndL1 better_crename_Cut fresh_atm)
    done
next
  case (AndL2 name1 trm name2)
  obtain x'::name where x': "x'\<sharp>(trm{x:=<c>.P},P,P[a\<turnstile>c>b],name1,trm[a\<turnstile>c>b]{x:=<c>.P[a\<turnstile>c>b]})"
    by (meson exists_fresh(1) fs_name1)
  with AndL2 show ?case
    apply (simp add: subst_fresh rename_fresh trm.inject)
    apply (auto simp: fresh_prod fresh_fun_simp_AndL2 better_crename_Cut fresh_atm)
    done
next
  case (OrL name1 trm1 name2 trm2 name3)
  obtain x'::name where x': "x'\<sharp>(trm1{x:=<c>.P},trm2{x:=<c>.P},P,P[a\<turnstile>c>b],name1,name2,
                                  trm1[a\<turnstile>c>b]{x:=<c>.P[a\<turnstile>c>b]},trm2[a\<turnstile>c>b]{x:=<c>.P[a\<turnstile>c>b]})"
    by (meson exists_fresh(1) fs_name1)
  with OrL show ?case
    apply (simp add: subst_fresh rename_fresh trm.inject)
    apply (auto simp: fresh_atm subst_fresh fresh_prod fresh_fun_simp_OrL better_crename_Cut)
    done
  next
  case (ImpL coname trm1 name1 trm2 name2)
  obtain x'::name where x': "x'\<sharp>(trm1{x:=<c>.P},trm2{x:=<c>.P},P,P[a\<turnstile>c>b],name1,name2,
                                  trm1[a\<turnstile>c>b]{x:=<c>.P[a\<turnstile>c>b]},trm2[a\<turnstile>c>b]{x:=<c>.P[a\<turnstile>c>b]})"
    by (meson exists_fresh(1) fs_name1)
  with ImpL show ?case
    apply (simp add: subst_fresh rename_fresh trm.inject)
    apply (auto simp: fresh_atm subst_fresh fresh_prod fresh_fun_simp_ImpL better_crename_Cut)
    done
qed (auto simp: subst_fresh rename_fresh)


lemma substc_crename_comm:
  assumes "c\<noteq>a" "c\<noteq>b"
  shows "M{c:=(x).P}[a\<turnstile>c>b] = M[a\<turnstile>c>b]{c:=(x).(P[a\<turnstile>c>b])}"
using assms
proof (nominal_induct M avoiding: x c P a b rule: trm.strong_induct)
  case (Ax name coname)
  then show ?case
    by(auto simp: better_crename_Cut fresh_atm)
next
  case (Cut coname trm1 name trm2)
  then show ?case
    apply(simp add: rename_fresh  better_crename_Cut)
    by (meson crename_ax)
next
  case (NotR name trm coname)
  obtain c'::coname where "c'\<sharp>(a,b,trm{coname:=(x).P},P,P[a\<turnstile>c>b],x,trm[a\<turnstile>c>b]{coname:=(x).P[a\<turnstile>c>b]})"
    by (meson exists_fresh' fs_coname1)
  with NotR show ?case
    apply(simp add: subst_fresh rename_fresh trm.inject)
    by(auto simp: fresh_prod fresh_fun_simp_NotR better_crename_Cut fresh_atm)
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  obtain c'::coname where "c'\<sharp>(coname1,coname2,a,b,trm1{coname3:=(x).P},trm2{coname3:=(x).P},
                   P,P[a\<turnstile>c>b],x,trm1[a\<turnstile>c>b]{coname3:=(x).P[a\<turnstile>c>b]},trm2[a\<turnstile>c>b]{coname3:=(x).P[a\<turnstile>c>b]})"
    by (meson exists_fresh' fs_coname1)
  with AndR show ?case
    apply(simp add: subst_fresh rename_fresh trm.inject)
    by (auto simp: fresh_prod fresh_fun_simp_AndR better_crename_Cut subst_fresh fresh_atm)
next
  case (OrR1 coname1 trm coname2)
  obtain c'::coname where "c'\<sharp>(coname1,trm{coname2:=(x).P},P,P[a\<turnstile>c>b],a,b, trm[a\<turnstile>c>b]{coname2:=(x).P[a\<turnstile>c>b]})"
    by (meson exists_fresh' fs_coname1)
  with OrR1 show ?case
    apply(simp add: subst_fresh rename_fresh trm.inject)
    by(auto simp: fresh_prod fresh_fun_simp_OrR1 better_crename_Cut fresh_atm)
next
  case (OrR2 coname1 trm coname2)
  obtain c'::coname where "c'\<sharp>(coname1,trm{coname2:=(x).P},P,P[a\<turnstile>c>b],a,b, trm[a\<turnstile>c>b]{coname2:=(x).P[a\<turnstile>c>b]})"
    by (meson exists_fresh' fs_coname1)
  with OrR2 show ?case
    apply(simp add: subst_fresh rename_fresh trm.inject)
    by(auto simp: fresh_prod fresh_fun_simp_OrR2 better_crename_Cut fresh_atm)
next
  case (ImpR name coname1 trm coname2)
  obtain c'::coname where "c'\<sharp>(coname1,trm{coname2:=(x).P},P,P[a\<turnstile>c>b],a,b, trm[a\<turnstile>c>b]{coname2:=(x).P[a\<turnstile>c>b]})"
    by (meson exists_fresh' fs_coname1)
  with ImpR show ?case
    apply(simp add: subst_fresh rename_fresh trm.inject)
    by(auto simp: fresh_prod fresh_fun_simp_ImpR better_crename_Cut fresh_atm)
qed (auto simp: subst_fresh rename_fresh trm.inject)


lemma substn_nrename_comm:
  assumes "x\<noteq>y" "x\<noteq>z"
  shows "M{x:=<c>.P}[y\<turnstile>n>z] = M[y\<turnstile>n>z]{x:=<c>.(P[y\<turnstile>n>z])}"
using assms
proof (nominal_induct M avoiding: x c P y z rule: trm.strong_induct)
  case (Ax name coname)
  then show ?case
    by (auto simp: better_nrename_Cut fresh_atm)
next
  case (Cut coname trm1 name trm2)
  then show ?case
    apply(clarsimp simp: subst_fresh rename_fresh trm.inject better_nrename_Cut)
    by (meson nrename_ax)
next
  case (NotL coname trm name)
  obtain x'::name where "x'\<sharp>(y,z,trm{x:=<c>.P},P,P[y\<turnstile>n>z],x,trm[y\<turnstile>n>z]{x:=<c>.P[y\<turnstile>n>z]})"
    by (meson exists_fresh' fs_name1)
  with NotL show ?case 
    apply(clarsimp simp: rename_fresh trm.inject)
    by (auto simp add: fresh_prod fresh_fun_simp_NotL better_nrename_Cut fresh_atm)
next
  case (AndL1 name1 trm name2)  
  obtain x'::name where "x'\<sharp>(trm{x:=<c>.P},P,P[y\<turnstile>n>z],name1,trm[y\<turnstile>n>z]{x:=<c>.P[y\<turnstile>n>z]},y,z)"
    by (meson exists_fresh' fs_name1)
  with AndL1 show ?case
    apply(clarsimp simp: subst_fresh rename_fresh trm.inject)
    by (auto simp add: fresh_prod fresh_fun_simp_AndL1 better_nrename_Cut fresh_atm)
next
  case (AndL2 name1 trm name2)
  obtain x'::name where "x'\<sharp>(trm{x:=<c>.P},P,P[y\<turnstile>n>z],name1,trm[y\<turnstile>n>z]{x:=<c>.P[y\<turnstile>n>z]},y,z)"
    by (meson exists_fresh' fs_name1)
  with AndL2 show ?case
    apply(clarsimp simp: subst_fresh rename_fresh trm.inject)
    by (auto simp add: fresh_prod fresh_fun_simp_AndL2 better_nrename_Cut fresh_atm)
next
  case (OrL name1 trm1 name2 trm2 name3)
  obtain x'::name where "x'\<sharp>(trm1{x:=<c>.P},trm2{x:=<c>.P},P,P[y\<turnstile>n>z],name1,name2,y,z,
                                  trm1[y\<turnstile>n>z]{x:=<c>.P[y\<turnstile>n>z]},trm2[y\<turnstile>n>z]{x:=<c>.P[y\<turnstile>n>z]})"
    by (meson exists_fresh' fs_name1)
  with OrL show ?case
    apply (clarsimp simp: subst_fresh rename_fresh trm.inject)
    by (auto simp add: fresh_prod fresh_fun_simp_OrL better_nrename_Cut subst_fresh fresh_atm)
next
  case (ImpL coname trm1 name1 trm2 name2)
  obtain x'::name where "x'\<sharp>(trm1{x:=<c>.P},trm2{x:=<c>.P},P,P[y\<turnstile>n>z],name1,name2,y,z,
                                  trm1[y\<turnstile>n>z]{x:=<c>.P[y\<turnstile>n>z]},trm2[y\<turnstile>n>z]{x:=<c>.P[y\<turnstile>n>z]})"
    by (meson exists_fresh' fs_name1)
  with ImpL show ?case
    apply (clarsimp simp: subst_fresh rename_fresh trm.inject)
    by (auto simp add: fresh_prod fresh_fun_simp_ImpL better_nrename_Cut subst_fresh fresh_atm)
qed (auto simp: subst_fresh rename_fresh trm.inject)
 


lemma substc_nrename_comm:
  assumes "x\<noteq>y" "x\<noteq>z"
  shows "M{c:=(x).P}[y\<turnstile>n>z] = M[y\<turnstile>n>z]{c:=(x).(P[y\<turnstile>n>z])}"
using assms
proof (nominal_induct M avoiding: x c P y z rule: trm.strong_induct)
  case (Ax name coname)
  then show ?case 
    by (auto simp: subst_fresh rename_fresh trm.inject better_nrename_Cut fresh_atm)
next
  case (Cut coname trm1 name trm2)
  then show ?case
    apply (clarsimp simp: subst_fresh rename_fresh trm.inject better_nrename_Cut fresh_atm)
    by (metis nrename_ax)
next
  case (NotR name trm coname)
  obtain c'::coname where "c'\<sharp>(y,z,trm{coname:=(x).P},P,P[y\<turnstile>n>z],x,trm[y\<turnstile>n>z]{coname:=(x).P[y\<turnstile>n>z]})"
    by (meson exists_fresh' fs_coname1)
  with NotR show ?case
    apply(simp add: subst_fresh rename_fresh trm.inject)
    by (auto simp add: fresh_prod fresh_fun_simp_NotR better_nrename_Cut fresh_atm)
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  obtain c'::coname where "c'\<sharp>(coname1,coname2,y,z,trm1{coname3:=(x).P},trm2{coname3:=(x).P},
                   P,P[y\<turnstile>n>z],x,trm1[y\<turnstile>n>z]{coname3:=(x).P[y\<turnstile>n>z]},trm2[y\<turnstile>n>z]{coname3:=(x).P[y\<turnstile>n>z]})"
    by (meson exists_fresh' fs_coname1)
  with AndR show ?case
    apply(simp add: subst_fresh rename_fresh trm.inject)
    by (auto simp add: fresh_prod fresh_fun_simp_AndR better_nrename_Cut fresh_atm subst_fresh)
next
  case (OrR1 coname1 trm coname2)
  obtain c'::coname where "c'\<sharp>(coname1,trm{coname2:=(x).P},P,P[y\<turnstile>n>z],y,z,
                         trm[y\<turnstile>n>z]{coname2:=(x).P[y\<turnstile>n>z]})"
    by (meson exists_fresh' fs_coname1)
  with OrR1 show ?case
    apply(simp add: subst_fresh rename_fresh trm.inject)
    by (auto simp add: fresh_prod fresh_fun_simp_OrR1 better_nrename_Cut fresh_atm subst_fresh)
next
  case (OrR2 coname1 trm coname2)
  obtain c'::coname where "c'\<sharp>(coname1,trm{coname2:=(x).P},P,P[y\<turnstile>n>z],y,z,
                         trm[y\<turnstile>n>z]{coname2:=(x).P[y\<turnstile>n>z]})"
    by (meson exists_fresh' fs_coname1)
  with OrR2 show ?case
    apply(simp add: subst_fresh rename_fresh trm.inject)
    by (auto simp add: fresh_prod fresh_fun_simp_OrR2 better_nrename_Cut fresh_atm subst_fresh)
next
  case (ImpR name coname1 trm coname2)
  obtain c'::coname where "c'\<sharp>(coname1,trm{coname2:=(x).P},P,P[y\<turnstile>n>z],y,z,
                         trm[y\<turnstile>n>z]{coname2:=(x).P[y\<turnstile>n>z]})"
    by (meson exists_fresh' fs_coname1)
  with ImpR show ?case
    apply(simp add: subst_fresh rename_fresh trm.inject)
    by (auto simp add: fresh_prod fresh_fun_simp_ImpR better_nrename_Cut fresh_atm subst_fresh)
qed (auto simp: subst_fresh rename_fresh trm.inject)


lemma substn_crename_comm':
  assumes "a\<noteq>c" "a\<sharp>P"
  shows "M{x:=<c>.P}[a\<turnstile>c>b] = M[a\<turnstile>c>b]{x:=<c>.P}"
proof -
  obtain c'::"coname" where fs2: "c'\<sharp>(c,P,a,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  have eq: "M{x:=<c>.P} = M{x:=<c'>.([(c',c)]\<bullet>P)}"
    using fs2 substn_rename4 by force
   have eq': "M[a\<turnstile>c>b]{x:=<c>.P} = M[a\<turnstile>c>b]{x:=<c'>.([(c',c)]\<bullet>P)}"
    using fs2 by (simp add: substn_rename4)
  have eq2: "([(c',c)]\<bullet>P)[a\<turnstile>c>b] = ([(c',c)]\<bullet>P)" using fs2 assms
    by (metis crename_fresh fresh_atm(2) fresh_aux(2) fresh_prod)
  have "M{x:=<c>.P}[a\<turnstile>c>b] = M{x:=<c'>.([(c',c)]\<bullet>P)}[a\<turnstile>c>b]" using eq by simp
  also have "\<dots> = M[a\<turnstile>c>b]{x:=<c'>.(([(c',c)]\<bullet>P)[a\<turnstile>c>b])}"
    using fs2
    by (simp add: fresh_atm(2) fresh_prod substn_crename_comm)
  also have "\<dots> = M[a\<turnstile>c>b]{x:=<c'>.(([(c',c)]\<bullet>P))}" using eq2 by simp
  also have "\<dots> = M[a\<turnstile>c>b]{x:=<c>.P}" using eq' by simp 
  finally show ?thesis by simp
qed

lemma substc_crename_comm':
  assumes "c\<noteq>a" "c\<noteq>b" "a\<sharp>P"
  shows "M{c:=(x).P}[a\<turnstile>c>b] = M[a\<turnstile>c>b]{c:=(x).P}"
proof -
  obtain c'::"coname" where fs2: "c'\<sharp>(c,M,a,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  have eq: "M{c:=(x).P} = ([(c',c)]\<bullet>M){c':=(x).P}"
    using fs2 by (simp add: substc_rename1)
   have eq': "([(c',c)]\<bullet>(M[a\<turnstile>c>b])){c':=(x).P} = M[a\<turnstile>c>b]{c:=(x).P}"
    using fs2 by (metis crename_cfresh' fresh_prod substc_rename1)
  have eq2: "([(c',c)]\<bullet>M)[a\<turnstile>c>b] = ([(c',c)]\<bullet>(M[a\<turnstile>c>b]))" using fs2 assms
    by (simp add: crename_coname_eqvt fresh_atm(2) fresh_prod swap_simps(6))
  have "M{c:=(x).P}[a\<turnstile>c>b] = ([(c',c)]\<bullet>M){c':=(x).P}[a\<turnstile>c>b]" using eq by simp
  also have "\<dots> = ([(c',c)]\<bullet>M)[a\<turnstile>c>b]{c':=(x).P[a\<turnstile>c>b]}"
    using fs2 assms
    by (metis crename_fresh eq eq' eq2 substc_crename_comm)
  also have "\<dots> = ([(c',c)]\<bullet>(M[a\<turnstile>c>b])){c':=(x).P[a\<turnstile>c>b]}" using eq2 by simp
  also have "\<dots> = ([(c',c)]\<bullet>(M[a\<turnstile>c>b])){c':=(x).P}" 
    using assms by (simp add: rename_fresh)
  also have "\<dots> = M[a\<turnstile>c>b]{c:=(x).P}" using eq' by simp
  finally show ?thesis by simp
qed

lemma substn_nrename_comm':
  assumes "x\<noteq>y" "x\<noteq>z" "y\<sharp>P"
  shows "M{x:=<c>.P}[y\<turnstile>n>z] = M[y\<turnstile>n>z]{x:=<c>.P}"
proof -
  obtain x'::"name" where fs2: "x'\<sharp>(x,M,y,z)" by (rule exists_fresh(1), rule fin_supp, blast)
  have eq: "M{x:=<c>.P} = ([(x',x)]\<bullet>M){x':=<c>.P}"
    using fs2 by (simp add: substn_rename3)
   have eq': "([(x',x)]\<bullet>(M[y\<turnstile>n>z])){x':=<c>.P} = M[y\<turnstile>n>z]{x:=<c>.P}"
    using fs2 by (metis fresh_prod nrename_nfresh' substn_rename3)
  have eq2: "([(x',x)]\<bullet>M)[y\<turnstile>n>z] = ([(x',x)]\<bullet>(M[y\<turnstile>n>z]))" 
    using fs2 by (simp add: assms fresh_atm(1) fresh_prod nrename_name_eqvt swap_simps(5)) 
  have "M{x:=<c>.P}[y\<turnstile>n>z] = ([(x',x)]\<bullet>M){x':=<c>.P}[y\<turnstile>n>z]" using eq by simp
  also have "\<dots> = ([(x',x)]\<bullet>M)[y\<turnstile>n>z]{x':=<c>.P[y\<turnstile>n>z]}"
    using fs2 by (metis assms eq eq' eq2 nrename_fresh substn_nrename_comm)
  also have "\<dots> = ([(x',x)]\<bullet>(M[y\<turnstile>n>z])){x':=<c>.P[y\<turnstile>n>z]}" using eq2 by simp
  also have "\<dots> = ([(x',x)]\<bullet>(M[y\<turnstile>n>z])){x':=<c>.P}" using assms by (simp add: rename_fresh)
  also have "\<dots> = M[y\<turnstile>n>z]{x:=<c>.P}" using eq' by simp
  finally show ?thesis by simp
qed

lemma substc_nrename_comm':
  assumes "x\<noteq>y" "y\<sharp>P"
  shows "M{c:=(x).P}[y\<turnstile>n>z] = M[y\<turnstile>n>z]{c:=(x).P}"
proof -
  obtain x'::"name" where fs2: "x'\<sharp>(x,P,y,z)" by (rule exists_fresh(1), rule fin_supp, blast)
  have eq: "M{c:=(x).P} = M{c:=(x').([(x',x)]\<bullet>P)}"
    using fs2
    using substc_rename2 by auto
   have eq': "M[y\<turnstile>n>z]{c:=(x).P} = M[y\<turnstile>n>z]{c:=(x').([(x',x)]\<bullet>P)}"
    using fs2 by (simp add: substc_rename2)
  have eq2: "([(x',x)]\<bullet>P)[y\<turnstile>n>z] = ([(x',x)]\<bullet>P)"
    using fs2 by (metis assms(2) fresh_atm(1) fresh_aux(1) fresh_prod nrename_fresh)
  have "M{c:=(x).P}[y\<turnstile>n>z] = M{c:=(x').([(x',x)]\<bullet>P)}[y\<turnstile>n>z]" using eq by simp
  also have "\<dots> = M[y\<turnstile>n>z]{c:=(x').(([(x',x)]\<bullet>P)[y\<turnstile>n>z])}"
    using fs2 by (simp add: fresh_atm(1) fresh_prod substc_nrename_comm)
  also have "\<dots> = M[y\<turnstile>n>z]{c:=(x').(([(x',x)]\<bullet>P))}" using eq2 by simp
  also have "\<dots> = M[y\<turnstile>n>z]{c:=(x).P}" using eq' by simp 
  finally show ?thesis by simp
qed

lemmas subst_comm = substn_crename_comm substc_crename_comm
                    substn_nrename_comm substc_nrename_comm
lemmas subst_comm' = substn_crename_comm' substc_crename_comm'
                     substn_nrename_comm' substc_nrename_comm'

text \<open>typing contexts\<close>

type_synonym ctxtn = "(name\<times>ty) list"
type_synonym ctxtc = "(coname\<times>ty) list"

inductive
  validc :: "ctxtc \<Rightarrow> bool"
where
  vc1[intro]: "validc []"
| vc2[intro]: "\<lbrakk>a\<sharp>\<Delta>; validc \<Delta>\<rbrakk> \<Longrightarrow> validc ((a,T)#\<Delta>)"

equivariance validc

inductive
  validn :: "ctxtn \<Rightarrow> bool"
where
  vn1[intro]: "validn []"
| vn2[intro]: "\<lbrakk>x\<sharp>\<Gamma>; validn \<Gamma>\<rbrakk> \<Longrightarrow> validn ((x,T)#\<Gamma>)"

equivariance validn

lemma fresh_ctxt:
  fixes a::"coname"
  and   x::"name"
  and   \<Gamma>::"ctxtn"
  and   \<Delta>::"ctxtc"
  shows "a\<sharp>\<Gamma>" and "x\<sharp>\<Delta>"
proof -
  show "a\<sharp>\<Gamma>" by (induct \<Gamma>) (auto simp: fresh_list_nil fresh_list_cons fresh_prod fresh_atm fresh_ty)
next
  show "x\<sharp>\<Delta>" by (induct \<Delta>) (auto simp: fresh_list_nil fresh_list_cons fresh_prod fresh_atm fresh_ty)
qed

text \<open>cut-reductions\<close>

declare abs_perm[eqvt]

inductive
  fin :: "trm \<Rightarrow> name \<Rightarrow> bool"
where
  [intro]: "fin (Ax x a) x"
| [intro]: "x\<sharp>M \<Longrightarrow> fin (NotL <a>.M x) x"
| [intro]: "y\<sharp>[x].M \<Longrightarrow> fin (AndL1 (x).M y) y"
| [intro]: "y\<sharp>[x].M \<Longrightarrow> fin (AndL2 (x).M y) y"
| [intro]: "\<lbrakk>z\<sharp>[x].M;z\<sharp>[y].N\<rbrakk> \<Longrightarrow> fin (OrL (x).M (y).N z) z"
| [intro]: "\<lbrakk>y\<sharp>M;y\<sharp>[x].N\<rbrakk> \<Longrightarrow> fin (ImpL <a>.M (x).N y) y"

equivariance fin

lemma fin_Ax_elim:
  assumes "fin (Ax x a) y"
  shows "x=y"
  using assms fin.simps trm.inject(1) by auto

lemma fin_NotL_elim:
  assumes a: "fin (NotL <a>.M x) y"
  shows "x=y \<and> x\<sharp>M"
  using assms 
  by (cases rule: fin.cases; simp add: trm.inject; metis abs_fresh(5))

lemma fin_AndL1_elim:
  assumes a: "fin (AndL1 (x).M y) z"
  shows "z=y \<and> z\<sharp>[x].M"
  using assms by (cases rule: fin.cases; simp add: trm.inject)

lemma fin_AndL2_elim:
  assumes a: "fin (AndL2 (x).M y) z"
  shows "z=y \<and> z\<sharp>[x].M"
  using assms by (cases rule: fin.cases; simp add: trm.inject)

lemma fin_OrL_elim:
  assumes a: "fin (OrL (x).M (y).N u) z"
  shows "z=u \<and> z\<sharp>[x].M \<and> z\<sharp>[y].N"
  using assms by (cases rule: fin.cases; simp add: trm.inject)

lemma fin_ImpL_elim:
  assumes a: "fin (ImpL <a>.M (x).N z) y"
  shows "z=y \<and> z\<sharp>M \<and> z\<sharp>[x].N"
  using assms
  by (cases rule: fin.cases; simp add: trm.inject; metis abs_fresh(5))
 

lemma fin_rest_elims:
  shows "fin (Cut <a>.M (x).N) y \<Longrightarrow> False"
  and   "fin (NotR (x).M c) y \<Longrightarrow> False"
  and   "fin (AndR <a>.M <b>.N c) y \<Longrightarrow> False"
  and   "fin (OrR1 <a>.M b) y \<Longrightarrow> False"
  and   "fin (OrR2 <a>.M b) y \<Longrightarrow> False"
  and   "fin (ImpR (x).<a>.M b) y \<Longrightarrow> False"
by (erule fin.cases, simp_all add: trm.inject)+

lemmas fin_elims = fin_Ax_elim fin_NotL_elim fin_AndL1_elim fin_AndL2_elim fin_OrL_elim 
                   fin_ImpL_elim fin_rest_elims

lemma fin_rename:
  shows "fin M x \<Longrightarrow> fin ([(x',x)]\<bullet>M) x'"
by (induct rule: fin.induct)
   (auto simp: calc_atm simp add: fresh_left abs_fresh)

lemma not_fin_subst1:
  assumes "\<not>(fin M x)" 
  shows "\<not>(fin (M{c:=(y).P}) x)"
using assms 
proof (nominal_induct M avoiding: x c y P rule: trm.strong_induct)
  case (Ax name coname)
  then show ?case 
    using fin_rest_elims(1) substc.simps(1) by presburger
next
  case (Cut coname trm1 name trm2)
  then show ?case
    using fin_rest_elims(1) substc.simps(1) by simp presburger
next
  case (NotR name trm coname)
  obtain a'::coname where "a'\<sharp>(trm{coname:=(y).P},P,x)"
    by (meson exists_fresh(2) fs_coname1)
  with NotR show ?case
    apply (simp add: fresh_prod trm.inject)
    using fresh_fun_simp_NotR fin_rest_elims by fastforce
next
  case (NotL coname trm name)
  then show ?case 
    using fin_NotL_elim freshn_after_substc by simp blast
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  obtain a'::coname where "a'\<sharp>(trm1{coname3:=(y).P},trm2{coname3:=(y).P},P,coname1,coname2,coname3,x)"
    by (meson exists_fresh(2) fs_coname1)
  with AndR show ?case
    apply (simp add: fresh_prod trm.inject)
    using fresh_fun_simp_AndR fin_rest_elims by fastforce
next
  case (AndL1 name1 trm name2)
  then show ?case 
    using fin_AndL1_elim freshn_after_substc
    by simp (metis abs_fresh(1) fin.intros(3))
next
  case (AndL2 name1 trm name2)
  then show ?case 
    using fin_AndL2_elim freshn_after_substc
    by simp (metis abs_fresh(1) fin.intros(4))
next
  case (OrR1 coname1 trm coname2)
  obtain a'::coname where "a'\<sharp>(trm{coname2:=(y).P},coname1,P,x)"
    by (meson exists_fresh(2) fs_coname1)
  with OrR1 show ?case
    apply (simp add: fresh_prod trm.inject)
    using fresh_fun_simp_OrR1 fin_rest_elims by fastforce
next
  case (OrR2 coname1 trm coname2)
  obtain a'::coname where "a'\<sharp>(trm{coname2:=(y).P},coname1,P,x)"
    by (meson exists_fresh(2) fs_coname1)
  with OrR2 show ?case
    apply (simp add: fresh_prod trm.inject)
    using fresh_fun_simp_OrR2 fin_rest_elims by fastforce
next
  case (OrL name1 trm1 name2 trm2 name3)
  then show ?case
    by simp (metis abs_fresh(1) fin.intros(5) fin_OrL_elim freshn_after_substc)
next
  case (ImpR name coname1 trm coname2)
  obtain a'::coname where "a'\<sharp>(trm{coname2:=(y).P},coname1,P,x)"
    by (meson exists_fresh(2) fs_coname1)
  with ImpR show ?case
    apply (simp add: fresh_prod trm.inject)
    using fresh_fun_simp_ImpR fin_rest_elims by fastforce
next
  case (ImpL coname trm1 name1 trm2 name2)
  then show ?case
    by simp (metis abs_fresh(1) fin.intros(6) fin_ImpL_elim freshn_after_substc)
qed



lemma not_fin_subst2:
  assumes "\<not>(fin M x)" 
  shows "\<not>(fin (M{y:=<c>.P}) x)"
using assms 
proof (nominal_induct M avoiding: x c y P rule: trm.strong_induct)
  case (Ax name coname)
  then show ?case
    using fin_rest_elims(1) substn.simps(1) by presburger
next
  case (Cut coname trm1 name trm2)
  then show ?case
    using fin_rest_elims(1) substc.simps(1) by simp presburger
next
  case (NotR name trm coname)
  with fin_rest_elims show ?case
    by (fastforce simp add: fresh_prod trm.inject)
next
  case (NotL coname trm name)
  obtain a'::name where "a'\<sharp>(trm{y:=<c>.P},P,x)"
    by (meson exists_fresh(1) fs_name1)
  with NotL show ?case 
    apply (clarsimp simp: fresh_prod fresh_fun_simp_NotL trm.inject)
    by (metis fin.intros(2) fin_NotL_elim fin_rest_elims(1) freshn_after_substn)
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  obtain a'::name where "a'\<sharp>(trm1{coname3:=(y).P},trm2{coname3:=(y).P},P,coname1,coname2,coname3,x)"
    by (meson exists_fresh(1) fs_name1)
  with AndR fin_rest_elims show ?case
    by (fastforce simp add: fresh_prod trm.inject)
next
  case (AndL1 name1 trm name2)
  obtain a'::name where "a'\<sharp>(trm{y:=<c>.P},P,name1,x)"
    by (meson exists_fresh(1) fs_name1)
  with AndL1 show ?case 
    apply (clarsimp simp: fresh_prod fresh_fun_simp_AndL1 trm.inject)
    by (metis abs_fresh(1) fin.intros(3) fin_AndL1_elim fin_rest_elims(1) freshn_after_substn)
next
  case (AndL2 name1 trm name2)
  obtain a'::name where "a'\<sharp>(trm{y:=<c>.P},P,name1,x)"
    by (meson exists_fresh(1) fs_name1)
  with AndL2 show ?case 
    apply (clarsimp simp: fresh_prod fresh_fun_simp_AndL2 trm.inject)
    by (metis abs_fresh(1) fin.intros(4) fin_AndL2_elim fin_rest_elims(1) freshn_after_substn)
next
  case (OrR1 coname1 trm coname2)
  then show ?case
    using fin_rest_elims by (fastforce simp: fresh_prod trm.inject)
next
  case (OrR2 coname1 trm coname2)
  then show ?case
    using fin_rest_elims by (fastforce simp: fresh_prod trm.inject)
next
  case (OrL name1 trm1 name2 trm2 name3)
  obtain a'::name where "a'\<sharp>(trm1{y:=<c>.P},trm2{y:=<c>.P},name1,name2,P,x)"
    by (meson exists_fresh(1) fs_name1)
  with OrL show ?case  
    apply (simp add: fresh_prod trm.inject)
    by (metis (full_types) abs_fresh(1) fin.intros(5) fin_OrL_elim fin_rest_elims(1) fresh_fun_simp_OrL freshn_after_substn)
next
  case (ImpR name coname1 trm coname2)
  with fin_rest_elims show ?case
    by (fastforce simp add: fresh_prod trm.inject)
next
  case (ImpL coname trm1 name1 trm2 name2)
  obtain a'::name where "a'\<sharp>(trm1{name2:=<c>.P},trm2{name2:=<c>.P},name1,P,x)"
    by (meson exists_fresh(1) fs_name1)
  with ImpL show ?case
    apply (simp add: fresh_prod trm.inject)
    by (metis abs_fresh(1) fin.intros(6) fin_ImpL_elim fin_rest_elims(1) fresh_fun_simp_ImpL freshn_after_substn)
qed


lemma fin_subst1:
  assumes "fin M x" "x\<noteq>y" "x\<sharp>P"
  shows "fin (M{y:=<c>.P}) x"
  using assms
proof (nominal_induct M avoiding: x y c P rule: trm.strong_induct)
  case (AndL1 name1 trm name2)
  then show ?case
    apply (clarsimp simp add: subst_fresh abs_fresh dest!: fin_AndL1_elim)
    by (metis abs_fresh(1) fin.intros(3) fresh_prod subst_fresh(3))
next
  case (AndL2 name1 trm name2)
  then show ?case
    apply (clarsimp simp add: subst_fresh abs_fresh dest!: fin_AndL2_elim)
    by (metis abs_fresh(1) fin.intros(4) fresh_prod subst_fresh(3))
next
  case (OrR1 coname1 trm coname2)
  then show ?case
    by (auto simp add: subst_fresh abs_fresh dest!: fin_rest_elims)
next
  case (OrR2 coname1 trm coname2)
  then show ?case
    by (auto simp add: subst_fresh abs_fresh dest!: fin_rest_elims)
next
  case (OrL name1 trm1 name2 trm2 name3)
  then show ?case
    apply (clarsimp simp add: subst_fresh abs_fresh)
    by (metis abs_fresh(1) fin.intros(5) fin_OrL_elim fresh_prod subst_fresh(3))
next
  case (ImpR name coname1 trm coname2)
  then show ?case
    by (auto simp add: subst_fresh abs_fresh dest!: fin_rest_elims)
next
  case (ImpL coname trm1 name1 trm2 name2)
  then show ?case
    apply (clarsimp simp add: subst_fresh abs_fresh)
    by (metis abs_fresh(1) fin.intros(6) fin_ImpL_elim fresh_prod subst_fresh(3))
qed (auto dest!: fin_elims simp add: subst_fresh abs_fresh)


thm abs_fresh fresh_prod

lemma fin_subst2:
  assumes "fin M y" "x\<noteq>y" "y\<sharp>P" "M\<noteq>Ax y c" 
  shows "fin (M{c:=(x).P}) y"
using assms
proof (nominal_induct M avoiding: x y c P rule: trm.strong_induct)
  case (Ax name coname)
  then show ?case
    using fin_Ax_elim by force
next
  case (NotL coname trm name)
  then show ?case
    by simp (metis fin.intros(2) fin_NotL_elim fresh_prod subst_fresh(5)) 
next
  case (AndL1 name1 trm name2)
  then show ?case 
    by simp (metis abs_fresh(1) fin.intros(3) fin_AndL1_elim fresh_prod subst_fresh(5))
next
  case (AndL2 name1 trm name2)
  then show ?case 
    by simp (metis abs_fresh(1) fin.intros(4) fin_AndL2_elim fresh_prod subst_fresh(5)) 
next
  case (OrL name1 trm1 name2 trm2 name3)
  then show ?case
    by simp (metis abs_fresh(1) fin.intros(5) fin_OrL_elim fresh_prod subst_fresh(5))
next
  case (ImpL coname trm1 name1 trm2 name2)
  then show ?case
    by simp (metis abs_fresh(1) fin.intros(6) fin_ImpL_elim fresh_prod subst_fresh(5))
qed (use fin_rest_elims in force)+


lemma fin_substn_nrename:
  assumes "fin M x" "x\<noteq>y" "x\<sharp>P"
  shows "M[x\<turnstile>n>y]{y:=<c>.P} = Cut <c>.P (x).(M{y:=<c>.P})"
using assms [[simproc del: defined_all]]
proof (nominal_induct M avoiding: x y c P rule: trm.strong_induct)
  case (Ax name coname)
  then show ?case
    by (metis fin_Ax_elim fresh_atm(1,3) fresh_prod nrename_swap subst_rename(3) substn.simps(1) trm.fresh(1))
next
  case (NotL coname trm name)
  obtain z::name where "z \<sharp> (trm,y,x,P,trm[x\<turnstile>n>y]{y:=<c>.P})"
    by (meson exists_fresh(1) fs_name1)
  with NotL show ?case 
    apply (clarsimp simp add: fresh_prod fresh_fun_simp_NotL trm.inject alpha fresh_atm calc_atm abs_fresh)
    by (metis fin_NotL_elim nrename_fresh nrename_swap substn_nrename_comm')
next
  case (AndL1 name1 trm name2)
  obtain z::name where "z \<sharp> (name2,name1,P,trm[name2\<turnstile>n>y]{y:=<c>.P},y,P,trm)"
    by (meson exists_fresh(1) fs_name1)
  with AndL1 show ?case 
    using fin_AndL1_elim[OF AndL1.prems(1)]
    by simp (metis abs_fresh(1) fresh_atm(1) fresh_fun_simp_AndL1 fresh_prod nrename_fresh subst_fresh(3))
next
  case (AndL2 name1 trm name2)
  obtain z::name where "z \<sharp> (name2,name1,P,trm[name2\<turnstile>n>y]{y:=<c>.P},y,P,trm)"
    by (meson exists_fresh(1) fs_name1)
  with AndL2 show ?case 
    using fin_AndL2_elim[OF AndL2.prems(1)]
    by simp (metis abs_fresh(1) fresh_atm(1) fresh_fun_simp_AndL2 fresh_prod nrename_fresh subst_fresh(3))
next
  case (OrL name1 trm1 name2 trm2 name3)
  obtain z::name where "z \<sharp> (name3,name2,name1,P,trm1[name3\<turnstile>n>y]{y:=<c>.P},trm2[name3\<turnstile>n>y]{y:=<c>.P},y,P,trm1,trm2)"
    by (meson exists_fresh(1) fs_name1)
  with OrL show ?case 
    using fin_OrL_elim[OF OrL.prems(1)]
    by (auto simp add: abs_fresh fresh_fun_simp_OrL fresh_atm(1) nrename_fresh subst_fresh(3))
next
  case (ImpL coname trm1 name1 trm2 name2)
  obtain z::name where "z \<sharp> (name1,x,P,trm1[x\<turnstile>n>y]{y:=<c>.P},trm2[x\<turnstile>n>y]{y:=<c>.P},y,P,trm1,trm2)"
    by (meson exists_fresh(1) fs_name1)
  with ImpL show ?case 
    using fin_ImpL_elim[OF ImpL.prems(1)]
    by (auto simp add: abs_fresh fresh_fun_simp_ImpL fresh_atm(1) nrename_fresh subst_fresh(3))
qed (use fin_rest_elims in force)+

inductive
  fic :: "trm \<Rightarrow> coname \<Rightarrow> bool"
where
  [intro]: "fic (Ax x a) a"
| [intro]: "a\<sharp>M \<Longrightarrow> fic (NotR (x).M a) a"
| [intro]: "\<lbrakk>c\<sharp>[a].M;c\<sharp>[b].N\<rbrakk> \<Longrightarrow> fic (AndR <a>.M <b>.N c) c"
| [intro]: "b\<sharp>[a].M \<Longrightarrow> fic (OrR1 <a>.M b) b"
| [intro]: "b\<sharp>[a].M \<Longrightarrow> fic (OrR2 <a>.M b) b"
| [intro]: "\<lbrakk>b\<sharp>[a].M\<rbrakk> \<Longrightarrow> fic (ImpR (x).<a>.M b) b"

equivariance fic

lemma fic_Ax_elim:
  assumes "fic (Ax x a) b"
  shows "a=b"
  using assms by (auto simp: trm.inject elim!: fic.cases)

lemma fic_NotR_elim:
  assumes "fic (NotR (x).M a) b"
  shows "a=b \<and> b\<sharp>M"
  using assms
  by (auto simp: trm.inject elim!: fic.cases) (metis abs_fresh(6))

lemma fic_OrR1_elim:
  assumes "fic (OrR1 <a>.M b) c"
  shows "b=c \<and> c\<sharp>[a].M"
  using assms by (auto simp: trm.inject elim!: fic.cases)

lemma fic_OrR2_elim:
  assumes "fic (OrR2 <a>.M b) c"
  shows "b=c \<and> c\<sharp>[a].M"
  using assms by (auto simp: trm.inject elim!: fic.cases)

lemma fic_AndR_elim:
  assumes "fic (AndR <a>.M <b>.N c) d"
  shows "c=d \<and> d\<sharp>[a].M \<and> d\<sharp>[b].N"
  using assms by (auto simp: trm.inject elim!: fic.cases)

lemma fic_ImpR_elim:
  assumes a: "fic (ImpR (x).<a>.M b) c"
  shows "b=c \<and> b\<sharp>[a].M"
  using assms by (auto simp: trm.inject elim!: fic.cases) (metis abs_fresh(6))

lemma fic_rest_elims:
  shows "fic (Cut <a>.M (x).N) d \<Longrightarrow> False"
  and   "fic (NotL <a>.M x) d \<Longrightarrow> False"
  and   "fic (OrL (x).M (y).N z) d \<Longrightarrow> False"
  and   "fic (AndL1 (x).M y) d \<Longrightarrow> False"
  and   "fic (AndL2 (x).M y) d \<Longrightarrow> False"
  and   "fic (ImpL <a>.M (x).N y) d \<Longrightarrow> False"
by (erule fic.cases, simp_all add: trm.inject)+

lemmas fic_elims = fic_Ax_elim fic_NotR_elim fic_OrR1_elim fic_OrR2_elim fic_AndR_elim 
                   fic_ImpR_elim fic_rest_elims

lemma fic_rename:
  shows "fic M a \<Longrightarrow> fic ([(a',a)]\<bullet>M) a'"
by (induct rule: fic.induct)
   (auto simp: calc_atm simp add: fresh_left abs_fresh)

lemma not_fic_subst1:
  assumes "\<not>(fic M a)" 
  shows "\<not>(fic (M{y:=<c>.P}) a)"
using assms
proof (nominal_induct M avoiding: a c y P rule: trm.strong_induct)
  case (Ax name coname)
  then show ?case
    using fic_rest_elims(1) substn.simps(1) by presburger
next
  case (Cut coname trm1 name trm2)
  then show ?case
    by (metis abs_fresh(2) better_Cut_substn fic_rest_elims(1) fresh_prod)
next
  case (NotR name trm coname)
  then show ?case
    by (metis fic.intros(2) fic_NotR_elim fresh_prod freshc_after_substn substn.simps(3))
next
  case (NotL coname trm name)
  obtain x'::name where "x' \<sharp> (trm{y:=<c>.P},P,a)"
    by (meson exists_fresh(1) fs_name1)
  with NotL show ?case
    by (simp add: fic.intros fresh_prod) (metis fic_rest_elims(1,2) fresh_fun_simp_NotL)
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  then show ?case
    by simp (metis abs_fresh(2) fic.intros(3) fic_AndR_elim freshc_after_substn)
next
  case (AndL1 name1 trm name2)
  obtain x'::name where "x' \<sharp> (trm{y:=<c>.P},P,name1,a)"
    by (meson exists_fresh(1) fs_name1)
  with AndL1 fic_rest_elims show ?case
    by (simp add: fic.intros fresh_prod)(metis fresh_fun_simp_AndL1)
next
  case (AndL2 name1 trm name2)
  obtain x'::name where "x' \<sharp> (trm{y:=<c>.P},P,name1,a)"
    by (meson exists_fresh(1) fs_name1)
  with AndL2 fic_rest_elims show ?case
    by (simp add: fic.intros fresh_prod) (metis fresh_fun_simp_AndL2)
next
  case (OrR1 coname1 trm coname2)
  then show ?case
    by simp (metis abs_fresh(2) fic.simps fic_OrR1_elim freshc_after_substn)
next
  case (OrR2 coname1 trm coname2)
  then show ?case
    by simp (metis abs_fresh(2) fic.simps fic_OrR2_elim freshc_after_substn)
next
  case (OrL name1 trm1 name2 trm2 name3)
  obtain x'::name where "x' \<sharp> (trm1{y:=<c>.P},trm2{y:=<c>.P},P,name1,name2,a)"
    by (meson exists_fresh(1) fs_name1)
  with OrL fic_rest_elims show ?case
    by (simp add: fic.intros fresh_prod) (metis fresh_fun_simp_OrL)
next
  case (ImpR name coname1 trm coname2)
  then show ?case 
    by simp (metis abs_fresh(2) fic.intros(6) fic_ImpR_elim freshc_after_substn)
next
  case (ImpL coname trm1 name1 trm2 name2)
  obtain x'::name where "x' \<sharp> (trm1{name2:=<c>.P},trm2{name2:=<c>.P},P,name1,name2,a)"
    by (meson exists_fresh(1) fs_name1)
  with ImpL fic_rest_elims fresh_fun_simp_ImpL show ?case
    by (simp add: fresh_prod) fastforce
qed

lemma not_fic_subst2:
  assumes "\<not>(fic M a)" 
  shows "\<not>(fic (M{c:=(y).P}) a)"
using assms
proof (nominal_induct M avoiding: a c y P rule: trm.strong_induct)
  case (NotR name trm coname)
  obtain c'::coname where "c'\<sharp>(trm{coname:=(y).P},P,a)"
    by (meson exists_fresh'(2) fs_coname1)
  with NotR fic_rest_elims show ?case
    apply (clarsimp simp: fresh_prod fresh_fun_simp_NotR)
    by (metis fic.intros(2) fic_NotR_elim freshc_after_substc)
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  obtain c'::coname where "c'\<sharp>(trm1{coname3:=(y).P},trm2{coname3:=(y).P},P,coname1,coname2,a)"
    by (meson exists_fresh'(2) fs_coname1)
  with AndR fic_rest_elims show ?case
    apply (clarsimp simp: fresh_prod fresh_fun_simp_AndR)
    by (metis abs_fresh(2) fic.intros(3) fic_AndR_elim freshc_after_substc)
next
  case (OrR1 coname1 trm coname2)
  obtain c'::coname where "c'\<sharp>(trm{coname2:=(y).P},P,coname1,a)"
    by (meson exists_fresh'(2) fs_coname1)
  with OrR1 fic_rest_elims show ?case
    apply (clarsimp simp: fresh_prod fresh_fun_simp_OrR1)
    by (metis abs_fresh(2) fic.intros(4) fic_OrR1_elim freshc_after_substc)
next
  case (OrR2 coname1 trm coname2)
  obtain c'::coname where "c'\<sharp>(trm{coname2:=(y).P},P,coname1,a)"
    by (meson exists_fresh'(2) fs_coname1)
  with OrR2 fic_rest_elims show ?case
    apply (clarsimp simp: fresh_prod fresh_fun_simp_OrR2)
    by (metis abs_fresh(2) fic.simps fic_OrR2_elim freshc_after_substc)
next
  case (ImpR name coname1 trm coname2)
  obtain c'::coname where "c'\<sharp>(trm{coname2:=(y).P},P,coname1,a)"
    by (meson exists_fresh'(2) fs_coname1)
  with ImpR fic_rest_elims show ?case
    apply (clarsimp simp: fresh_prod fresh_fun_simp_ImpR)
    by (metis abs_fresh(2) fic.intros(6) fic_ImpR_elim freshc_after_substc)
qed (use fic_rest_elims in auto)

lemma fic_subst1:
  assumes "fic M a" "a\<noteq>b" "a\<sharp>P"
  shows "fic (M{b:=(x).P}) a"
using assms
proof (nominal_induct M avoiding: x b a P rule: trm.strong_induct)
  case (Ax name coname)
  then show ?case
    using fic_Ax_elim by force
next
  case (NotR name trm coname)
  with fic_NotR_elim show ?case
    by (fastforce simp add: fresh_prod subst_fresh)
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  with fic_AndR_elim show ?case
    by (fastforce simp add: abs_fresh fresh_prod subst_fresh)
next
  case (OrR1 coname1 trm coname2)
  with fic_OrR1_elim show ?case
    by (fastforce simp add: abs_fresh fresh_prod subst_fresh)
next
  case (OrR2 coname1 trm coname2)
  with fic_OrR2_elim show ?case
    by (fastforce simp add: abs_fresh fresh_prod subst_fresh)
next
  case (ImpR name coname1 trm coname2)
  with fic_ImpR_elim show ?case
    by (fastforce simp add: abs_fresh fresh_prod subst_fresh)
qed (use fic_rest_elims in force)+

lemma fic_subst2:
  assumes "fic M a" "c\<noteq>a" "a\<sharp>P" "M\<noteq>Ax x a" 
  shows "fic (M{x:=<c>.P}) a"
using assms
proof (nominal_induct M avoiding: x a c P rule: trm.strong_induct)
  case (Ax name coname)
  then show ?case
    using fic_Ax_elim by force
next
  case (NotR name trm coname)
  with fic_NotR_elim show ?case
    by (fastforce simp add: fresh_prod subst_fresh)
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  with fic_AndR_elim show ?case
    by simp (metis abs_fresh(2) crename_cfresh crename_fresh fic.intros(3) fresh_atm(2) substn_crename_comm')
next
  case (OrR1 coname1 trm coname2)
  with fic_OrR1_elim show ?case
    by (fastforce simp add: abs_fresh fresh_prod subst_fresh)
next
  case (OrR2 coname1 trm coname2)
  with fic_OrR2_elim show ?case
    by (fastforce simp add: abs_fresh fresh_prod subst_fresh)
next
  case (ImpR name coname1 trm coname2)
  with fic_ImpR_elim show ?case
    by (fastforce simp add: abs_fresh fresh_prod subst_fresh)
qed (use fic_rest_elims in force)+

lemma fic_substc_crename:
  assumes "fic M a" "a\<noteq>b" "a\<sharp>P"
  shows "M[a\<turnstile>c>b]{b:=(y).P} = Cut <a>.(M{b:=(y).P}) (y).P"
using assms
proof (nominal_induct M avoiding: a b  y P rule: trm.strong_induct)
  case (Ax name coname)
  with fic_Ax_elim show ?case
    by(force simp add: trm.inject alpha(2) fresh_atm(2,4) swap_simps(4,8))
next
  case (Cut coname trm1 name trm2)
  with fic_rest_elims show ?case by force
next
  case (NotR name trm coname)
  with fic_NotR_elim[OF NotR.prems(1)] show ?case
    by (simp add: trm.inject crename_fresh fresh_fun_simp_NotR subst_fresh(6))
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  with AndR fic_AndR_elim[OF AndR.prems(1)] show ?case
    by (simp add: abs_fresh rename_fresh fresh_fun_simp_AndR fresh_atm(2) subst_fresh(6))
next
  case (OrR1 coname1 trm coname2)
  with fic_OrR1_elim[OF OrR1.prems(1)] show ?case
    by (simp add: abs_fresh rename_fresh fresh_fun_simp_OrR1 fresh_atm(2) subst_fresh(6))
next
  case (OrR2 coname1 trm coname2)
  with fic_OrR2_elim[OF OrR2.prems(1)] show ?case
    by (simp add: abs_fresh rename_fresh fresh_fun_simp_OrR2 fresh_atm(2) subst_fresh(6))
next
  case (ImpR name coname1 trm coname2)
  with fic_ImpR_elim[OF ImpR.prems(1)] crename_fresh show ?case
    by (force simp add: abs_fresh fresh_fun_simp_ImpR fresh_atm(2) subst_fresh(6))
qed (use fic_rest_elims in force)+

inductive
  l_redu :: "trm \<Rightarrow> trm \<Rightarrow> bool" (\<open>_ \<longrightarrow>\<^sub>l _\<close> [100,100] 100)
where
  LAxR:  "\<lbrakk>x\<sharp>M; a\<sharp>b; fic M a\<rbrakk> \<Longrightarrow> Cut <a>.M (x).(Ax x b) \<longrightarrow>\<^sub>l M[a\<turnstile>c>b]"
| LAxL:  "\<lbrakk>a\<sharp>M; x\<sharp>y; fin M x\<rbrakk> \<Longrightarrow> Cut <a>.(Ax y a) (x).M \<longrightarrow>\<^sub>l M[x\<turnstile>n>y]"
| LNot:  "\<lbrakk>y\<sharp>(M,N); x\<sharp>(N,y); a\<sharp>(M,N,b); b\<sharp>M; y\<noteq>x; b\<noteq>a\<rbrakk> \<Longrightarrow>
          Cut <a>.(NotR (x).M a) (y).(NotL <b>.N y) \<longrightarrow>\<^sub>l Cut <b>.N (x).M" 
| LAnd1: "\<lbrakk>b\<sharp>([a1].M1,[a2].M2,N,a1,a2); y\<sharp>([x].N,M1,M2,x); x\<sharp>(M1,M2); a1\<sharp>(M2,N); a2\<sharp>(M1,N); a1\<noteq>a2\<rbrakk> \<Longrightarrow>
          Cut <b>.(AndR <a1>.M1 <a2>.M2 b) (y).(AndL1 (x).N y) \<longrightarrow>\<^sub>l Cut <a1>.M1 (x).N"
| LAnd2: "\<lbrakk>b\<sharp>([a1].M1,[a2].M2,N,a1,a2); y\<sharp>([x].N,M1,M2,x); x\<sharp>(M1,M2); a1\<sharp>(M2,N); a2\<sharp>(M1,N); a1\<noteq>a2\<rbrakk> \<Longrightarrow>
          Cut <b>.(AndR <a1>.M1 <a2>.M2 b) (y).(AndL2 (x).N y) \<longrightarrow>\<^sub>l Cut <a2>.M2 (x).N"
| LOr1:  "\<lbrakk>b\<sharp>([a].M,N1,N2,a); y\<sharp>([x1].N1,[x2].N2,M,x1,x2); x1\<sharp>(M,N2); x2\<sharp>(M,N1); a\<sharp>(N1,N2); x1\<noteq>x2\<rbrakk> \<Longrightarrow>
          Cut <b>.(OrR1 <a>.M b) (y).(OrL (x1).N1 (x2).N2 y) \<longrightarrow>\<^sub>l Cut <a>.M (x1).N1"
| LOr2:  "\<lbrakk>b\<sharp>([a].M,N1,N2,a); y\<sharp>([x1].N1,[x2].N2,M,x1,x2); x1\<sharp>(M,N2); x2\<sharp>(M,N1); a\<sharp>(N1,N2); x1\<noteq>x2\<rbrakk> \<Longrightarrow>
          Cut <b>.(OrR2 <a>.M b) (y).(OrL (x1).N1 (x2).N2 y) \<longrightarrow>\<^sub>l Cut <a>.M (x2).N2"
| LImp:  "\<lbrakk>z\<sharp>(N,[y].P,[x].M,y,x); b\<sharp>([a].M,[c].N,P,c,a); x\<sharp>(N,[y].P,y); 
          c\<sharp>(P,[a].M,b,a); a\<sharp>([c].N,P); y\<sharp>(N,[x].M)\<rbrakk> \<Longrightarrow>
          Cut <b>.(ImpR (x).<a>.M b) (z).(ImpL <c>.N (y).P z) \<longrightarrow>\<^sub>l Cut <a>.(Cut <c>.N (x).M) (y).P"

equivariance l_redu

lemma l_redu_eqvt':
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "(pi1\<bullet>M) \<longrightarrow>\<^sub>l (pi1\<bullet>M') \<Longrightarrow> M \<longrightarrow>\<^sub>l M'"
  and   "(pi2\<bullet>M) \<longrightarrow>\<^sub>l (pi2\<bullet>M') \<Longrightarrow> M \<longrightarrow>\<^sub>l M'"
  using l_redu.eqvt perm_pi_simp by metis+

nominal_inductive l_redu
  by (force simp add: abs_fresh fresh_atm rename_fresh fresh_prod abs_supp fin_supp)+


lemma fresh_l_redu_x:
  fixes z::"name"
  shows "M \<longrightarrow>\<^sub>l M' \<Longrightarrow> z\<sharp>M \<Longrightarrow> z\<sharp>M'"
proof (induct rule: l_redu.induct)
  case (LAxL a M x y)
  then show ?case
    by (metis abs_fresh(1,5) nrename_nfresh nrename_rename trm.fresh(1,3))
next
  case (LImp z N y P x M b a c)
  then show ?case
    apply (simp add: abs_fresh fresh_prod)
    by (metis abs_fresh(3,5) abs_supp(5) fs_name1)
qed (auto simp add: abs_fresh fresh_prod crename_nfresh)

lemma fresh_l_redu_a:
  fixes c::"coname"
  shows "M \<longrightarrow>\<^sub>l M' \<Longrightarrow> c\<sharp>M \<Longrightarrow> c\<sharp>M'"
proof (induct rule: l_redu.induct)
  case (LAxR x M a b)
  then show ?case
    apply (simp add: abs_fresh)
    by (metis crename_cfresh crename_rename)
next
  case (LAxL a M x y)
  with nrename_cfresh show ?case
    by (simp add: abs_fresh)
qed (auto simp add: abs_fresh fresh_prod crename_nfresh)


lemmas fresh_l_redu = fresh_l_redu_x fresh_l_redu_a

lemma better_LAxR_intro[intro]:
  shows "fic M a \<Longrightarrow> Cut <a>.M (x).(Ax x b) \<longrightarrow>\<^sub>l M[a\<turnstile>c>b]"
proof -
  assume fin: "fic M a"
  obtain x'::"name" where fs1: "x'\<sharp>(M,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(a,M,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.M (x).(Ax x b) =  Cut <a'>.([(a',a)]\<bullet>M) (x').(Ax x' b)"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>l ([(a',a)]\<bullet>M)[a'\<turnstile>c>b]" using fs1 fs2 fin
    by (auto intro: l_redu.intros simp add: fresh_left calc_atm fic_rename)
  also have "\<dots> = M[a\<turnstile>c>b]" using fs1 fs2 by (simp add: crename_rename)
  finally show ?thesis by simp
qed
    
lemma better_LAxL_intro[intro]:
  shows "fin M x \<Longrightarrow> Cut <a>.(Ax y a) (x).M \<longrightarrow>\<^sub>l M[x\<turnstile>n>y]"
proof -
  assume fin: "fin M x"
  obtain x'::"name" where fs1: "x'\<sharp>(y,M,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(a,M)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.(Ax y a) (x).M = Cut <a'>.(Ax y a') (x').([(x',x)]\<bullet>M)"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>l ([(x',x)]\<bullet>M)[x'\<turnstile>n>y]" using fs1 fs2 fin
    by (auto intro: l_redu.intros simp add: fresh_left calc_atm fin_rename)
  also have "\<dots> = M[x\<turnstile>n>y]" using fs1 fs2 by (simp add: nrename_rename)
  finally show ?thesis by simp
qed

lemma better_LNot_intro[intro]:
  shows "\<lbrakk>y\<sharp>N; a\<sharp>M\<rbrakk> \<Longrightarrow> Cut <a>.(NotR (x).M a) (y).(NotL <b>.N y) \<longrightarrow>\<^sub>l Cut <b>.N (x).M"
proof -
  assume fs: "y\<sharp>N" "a\<sharp>M"
  obtain x'::"name" where f1: "x'\<sharp>(y,N,M,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain y'::"name" where f2: "y'\<sharp>(y,N,M,x,x')" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where f3: "a'\<sharp>(a,M,N,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain b'::"coname" where f4: "b'\<sharp>(a,M,N,b,a')" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.(NotR (x).M a) (y).(NotL <b>.N y) 
                      = Cut <a'>.(NotR (x).([(a',a)]\<bullet>M) a') (y').(NotL <b>.([(y',y)]\<bullet>N) y')"
    using f1 f2 f3 f4 
    by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm abs_fresh)
  also have "\<dots> = Cut <a'>.(NotR (x).M a') (y').(NotL <b>.N y')"
    using f1 f2 f3 f4 fs by (perm_simp)
  also have "\<dots> = Cut <a'>.(NotR (x').([(x',x)]\<bullet>M) a') (y').(NotL <b'>.([(b',b)]\<bullet>N) y')"
    using f1 f2 f3 f4 
    by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>l Cut <b'>.([(b',b)]\<bullet>N) (x').([(x',x)]\<bullet>M)"
    using f1 f2 f3 f4 fs
    by (auto intro:  l_redu.intros simp add: fresh_prod fresh_left calc_atm fresh_atm)
  also have "\<dots> = Cut <b>.N (x).M"
    using f1 f2 f3 f4 by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  finally show ?thesis by simp
qed 

lemma better_LAnd1_intro[intro]:
  shows "\<lbrakk>a\<sharp>([b1].M1,[b2].M2); y\<sharp>[x].N\<rbrakk> 
         \<Longrightarrow> Cut <a>.(AndR <b1>.M1 <b2>.M2 a) (y).(AndL1 (x).N y) \<longrightarrow>\<^sub>l Cut <b1>.M1 (x).N"
proof -
  assume fs: "a\<sharp>([b1].M1,[b2].M2)" "y\<sharp>[x].N"
  obtain x'::"name" where f1: "x'\<sharp>(y,N,M1,M2,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain y'::"name" where f2: "y'\<sharp>(y,N,M1,M2,x,x')" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where f3: "a'\<sharp>(a,M1,M2,N,b1,b2)" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain b1'::"coname" where f4:"b1'\<sharp>(a,M1,M2,N,b1,b2,a')" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain b2'::"coname" where f5:"b2'\<sharp>(a,M1,M2,N,b1,b2,a',b1')" by (rule exists_fresh(2),rule fin_supp, blast)
  have "Cut <a>.(AndR <b1>.M1 <b2>.M2 a) (y).(AndL1 (x).N y)
                      = Cut <a'>.(AndR <b1>.M1 <b2>.M2 a') (y').(AndL1 (x).N y')"
    using f1 f2 f3 f4 fs
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    apply(auto simp: perm_fresh_fresh)
    done
  also have "\<dots> = Cut <a'>.(AndR <b1'>.([(b1',b1)]\<bullet>M1) <b2'>.([(b2',b2)]\<bullet>M2) a') 
                                                               (y').(AndL1 (x').([(x',x)]\<bullet>N) y')"
    using f1 f2 f3 f4 f5 fs 
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    done
  also have "\<dots> \<longrightarrow>\<^sub>l Cut <b1'>.([(b1',b1)]\<bullet>M1) (x').([(x',x)]\<bullet>N)"
    using f1 f2 f3 f4 f5 fs
    apply -
    apply(rule l_redu.intros)
    apply(auto simp: abs_fresh fresh_prod fresh_left calc_atm fresh_atm)
    done
  also have "\<dots> = Cut <b1>.M1 (x).N"
    using f1 f2 f3 f4 f5 fs by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  finally show ?thesis by simp
qed 

lemma better_LAnd2_intro[intro]:
  shows "\<lbrakk>a\<sharp>([b1].M1,[b2].M2); y\<sharp>[x].N\<rbrakk> 
         \<Longrightarrow> Cut <a>.(AndR <b1>.M1 <b2>.M2 a) (y).(AndL2 (x).N y) \<longrightarrow>\<^sub>l Cut <b2>.M2 (x).N"
proof -
  assume fs: "a\<sharp>([b1].M1,[b2].M2)" "y\<sharp>[x].N"
  obtain x'::"name" where f1: "x'\<sharp>(y,N,M1,M2,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain y'::"name" where f2: "y'\<sharp>(y,N,M1,M2,x,x')" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where f3: "a'\<sharp>(a,M1,M2,N,b1,b2)" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain b1'::"coname" where f4:"b1'\<sharp>(a,M1,M2,N,b1,b2,a')" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain b2'::"coname" where f5:"b2'\<sharp>(a,M1,M2,N,b1,b2,a',b1')" by (rule exists_fresh(2),rule fin_supp, blast)
  have "Cut <a>.(AndR <b1>.M1 <b2>.M2 a) (y).(AndL2 (x).N y)
                      = Cut <a'>.(AndR <b1>.M1 <b2>.M2 a') (y').(AndL2 (x).N y')"
    using f1 f2 f3 f4 fs
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    apply(auto simp: perm_fresh_fresh)
    done
  also have "\<dots> = Cut <a'>.(AndR <b1'>.([(b1',b1)]\<bullet>M1) <b2'>.([(b2',b2)]\<bullet>M2) a') 
                                                               (y').(AndL2 (x').([(x',x)]\<bullet>N) y')"
    using f1 f2 f3 f4 f5 fs 
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    done
  also have "\<dots> \<longrightarrow>\<^sub>l Cut <b2'>.([(b2',b2)]\<bullet>M2) (x').([(x',x)]\<bullet>N)"
    using f1 f2 f3 f4 f5 fs
    apply -
    apply(rule l_redu.intros)
    apply(auto simp: abs_fresh fresh_prod fresh_left calc_atm fresh_atm)
    done
  also have "\<dots> = Cut <b2>.M2 (x).N"
    using f1 f2 f3 f4 f5 fs by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  finally show ?thesis by simp
qed

lemma better_LOr1_intro[intro]:
  shows "\<lbrakk>y\<sharp>([x1].N1,[x2].N2); b\<sharp>[a].M\<rbrakk> 
         \<Longrightarrow> Cut <b>.(OrR1 <a>.M b) (y).(OrL (x1).N1 (x2).N2 y) \<longrightarrow>\<^sub>l Cut <a>.M (x1).N1"
proof -
  assume fs: "y\<sharp>([x1].N1,[x2].N2)" "b\<sharp>[a].M"
  obtain y'::"name" where f1: "y'\<sharp>(y,M,N1,N2,x1,x2)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain x1'::"name" where f2: "x1'\<sharp>(y,M,N1,N2,x1,x2,y')" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain x2'::"name" where f3: "x2'\<sharp>(y,M,N1,N2,x1,x2,y',x1')" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where f4: "a'\<sharp>(a,N1,N2,M,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain b'::"coname" where f5: "b'\<sharp>(a,N1,N2,M,b,a')" by (rule exists_fresh(2),rule fin_supp, blast)
  have "Cut <b>.(OrR1 <a>.M b) (y).(OrL (x1).N1 (x2).N2 y)
                      = Cut <b'>.(OrR1 <a>.M b') (y').(OrL (x1).N1 (x2).N2 y')"
    using f1 f2 f3 f4 f5 fs
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    apply(auto simp: perm_fresh_fresh)
    done
  also have "\<dots> = Cut <b'>.(OrR1 <a'>.([(a',a)]\<bullet>M) b') 
              (y').(OrL (x1').([(x1',x1)]\<bullet>N1) (x2').([(x2',x2)]\<bullet>N2) y')"   
    using f1 f2 f3 f4 f5 fs 
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    done
  also have "\<dots> \<longrightarrow>\<^sub>l Cut <a'>.([(a',a)]\<bullet>M) (x1').([(x1',x1)]\<bullet>N1)"
    using f1 f2 f3 f4 f5 fs
    apply -
    apply(rule l_redu.intros)
    apply(auto simp: abs_fresh fresh_prod fresh_left calc_atm fresh_atm)
    done
  also have "\<dots> = Cut <a>.M (x1).N1"
    using f1 f2 f3 f4 f5 fs by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  finally show ?thesis by simp
qed

lemma better_LOr2_intro[intro]:
  shows "\<lbrakk>y\<sharp>([x1].N1,[x2].N2); b\<sharp>[a].M\<rbrakk> 
         \<Longrightarrow> Cut <b>.(OrR2 <a>.M b) (y).(OrL (x1).N1 (x2).N2 y) \<longrightarrow>\<^sub>l Cut <a>.M (x2).N2"
proof -
  assume fs: "y\<sharp>([x1].N1,[x2].N2)" "b\<sharp>[a].M"
  obtain y'::"name" where f1: "y'\<sharp>(y,M,N1,N2,x1,x2)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain x1'::"name" where f2: "x1'\<sharp>(y,M,N1,N2,x1,x2,y')" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain x2'::"name" where f3: "x2'\<sharp>(y,M,N1,N2,x1,x2,y',x1')" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where f4: "a'\<sharp>(a,N1,N2,M,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain b'::"coname" where f5: "b'\<sharp>(a,N1,N2,M,b,a')" by (rule exists_fresh(2),rule fin_supp, blast)
  have "Cut <b>.(OrR2 <a>.M b) (y).(OrL (x1).N1 (x2).N2 y)
                      = Cut <b'>.(OrR2 <a>.M b') (y').(OrL (x1).N1 (x2).N2 y')"
    using f1 f2 f3 f4 f5 fs
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    apply(auto simp: perm_fresh_fresh)
    done
  also have "\<dots> = Cut <b'>.(OrR2 <a'>.([(a',a)]\<bullet>M) b') 
              (y').(OrL (x1').([(x1',x1)]\<bullet>N1) (x2').([(x2',x2)]\<bullet>N2) y')"   
    using f1 f2 f3 f4 f5 fs 
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    done
  also have "\<dots> \<longrightarrow>\<^sub>l Cut <a'>.([(a',a)]\<bullet>M) (x2').([(x2',x2)]\<bullet>N2)"
    using f1 f2 f3 f4 f5 fs
    apply -
    apply(rule l_redu.intros)
    apply(auto simp: abs_fresh fresh_prod fresh_left calc_atm fresh_atm)
    done
  also have "\<dots> = Cut <a>.M (x2).N2"
    using f1 f2 f3 f4 f5 fs by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  finally show ?thesis by simp
qed 

lemma better_LImp_intro[intro]:
  shows "\<lbrakk>z\<sharp>(N,[y].P); b\<sharp>[a].M; a\<sharp>N\<rbrakk> 
         \<Longrightarrow> Cut <b>.(ImpR (x).<a>.M b) (z).(ImpL <c>.N (y).P z) \<longrightarrow>\<^sub>l Cut <a>.(Cut <c>.N (x).M) (y).P"
proof -
  assume fs: "z\<sharp>(N,[y].P)" "b\<sharp>[a].M" "a\<sharp>N"
  obtain y'::"name" and x'::"name" and z'::"name" 
    where f1: "y'\<sharp>(y,M,N,P,z,x)" and f2: "x'\<sharp>(y,M,N,P,z,x,y')" and f3: "z'\<sharp>(y,M,N,P,z,x,y',x')"
    by (meson exists_fresh(1) fs_name1)
  obtain a'::"coname" and b'::"coname" and c'::"coname" 
    where f4: "a'\<sharp>(a,N,P,M,b)" and f5: "b'\<sharp>(a,N,P,M,b,c,a')" and f6: "c'\<sharp>(a,N,P,M,b,c,a',b')"
    by (meson exists_fresh(2) fs_coname1)
  have "Cut <b>.(ImpR (x).<a>.M b) (z).(ImpL <c>.N (y).P z)
                      =  Cut <b'>.(ImpR (x).<a>.M b') (z').(ImpL <c>.N (y).P z')"
    using f1 f2 f3 f4 f5 fs
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    apply(auto simp: perm_fresh_fresh)
    done
  also have "\<dots> = Cut <b'>.(ImpR (x').<a'>.([(a',a)]\<bullet>([(x',x)]\<bullet>M)) b') 
                           (z').(ImpL <c'>.([(c',c)]\<bullet>N) (y').([(y',y)]\<bullet>P) z')"
    using f1 f2 f3 f4 f5 f6 fs 
    apply(rule_tac sym)
    apply(simp add: trm.inject alpha fresh_prod fresh_atm abs_perm calc_atm fresh_left abs_fresh)
    done
  also have "\<dots> \<longrightarrow>\<^sub>l Cut <a'>.(Cut <c'>.([(c',c)]\<bullet>N) (x').([(a',a)]\<bullet>[(x',x)]\<bullet>M)) (y').([(y',y)]\<bullet>P)"
    using f1 f2 f3 f4 f5 f6 fs
    apply -
    apply(rule l_redu.intros)
    apply(auto simp: abs_fresh fresh_prod fresh_left calc_atm fresh_atm)
    done
  also have "\<dots> = Cut <a>.(Cut <c>.N (x).M) (y).P"
    using f1 f2 f3 f4 f5 f6 fs 
    apply(simp add: trm.inject)
    apply(perm_simp add: alpha fresh_prod fresh_atm)
    apply(simp add: trm.inject abs_fresh alpha(1) fresh_perm_app(4) perm_compose(4) perm_dj(4))
    apply (metis alpha'(2) crename_fresh crename_swap swap_simps(2,4,6))
    done
  finally show ?thesis by simp
qed 

lemma alpha_coname:
  fixes M::"trm"
    and   a::"coname"
  assumes "[a].M = [b].N" "c\<sharp>(a,b,M,N)"
  shows "M = [(a,c)]\<bullet>[(b,c)]\<bullet>N"
  by (metis alpha_fresh'(2) assms fresh_atm(2) fresh_prod)

lemma alpha_name:
  fixes M::"trm"
    and   x::"name"
  assumes "[x].M = [y].N" "z\<sharp>(x,y,M,N)"
  shows "M = [(x,z)]\<bullet>[(y,z)]\<bullet>N"
  by (metis alpha_fresh'(1) assms fresh_atm(1) fresh_prod)

lemma alpha_name_coname:
  fixes M::"trm"
  and   x::"name"
  and   a::"coname"
assumes "[x].[b].M = [y].[c].N" "z\<sharp>(x,y,M,N)" "a\<sharp>(b,c,M,N)"
  shows "M = [(x,z)]\<bullet>[(b,a)]\<bullet>[(c,a)]\<bullet>[(y,z)]\<bullet>N"
  using assms
  apply(clarsimp simp: alpha_fresh fresh_prod fresh_atm 
      abs_supp fin_supp abs_fresh abs_perm fresh_left calc_atm)
  by (metis perm_swap(1,2))


lemma Cut_l_redu_elim:
  assumes "Cut <a>.M (x).N \<longrightarrow>\<^sub>l R"
  shows "(\<exists>b. R = M[a\<turnstile>c>b]) \<or> (\<exists>y. R = N[x\<turnstile>n>y]) \<or>
  (\<exists>y M' b N'. M = NotR (y).M' a \<and> N = NotL <b>.N' x \<and> R = Cut <b>.N' (y).M' \<and> fic M a \<and> fin N x) \<or>
  (\<exists>b M1 c M2 y N'. M = AndR <b>.M1 <c>.M2 a \<and> N = AndL1 (y).N' x \<and> R = Cut <b>.M1 (y).N' 
                                                                            \<and> fic M a \<and> fin N x) \<or>
  (\<exists>b M1 c M2 y N'. M = AndR <b>.M1 <c>.M2 a \<and> N = AndL2 (y).N' x \<and> R = Cut <c>.M2 (y).N' 
                                                                            \<and> fic M a \<and> fin N x) \<or>
  (\<exists>b N' z M1 y M2. M = OrR1 <b>.N' a \<and> N = OrL (z).M1 (y).M2 x \<and> R = Cut <b>.N' (z).M1 
                                                                            \<and> fic M a \<and> fin N x) \<or>
  (\<exists>b N' z M1 y M2. M = OrR2 <b>.N' a \<and> N = OrL (z).M1 (y).M2 x \<and> R = Cut <b>.N' (y).M2 
                                                                            \<and> fic M a \<and> fin N x) \<or>
  (\<exists>z b M' c N1 y N2. M = ImpR (z).<b>.M' a \<and> N = ImpL <c>.N1 (y).N2 x \<and> 
            R = Cut <b>.(Cut <c>.N1 (z).M') (y).N2 \<and> b\<sharp>(c,N1) \<and> fic M a \<and> fin N x)"
using assms
proof (cases rule: l_redu.cases)
  case (LAxR x M a b)
  then show ?thesis
    apply(simp add: trm.inject)
    by (metis alpha(2) crename_rename)
next
  case (LAxL a M x y)
  then show ?thesis
    apply(simp add: trm.inject)
    by (metis alpha(1) nrename_rename)
next
  case (LNot y M N x a b)
  then show ?thesis
    apply(simp add: trm.inject)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI1)
    apply(erule conjE)+
    apply(generate_fresh "coname")
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(auto)[1]
    apply(drule_tac c="c" in  alpha_coname)
     apply(simp add: fresh_prod fresh_atm abs_fresh)
    apply(simp add: calc_atm)
    apply(rule exI)+
    apply(rule conjI)
     apply(rule refl)
    apply(generate_fresh "name")
    apply(simp add: calc_atm abs_fresh fresh_prod fresh_atm fresh_left)
    apply(auto)[1]
    apply(drule_tac z="ca" in  alpha_name)
     apply(simp add: fresh_prod fresh_atm abs_fresh)
    apply(simp add: calc_atm)
    apply(rule exI)+
    apply(rule conjI)
     apply(rule refl)
    apply(auto simp: calc_atm abs_fresh fresh_left)[1]
    using nrename_fresh nrename_swap apply presburger
    using crename_fresh crename_swap by presburger
next
  case (LAnd1 b a1 M1 a2 M2 N y x)
  then show ?thesis
    apply -
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI1)
    apply(clarsimp simp add: trm.inject)
    apply(generate_fresh "coname")
    apply(clarsimp simp add: abs_fresh fresh_prod fresh_atm)
    apply(drule_tac c="c" in  alpha_coname)
     apply(simp add: fresh_prod fresh_atm abs_fresh)
    apply(simp)
    apply(rule exI)+
    apply(rule conjI)
     apply(rule exI)+
     apply(rule_tac s="a" and t="[(a,c)]\<bullet>[(b,c)]\<bullet>b" in subst)
      apply(simp add: calc_atm)
     apply(rule refl)
    apply(generate_fresh "name")
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(auto)[1]
       apply(drule_tac z="ca" in  alpha_name)
        apply(simp add: fresh_prod fresh_atm abs_fresh)
       apply(simp)
       apply (metis swap_simps(6))
      apply(generate_fresh "name")
      apply(simp add: abs_fresh fresh_prod fresh_atm)
      apply(auto)[1]
      apply(drule_tac z="cb" in  alpha_name)
       apply(simp add: fresh_prod fresh_atm abs_fresh)
      apply(simp)
      apply(perm_simp)
      apply (smt (verit, del_insts) abs_fresh(1,2) abs_perm(1,2) fic.intros(3) fin.intros(3) fresh_bij(1) perm_fresh_fresh(1,2) swap_simps(1,6))
     apply(perm_simp)+
     apply(generate_fresh "name")
     apply(simp add: abs_fresh fresh_prod fresh_atm)
     apply(auto)[1]
     apply(drule_tac z="cb" in  alpha_name)
      apply(simp add: fresh_prod fresh_atm abs_fresh)
     apply(perm_simp)
     apply (smt (verit) abs_fresh(1,2) abs_perm(1,2) fic.intros(3) fin.intros(3) perm_fresh_fresh(1,2) perm_swap(3) swap_simps(1,6))
    apply(perm_simp)+
    apply(generate_fresh "name")
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(auto)[1]
    apply(drule_tac z="cb" in  alpha_name)
     apply(simp add: fresh_prod fresh_atm abs_fresh cong: conj_cong)
    apply(perm_simp)
    by (smt (verit, best) abs_fresh(1,2) abs_perm(1) alpha(2) fic.intros(3) fin.intros(3) fresh_bij(1,2) perm_fresh_fresh(1,2) swap_simps(2,3))
next
  case (LAnd2 b a1 M1 a2 M2 N y x)
  then show ?thesis
    apply -
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI1)
    apply(clarsimp simp add: trm.inject)
    apply(generate_fresh "coname")
    apply(clarsimp simp add: abs_fresh fresh_prod fresh_atm)
    apply(drule_tac c="c" in  alpha_coname)
     apply(simp add: fresh_prod fresh_atm abs_fresh)
    apply(simp)
    apply(rule exI)+
    apply(rule conjI)
     apply(rule_tac s="a" and t="[(a,c)]\<bullet>[(b,c)]\<bullet>b" in subst)
      apply(simp add: calc_atm)
     apply(rule refl)
    apply(generate_fresh "name")
    apply(auto simp add: abs_fresh fresh_prod fresh_atm)
       apply(drule_tac z="ca" in  alpha_name)
        apply(simp add: fresh_prod fresh_atm abs_fresh)
       apply (metis swap_simps(6))
      apply(generate_fresh "name")
      apply(simp add: abs_fresh fresh_prod fresh_atm)
      apply(auto)[1]
      apply(drule_tac z="cb" in  alpha_name)
       apply(simp add: fresh_prod fresh_atm abs_fresh)
      apply(perm_simp)
      apply (smt (verit, ccfv_threshold) abs_fresh(1,2) abs_perm(1) fic.intros(3) fin.intros(4) fresh_bij(1,2) perm_fresh_fresh(1,2) swap_simps(1,4,6))
     apply(generate_fresh "name")
     apply(simp add: abs_fresh fresh_prod fresh_atm)
     apply(auto)[1]
     apply(drule_tac z="cb" in  alpha_name)
      apply(simp add: fresh_prod fresh_atm abs_fresh)
     apply(simp)
     apply(perm_simp)
     apply (smt (verit) abs_fresh(1,2) abs_perm(1,2) fic.intros(3) fin.intros(4) fresh_bij(1) perm_fresh_fresh(1,2) swap_simps(1,6))
    apply(generate_fresh "name")
    apply(clarsimp simp add: abs_fresh fresh_prod fresh_atm)
    apply(drule_tac z="cb" in  alpha_name)
     apply(simp add: fresh_prod fresh_atm abs_fresh)
    apply(perm_simp)
    by (smt (verit, ccfv_SIG) abs_fresh(1,2) abs_perm(1) alpha(2) fic.intros(3) fin.intros(4) fresh_bij(1,2) perm_fresh_fresh(1,2) swap_simps(2,3))
next
  case (LOr1 b a M N1 N2 y x1 x2)
  then show ?thesis
    apply -
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI1)
    apply(clarsimp simp add: trm.inject)
    apply(generate_fresh "coname")
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(auto)[1]
    apply(drule_tac c="c" in  alpha_coname)
     apply(simp add: fresh_prod fresh_atm abs_fresh)
    apply(simp)
    apply(perm_simp)
    apply(rule exI)+
    apply(rule conjI)
     apply(rule_tac s="a" and t="[(a,c)]\<bullet>[(b,c)]\<bullet>b" in subst)
      apply(simp add: calc_atm)
     apply(rule refl)
    apply(generate_fresh "name")
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(auto)[1]
     apply(drule_tac z="ca" in  alpha_name)
      apply(simp add: fresh_prod fresh_atm abs_fresh)
     apply(simp)
     apply(rule exI)+
     apply(rule conjI)
      apply(rule exI)+
      apply(rule_tac s="x" and t="[(x,ca)]\<bullet>[(y,ca)]\<bullet>y" in subst)
       apply(simp add: calc_atm)
      apply(rule refl)
     apply(auto simp: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
        apply(perm_simp)+
    apply(generate_fresh "name")
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(auto)[1]
    apply(drule_tac z="cb" in  alpha_name)
     apply(simp add: fresh_prod fresh_atm abs_fresh)
    apply(simp)
    apply(rule exI)+
    apply(rule conjI)
     apply(rule exI)+
     apply(rule_tac s="x" and t="[(x,cb)]\<bullet>[(y,cb)]\<bullet>y" in subst)
      apply(simp add: calc_atm)
     apply(rule refl)
    apply(auto simp: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
     apply(perm_simp)+
    done
next
  case (LOr2 b a M N1 N2 y x1 x2)
  then show ?thesis
    apply -
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule disjI1)
    apply(simp add: trm.inject)
    apply(erule conjE)+
    apply(generate_fresh "coname")
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(auto)[1]
    apply(drule_tac c="c" in  alpha_coname)
     apply(simp add: fresh_prod fresh_atm abs_fresh)
    apply(simp)
     apply(perm_simp)
    apply(rule exI)+
    apply(rule conjI)
     apply(rule_tac s="a" and t="[(a,c)]\<bullet>[(b,c)]\<bullet>b" in subst)
      apply(simp add: calc_atm)
     apply(rule refl)
     apply(generate_fresh "name")
     apply(simp add: abs_fresh fresh_prod fresh_atm)
     apply(auto)[1]
      apply(drule_tac z="ca" in  alpha_name)
       apply(simp add: fresh_prod fresh_atm abs_fresh)
      apply(simp)
      apply(rule exI)+
      apply(rule conjI)
      apply(rule_tac s="x" and t="[(x,ca)]\<bullet>[(y,ca)]\<bullet>y" in subst)
       apply(simp add: calc_atm)
      apply(rule refl)
      apply(auto simp: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
     apply(perm_simp)+
     apply(generate_fresh "name")
     apply(simp add: abs_fresh fresh_prod fresh_atm)
     apply(auto)[1]
     apply(drule_tac z="cb" in  alpha_name)
      apply(simp add: fresh_prod fresh_atm abs_fresh)
     apply(simp)
     apply(rule exI)+
     apply(rule conjI)
     apply(rule_tac s="x" and t="[(x,cb)]\<bullet>[(y,cb)]\<bullet>y" in subst)
      apply(simp add: calc_atm)
     apply(rule refl)
     apply(auto simp: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
       apply(perm_simp)+
    done
next
  case (LImp z N y P x M b a c)
  then show ?thesis
    apply(intro disjI2)
    apply(clarsimp simp add: trm.inject)
    apply(generate_fresh "coname")
    apply(clarsimp simp add: abs_fresh fresh_prod fresh_atm)
    apply(drule_tac c="ca" in  alpha_coname)
     apply(simp add: fresh_prod fresh_atm abs_fresh)
    apply(simp)
    apply(perm_simp)
    apply(rule exI)+
    apply(rule conjI)
     apply(rule_tac s="a" and t="[(a,ca)]\<bullet>[(b,ca)]\<bullet>b" in subst)
      apply(simp add: calc_atm)
     apply(rule refl)
    apply(generate_fresh "name")
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(auto)[1]
     apply(drule_tac z="caa" in  alpha_name)
      apply(simp add: fresh_prod fresh_atm abs_fresh)
     apply(simp)
     apply(perm_simp)
     apply(rule exI)+
     apply(rule conjI)
      apply(rule_tac s="x" and t="[(x,caa)]\<bullet>[(z,caa)]\<bullet>z" in subst)
       apply(simp add: calc_atm)
      apply(rule refl)
     apply(auto simp: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
       apply(perm_simp)+
    apply(generate_fresh "name")
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(auto)[1]
    apply(drule_tac z="cb" in  alpha_name)
     apply(simp add: fresh_prod fresh_atm abs_fresh)
    apply(simp)
    apply(perm_simp)
    apply(rule exI)+
    apply(rule conjI)
     apply(rule_tac s="x" and t="[(x,cb)]\<bullet>[(z,cb)]\<bullet>z" in subst)
      apply(simp add: calc_atm)
     apply(rule refl)
    apply(auto simp: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
     apply(perm_simp)+
    done
qed


inductive
  c_redu :: "trm \<Rightarrow> trm \<Rightarrow> bool" (\<open>_ \<longrightarrow>\<^sub>c _\<close> [100,100] 100)
where
  left[intro]:  "\<lbrakk>\<not>fic M a; a\<sharp>N; x\<sharp>M\<rbrakk> \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^sub>c M{a:=(x).N}"
| right[intro]: "\<lbrakk>\<not>fin N x; a\<sharp>N; x\<sharp>M\<rbrakk> \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^sub>c N{x:=<a>.M}"

equivariance c_redu

nominal_inductive c_redu
 by (simp_all add: abs_fresh subst_fresh)

lemma better_left[intro]:
  shows "\<not>fic M a \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^sub>c M{a:=(x).N}"
proof -
  assume not_fic: "\<not>fic M a"
  obtain x'::"name" where fs1: "x'\<sharp>(N,M,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(a,M,N)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.M (x).N =  Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N)"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>c ([(a',a)]\<bullet>M){a':=(x').([(x',x)]\<bullet>N)}" using fs1 fs2 not_fic
    apply(intro left)
    apply (metis fic_rename perm_swap(4))
    apply(simp add: fresh_left calc_atm)+
    done
  also have "\<dots> = M{a:=(x).N}" using fs1 fs2
    by (simp add: subst_rename[symmetric] fresh_atm fresh_prod fresh_left calc_atm)
  finally show ?thesis by simp
qed

lemma better_right[intro]:
  shows "\<not>fin N x \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^sub>c N{x:=<a>.M}"
proof -
  assume not_fin: "\<not>fin N x"
  obtain x'::"name" where fs1: "x'\<sharp>(N,M,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(a,M,N)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.M (x).N =  Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N)"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>c ([(x',x)]\<bullet>N){x':=<a'>.([(a',a)]\<bullet>M)}" using fs1 fs2 not_fin
    apply (intro right)
    apply (metis fin_rename perm_swap(3))
    apply (simp add: fresh_left calc_atm)+
    done
  also have "\<dots> = N{x:=<a>.M}" using fs1 fs2
    by (simp add: subst_rename[symmetric] fresh_atm fresh_prod fresh_left calc_atm)
  finally show ?thesis by simp
qed

lemma fresh_c_redu:
  fixes x::"name"
  and   c::"coname"
  shows "M \<longrightarrow>\<^sub>c M' \<Longrightarrow> x\<sharp>M \<Longrightarrow> x\<sharp>M'"
  and   "M \<longrightarrow>\<^sub>c M' \<Longrightarrow> c\<sharp>M \<Longrightarrow> c\<sharp>M'"
  by (induct rule: c_redu.induct) (auto simp: abs_fresh rename_fresh subst_fresh)+

inductive
  a_redu :: "trm \<Rightarrow> trm \<Rightarrow> bool" (\<open>_ \<longrightarrow>\<^sub>a _\<close> [100,100] 100)
where
  al_redu[intro]: "M\<longrightarrow>\<^sub>l M' \<Longrightarrow> M \<longrightarrow>\<^sub>a M'"
| ac_redu[intro]: "M\<longrightarrow>\<^sub>c M' \<Longrightarrow> M \<longrightarrow>\<^sub>a M'"
| a_Cut_l: "\<lbrakk>a\<sharp>N; x\<sharp>M; M\<longrightarrow>\<^sub>a M'\<rbrakk> \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^sub>a Cut <a>.M' (x).N"
| a_Cut_r: "\<lbrakk>a\<sharp>N; x\<sharp>M; N\<longrightarrow>\<^sub>a N'\<rbrakk> \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^sub>a Cut <a>.M (x).N'"
| a_NotL[intro]: "M\<longrightarrow>\<^sub>a M' \<Longrightarrow> NotL <a>.M x \<longrightarrow>\<^sub>a NotL <a>.M' x"
| a_NotR[intro]: "M\<longrightarrow>\<^sub>a M' \<Longrightarrow> NotR (x).M a \<longrightarrow>\<^sub>a NotR (x).M' a"
| a_AndR_l: "\<lbrakk>a\<sharp>(N,c); b\<sharp>(M,c); b\<noteq>a; M\<longrightarrow>\<^sub>a M'\<rbrakk> \<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^sub>a AndR <a>.M' <b>.N c"
| a_AndR_r: "\<lbrakk>a\<sharp>(N,c); b\<sharp>(M,c); b\<noteq>a; N\<longrightarrow>\<^sub>a N'\<rbrakk> \<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^sub>a AndR <a>.M <b>.N' c"
| a_AndL1: "\<lbrakk>x\<sharp>y; M\<longrightarrow>\<^sub>a M'\<rbrakk> \<Longrightarrow> AndL1 (x).M y \<longrightarrow>\<^sub>a AndL1 (x).M' y"
| a_AndL2: "\<lbrakk>x\<sharp>y; M\<longrightarrow>\<^sub>a M'\<rbrakk> \<Longrightarrow> AndL2 (x).M y \<longrightarrow>\<^sub>a AndL2 (x).M' y"
| a_OrL_l: "\<lbrakk>x\<sharp>(N,z); y\<sharp>(M,z); y\<noteq>x; M\<longrightarrow>\<^sub>a M'\<rbrakk> \<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^sub>a OrL (x).M' (y).N z"
| a_OrL_r: "\<lbrakk>x\<sharp>(N,z); y\<sharp>(M,z); y\<noteq>x; N\<longrightarrow>\<^sub>a N'\<rbrakk> \<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^sub>a OrL (x).M (y).N' z"
| a_OrR1: "\<lbrakk>a\<sharp>b; M\<longrightarrow>\<^sub>a M'\<rbrakk> \<Longrightarrow> OrR1 <a>.M b \<longrightarrow>\<^sub>a OrR1 <a>.M' b"
| a_OrR2: "\<lbrakk>a\<sharp>b; M\<longrightarrow>\<^sub>a M'\<rbrakk> \<Longrightarrow> OrR2 <a>.M b \<longrightarrow>\<^sub>a OrR2 <a>.M' b"
| a_ImpL_l: "\<lbrakk>a\<sharp>N; x\<sharp>(M,y); M\<longrightarrow>\<^sub>a M'\<rbrakk> \<Longrightarrow> ImpL <a>.M (x).N y \<longrightarrow>\<^sub>a ImpL <a>.M' (x).N y"
| a_ImpL_r: "\<lbrakk>a\<sharp>N; x\<sharp>(M,y); N\<longrightarrow>\<^sub>a N'\<rbrakk> \<Longrightarrow> ImpL <a>.M (x).N y \<longrightarrow>\<^sub>a ImpL <a>.M (x).N' y"
| a_ImpR: "\<lbrakk>a\<sharp>b; M\<longrightarrow>\<^sub>a M'\<rbrakk> \<Longrightarrow> ImpR (x).<a>.M b \<longrightarrow>\<^sub>a ImpR (x).<a>.M' b"

lemma fresh_a_redu1:
  fixes x::"name"
  shows "M \<longrightarrow>\<^sub>a M' \<Longrightarrow> x\<sharp>M \<Longrightarrow> x\<sharp>M'"
  by (induct rule: a_redu.induct) (auto simp: fresh_l_redu fresh_c_redu abs_fresh abs_supp fin_supp)

lemma fresh_a_redu2:
  fixes c::"coname"
  shows "M \<longrightarrow>\<^sub>a M' \<Longrightarrow> c\<sharp>M \<Longrightarrow> c\<sharp>M'"
  by (induct rule: a_redu.induct) (auto simp: fresh_l_redu fresh_c_redu abs_fresh abs_supp fin_supp)

lemmas fresh_a_redu = fresh_a_redu1 fresh_a_redu2

equivariance a_redu

nominal_inductive a_redu
  by (simp_all add: abs_fresh fresh_atm fresh_prod abs_supp fin_supp fresh_a_redu)

lemma better_CutL_intro[intro]:
  shows "M\<longrightarrow>\<^sub>a M' \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^sub>a Cut <a>.M' (x).N"
proof -
  assume red: "M\<longrightarrow>\<^sub>a M'"
  obtain x'::"name"   where fs1: "x'\<sharp>(M,N,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.M (x).N =  Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N)"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a  Cut <a'>.([(a',a)]\<bullet>M') (x').([(x',x)]\<bullet>N)" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt)
  also have "\<dots> = Cut <a>.M' (x).N" 
    using fs1 fs2 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_CutR_intro[intro]:
  shows "N\<longrightarrow>\<^sub>a N' \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^sub>a Cut <a>.M (x).N'"
proof -
  assume red: "N\<longrightarrow>\<^sub>a N'"
  obtain x'::"name"   where fs1: "x'\<sharp>(M,N,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.M (x).N =  Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N)"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a  Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N')" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt)
  also have "\<dots> = Cut <a>.M (x).N'" 
    using fs1 fs2 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed
    
lemma better_AndRL_intro[intro]:
  shows "M\<longrightarrow>\<^sub>a M' \<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^sub>a AndR <a>.M' <b>.N c"
proof -
  assume red: "M\<longrightarrow>\<^sub>a M'"
  obtain b'::"coname" where fs1: "b'\<sharp>(M,N,a,b,c)" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a,b,c,b')" by (rule exists_fresh(2), rule fin_supp, blast)
  have "AndR <a>.M <b>.N c =  AndR <a'>.([(a',a)]\<bullet>M) <b'>.([(b',b)]\<bullet>N) c"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a  AndR <a'>.([(a',a)]\<bullet>M') <b'>.([(b',b)]\<bullet>N) c" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = AndR <a>.M' <b>.N c" 
    using fs1 fs2 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_AndRR_intro[intro]:
  shows "N\<longrightarrow>\<^sub>a N' \<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^sub>a AndR <a>.M <b>.N' c"
proof -
  assume red: "N\<longrightarrow>\<^sub>a N'"
  obtain b'::"coname" where fs1: "b'\<sharp>(M,N,a,b,c)" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a,b,c,b')" by (rule exists_fresh(2), rule fin_supp, blast)
  have "AndR <a>.M <b>.N c =  AndR <a'>.([(a',a)]\<bullet>M) <b'>.([(b',b)]\<bullet>N) c"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a  AndR <a'>.([(a',a)]\<bullet>M) <b'>.([(b',b)]\<bullet>N') c" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = AndR <a>.M <b>.N' c" 
    using fs1 fs2 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_AndL1_intro[intro]:
  shows "M\<longrightarrow>\<^sub>a M' \<Longrightarrow> AndL1 (x).M y \<longrightarrow>\<^sub>a AndL1 (x).M' y"
proof -
  assume red: "M\<longrightarrow>\<^sub>a M'"
  obtain x'::"name" where fs1: "x'\<sharp>(M,y,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  have "AndL1 (x).M y = AndL1 (x').([(x',x)]\<bullet>M) y"
    using fs1 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a AndL1 (x').([(x',x)]\<bullet>M') y" using fs1 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = AndL1 (x).M' y" 
    using fs1 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_AndL2_intro[intro]:
  shows "M\<longrightarrow>\<^sub>a M' \<Longrightarrow> AndL2 (x).M y \<longrightarrow>\<^sub>a AndL2 (x).M' y"
proof -
  assume red: "M\<longrightarrow>\<^sub>a M'"
  obtain x'::"name" where fs1: "x'\<sharp>(M,y,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  have "AndL2 (x).M y = AndL2 (x').([(x',x)]\<bullet>M) y"
    using fs1 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a AndL2 (x').([(x',x)]\<bullet>M') y" using fs1 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = AndL2 (x).M' y" 
    using fs1 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_OrLL_intro[intro]:
  shows "M\<longrightarrow>\<^sub>a M' \<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^sub>a OrL (x).M' (y).N z"
proof -
  assume red: "M\<longrightarrow>\<^sub>a M'"
  obtain x'::"name" where fs1: "x'\<sharp>(M,N,x,y,z)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain y'::"name" where fs2: "y'\<sharp>(M,N,x,y,z,x')" by (rule exists_fresh(1), rule fin_supp, blast)
  have "OrL (x).M (y).N z =  OrL (x').([(x',x)]\<bullet>M) (y').([(y',y)]\<bullet>N) z"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a OrL (x').([(x',x)]\<bullet>M') (y').([(y',y)]\<bullet>N) z" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = OrL (x).M' (y).N z" 
    using fs1 fs2 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_OrLR_intro[intro]:
  shows "N\<longrightarrow>\<^sub>a N' \<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^sub>a OrL (x).M (y).N' z"
proof -
  assume red: "N\<longrightarrow>\<^sub>a N'"
  obtain x'::"name" where fs1: "x'\<sharp>(M,N,x,y,z)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain y'::"name" where fs2: "y'\<sharp>(M,N,x,y,z,x')" by (rule exists_fresh(1), rule fin_supp, blast)
  have "OrL (x).M (y).N z =  OrL (x').([(x',x)]\<bullet>M) (y').([(y',y)]\<bullet>N) z"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a OrL (x').([(x',x)]\<bullet>M) (y').([(y',y)]\<bullet>N') z" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = OrL (x).M (y).N' z" 
    using fs1 fs2 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_OrR1_intro[intro]:
  shows "M\<longrightarrow>\<^sub>a M' \<Longrightarrow> OrR1 <a>.M b \<longrightarrow>\<^sub>a OrR1 <a>.M' b"
proof -
  assume red: "M\<longrightarrow>\<^sub>a M'"
  obtain a'::"coname" where fs1: "a'\<sharp>(M,b,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "OrR1 <a>.M b = OrR1 <a'>.([(a',a)]\<bullet>M) b"
    using fs1 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a OrR1 <a'>.([(a',a)]\<bullet>M') b" using fs1 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = OrR1 <a>.M' b" 
    using fs1 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_OrR2_intro[intro]:
  shows "M\<longrightarrow>\<^sub>a M' \<Longrightarrow> OrR2 <a>.M b \<longrightarrow>\<^sub>a OrR2 <a>.M' b"
proof -
  assume red: "M\<longrightarrow>\<^sub>a M'"
  obtain a'::"coname" where fs1: "a'\<sharp>(M,b,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "OrR2 <a>.M b = OrR2 <a'>.([(a',a)]\<bullet>M) b"
    using fs1 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a OrR2 <a'>.([(a',a)]\<bullet>M') b" using fs1 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = OrR2 <a>.M' b" 
    using fs1 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_ImpLL_intro[intro]:
  shows "M\<longrightarrow>\<^sub>a M' \<Longrightarrow> ImpL <a>.M (x).N y \<longrightarrow>\<^sub>a ImpL <a>.M' (x).N y"
proof -
  assume red: "M\<longrightarrow>\<^sub>a M'"
  obtain x'::"name"   where fs1: "x'\<sharp>(M,N,x,y)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "ImpL <a>.M (x).N y =  ImpL <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N) y"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a  ImpL <a'>.([(a',a)]\<bullet>M') (x').([(x',x)]\<bullet>N) y" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = ImpL <a>.M' (x).N y" 
    using fs1 fs2 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_ImpLR_intro[intro]:
  shows "N\<longrightarrow>\<^sub>a N' \<Longrightarrow> ImpL <a>.M (x).N y \<longrightarrow>\<^sub>a ImpL <a>.M (x).N' y"
proof -
  assume red: "N\<longrightarrow>\<^sub>a N'"
  obtain x'::"name"   where fs1: "x'\<sharp>(M,N,x,y)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "ImpL <a>.M (x).N y =  ImpL <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N) y"
    using fs1 fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a  ImpL <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N') y" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = ImpL <a>.M (x).N' y" 
    using fs1 fs2 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_ImpR_intro[intro]:
  shows "M\<longrightarrow>\<^sub>a M' \<Longrightarrow> ImpR (x).<a>.M b \<longrightarrow>\<^sub>a ImpR (x).<a>.M' b"
proof -
  assume red: "M\<longrightarrow>\<^sub>a M'"
  obtain a'::"coname" where fs2: "a'\<sharp>(M,a,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "ImpR (x).<a>.M b = ImpR (x).<a'>.([(a',a)]\<bullet>M) b"
    using fs2 by (rule_tac sym, auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a ImpR (x).<a'>.([(a',a)]\<bullet>M') b" using fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = ImpR (x).<a>.M' b" 
    using fs2 red by (auto simp: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

text \<open>axioms do not reduce\<close>

lemma ax_do_not_l_reduce:
  shows "Ax x a \<longrightarrow>\<^sub>l M \<Longrightarrow> False"
by (erule_tac l_redu.cases) (simp_all add: trm.inject)
 
lemma ax_do_not_c_reduce:
  shows "Ax x a \<longrightarrow>\<^sub>c M \<Longrightarrow> False"
by (erule_tac c_redu.cases) (simp_all add: trm.inject)

lemma ax_do_not_a_reduce:
  shows "Ax x a \<longrightarrow>\<^sub>a M \<Longrightarrow> False"
apply(erule_tac a_redu.cases) 
apply(simp_all add: trm.inject)
  using ax_do_not_l_reduce ax_do_not_c_reduce by blast+

lemma a_redu_NotL_elim:
  assumes "NotL <a>.M x \<longrightarrow>\<^sub>a R"
  shows "\<exists>M'. R = NotL <a>.M' x \<and> M\<longrightarrow>\<^sub>aM'"
  using assms
  apply(erule_tac a_redu.cases, simp_all add: trm.inject)
    apply(erule_tac l_redu.cases, simp_all add: trm.inject)
   apply(erule_tac c_redu.cases, simp_all add: trm.inject)
  apply (smt (verit, best) a_redu.eqvt(2) alpha(2) fresh_a_redu2)+
  done

lemma a_redu_NotR_elim:
  assumes "NotR (x).M a \<longrightarrow>\<^sub>a R"
  shows "\<exists>M'. R = NotR (x).M' a \<and> M\<longrightarrow>\<^sub>aM'"
  using assms
  apply(erule_tac a_redu.cases, simp_all add: trm.inject)
    apply(erule_tac l_redu.cases, simp_all add: trm.inject)
   apply(erule_tac c_redu.cases, simp_all add: trm.inject)
  apply (smt (verit, best) a_redu.eqvt(1) alpha(1) fresh_a_redu1)+
  done

lemma a_redu_AndR_elim:
  assumes "AndR <a>.M <b>.N c\<longrightarrow>\<^sub>a R"
  shows "(\<exists>M'. R = AndR <a>.M' <b>.N c \<and> M\<longrightarrow>\<^sub>aM') \<or> (\<exists>N'. R = AndR <a>.M <b>.N' c \<and> N\<longrightarrow>\<^sub>aN')"
  using assms
  apply(erule_tac a_redu.cases, simp_all add: trm.inject)
     apply(erule_tac l_redu.cases, simp_all add: trm.inject)
    apply(erule_tac c_redu.cases, simp_all add: trm.inject)
   apply (smt (verit) a_redu.eqvt(2) alpha'(2) fresh_a_redu2)
  by (metis a_NotL a_redu_NotL_elim trm.inject(4))

lemma a_redu_AndL1_elim:
  assumes "AndL1 (x).M y \<longrightarrow>\<^sub>a R"
  shows "\<exists>M'. R = AndL1 (x).M' y \<and> M\<longrightarrow>\<^sub>aM'"
  using assms
  apply(erule_tac a_redu.cases, simp_all add: trm.inject)
    apply(erule_tac l_redu.cases, simp_all add: trm.inject)
   apply(erule_tac c_redu.cases, simp_all add: trm.inject)
  by (metis a_NotR a_redu_NotR_elim trm.inject(3))

lemma a_redu_AndL2_elim:
  assumes a: "AndL2 (x).M y \<longrightarrow>\<^sub>a R"
  shows "\<exists>M'. R = AndL2 (x).M' y \<and> M\<longrightarrow>\<^sub>aM'"
  using a
  apply(erule_tac a_redu.cases, simp_all add: trm.inject)
  apply(erule_tac l_redu.cases, simp_all add: trm.inject)
   apply(erule_tac c_redu.cases, simp_all add: trm.inject)
  by (metis a_NotR a_redu_NotR_elim trm.inject(3))

lemma a_redu_OrL_elim:
  assumes "OrL (x).M (y).N z\<longrightarrow>\<^sub>a R"
  shows "(\<exists>M'. R = OrL (x).M' (y).N z \<and> M\<longrightarrow>\<^sub>aM') \<or> (\<exists>N'. R = OrL (x).M (y).N' z \<and> N\<longrightarrow>\<^sub>aN')"
  using assms
  apply(erule_tac a_redu.cases, simp_all add: trm.inject)
     apply(erule_tac l_redu.cases, simp_all add: trm.inject)
    apply(erule_tac c_redu.cases, simp_all add: trm.inject)
   apply (metis a_NotR a_redu_NotR_elim trm.inject(3))+
done

lemma a_redu_OrR1_elim:
  assumes "OrR1 <a>.M b \<longrightarrow>\<^sub>a R"
  shows "\<exists>M'. R = OrR1 <a>.M' b \<and> M\<longrightarrow>\<^sub>aM'"
  using assms
  apply(erule_tac a_redu.cases, simp_all add: trm.inject)
    apply(erule_tac l_redu.cases, simp_all add: trm.inject)
   apply(erule_tac c_redu.cases, simp_all add: trm.inject)
  by (metis a_NotL a_redu_NotL_elim trm.inject(4))

lemma a_redu_OrR2_elim:
  assumes a: "OrR2 <a>.M b \<longrightarrow>\<^sub>a R"
  shows "\<exists>M'. R = OrR2 <a>.M' b \<and> M\<longrightarrow>\<^sub>aM'"
  using assms
  apply(erule_tac a_redu.cases, simp_all add: trm.inject)
    apply(erule_tac l_redu.cases, simp_all add: trm.inject)
   apply(erule_tac c_redu.cases, simp_all add: trm.inject)
  by (metis a_redu_OrR1_elim better_OrR1_intro trm.inject(8))

lemma a_redu_ImpL_elim:
  assumes a: "ImpL <a>.M (y).N z\<longrightarrow>\<^sub>a R"
  shows "(\<exists>M'. R = ImpL <a>.M' (y).N z \<and> M\<longrightarrow>\<^sub>aM') \<or> (\<exists>N'. R = ImpL <a>.M (y).N' z \<and> N\<longrightarrow>\<^sub>aN')"
  using assms
  apply(erule_tac a_redu.cases, simp_all add: trm.inject)
     apply(erule_tac l_redu.cases, simp_all add: trm.inject)
    apply(erule_tac c_redu.cases, simp_all add: trm.inject)
   apply (smt (verit) a_redu.eqvt(2) alpha'(2) fresh_a_redu2)
  by (metis a_NotR a_redu_NotR_elim trm.inject(3))

lemma a_redu_ImpR_elim:
  assumes a: "ImpR (x).<a>.M b \<longrightarrow>\<^sub>a R"
  shows "\<exists>M'. R = ImpR (x).<a>.M' b \<and> M\<longrightarrow>\<^sub>aM'"
using a [[simproc del: defined_all]]
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto)
apply(rotate_tac 3)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
  apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto simp: alpha a_redu.eqvt abs_perm abs_fresh)
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(a,aa)]\<bullet>[(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule sym)
apply(rule trans)
apply(rule perm_compose)
apply(simp add: calc_atm perm_swap)
apply(rule_tac x="([(a,aaa)]\<bullet>[(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule sym)
apply(rule trans)
apply(rule perm_compose)
apply(simp add: calc_atm perm_swap)
apply(rule_tac x="([(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(a,aa)]\<bullet>[(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
  apply (simp add: cp_coname_name1 perm_dj(4) perm_swap(3,4))
  apply(rule_tac x="([(a,aaa)]\<bullet>[(x,xaa)]\<bullet>M'a)" in exI)
by(simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap perm_compose(4) perm_dj(4))

text \<open>Transitive Closure\<close>

abbreviation
 a_star_redu :: "trm \<Rightarrow> trm \<Rightarrow> bool" (\<open>_ \<longrightarrow>\<^sub>a* _\<close> [80,80] 80)
where
  "M \<longrightarrow>\<^sub>a* M' \<equiv> (a_redu)\<^sup>*\<^sup>* M M'"

lemmas a_starI = r_into_rtranclp

lemma a_starE:
  assumes a: "M \<longrightarrow>\<^sub>a* M'"
  shows "M = M' \<or> (\<exists>N. M \<longrightarrow>\<^sub>a N \<and> N \<longrightarrow>\<^sub>a* M')"
  using a  by (induct) (auto)

lemma a_star_refl:
  shows "M \<longrightarrow>\<^sub>a* M"
  by blast

declare rtranclp_trans [trans]

text \<open>congruence rules for \<open>\<longrightarrow>\<^sub>a*\<close>\<close>

lemma ax_do_not_a_star_reduce:
  shows "Ax x a \<longrightarrow>\<^sub>a* M \<Longrightarrow> M = Ax x a"
  using a_starE ax_do_not_a_reduce by blast


lemma a_star_CutL:
    "M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^sub>a* Cut <a>.M' (x).N"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_CutR:
    "N \<longrightarrow>\<^sub>a* N'\<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^sub>a* Cut <a>.M (x).N'"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_Cut:
    "\<lbrakk>M \<longrightarrow>\<^sub>a* M'; N \<longrightarrow>\<^sub>a* N'\<rbrakk> \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^sub>a* Cut <a>.M' (x).N'"
by (blast intro!: a_star_CutL a_star_CutR intro: rtranclp_trans)

lemma a_star_NotR:
    "M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> NotR (x).M a \<longrightarrow>\<^sub>a* NotR (x).M' a"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_NotL:
    "M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> NotL <a>.M x \<longrightarrow>\<^sub>a* NotL <a>.M' x"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_AndRL:
    "M \<longrightarrow>\<^sub>a* M'\<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^sub>a* AndR <a>.M' <b>.N c"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_AndRR:
    "N \<longrightarrow>\<^sub>a* N'\<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^sub>a* AndR <a>.M <b>.N' c"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_AndR:
    "\<lbrakk>M \<longrightarrow>\<^sub>a* M'; N \<longrightarrow>\<^sub>a* N'\<rbrakk> \<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^sub>a* AndR <a>.M' <b>.N' c"
by (blast intro!: a_star_AndRL a_star_AndRR intro: rtranclp_trans)

lemma a_star_AndL1:
    "M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> AndL1 (x).M y \<longrightarrow>\<^sub>a* AndL1 (x).M' y"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_AndL2:
    "M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> AndL2 (x).M y \<longrightarrow>\<^sub>a* AndL2 (x).M' y"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_OrLL:
    "M \<longrightarrow>\<^sub>a* M'\<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^sub>a* OrL (x).M' (y).N z"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_OrLR:
    "N \<longrightarrow>\<^sub>a* N'\<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^sub>a* OrL (x).M (y).N' z"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_OrL:
    "\<lbrakk>M \<longrightarrow>\<^sub>a* M'; N \<longrightarrow>\<^sub>a* N'\<rbrakk> \<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^sub>a* OrL (x).M' (y).N' z"
by (blast intro!: a_star_OrLL a_star_OrLR intro: rtranclp_trans)

lemma a_star_OrR1:
    "M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> OrR1 <a>.M b \<longrightarrow>\<^sub>a* OrR1 <a>.M' b"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_OrR2:
    "M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> OrR2 <a>.M b \<longrightarrow>\<^sub>a* OrR2 <a>.M' b"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_ImpLL:
    "M \<longrightarrow>\<^sub>a* M'\<Longrightarrow> ImpL <a>.M (y).N z \<longrightarrow>\<^sub>a* ImpL <a>.M' (y).N z"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_ImpLR:
    "N \<longrightarrow>\<^sub>a* N'\<Longrightarrow> ImpL <a>.M (y).N z \<longrightarrow>\<^sub>a* ImpL <a>.M (y).N' z"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_ImpL:
    "\<lbrakk>M \<longrightarrow>\<^sub>a* M'; N \<longrightarrow>\<^sub>a* N'\<rbrakk> \<Longrightarrow> ImpL <a>.M (y).N z \<longrightarrow>\<^sub>a* ImpL <a>.M' (y).N' z"
by (blast intro!: a_star_ImpLL a_star_ImpLR intro: rtranclp_trans)

lemma a_star_ImpR:
    "M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> ImpR (x).<a>.M b \<longrightarrow>\<^sub>a* ImpR (x).<a>.M' b"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemmas a_star_congs = a_star_Cut a_star_NotR a_star_NotL a_star_AndR a_star_AndL1 a_star_AndL2
                      a_star_OrL a_star_OrR1 a_star_OrR2 a_star_ImpL a_star_ImpR

lemma a_star_redu_NotL_elim:
  assumes "NotL <a>.M x \<longrightarrow>\<^sub>a* R"
  shows "\<exists>M'. R = NotL <a>.M' x \<and> M \<longrightarrow>\<^sub>a* M'"
  using assms by (induct set: rtranclp) (use a_redu_NotL_elim in force)+

lemma a_star_redu_NotR_elim:
  assumes "NotR (x).M a \<longrightarrow>\<^sub>a* R"
  shows "\<exists>M'. R = NotR (x).M' a \<and> M \<longrightarrow>\<^sub>a* M'"
  using assms by (induct set: rtranclp) (use a_redu_NotR_elim in force)+

lemma a_star_redu_AndR_elim:
  assumes "AndR <a>.M <b>.N c\<longrightarrow>\<^sub>a* R"
  shows "(\<exists>M' N'. R = AndR <a>.M' <b>.N' c \<and> M \<longrightarrow>\<^sub>a* M' \<and> N \<longrightarrow>\<^sub>a* N')"
  using assms by (induct set: rtranclp) (use a_redu_AndR_elim in force)+

lemma a_star_redu_AndL1_elim:
  assumes "AndL1 (x).M y \<longrightarrow>\<^sub>a* R"
  shows "\<exists>M'. R = AndL1 (x).M' y \<and> M \<longrightarrow>\<^sub>a* M'"
  using assms by (induct set: rtranclp) (use a_redu_AndL1_elim in force)+

lemma a_star_redu_AndL2_elim:
  assumes "AndL2 (x).M y \<longrightarrow>\<^sub>a* R"
  shows "\<exists>M'. R = AndL2 (x).M' y \<and> M \<longrightarrow>\<^sub>a* M'"
  using assms by (induct set: rtranclp) (use a_redu_AndL2_elim in force)+

lemma a_star_redu_OrL_elim:
  assumes "OrL (x).M (y).N z \<longrightarrow>\<^sub>a* R"
  shows "(\<exists>M' N'. R = OrL (x).M' (y).N' z \<and> M \<longrightarrow>\<^sub>a* M' \<and> N \<longrightarrow>\<^sub>a* N')"
  using assms by (induct set: rtranclp) (use a_redu_OrL_elim in force)+

lemma a_star_redu_OrR1_elim:
  assumes "OrR1 <a>.M y \<longrightarrow>\<^sub>a* R"
  shows "\<exists>M'. R = OrR1 <a>.M' y \<and> M \<longrightarrow>\<^sub>a* M'"
  using assms by (induct set: rtranclp) (use a_redu_OrR1_elim in force)+

lemma a_star_redu_OrR2_elim:
  assumes "OrR2 <a>.M y \<longrightarrow>\<^sub>a* R"
  shows "\<exists>M'. R = OrR2 <a>.M' y \<and> M \<longrightarrow>\<^sub>a* M'"
  using assms by (induct set: rtranclp) (use a_redu_OrR2_elim in force)+

lemma a_star_redu_ImpR_elim:
  assumes "ImpR (x).<a>.M y \<longrightarrow>\<^sub>a* R"
  shows "\<exists>M'. R = ImpR (x).<a>.M' y \<and> M \<longrightarrow>\<^sub>a* M'"
  using assms by (induct set: rtranclp) (use a_redu_ImpR_elim in force)+

lemma a_star_redu_ImpL_elim:
  assumes "ImpL <a>.M (y).N z \<longrightarrow>\<^sub>a* R"
  shows "(\<exists>M' N'. R = ImpL <a>.M' (y).N' z \<and> M \<longrightarrow>\<^sub>a* M' \<and> N \<longrightarrow>\<^sub>a* N')"
  using assms by (induct set: rtranclp) (use a_redu_ImpL_elim in force)+

text \<open>Substitution\<close>

lemma subst_not_fin1:
  shows "\<not>fin(M{x:=<c>.P}) x"
proof (nominal_induct M avoiding: x c P rule: trm.strong_induct)
  case (Ax name coname)
  with fin_rest_elims show ?case
    by (auto simp: fin_Ax_elim)
next
  case (NotL coname trm name)
  obtain x'::name where "x'\<sharp>(trm{x:=<c>.P},P)"
    by (meson exists_fresh(1) fs_name1)
  with NotL fin_NotL_elim fresh_fun_simp_NotL show ?case
    by simp (metis fin_rest_elims(1) fresh_prod)
next
  case (AndL1 name1 trm name2)
  obtain x'::name where "x' \<sharp> (trm{x:=<c>.P},P,name1)"
    by (meson exists_fresh(1) fs_name1)
  with AndL1 fin_AndL1_elim fresh_fun_simp_AndL1 show ?case
    by simp (metis fin_rest_elims(1) fresh_prod)
next
  case (AndL2 name2 trm name2)
  obtain x'::name where "x' \<sharp> (trm{x:=<c>.P},P,name2)"
    by (meson exists_fresh(1) fs_name1)
  with AndL2 fin_AndL2_elim fresh_fun_simp_AndL2 better_AndL2_substn show ?case
    by (metis abs_fresh(1) fresh_atm(1) not_fin_subst2)
next
  case (OrL name1 trm1 name2 trm2 name3)
  obtain x'::name where "x' \<sharp> (trm1{x:=<c>.P},P,name1,trm2{x:=<c>.P},name2)"
    by (meson exists_fresh(1) fs_name1)
  with OrL fin_OrL_elim fresh_fun_simp_OrL show ?case
    by simp (metis fin_rest_elims(1) fresh_prod)
next
  case (ImpL coname trm1 name1 trm2 name2)
  obtain x'::name where "x' \<sharp> (trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})"
    by (meson exists_fresh(1) fs_name1)
  with ImpL fin_ImpL_elim fresh_fun_simp_ImpL show ?case
    by simp (metis fin_rest_elims(1) fresh_prod)
qed (use fin_rest_elims not_fin_subst2 in auto)

lemmas subst_not_fin2 = not_fin_subst1

text \<open>Reductions\<close>

lemma fin_l_reduce:
  assumes "fin M x" and "M \<longrightarrow>\<^sub>l M'"
  shows "fin M' x"
  using assms fin_rest_elims(1) l_redu.simps by fastforce

lemma fin_c_reduce:
  assumes "fin M x" and "M \<longrightarrow>\<^sub>c M'"
  shows "fin M' x"
  using assms c_redu.simps fin_rest_elims(1) by fastforce

lemma fin_a_reduce:
  assumes  a: "fin M x"
  and      b: "M \<longrightarrow>\<^sub>a M'"
  shows "fin M' x"
using assms
proof (induct)
  case (1 x a)
  then show ?case
    using ax_do_not_a_reduce by auto
next
  case (2 x M a)
  then show ?case
    using a_redu_NotL_elim fresh_a_redu1 by blast
next
  case (3 y x M)
  then show ?case
    by (metis a_redu_AndL1_elim abs_fresh(1) fin.intros(3) fresh_a_redu1)
next
  case (4 y x M)
  then show ?case
    by (metis a_redu_AndL2_elim abs_fresh(1) fin.intros(4) fresh_a_redu1)
next
  case (5 z x M y N)
  then show ?case
    by (smt (verit) a_redu_OrL_elim abs_fresh(1) fin.intros(5) fresh_a_redu1)
next
  case (6 y M x N a)
  then show ?case
    by (smt (verit, best) a_redu_ImpL_elim abs_fresh(1) fin.simps fresh_a_redu1)
qed


lemma fin_a_star_reduce:
  assumes  a: "fin M x"
  and      b: "M \<longrightarrow>\<^sub>a* M'"
  shows "fin M' x"
using b a by (induct set: rtranclp)(auto simp: fin_a_reduce)

lemma fic_l_reduce:
  assumes  a: "fic M x"
  and      b: "M \<longrightarrow>\<^sub>l M'"
  shows "fic M' x"
  using b a
  by induction (use fic_rest_elims in force)+

lemma fic_c_reduce:
  assumes a: "fic M x"
  and     b: "M \<longrightarrow>\<^sub>c M'"
  shows "fic M' x"
using b a
  by induction (use fic_rest_elims in force)+

lemma fic_a_reduce:
  assumes a: "fic M x"
  and     b: "M \<longrightarrow>\<^sub>a M'"
shows "fic M' x"
  using assms
proof induction
  case (1 x a)
  then show ?case
    using ax_do_not_a_reduce by fastforce
next
  case (2 a M x)
  then show ?case
    using a_redu_NotR_elim fresh_a_redu2 by blast
next
  case (3 c a M b N)
  then show ?case
    by (smt (verit) a_redu_AndR_elim abs_fresh(2) fic.intros(3) fresh_a_redu2)
next
  case (4 b a M)
  then show ?case
    by (metis a_redu_OrR1_elim abs_fresh(2) fic.intros(4) fresh_a_redu2)
next
  case (5 b a M)
  then show ?case
    by (metis a_redu_OrR2_elim abs_fresh(2) fic.simps fresh_a_redu2)
next
  case (6 b a M x)
  then show ?case
    by (metis a_redu_ImpR_elim abs_fresh(2) fic.simps fresh_a_redu2)
qed


lemma fic_a_star_reduce:
  assumes  a: "fic M x"
  and      b: "M \<longrightarrow>\<^sub>a* M'"
  shows "fic M' x"
using b a
  by (induct set: rtranclp) (auto simp: fic_a_reduce)

text \<open>substitution properties\<close>

lemma subst_with_ax1:
  shows "M{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* M[x\<turnstile>n>y]"
proof(nominal_induct M avoiding: x a y rule: trm.strong_induct)
  case (Ax z b x a y)
  show "(Ax z b){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (Ax z b)[x\<turnstile>n>y]"
  proof (cases "z=x")
    case True
    assume eq: "z=x"
    have "(Ax z b){x:=<a>.Ax y a} = Cut <a>.Ax y a (x).Ax x b" using eq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* (Ax x b)[x\<turnstile>n>y]" by blast
    finally show "Ax z b{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (Ax z b)[x\<turnstile>n>y]" using eq by simp
  next
    case False
    assume neq: "z\<noteq>x"
    then show "(Ax z b){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (Ax z b)[x\<turnstile>n>y]" using neq by simp
  qed
next
  case (Cut b M z N x a y)
  have fs: "b\<sharp>x" "b\<sharp>a" "b\<sharp>y" "b\<sharp>N" "z\<sharp>x" "z\<sharp>a" "z\<sharp>y" "z\<sharp>M" by fact+
  have ih1: "M{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* M[x\<turnstile>n>y]" by fact
  have ih2: "N{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* N[x\<turnstile>n>y]" by fact
  show "(Cut <b>.M (z).N){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (Cut <b>.M (z).N)[x\<turnstile>n>y]"
  proof (cases "M = Ax x b")
    case True
    assume eq: "M = Ax x b"
    have "(Cut <b>.M (z).N){x:=<a>.Ax y a} = Cut <a>.Ax y a (z).(N{x:=<a>.Ax y a})" using fs eq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.Ax y a (z).(N[x\<turnstile>n>y])" using ih2 a_star_congs by blast
    also have "\<dots> = Cut <b>.(M[x\<turnstile>n>y]) (z).(N[x\<turnstile>n>y])" using eq
      by (simp add: trm.inject alpha calc_atm fresh_atm)
    finally show "(Cut <b>.M (z).N){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (Cut <b>.M (z).N)[x\<turnstile>n>y]" using fs by simp
  next
    case False
    assume neq: "M \<noteq> Ax x b"
    have "(Cut <b>.M (z).N){x:=<a>.Ax y a} = Cut <b>.(M{x:=<a>.Ax y a}) (z).(N{x:=<a>.Ax y a})" 
      using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* Cut <b>.(M[x\<turnstile>n>y]) (z).(N[x\<turnstile>n>y])" using ih1 ih2 a_star_congs by blast
    finally show "(Cut <b>.M (z).N){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (Cut <b>.M (z).N)[x\<turnstile>n>y]" using fs by simp
  qed
next
  case (NotR z M b x a y)
  have fs: "z\<sharp>x" "z\<sharp>a" "z\<sharp>y" "z\<sharp>b" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* M[x\<turnstile>n>y]" by fact
  have "(NotR (z).M b){x:=<a>.Ax y a} = NotR (z).(M{x:=<a>.Ax y a}) b" using fs by simp
  also have "\<dots> \<longrightarrow>\<^sub>a* NotR (z).(M[x\<turnstile>n>y]) b" using ih by (auto intro: a_star_congs)
  finally show "(NotR (z).M b){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (NotR (z).M b)[x\<turnstile>n>y]" using fs by simp
next
  case (NotL b M z x a y)  
  have fs: "b\<sharp>x" "b\<sharp>a" "b\<sharp>y" "b\<sharp>z" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* M[x\<turnstile>n>y]" by fact
  show "(NotL <b>.M z){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (NotL <b>.M z)[x\<turnstile>n>y]"
  proof(cases "z=x")
    case True
    assume eq: "z=x"
    obtain x'::"name" where new: "x'\<sharp>(Ax y a,M{x:=<a>.Ax y a})" by (rule exists_fresh(1)[OF fs_name1])
    have "(NotL <b>.M z){x:=<a>.Ax y a} = 
                        fresh_fun (\<lambda>x'. Cut <a>.Ax y a (x').NotL <b>.(M{x:=<a>.Ax y a}) x')"
      using eq fs by simp
    also have "\<dots> = Cut <a>.Ax y a (x').NotL <b>.(M{x:=<a>.Ax y a}) x'" 
      using new by (simp add: fresh_fun_simp_NotL fresh_prod)
    also have "\<dots> \<longrightarrow>\<^sub>a* (NotL <b>.(M{x:=<a>.Ax y a}) x')[x'\<turnstile>n>y]"
      using new 
      by (intro a_starI al_redu better_LAxL_intro) auto
    also have "\<dots> = NotL <b>.(M{x:=<a>.Ax y a}) y" using new by (simp add: nrename_fresh)
    also have "\<dots> \<longrightarrow>\<^sub>a* NotL <b>.(M[x\<turnstile>n>y]) y" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (NotL <b>.M z)[x\<turnstile>n>y]" using eq by simp
    finally show "(NotL <b>.M z){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (NotL <b>.M z)[x\<turnstile>n>y]" by simp
  next
    case False
    assume neq: "z\<noteq>x"
    have "(NotL <b>.M z){x:=<a>.Ax y a} = NotL <b>.(M{x:=<a>.Ax y a}) z" using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* NotL <b>.(M[x\<turnstile>n>y]) z" using ih by (auto intro: a_star_congs)
    finally show "(NotL <b>.M z){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (NotL <b>.M z)[x\<turnstile>n>y]" using neq by simp
  qed
next
  case (AndR c M d N e x a y)
  have fs: "c\<sharp>x" "c\<sharp>a" "c\<sharp>y" "d\<sharp>x" "d\<sharp>a" "d\<sharp>y" "d\<noteq>c" "c\<sharp>N" "c\<sharp>e" "d\<sharp>M" "d\<sharp>e" by fact+
  have ih1: "M{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* M[x\<turnstile>n>y]" by fact
  have ih2: "N{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* N[x\<turnstile>n>y]" by fact
  have "(AndR <c>.M <d>.N e){x:=<a>.Ax y a} = AndR <c>.(M{x:=<a>.Ax y a}) <d>.(N{x:=<a>.Ax y a}) e"
    using fs by simp
  also have "\<dots> \<longrightarrow>\<^sub>a* AndR <c>.(M[x\<turnstile>n>y]) <d>.(N[x\<turnstile>n>y]) e" using ih1 ih2 by (auto intro: a_star_congs)
  finally show "(AndR <c>.M <d>.N e){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (AndR <c>.M <d>.N e)[x\<turnstile>n>y]"
    using fs by simp
next
  case (AndL1 u M v x a y)
  have fs: "u\<sharp>x" "u\<sharp>a" "u\<sharp>y" "u\<sharp>v" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* M[x\<turnstile>n>y]" by fact
  show "(AndL1 (u).M v){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (AndL1 (u).M v)[x\<turnstile>n>y]"
  proof(cases "v=x")
    case True
    assume eq: "v=x"
    obtain v'::"name" where new: "v'\<sharp>(Ax y a,M{x:=<a>.Ax y a},u)" by (rule exists_fresh(1)[OF fs_name1])
    have "(AndL1 (u).M v){x:=<a>.Ax y a} = 
                        fresh_fun (\<lambda>v'. Cut <a>.Ax y a (v').AndL1 (u).(M{x:=<a>.Ax y a}) v')"
      using eq fs by simp
    also have "\<dots> = Cut <a>.Ax y a (v').AndL1 (u).(M{x:=<a>.Ax y a}) v'" 
      using new by (simp add: fresh_fun_simp_AndL1 fresh_prod)
    also have "\<dots> \<longrightarrow>\<^sub>a* (AndL1 (u).(M{x:=<a>.Ax y a}) v')[v'\<turnstile>n>y]"
      using new 
      by (intro a_starI a_redu.intros better_LAxL_intro fin.intros) (simp add: abs_fresh)
    also have "\<dots> = AndL1 (u).(M{x:=<a>.Ax y a}) y" using fs new
      by (auto simp: fresh_prod fresh_atm nrename_fresh)
    also have "\<dots> \<longrightarrow>\<^sub>a* AndL1 (u).(M[x\<turnstile>n>y]) y" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (AndL1 (u).M v)[x\<turnstile>n>y]" using eq fs by simp
    finally show "(AndL1 (u).M v){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (AndL1 (u).M v)[x\<turnstile>n>y]" by simp
  next
    case False
    assume neq: "v\<noteq>x"
    have "(AndL1 (u).M v){x:=<a>.Ax y a} = AndL1 (u).(M{x:=<a>.Ax y a}) v" using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* AndL1 (u).(M[x\<turnstile>n>y]) v" using ih by (auto intro: a_star_congs)
    finally show "(AndL1 (u).M v){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (AndL1 (u).M v)[x\<turnstile>n>y]" using fs neq by simp
  qed
next
  case (AndL2 u M v x a y)
  have fs: "u\<sharp>x" "u\<sharp>a" "u\<sharp>y" "u\<sharp>v" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* M[x\<turnstile>n>y]" by fact
  show "(AndL2 (u).M v){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (AndL2 (u).M v)[x\<turnstile>n>y]"
  proof(cases "v=x")
    case True
    assume eq: "v=x"
    obtain v'::"name" where new: "v'\<sharp>(Ax y a,M{x:=<a>.Ax y a},u)" by (rule exists_fresh(1)[OF fs_name1])
    have "(AndL2 (u).M v){x:=<a>.Ax y a} = 
                        fresh_fun (\<lambda>v'. Cut <a>.Ax y a (v').AndL2 (u).(M{x:=<a>.Ax y a}) v')"
      using eq fs by simp
    also have "\<dots> = Cut <a>.Ax y a (v').AndL2 (u).(M{x:=<a>.Ax y a}) v'" 
      using new by (simp add: fresh_fun_simp_AndL2 fresh_prod)
    also have "\<dots> \<longrightarrow>\<^sub>a* (AndL2 (u).(M{x:=<a>.Ax y a}) v')[v'\<turnstile>n>y]"
      using new 
      by (intro a_starI a_redu.intros better_LAxL_intro fin.intros) (simp add: abs_fresh)
    also have "\<dots> = AndL2 (u).(M{x:=<a>.Ax y a}) y" using fs new
      by (auto simp: fresh_prod fresh_atm nrename_fresh)
    also have "\<dots> \<longrightarrow>\<^sub>a* AndL2 (u).(M[x\<turnstile>n>y]) y" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (AndL2 (u).M v)[x\<turnstile>n>y]" using eq fs by simp
    finally show "(AndL2 (u).M v){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (AndL2 (u).M v)[x\<turnstile>n>y]" by simp
  next
    case False
    assume neq: "v\<noteq>x"
    have "(AndL2 (u).M v){x:=<a>.Ax y a} = AndL2 (u).(M{x:=<a>.Ax y a}) v" using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* AndL2 (u).(M[x\<turnstile>n>y]) v" using ih by (auto intro: a_star_congs)
    finally show "(AndL2 (u).M v){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (AndL2 (u).M v)[x\<turnstile>n>y]" using fs neq by simp
  qed
next
  case (OrR1 c M d  x a y)
  have fs: "c\<sharp>x" "c\<sharp>a" "c\<sharp>y" "c\<sharp>d" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* M[x\<turnstile>n>y]" by fact
  have "(OrR1 <c>.M d){x:=<a>.Ax y a} = OrR1 <c>.(M{x:=<a>.Ax y a}) d" using fs by (simp add: fresh_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a* OrR1 <c>.(M[x\<turnstile>n>y]) d" using ih by (auto intro: a_star_congs)
  finally show "(OrR1 <c>.M d){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (OrR1 <c>.M d)[x\<turnstile>n>y]" using fs by simp
next
  case (OrR2 c M d  x a y)
  have fs: "c\<sharp>x" "c\<sharp>a" "c\<sharp>y" "c\<sharp>d" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* M[x\<turnstile>n>y]" by fact
  have "(OrR2 <c>.M d){x:=<a>.Ax y a} = OrR2 <c>.(M{x:=<a>.Ax y a}) d" using fs by (simp add: fresh_atm)
  also have "\<dots> \<longrightarrow>\<^sub>a* OrR2 <c>.(M[x\<turnstile>n>y]) d" using ih by (auto intro: a_star_congs)
  finally show "(OrR2 <c>.M d){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (OrR2 <c>.M d)[x\<turnstile>n>y]" using fs by simp
next
  case (OrL u M v N z x a y)
  have fs: "u\<sharp>x" "u\<sharp>a" "u\<sharp>y" "v\<sharp>x" "v\<sharp>a" "v\<sharp>y" "v\<noteq>u" "u\<sharp>N" "u\<sharp>z" "v\<sharp>M" "v\<sharp>z" by fact+
  have ih1: "M{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* M[x\<turnstile>n>y]" by fact
  have ih2: "N{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* N[x\<turnstile>n>y]" by fact
  show "(OrL (u).M (v).N z){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (OrL (u).M (v).N z)[x\<turnstile>n>y]"
  proof(cases "z=x")
    case True
    assume eq: "z=x"
    obtain z'::"name" where new: "z'\<sharp>(Ax y a,M{x:=<a>.Ax y a},N{x:=<a>.Ax y a},u,v,y,a)" 
      by (rule exists_fresh(1)[OF fs_name1])
    have "(OrL (u).M (v).N z){x:=<a>.Ax y a} = 
                 fresh_fun (\<lambda>z'. Cut <a>.Ax y a (z').OrL (u).(M{x:=<a>.Ax y a}) (v).(N{x:=<a>.Ax y a}) z')"
      using eq fs by simp
    also have "\<dots> = Cut <a>.Ax y a (z').OrL (u).(M{x:=<a>.Ax y a}) (v).(N{x:=<a>.Ax y a}) z'" 
      using new by (simp add: fresh_fun_simp_OrL)
    also have "\<dots> \<longrightarrow>\<^sub>a* (OrL (u).(M{x:=<a>.Ax y a}) (v).(N{x:=<a>.Ax y a}) z')[z'\<turnstile>n>y]"
      using new 
      by (intro a_starI a_redu.intros better_LAxL_intro fin.intros) (simp_all add: abs_fresh)
    also have "\<dots> = OrL (u).(M{x:=<a>.Ax y a}) (v).(N{x:=<a>.Ax y a}) y" using fs new
      by (auto simp: fresh_prod fresh_atm nrename_fresh subst_fresh)
    also have "\<dots> \<longrightarrow>\<^sub>a* OrL (u).(M[x\<turnstile>n>y]) (v).(N[x\<turnstile>n>y]) y" 
      using ih1 ih2 by (auto intro: a_star_congs)
    also have "\<dots> = (OrL (u).M (v).N z)[x\<turnstile>n>y]" using eq fs by simp
    finally show "(OrL (u).M (v).N z){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (OrL (u).M (v).N z)[x\<turnstile>n>y]" by simp
  next
    case False
    assume neq: "z\<noteq>x"
    have "(OrL (u).M (v).N z){x:=<a>.Ax y a} = OrL (u).(M{x:=<a>.Ax y a}) (v).(N{x:=<a>.Ax y a}) z" 
      using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* OrL (u).(M[x\<turnstile>n>y]) (v).(N[x\<turnstile>n>y]) z" 
      using ih1 ih2 by (auto intro: a_star_congs)
    finally show "(OrL (u).M (v).N z){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (OrL (u).M (v).N z)[x\<turnstile>n>y]" using fs neq by simp
  qed
next
  case (ImpR z c M d x a y)
  have fs: "z\<sharp>x" "z\<sharp>a" "z\<sharp>y" "c\<sharp>x" "c\<sharp>a" "c\<sharp>y" "z\<sharp>d" "c\<sharp>d" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* M[x\<turnstile>n>y]" by fact
  have "(ImpR (z).<c>.M d){x:=<a>.Ax y a} = ImpR (z).<c>.(M{x:=<a>.Ax y a}) d" using fs by simp
  also have "\<dots> \<longrightarrow>\<^sub>a* ImpR (z).<c>.(M[x\<turnstile>n>y]) d" using ih by (auto intro: a_star_congs)
  finally show "(ImpR (z).<c>.M d){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (ImpR (z).<c>.M d)[x\<turnstile>n>y]" using fs by simp
next
  case (ImpL c M u N v x a y)
  have fs: "c\<sharp>x" "c\<sharp>a" "c\<sharp>y" "u\<sharp>x" "u\<sharp>a" "u\<sharp>y" "c\<sharp>N" "c\<sharp>v" "u\<sharp>M" "u\<sharp>v" by fact+
  have ih1: "M{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* M[x\<turnstile>n>y]" by fact
  have ih2: "N{x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* N[x\<turnstile>n>y]" by fact
  show "(ImpL <c>.M (u).N v){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (ImpL <c>.M (u).N v)[x\<turnstile>n>y]"
  proof(cases "v=x")
    case True
    assume eq: "v=x"
    obtain v'::"name" where new: "v'\<sharp>(Ax y a,M{x:=<a>.Ax y a},N{x:=<a>.Ax y a},y,a,u)" 
      by (rule exists_fresh(1)[OF fs_name1])
    have "(ImpL <c>.M (u).N v){x:=<a>.Ax y a} = 
                 fresh_fun (\<lambda>v'. Cut <a>.Ax y a (v').ImpL <c>.(M{x:=<a>.Ax y a}) (u).(N{x:=<a>.Ax y a}) v')"
      using eq fs by simp 
    also have "\<dots> = Cut <a>.Ax y a (v').ImpL <c>.(M{x:=<a>.Ax y a}) (u).(N{x:=<a>.Ax y a}) v'" 
      using new by (simp add: fresh_fun_simp_ImpL)
    also have "\<dots> \<longrightarrow>\<^sub>a* (ImpL <c>.(M{x:=<a>.Ax y a}) (u).(N{x:=<a>.Ax y a}) v')[v'\<turnstile>n>y]"
      using new 
      by (intro a_starI a_redu.intros better_LAxL_intro fin.intros) (simp_all add: abs_fresh)
    also have "\<dots> = ImpL <c>.(M{x:=<a>.Ax y a}) (u).(N{x:=<a>.Ax y a}) y" using fs new
      by (auto simp: fresh_prod subst_fresh fresh_atm trm.inject alpha rename_fresh)
    also have "\<dots> \<longrightarrow>\<^sub>a* ImpL <c>.(M[x\<turnstile>n>y]) (u).(N[x\<turnstile>n>y]) y" 
      using ih1 ih2 by (auto intro: a_star_congs)
    also have "\<dots> = (ImpL <c>.M (u).N v)[x\<turnstile>n>y]" using eq fs by simp
    finally show "(ImpL <c>.M (u).N v){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (ImpL <c>.M (u).N v)[x\<turnstile>n>y]" using fs by simp
  next
    case False
    assume neq: "v\<noteq>x"
    have "(ImpL <c>.M (u).N v){x:=<a>.Ax y a} = ImpL <c>.(M{x:=<a>.Ax y a}) (u).(N{x:=<a>.Ax y a}) v" 
      using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* ImpL <c>.(M[x\<turnstile>n>y]) (u).(N[x\<turnstile>n>y]) v" 
      using ih1 ih2 by (auto intro: a_star_congs)
    finally show "(ImpL <c>.M (u).N v){x:=<a>.Ax y a} \<longrightarrow>\<^sub>a* (ImpL <c>.M (u).N v)[x\<turnstile>n>y]" 
      using fs neq by simp
  qed
qed

lemma subst_with_ax2:
  shows "M{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* M[b\<turnstile>c>a]"
proof(nominal_induct M avoiding: b a x rule: trm.strong_induct)
  case (Ax z c b a x)
  show "(Ax z c){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (Ax z c)[b\<turnstile>c>a]"
  proof (cases "c=b")
    case True
    assume eq: "c=b"
    have "(Ax z c){b:=(x).Ax x a} = Cut <b>.Ax z c (x).Ax x a" using eq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* (Ax z c)[b\<turnstile>c>a]" using eq by blast
    finally show "(Ax z c){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (Ax z c)[b\<turnstile>c>a]" by simp
  next
    case False
    assume neq: "c\<noteq>b"
    then show "(Ax z c){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (Ax z c)[b\<turnstile>c>a]" by simp
  qed
next
  case (Cut c M z N b a x)
  have fs: "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "c\<sharp>N" "z\<sharp>b" "z\<sharp>a" "z\<sharp>x" "z\<sharp>M" by fact+
  have ih1: "M{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* M[b\<turnstile>c>a]" by fact
  have ih2: "N{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* N[b\<turnstile>c>a]" by fact
  show "(Cut <c>.M (z).N){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (Cut <c>.M (z).N)[b\<turnstile>c>a]"
  proof (cases "N = Ax z b")
    case True
    assume eq: "N = Ax z b"
    have "(Cut <c>.M (z).N){b:=(x).Ax x a} = Cut <c>.(M{b:=(x).Ax x a}) (x).Ax x a" using eq fs by simp 
    also have "\<dots> \<longrightarrow>\<^sub>a* Cut <c>.(M[b\<turnstile>c>a]) (x).Ax x a" using ih1 a_star_congs by blast
    also have "\<dots> = Cut <c>.(M[b\<turnstile>c>a]) (z).(N[b\<turnstile>c>a])" using eq fs
      by (simp add: trm.inject alpha calc_atm fresh_atm)
    finally show "(Cut <c>.M (z).N){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (Cut <c>.M (z).N)[b\<turnstile>c>a]" using fs by simp
  next
    case False
    assume neq: "N \<noteq> Ax z b"
    have "(Cut <c>.M (z).N){b:=(x).Ax x a} = Cut <c>.(M{b:=(x).Ax x a}) (z).(N{b:=(x).Ax x a})" 
      using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* Cut <c>.(M[b\<turnstile>c>a]) (z).(N[b\<turnstile>c>a])" using ih1 ih2 a_star_congs by blast
    finally show "(Cut <c>.M (z).N){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (Cut <c>.M (z).N)[b\<turnstile>c>a]" using fs by simp
  qed
next
  case (NotR z M c b a x)
  have fs: "z\<sharp>b" "z\<sharp>a" "z\<sharp>x" "z\<sharp>c" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* M[b\<turnstile>c>a]" by fact
  show "(NotR (z).M c){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (NotR (z).M c)[b\<turnstile>c>a]"
  proof (cases "c=b")
    case True
    assume eq: "c=b"
    obtain a'::"coname" where new: "a'\<sharp>(Ax x a,M{b:=(x).Ax x a})" by (rule exists_fresh(2)[OF fs_coname1])
    have "(NotR (z).M c){b:=(x).Ax x a} = 
                        fresh_fun (\<lambda>a'. Cut <a'>.NotR (z).M{b:=(x).Ax x a} a' (x).Ax x a)" 
      using eq fs by simp
    also have "\<dots> = Cut <a'>.NotR (z).M{b:=(x).Ax x a} a' (x).Ax x a"
      using new by (simp add: fresh_fun_simp_NotR fresh_prod)
    also have "\<dots> \<longrightarrow>\<^sub>a* (NotR (z).(M{b:=(x).Ax x a}) a')[a'\<turnstile>c>a]"
      using new 
      by (intro a_starI a_redu.intros better_LAxR_intro fic.intros) auto
    also have "\<dots> = NotR (z).(M{b:=(x).Ax x a}) a" using new by (simp add: crename_fresh)
    also have "\<dots> \<longrightarrow>\<^sub>a* NotR (z).(M[b\<turnstile>c>a]) a" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (NotR (z).M c)[b\<turnstile>c>a]" using eq by simp
    finally show "(NotR (z).M c){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (NotR (z).M c)[b\<turnstile>c>a]" by simp
  next
    case False
    assume neq: "c\<noteq>b"
    have "(NotR (z).M c){b:=(x).Ax x a} = NotR (z).(M{b:=(x).Ax x a}) c" using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* NotR (z).(M[b\<turnstile>c>a]) c" using ih by (auto intro: a_star_congs)
    finally show "(NotR (z).M c){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (NotR (z).M c)[b\<turnstile>c>a]" using neq by simp
  qed
next
  case (NotL c M z b a x)  
  have fs: "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "c\<sharp>z" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* M[b\<turnstile>c>a]" by fact
  have "(NotL <c>.M z){b:=(x).Ax x a} = NotL <c>.(M{b:=(x).Ax x a}) z" using fs by simp
  also have "\<dots> \<longrightarrow>\<^sub>a* NotL <c>.(M[b\<turnstile>c>a]) z" using ih by (auto intro: a_star_congs)
  finally show "(NotL <c>.M z){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (NotL <c>.M z)[b\<turnstile>c>a]" using fs by simp
next
  case (AndR c M d N e b a x)
  have fs: "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "d\<sharp>b" "d\<sharp>a" "d\<sharp>x" "d\<noteq>c" "c\<sharp>N" "c\<sharp>e" "d\<sharp>M" "d\<sharp>e" by fact+
  have ih1: "M{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* M[b\<turnstile>c>a]" by fact
  have ih2: "N{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* N[b\<turnstile>c>a]" by fact
  show "(AndR <c>.M <d>.N e){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (AndR <c>.M <d>.N e)[b\<turnstile>c>a]"
  proof(cases "e=b")
    case True
    assume eq: "e=b"
    obtain e'::"coname" where new: "e'\<sharp>(Ax x a,M{b:=(x).Ax x a},N{b:=(x).Ax x a},c,d)" 
      by (rule exists_fresh(2)[OF fs_coname1])
    have "(AndR <c>.M <d>.N e){b:=(x).Ax x a} = 
               fresh_fun (\<lambda>e'. Cut <e'>.AndR <c>.(M{b:=(x).Ax x a}) <d>.(N{b:=(x).Ax x a}) e' (x).Ax x a)"
      using eq fs by simp
    also have "\<dots> = Cut <e'>.AndR <c>.(M{b:=(x).Ax x a}) <d>.(N{b:=(x).Ax x a}) e' (x).Ax x a"
      using new by (simp add: fresh_fun_simp_AndR fresh_prod)
    also have "\<dots> \<longrightarrow>\<^sub>a* (AndR <c>.(M{b:=(x).Ax x a}) <d>.(N{b:=(x).Ax x a}) e')[e'\<turnstile>c>a]"
      using new 
      by (intro a_starI a_redu.intros better_LAxR_intro fic.intros) (simp_all add: abs_fresh)
    also have "\<dots> = AndR <c>.(M{b:=(x).Ax x a}) <d>.(N{b:=(x).Ax x a}) a" using fs new
      by (auto simp: fresh_prod fresh_atm subst_fresh crename_fresh)
    also have "\<dots> \<longrightarrow>\<^sub>a* AndR <c>.(M[b\<turnstile>c>a]) <d>.(N[b\<turnstile>c>a]) a" using ih1 ih2 by (auto intro: a_star_congs)
    also have "\<dots> = (AndR <c>.M <d>.N e)[b\<turnstile>c>a]" using eq fs by simp
    finally show "(AndR <c>.M <d>.N e){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (AndR <c>.M <d>.N e)[b\<turnstile>c>a]" by simp
  next
    case False
    assume neq: "e\<noteq>b"
    have "(AndR <c>.M <d>.N e){b:=(x).Ax x a} = AndR <c>.(M{b:=(x).Ax x a}) <d>.(N{b:=(x).Ax x a}) e"
      using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* AndR <c>.(M[b\<turnstile>c>a]) <d>.(N[b\<turnstile>c>a]) e" using ih1 ih2 by (auto intro: a_star_congs)
    finally show "(AndR <c>.M <d>.N e){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (AndR <c>.M <d>.N e)[b\<turnstile>c>a]"
      using fs neq by simp
  qed
next
  case (AndL1 u M v b a x)
  have fs: "u\<sharp>b" "u\<sharp>a" "u\<sharp>x" "u\<sharp>v" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* M[b\<turnstile>c>a]" by fact
  have "(AndL1 (u).M v){b:=(x).Ax x a} = AndL1 (u).(M{b:=(x).Ax x a}) v" using fs by simp
  also have "\<dots> \<longrightarrow>\<^sub>a* AndL1 (u).(M[b\<turnstile>c>a]) v" using ih by (auto intro: a_star_congs)
  finally show "(AndL1 (u).M v){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (AndL1 (u).M v)[b\<turnstile>c>a]" using fs by simp
next
  case (AndL2 u M v b a x)
  have fs: "u\<sharp>b" "u\<sharp>a" "u\<sharp>x" "u\<sharp>v" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* M[b\<turnstile>c>a]" by fact
  have "(AndL2 (u).M v){b:=(x).Ax x a} = AndL2 (u).(M{b:=(x).Ax x a}) v" using fs by simp
  also have "\<dots> \<longrightarrow>\<^sub>a* AndL2 (u).(M[b\<turnstile>c>a]) v" using ih by (auto intro: a_star_congs)
  finally show "(AndL2 (u).M v){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (AndL2 (u).M v)[b\<turnstile>c>a]" using fs by simp
next
  case (OrR1 c M d  b a x)
  have fs: "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "c\<sharp>d" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* M[b\<turnstile>c>a]" by fact
  show "(OrR1 <c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (OrR1 <c>.M d)[b\<turnstile>c>a]"
  proof(cases "d=b")
    case True
    assume eq: "d=b"
    obtain a'::"coname" where new: "a'\<sharp>(Ax x a,M{b:=(x).Ax x a},c,x,a)" 
      by (rule exists_fresh(2)[OF fs_coname1])
    have "(OrR1 <c>.M d){b:=(x).Ax x a} = 
             fresh_fun (\<lambda>a'. Cut <a'>.OrR1 <c>.M{b:=(x).Ax x a} a' (x).Ax x a)" using fs eq by (simp)
    also have "\<dots> = Cut <a'>.OrR1 <c>.M{b:=(x).Ax x a} a' (x).Ax x a"
      using new by (simp add: fresh_fun_simp_OrR1)
    also have "\<dots> \<longrightarrow>\<^sub>a* (OrR1 <c>.M{b:=(x).Ax x a} a')[a'\<turnstile>c>a]"
      using new 
      by (intro a_starI a_redu.intros better_LAxR_intro fic.intros) (simp_all add: abs_fresh)
    also have "\<dots> = OrR1 <c>.M{b:=(x).Ax x a} a" using fs new
      by (auto simp: fresh_prod fresh_atm crename_fresh subst_fresh)
    also have "\<dots> \<longrightarrow>\<^sub>a* OrR1 <c>.(M[b\<turnstile>c>a]) a" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (OrR1 <c>.M d)[b\<turnstile>c>a]" using eq fs by simp
    finally show "(OrR1 <c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (OrR1 <c>.M d)[b\<turnstile>c>a]" by simp
  next
    case False
    assume neq: "d\<noteq>b"
    have "(OrR1 <c>.M d){b:=(x).Ax x a} = OrR1 <c>.(M{b:=(x).Ax x a}) d" using fs neq by (simp)
    also have "\<dots> \<longrightarrow>\<^sub>a* OrR1 <c>.(M[b\<turnstile>c>a]) d" using ih by (auto intro: a_star_congs)
    finally show "(OrR1 <c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (OrR1 <c>.M d)[b\<turnstile>c>a]" using fs neq by simp
  qed
next
  case (OrR2 c M d  b a x)
  have fs: "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "c\<sharp>d" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* M[b\<turnstile>c>a]" by fact
  show "(OrR2 <c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (OrR2 <c>.M d)[b\<turnstile>c>a]"
  proof(cases "d=b")
    case True
    assume eq: "d=b"
    obtain a'::"coname" where new: "a'\<sharp>(Ax x a,M{b:=(x).Ax x a},c,x,a)" 
      by (rule exists_fresh(2)[OF fs_coname1])
    have "(OrR2 <c>.M d){b:=(x).Ax x a} = 
             fresh_fun (\<lambda>a'. Cut <a'>.OrR2 <c>.M{b:=(x).Ax x a} a' (x).Ax x a)" using fs eq by (simp)
    also have "\<dots> = Cut <a'>.OrR2 <c>.M{b:=(x).Ax x a} a' (x).Ax x a"
      using new by (simp add: fresh_fun_simp_OrR2)
    also have "\<dots> \<longrightarrow>\<^sub>a* (OrR2 <c>.M{b:=(x).Ax x a} a')[a'\<turnstile>c>a]"
      using new 
      by (intro a_starI a_redu.intros better_LAxR_intro fic.intros) (simp_all add: abs_fresh)
    also have "\<dots> = OrR2 <c>.M{b:=(x).Ax x a} a" using fs new
      by (auto simp: fresh_prod fresh_atm crename_fresh subst_fresh)
    also have "\<dots> \<longrightarrow>\<^sub>a* OrR2 <c>.(M[b\<turnstile>c>a]) a" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (OrR2 <c>.M d)[b\<turnstile>c>a]" using eq fs by simp
    finally show "(OrR2 <c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (OrR2 <c>.M d)[b\<turnstile>c>a]" by simp
  next
    case False
    assume neq: "d\<noteq>b"
    have "(OrR2 <c>.M d){b:=(x).Ax x a} = OrR2 <c>.(M{b:=(x).Ax x a}) d" using fs neq by (simp)
    also have "\<dots> \<longrightarrow>\<^sub>a* OrR2 <c>.(M[b\<turnstile>c>a]) d" using ih by (auto intro: a_star_congs)
    finally show "(OrR2 <c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (OrR2 <c>.M d)[b\<turnstile>c>a]" using fs neq by simp
  qed
next
  case (OrL u M v N z b a x)
  have fs: "u\<sharp>b" "u\<sharp>a" "u\<sharp>x" "v\<sharp>b" "v\<sharp>a" "v\<sharp>x" "v\<noteq>u" "u\<sharp>N" "u\<sharp>z" "v\<sharp>M" "v\<sharp>z" by fact+
  have ih1: "M{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* M[b\<turnstile>c>a]" by fact
  have ih2: "N{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* N[b\<turnstile>c>a]" by fact
  have "(OrL (u).M (v).N z){b:=(x).Ax x a} = OrL (u).(M{b:=(x).Ax x a}) (v).(N{b:=(x).Ax x a}) z" 
    using fs by simp
  also have "\<dots> \<longrightarrow>\<^sub>a* OrL (u).(M[b\<turnstile>c>a]) (v).(N[b\<turnstile>c>a]) z" using ih1 ih2 by (auto intro: a_star_congs)
  finally show "(OrL (u).M (v).N z){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (OrL (u).M (v).N z)[b\<turnstile>c>a]" using fs by simp
next
  case (ImpR z c M d b a x)
  have fs: "z\<sharp>b" "z\<sharp>a" "z\<sharp>x" "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "z\<sharp>d" "c\<sharp>d" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* M[b\<turnstile>c>a]" by fact
  show "(ImpR (z).<c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (ImpR (z).<c>.M d)[b\<turnstile>c>a]"
  proof(cases "b=d")
    case True
    assume eq: "b=d"
    obtain a'::"coname" where new: "a'\<sharp>(Ax x a,M{b:=(x).Ax x a},x,a,c)" 
      by (rule exists_fresh(2)[OF fs_coname1])
    have "(ImpR (z).<c>.M d){b:=(x).Ax x a} =
                fresh_fun (\<lambda>a'. Cut <a'>.ImpR z.<c>.M{b:=(x).Ax x a} a' (x).Ax x a)" using fs eq by simp
    also have "\<dots> = Cut <a'>.ImpR z.<c>.M{b:=(x).Ax x a} a' (x).Ax x a" 
      using new by (simp add: fresh_fun_simp_ImpR)
    also have "\<dots> \<longrightarrow>\<^sub>a* (ImpR z.<c>.M{b:=(x).Ax x a} a')[a'\<turnstile>c>a]"
      using new 
      by (intro a_starI a_redu.intros better_LAxR_intro fic.intros) (simp_all add: abs_fresh)
    also have "\<dots> = ImpR z.<c>.M{b:=(x).Ax x a} a" using fs new
      by (auto simp: fresh_prod crename_fresh subst_fresh fresh_atm)
    also have "\<dots> \<longrightarrow>\<^sub>a* ImpR z.<c>.(M[b\<turnstile>c>a]) a" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (ImpR z.<c>.M b)[b\<turnstile>c>a]" using eq fs by simp
    finally show "(ImpR (z).<c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (ImpR (z).<c>.M d)[b\<turnstile>c>a]" using eq by simp
  next
    case False
    assume neq: "b\<noteq>d"
    have "(ImpR (z).<c>.M d){b:=(x).Ax x a} = ImpR (z).<c>.(M{b:=(x).Ax x a}) d" using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^sub>a* ImpR (z).<c>.(M[b\<turnstile>c>a]) d" using ih by (auto intro: a_star_congs)
    finally show "(ImpR (z).<c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (ImpR (z).<c>.M d)[b\<turnstile>c>a]" using neq fs by simp
  qed
next
  case (ImpL c M u N v b a x)
  have fs: "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "u\<sharp>b" "u\<sharp>a" "u\<sharp>x" "c\<sharp>N" "c\<sharp>v" "u\<sharp>M" "u\<sharp>v" by fact+
  have ih1: "M{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* M[b\<turnstile>c>a]" by fact
  have ih2: "N{b:=(x).Ax x a} \<longrightarrow>\<^sub>a* N[b\<turnstile>c>a]" by fact
  have "(ImpL <c>.M (u).N v){b:=(x).Ax x a} = ImpL <c>.(M{b:=(x).Ax x a}) (u).(N{b:=(x).Ax x a}) v" 
    using fs by simp
  also have "\<dots> \<longrightarrow>\<^sub>a* ImpL <c>.(M[b\<turnstile>c>a]) (u).(N[b\<turnstile>c>a]) v" 
    using ih1 ih2 by (auto intro: a_star_congs)
  finally show "(ImpL <c>.M (u).N v){b:=(x).Ax x a} \<longrightarrow>\<^sub>a* (ImpL <c>.M (u).N v)[b\<turnstile>c>a]" 
    using fs by simp
qed

text \<open>substitution lemmas\<close>

lemma not_Ax1: "\<not>(b\<sharp>M) \<Longrightarrow> M{b:=(y).Q} \<noteq> Ax x a"
proof (nominal_induct M avoiding: b y Q x a rule: trm.strong_induct)
  case (NotR name trm coname)
  then show ?case
    by (metis fin.intros(1) fin_rest_elims(2) subst_not_fin2)
next
  case (AndR coname1 trm1 coname2 trm2 coname3)
  then show ?case
    by (metis fin.intros(1) fin_rest_elims(3) subst_not_fin2)
next
  case (OrR1 coname1 trm coname2)
  then show ?case
    by (metis fin.intros(1) fin_rest_elims(4) subst_not_fin2)
next
  case (OrR2 coname1 trm coname2)
  then show ?case
    by (metis fin.intros(1) fin_rest_elims(5) subst_not_fin2)
next
  case (ImpR name coname1 trm coname2)
  then show ?case
    by (metis fin.intros(1) fin_rest_elims(6) subst_not_fin2)
qed (auto simp: fresh_atm abs_fresh abs_supp fin_supp)



lemma not_Ax2: "\<not>(x\<sharp>M) \<Longrightarrow> M{x:=<b>.Q} \<noteq> Ax y a"
proof (nominal_induct M avoiding: b y Q x a rule: trm.strong_induct)
  case (NotL coname trm name)
  then show ?case
    by (metis fic.intros(1) fic_rest_elims(2) not_fic_subst1)
next
  case (AndL1 name1 trm name2)
  then show ?case
    by (metis fic.intros(1) fic_rest_elims(4) not_fic_subst1)
next
  case (AndL2 name1 trm name2)
  then show ?case
    by (metis fic.intros(1) fic_rest_elims(5) not_fic_subst1)
next
  case (OrL name1 trm1 name2 trm2 name3)
  then show ?case
    by (metis fic.intros(1) fic_rest_elims(3) not_fic_subst1)
next
  case (ImpL coname trm1 name1 trm2 name2)
  then show ?case
    by (metis fic.intros(1) fic_rest_elims(6) not_fic_subst1)
qed (auto simp: fresh_atm abs_fresh abs_supp fin_supp)


lemma interesting_subst1:
  assumes a: "x\<noteq>y" "x\<sharp>P" "y\<sharp>P" 
  shows "N{y:=<c>.P}{x:=<c>.P} = N{x:=<c>.Ax y c}{y:=<c>.P}"
  using a
proof(nominal_induct N avoiding: x y c P rule: trm.strong_induct)
  case (Cut d M u M' x' y' c P)
  with assms show ?case
    apply (simp add: abs_fresh)
    by (smt (verit) forget(1) not_Ax2)
next
  case (NotL d M u)
  obtain x'::name and x''::name 
    where "x' \<sharp> (P,M{y:=<c>.P},M{x:=<c>.Ax y c}{y:=<c>.P},y,x)"
      and  "x''\<sharp> (P,M{x:=<c>.Ax y c},M{x:=<c>.Ax y c}{y:=<c>.P},Ax y c,y,x)"
    by (meson exists_fresh(1) fs_name1)
  then show ?case
    using NotL
    by (auto simp: perm_fresh_fresh(1) swap_simps(3,7) trm.inject alpha forget 
        fresh_atm abs_fresh fresh_fun_simp_NotL fresh_prod)
next
  case (AndL1 u M d)
  obtain x'::name and x''::name 
    where "x' \<sharp> (P,M{y:=<c>.P},M{x:=<c>.Ax y c}{y:=<c>.P},u,y,x)"
      and  "x''\<sharp> (P,Ax y c,M{x:=<c>.Ax y c},M{x:=<c>.Ax y c}{y:=<c>.P},u,y,x)"
    by (meson exists_fresh(1) fs_name1)
  then show ?case
    using AndL1
    by (auto simp: perm_fresh_fresh(1) swap_simps(3,7) trm.inject alpha forget 
        fresh_atm abs_fresh fresh_fun_simp_AndL1 fresh_prod)
next
  case (AndL2 u M d)
  obtain x'::name and x''::name 
    where "x' \<sharp> (P,M{y:=<c>.P},M{x:=<c>.Ax y c}{y:=<c>.P},u,y,x)"
      and  "x''\<sharp> (P,Ax y c,M{x:=<c>.Ax y c},M{x:=<c>.Ax y c}{y:=<c>.P},u,y,x)"
    by (meson exists_fresh(1) fs_name1)
  then show ?case
    using AndL2
    by (auto simp: perm_fresh_fresh(1) swap_simps(3,7) trm.inject alpha forget 
        fresh_atm abs_fresh fresh_fun_simp_AndL2 fresh_prod)
next
  case (OrL x1 M x2 M' x3)
  obtain x'::name and x''::name 
    where "x' \<sharp> (P,M{y:=<c>.P},M{x:=<c>.Ax y c}{y:=<c>.P},
                       M'{y:=<c>.P},M'{x:=<c>.Ax y c}{y:=<c>.P},x1,x2,x3,y,x)"
      and  "x''\<sharp> (P,Ax y c,M{x:=<c>.Ax y c},M{x:=<c>.Ax y c}{y:=<c>.P},
                                        M'{x:=<c>.Ax y c},M'{x:=<c>.Ax y c}{y:=<c>.P},x1,x2,x3,y,x)"
    by (meson exists_fresh(1) fs_name1)
  then show ?case
    using OrL
    by (auto simp: perm_fresh_fresh(1) swap_simps(3,7) trm.inject alpha forget 
        fresh_atm abs_fresh fresh_fun_simp_OrL fresh_prod subst_fresh)
next
  case (ImpL a M x1 M' x2)
  obtain x'::name and x''::name 
    where "x' \<sharp> (P,M{x2:=<c>.P},M{x:=<c>.Ax x2 c}{x2:=<c>.P},
                                        M'{x2:=<c>.P},M'{x:=<c>.Ax x2 c}{x2:=<c>.P},x1,y,x)"
      and  "x''\<sharp> (P,Ax y c,M{x2:=<c>.Ax y c},M{x2:=<c>.Ax y c}{y:=<c>.P},
                                        M'{x2:=<c>.Ax y c},M'{x2:=<c>.Ax y c}{y:=<c>.P},x1,x2,y,x)"
    by (meson exists_fresh(1) fs_name1)
  then show ?case
    using ImpL
    by (auto simp: perm_fresh_fresh(1) swap_simps(3,7) trm.inject alpha forget 
        fresh_atm abs_fresh fresh_fun_simp_ImpL fresh_prod subst_fresh)
qed (auto simp: abs_fresh fresh_atm forget trm.inject subst_fresh)

lemma interesting_subst1':
  assumes "x\<noteq>y" "x\<sharp>P" "y\<sharp>P" 
  shows "N{y:=<c>.P}{x:=<c>.P} = N{x:=<a>.Ax y a}{y:=<c>.P}"
proof -
  show ?thesis
  proof (cases "c=a")
    case True with assms show ?thesis 
      by (simp add: interesting_subst1)
  next
    case False 
    then have "N{x:=<a>.Ax y a} = N{x:=<c>.([(c,a)]\<bullet>Ax y a)}"
      by (simp add: fresh_atm(2,4) fresh_prod substn_rename4)
    with assms show ?thesis
      by (simp add: interesting_subst1 swap_simps) 
  qed
qed

lemma interesting_subst2:
  assumes a: "a\<noteq>b" "a\<sharp>P" "b\<sharp>P" 
  shows "N{a:=(y).P}{b:=(y).P} = N{b:=(y).Ax y a}{a:=(y).P}"
  using a
proof(nominal_induct N avoiding: a b y P rule: trm.strong_induct)
  case Ax
  then show ?case
    by (auto simp: abs_fresh fresh_atm forget trm.inject)
next 
  case (Cut d M u M' x' y' c P)
  with assms show ?case
    apply(auto simp: trm.inject)
      apply (force simp add: abs_fresh forget)
     apply (simp add: abs_fresh forget)
    by (smt (verit, ccfv_threshold) abs_fresh(1) better_Cut_substc forget(2) fresh_prod not_Ax1)
next
  case NotL
  then show ?case
    by (auto simp: abs_fresh fresh_atm forget)
next
  case (NotR u M d)
  obtain a' a''::coname 
    where "a' \<sharp> (b,P,M{d:=(y).P},M{b:=(y).Ax y d}{d:=(y).P},u,y)"
      and  "a'' \<sharp> (P,M{d:=(y).Ax y a},M{d:=(y).Ax y a}{a:=(y).P},Ax y a,y,d)"
    by (meson exists_fresh'(2) fs_coname1)
  with NotR show ?case
    by (auto simp: abs_fresh fresh_atm forget fresh_prod fresh_fun_simp_NotR)
next
  case (AndR d1 M d2 M' d3)
  obtain a' a''::coname 
    where "a' \<sharp> (P,M{d3:=(y).P},M{b:=(y).Ax y d3}{d3:=(y).P},
                   M'{d3:=(y).P},M'{b:=(y).Ax y d3}{d3:=(y).P},d1,d2,d3,b,y)"
      and "a'' \<sharp> (P,Ax y a,M{d3:=(y).Ax y a},M{d3:=(y).Ax y a}{a:=(y).P},
                   M'{d3:=(y).Ax y a},M'{d3:=(y).Ax y a}{a:=(y).P},d1,d2,d3,y,b)"
    by (meson exists_fresh'(2) fs_coname1)
  with AndR show ?case
    apply(auto simp: abs_fresh fresh_atm forget trm.inject subst_fresh)
     apply(auto simp only: fresh_prod fresh_fun_simp_AndR)
     apply (force simp:  forget abs_fresh subst_fresh fresh_atm)+
    done
next
  case (AndL1 u M d)
  then show ?case
    by (auto simp: abs_fresh fresh_atm forget trm.inject subst_fresh)
next
  case (AndL2 u M d)
  then show ?case
    by (auto simp: abs_fresh fresh_atm forget trm.inject subst_fresh)
next
  case (OrR1 d M e)
  obtain a' a''::coname 
    where "a' \<sharp> (b,P,M{e:=(y).P},M{b:=(y).Ax y e}{e:=(y).P},d,e)"
      and "a'' \<sharp> (b,P,Ax y a,M{e:=(y).Ax y a},M{e:=(y).Ax y a}{a:=(y).P},d,e)"
    by (meson exists_fresh'(2) fs_coname1)
  with OrR1 show ?case
    by (auto simp: abs_fresh fresh_atm forget fresh_prod fresh_fun_simp_OrR1)
next
  case (OrR2 d M e)
  obtain a' a''::coname 
    where "a' \<sharp> (b,P,M{e:=(y).P},M{b:=(y).Ax y e}{e:=(y).P},d,e)"
      and  "a'' \<sharp> (b,P,Ax y a,M{e:=(y).Ax y a},M{e:=(y).Ax y a}{a:=(y).P},d,e)"
    by (meson exists_fresh'(2) fs_coname1)
  with OrR2 show ?case
    by (auto simp: abs_fresh fresh_atm forget fresh_prod fresh_fun_simp_OrR2)
next
  case (OrL x1 M x2 M' x3)
  then show ?case
    by(auto simp: abs_fresh fresh_atm forget trm.inject subst_fresh)
next
  case ImpL
  then show ?case
    by (auto simp: abs_fresh fresh_atm forget trm.inject subst_fresh)
next
  case (ImpR u e M d)
  obtain a' a''::coname 
    where "a' \<sharp> (b,e,d,P,M{d:=(y).P},M{b:=(y).Ax y d}{d:=(y).P})"
      and  "a'' \<sharp> (e,d,P,Ax y a,M{d:=(y).Ax y a},M{d:=(y).Ax y a}{a:=(y).P})"
    by (meson exists_fresh'(2) fs_coname1)
  with ImpR show ?case
    by (auto simp: abs_fresh fresh_atm forget fresh_prod fresh_fun_simp_ImpR)
qed 

lemma interesting_subst2':
  assumes "a\<noteq>b" "a\<sharp>P" "b\<sharp>P" 
  shows "N{a:=(y).P}{b:=(y).P} = N{b:=(z).Ax z a}{a:=(y).P}"
proof -
  show ?thesis
  proof (cases "z=y")
    case True then show ?thesis using assms by (simp add: interesting_subst2)
  next
    case False 
    then have "N{b:=(z).Ax z a} = N{b:=(y).([(y,z)]\<bullet>Ax z a)}"
      by (metis fresh_atm(1,3) fresh_prod substc_rename2 trm.fresh(1))
    with False assms show ?thesis
      by (simp add: interesting_subst2 calc_atm)
  qed
qed


lemma subst_subst1:
  assumes a: "a\<sharp>(Q,b)" "x\<sharp>(y,P,Q)" "b\<sharp>Q" "y\<sharp>P" 
  shows "M{x:=<a>.P}{b:=(y).Q} = M{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}"
  using a
proof(nominal_induct M avoiding: x a P b y Q rule: trm.strong_induct)
  case (Ax z c)
  then show ?case
    by (auto simp add: abs_fresh fresh_prod fresh_atm subst_fresh trm.inject forget)
next
  case (Cut c M z N)
  then show ?case
    apply (clarsimp simp add: abs_fresh fresh_prod fresh_atm subst_fresh)
    apply (metis forget not_Ax1 not_Ax2)
    done
next
  case (NotR z M c)
  then show ?case
    by (auto simp: forget fresh_prod fresh_atm subst_fresh abs_fresh fresh_fun_simp_NotR)
next
  case (NotL c M z)
  obtain x'::name where "x' \<sharp> (P,M{x:=<a>.P},P{b:=(y).Q},M{b:=(y).Q}{x:=<a>.P{b:=(y).Q}},y,Q)"
    by (meson exists_fresh(1) fs_name1)
  with NotL show ?case  
    apply(auto simp: fresh_prod fresh_atm abs_fresh subst_fresh subst_fresh fresh_fun_simp_NotL)
    by (metis fresh_fun_simp_NotL fresh_prod subst_fresh(5))
next
  case (AndR c1 M c2 N c3)
  then show ?case  
    by (auto simp: forget fresh_prod fresh_atm subst_fresh abs_fresh fresh_fun_simp_AndR)
next
  case (AndL1 z1 M z2)
  obtain x'::name where "x' \<sharp> (P,M{x:=<a>.P},P{b:=(y).Q},z1,y,Q,M{b:=(y).Q}{x:=<a>.P{b:=(y).Q}})"
    by (meson exists_fresh(1) fs_name1)
  with AndL1 show ?case  
    apply(auto simp: fresh_prod fresh_atm abs_fresh subst_fresh fresh_fun_simp_AndL1)
    by (metis fresh_atm(1) fresh_fun_simp_AndL1 fresh_prod subst_fresh(5))
next
  case (AndL2 z1 M z2)
  obtain x'::name where "x' \<sharp> (P,M{x:=<a>.P},P{b:=(y).Q},z1,y,Q,M{b:=(y).Q}{x:=<a>.P{b:=(y).Q}})"
    by (meson exists_fresh(1) fs_name1)
  with AndL2 show ?case  
    apply(auto simp: fresh_prod fresh_atm abs_fresh subst_fresh fresh_fun_simp_AndL2)
    by (metis fresh_atm(1) fresh_fun_simp_AndL2 fresh_prod subst_fresh(5))
next
  case (OrL z1 M z2 N z3)
  obtain x'::name where "x' \<sharp> (P,M{x:=<a>.P},M{b:=(y).Q}{x:=<a>.P{b:=(y).Q}},z2,z3,a,y,Q,
                                     P{b:=(y).Q},N{x:=<a>.P},N{b:=(y).Q}{x:=<a>.P{b:=(y).Q}},z1)"
    by (meson exists_fresh(1) fs_name1)
  with OrL show ?case  
    apply(auto simp: fresh_prod fresh_atm abs_fresh subst_fresh fresh_fun_simp_OrL)
    by (metis (full_types) fresh_atm(1) fresh_fun_simp_OrL fresh_prod subst_fresh(5))
next
  case (OrR1 c1 M c2)
  then show ?case  
    by (auto simp: forget fresh_prod fresh_atm subst_fresh abs_fresh fresh_fun_simp_OrR1)
next
  case (OrR2 c1 M c2)
  then show ?case  
    by (auto simp: forget fresh_prod fresh_atm subst_fresh abs_fresh fresh_fun_simp_OrR2)
next
  case (ImpR z c M d)
  then show ?case  
    by (auto simp: forget fresh_prod fresh_atm subst_fresh abs_fresh fresh_fun_simp_ImpR)
next
  case (ImpL c M z N u)
  obtain z'::name where "z' \<sharp> (P,P{b:=(y).Q},M{u:=<a>.P},N{u:=<a>.P},y,Q,
                        M{b:=(y).Q}{u:=<a>.P{b:=(y).Q}},N{b:=(y).Q}{u:=<a>.P{b:=(y).Q}},z)"
    by (meson exists_fresh(1) fs_name1)
  with ImpL show ?case  
    apply(auto simp: fresh_prod fresh_atm abs_fresh subst_fresh fresh_fun_simp_ImpL)
    by (metis (full_types) fresh_atm(1) fresh_prod subst_fresh(5) fresh_fun_simp_ImpL)
qed

lemma subst_subst2:
  assumes a: "a\<sharp>(b,P,N)" "x\<sharp>(y,P,M)" "b\<sharp>(M,N)" "y\<sharp>P"
  shows "M{a:=(x).N}{y:=<b>.P} = M{y:=<b>.P}{a:=(x).N{y:=<b>.P}}"
  using a
proof(nominal_induct M avoiding: a x N y b P rule: trm.strong_induct)
  case (Ax z c)
  then show ?case
    by (auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget trm.inject)
next
  case (Cut d M' u M'')
  then show ?case
    apply (clarsimp simp add: abs_fresh fresh_prod fresh_atm subst_fresh)
    apply (metis forget not_Ax1 not_Ax2)
    done
next
  case (NotR z M' d) 
  obtain a'::coname where "a' \<sharp> (y,P,N,N{y:=<b>.P},M'{d:=(x).N},M'{y:=<b>.P}{d:=(x).N{y:=<b>.P}})"
    by (meson exists_fresh'(2) fs_coname1)
  with NotR show ?case
    apply(simp add: fresh_atm subst_fresh)
    apply(auto simp only: fresh_prod fresh_fun_simp_NotR; simp add: abs_fresh NotR)
    done
next
  case (NotL d M' z) 
  obtain x'::name where "x' \<sharp> (z,y,P,N,N{y:=<b>.P},M'{y:=<b>.P},M'{y:=<b>.P}{a:=(x).N{y:=<b>.P}})"
    by (meson exists_fresh(1) fs_name1)
  with NotL show ?case  
    apply(simp add: fresh_prod fresh_atm abs_fresh)
    apply(auto simp only: fresh_fun_simp_NotL)
    by (auto simp: subst_fresh abs_fresh fresh_atm forget)
next
  case (AndR d M' e M'' f) 
  obtain a'::coname where "a' \<sharp> (P,b,d,e,N,N{y:=<b>.P},M'{f:=(x).N},M''{f:=(x).N},
                  M'{y:=<b>.P}{f:=(x).N{y:=<b>.P}},M''{y:=<b>.P}{f:=(x).N{y:=<b>.P}})"
    by (meson exists_fresh'(2) fs_coname1)
  with AndR show ?case
    apply(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(P,b,d,e,N,N{y:=<b>.P},M'{f:=(x).N},M''{f:=(x).N},
                  M'{y:=<b>.P}{f:=(x).N{y:=<b>.P}},M''{y:=<b>.P}{f:=(x).N{y:=<b>.P}})")
     apply(erule exE, simp add: fresh_prod)
     apply(erule conjE)+
     apply(simp add: fresh_fun_simp_AndR)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (AndL1 z M' u) 
  obtain x'::name where "x' \<sharp> (P,b,z,u,x,N,M'{y:=<b>.P},M'{y:=<b>.P}{a:=(x).N{y:=<b>.P}})"
    by (meson exists_fresh(1) fs_name1)
  with AndL1 show ?case  
    by (force simp add: fresh_prod fresh_atm fresh_fun_simp_AndL1 subst_fresh abs_fresh forget)
next
  case (AndL2 z M' u) 
  obtain x'::name where "x' \<sharp> (P,b,z,u,x,N,M'{y:=<b>.P},M'{y:=<b>.P}{a:=(x).N{y:=<b>.P}})"
    by (meson exists_fresh(1) fs_name1)
  with AndL2 show ?case  
    by (force simp add: fresh_prod fresh_atm fresh_fun_simp_AndL2 subst_fresh abs_fresh forget) 
next
  case (OrL u M' v M'' w) 
  obtain x'::name where "x' \<sharp> (P,b,u,w,v,N,N{y:=<b>.P},M'{y:=<b>.P},M''{y:=<b>.P},
                  M'{y:=<b>.P}{a:=(x).N{y:=<b>.P}},M''{y:=<b>.P}{a:=(x).N{y:=<b>.P}})"
    by (meson exists_fresh(1) fs_name1)
  with OrL show ?case  
    by (force simp add: fresh_prod fresh_atm fresh_fun_simp_OrL subst_fresh abs_fresh forget)
next
  case (OrR1 e M' f) 
  obtain c'::coname where c': "c' \<sharp> (P,b,e,f,x,N,N{y:=<b>.P},
                                        M'{f:=(x).N},M'{y:=<b>.P}{f:=(x).N{y:=<b>.P}})"
    by (meson exists_fresh(2) fs_coname1)
  with OrR1 show ?case  
    apply (clarsimp simp: fresh_prod fresh_fun_simp_OrR1)
    apply (clarsimp simp: subst_fresh abs_fresh fresh_atm)
    using c' apply (auto simp: fresh_prod fresh_fun_simp_OrR1)
    done
next
  case (OrR2 e M' f) 
  obtain c'::coname where c': "c' \<sharp> (P,b,e,f,x,N,N{y:=<b>.P},
                                        M'{f:=(x).N},M'{y:=<b>.P}{f:=(x).N{y:=<b>.P}})"
    by (meson exists_fresh(2) fs_coname1)
  with OrR2 show ?case  
    apply (clarsimp simp: fresh_prod fresh_fun_simp_OrR2)
    apply (clarsimp simp: subst_fresh abs_fresh fresh_atm)
    using c' apply (auto simp: fresh_prod fresh_fun_simp_OrR2)
    done
next
  case (ImpR x e M' f) 
  obtain c'::coname where c': "c' \<sharp> (P,b,e,f,x,N,N{y:=<b>.P},
                                     M'{f:=(x).N},M'{y:=<b>.P}{f:=(x).N{y:=<b>.P}})"
    by (meson exists_fresh(2) fs_coname1)
  with ImpR show ?case  
    apply (clarsimp simp: fresh_prod fresh_fun_simp_ImpR)
    apply (clarsimp simp: subst_fresh abs_fresh fresh_atm)
    using c' apply (auto simp add: abs_fresh abs_supp fin_supp fresh_prod fresh_fun_simp_ImpR)
    done
next
  case (ImpL e M' v M'' w) 
  obtain z'::name where z': "z' \<sharp> (P,b,e,w,v,N,N{y:=<b>.P},M'{w:=<b>.P},M''{w:=<b>.P},
                  M'{w:=<b>.P}{a:=(x).N{w:=<b>.P}},M''{w:=<b>.P}{a:=(x).N{w:=<b>.P}})"
    by (meson exists_fresh(1) fs_name1)
  with ImpL show ?case  
    by (force simp add: fresh_prod fresh_atm fresh_fun_simp_ImpL subst_fresh abs_fresh forget)
qed

lemma subst_subst3:
  assumes a: "a\<sharp>(P,N,c)" "c\<sharp>(M,N)" "x\<sharp>(y,P,M)" "y\<sharp>(P,x)" "M\<noteq>Ax y a"
  shows "N{x:=<a>.M}{y:=<c>.P} = N{y:=<c>.P}{x:=<a>.(M{y:=<c>.P})}"
  using a
proof(nominal_induct N avoiding: x y a c M P rule: trm.strong_induct)
  case (Ax z c)
  then show ?case
    by(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (Cut d M' u M'')
  then show ?case
    apply(simp add: fresh_atm fresh_prod trm.inject abs_fresh)
    apply(auto)
       apply(auto simp add: fresh_atm trm.inject forget)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply (metis forget(1) not_Ax2)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
     apply(rule sym)
     apply(rule trans)
      apply(rule better_Cut_substn)
       apply(simp add: abs_fresh subst_fresh)
      apply(simp add: fresh_prod subst_fresh fresh_atm)
     apply(simp)
    by (metis forget(1) not_Ax2)
next
  case NotR
  then show ?case
    by(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (NotL d M' u)
  then show ?case
    apply(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
     apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(y,P,M,M{y:=<c>.P},M'{x:=<a>.M},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
      apply(erule exE, simp add: fresh_prod)
      apply(erule conjE)+
      apply(simp add: fresh_fun_simp_NotL)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
     apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(x,y,P,M,M'{y:=<c>.P},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
     apply(erule exE, simp add: fresh_prod)
     apply(erule conjE)+
     apply(simp add: fresh_fun_simp_NotL)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case AndR
  then show ?case
    by(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (AndL1 u M' v)
  then show ?case
    apply(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
     apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(u,y,v,P,M,M{y:=<c>.P},M'{x:=<a>.M},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
      apply(erule exE, simp add: fresh_prod)
      apply(erule conjE)+
      apply(simp add: fresh_fun_simp_AndL1)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
     apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(x,y,u,v,P,M,M'{y:=<c>.P},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
     apply(erule exE, simp add: fresh_prod)
     apply(erule conjE)+
     apply(simp add: fresh_fun_simp_AndL1)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (AndL2 u M' v)
  then show ?case
    apply(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
     apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(u,y,v,P,M,M{y:=<c>.P},M'{x:=<a>.M},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
      apply(erule exE, simp add: fresh_prod)
      apply(erule conjE)+
      apply(simp add: fresh_fun_simp_AndL2)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
     apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(x,y,u,v,P,M,M'{y:=<c>.P},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
     apply(erule exE, simp add: fresh_prod)
     apply(erule conjE)+
     apply(simp add: fresh_fun_simp_AndL2)     
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case OrR1
  then show ?case
    by(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case OrR2
  then show ?case
    by(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (OrL x1 M' x2 M'' x3)
  then show ?case
    apply(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
     apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(y,P,M,M{y:=<c>.P},M'{x:=<a>.M},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}},
                                      x1,x2,x3,M''{x:=<a>.M},M''{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
      apply(erule exE, simp add: fresh_prod)
      apply(erule conjE)+
      apply(simp add: fresh_fun_simp_OrL)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
     apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(x,y,P,M,M'{y:=<c>.P},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}},
                                      x1,x2,x3,M''{y:=<c>.P},M''{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
     apply(erule exE, simp add: fresh_prod)
     apply(erule conjE)+
     apply(simp add: fresh_fun_simp_OrL)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case ImpR
  then show ?case
    by(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (ImpL d M' x1 M'' x2)
  then show ?case
    apply(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
     apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(y,P,M,M{y:=<c>.P},M'{x2:=<a>.M},M'{y:=<c>.P}{x2:=<a>.M{y:=<c>.P}},
                                      x1,x2,M''{x2:=<a>.M},M''{y:=<c>.P}{x2:=<a>.M{y:=<c>.P}})")
      apply(erule exE, simp add: fresh_prod)
      apply(erule conjE)+
      apply(simp add: fresh_fun_simp_ImpL)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
     apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(x,y,P,M,M'{x2:=<c>.P},M'{x2:=<c>.P}{x:=<a>.M{x2:=<c>.P}},
                                      x1,x2,M''{x2:=<c>.P},M''{x2:=<c>.P}{x:=<a>.M{x2:=<c>.P}})")
     apply(erule exE, simp add: fresh_prod)
     apply(erule conjE)+
     apply(simp add: fresh_fun_simp_ImpL)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
qed

lemma subst_subst4:
  assumes a: "x\<sharp>(P,N,y)" "y\<sharp>(M,N)" "a\<sharp>(c,P,M)" "c\<sharp>(P,a)" "M\<noteq>Ax x c"
  shows "N{a:=(x).M}{c:=(y).P} = N{c:=(y).P}{a:=(x).(M{c:=(y).P})}"
  using a
proof(nominal_induct N avoiding: x y a c M P rule: trm.strong_induct)
  case (Cut d M' u M'')
  then show ?case
    apply(simp add: fresh_atm fresh_prod trm.inject abs_fresh)
    apply(auto)
       apply(simp add: fresh_atm)
       apply(simp add: trm.inject)
       apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
      apply (metis forget(2) not_Ax1)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply(rule sym)
    apply(rule trans)
     apply(rule better_Cut_substc)
      apply(simp add: fresh_prod subst_fresh fresh_atm)
     apply(simp add: abs_fresh subst_fresh)
    apply(auto)
    by (metis forget(2) not_Ax1)
next
  case (NotR u M' d)
  then show ?case
    apply(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(fresh_fun_simp)
      apply(simp add: abs_fresh subst_fresh)
      apply(simp add: abs_fresh subst_fresh)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    done
next
  case (AndR d M e M' f)
  then show ?case
    apply(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(fresh_fun_simp)
      apply(simp add: abs_fresh subst_fresh)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    done
next
  case (OrR1 d M' e)
  then show ?case
    apply(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(fresh_fun_simp)
      apply(simp add: abs_fresh subst_fresh)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    done
next
  case (OrR2 d M' e)
  then show ?case
    apply(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(fresh_fun_simp)
      apply(simp add: abs_fresh subst_fresh)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    done
next
  case (ImpR u d M' e)
  then show ?case
    apply(auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(fresh_fun_simp)
      apply(simp add: abs_fresh subst_fresh)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
     apply (force simp add: trm.inject alpha forget fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)+
    done
qed (auto simp: subst_fresh abs_fresh fresh_atm fresh_prod forget)


end
