theory Class
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

nominal_primrec (freshness_context: "(d::coname,z::name,P::trm)")
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


text \<open>Reduction\<close>

lemma fin_not_Cut:
  assumes a: "fin M x"
  shows "\<not>(\<exists>a M' x N'. M = Cut <a>.M' (x).N')"
using a
by (induct) (auto)

lemma fresh_not_fin:
  assumes a: "x\<sharp>M"
  shows "\<not>fin M x"
proof -
  have "fin M x \<Longrightarrow> x\<sharp>M \<Longrightarrow> False" by (induct rule: fin.induct) (auto simp add: abs_fresh fresh_atm)
  with a show "\<not>fin M x" by blast
qed

lemma fresh_not_fic:
  assumes a: "a\<sharp>M"
  shows "\<not>fic M a"
proof -
  have "fic M a \<Longrightarrow> a\<sharp>M \<Longrightarrow> False" by (induct rule: fic.induct) (auto simp add: abs_fresh fresh_atm)
  with a show "\<not>fic M a" by blast
qed

lemma c_redu_subst1:
  assumes a: "M \<longrightarrow>\<^sub>c M'" "c\<sharp>M" "y\<sharp>P"
  shows "M{y:=<c>.P} \<longrightarrow>\<^sub>c M'{y:=<c>.P}"
using a
proof(nominal_induct avoiding: y c P rule: c_redu.strong_induct)
  case (left M a N x)
  then show ?case
    apply -
    apply(simp)
    apply(rule conjI)
    apply(force)
    apply(auto)
    apply(subgoal_tac "M{a:=(x).N}{y:=<c>.P} = M{y:=<c>.P}{a:=(x).(N{y:=<c>.P})}")(*A*)
    apply(simp)
    apply(rule c_redu.intros)
    apply(rule not_fic_subst1)
    apply(simp)
    apply(simp add: subst_fresh)
    apply(simp add: subst_fresh)
    apply(simp add: abs_fresh fresh_atm)
    apply(rule subst_subst2)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp)
    done
next
  case (right N x a M)
  then show ?case
    apply -
    apply(simp)
    apply(rule conjI)
    (* case M = Ax y a *)
    apply(rule impI)
    apply(subgoal_tac "N{x:=<a>.Ax y a}{y:=<c>.P} = N{y:=<c>.P}{x:=<c>.P}")
    apply(simp)
    apply(rule c_redu.right)
    apply(rule not_fin_subst2)
    apply(simp)
    apply(rule subst_fresh)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(rule sym)
    apply(rule interesting_subst1')
    apply(simp add: fresh_atm)
    apply(simp)
    apply(simp)
    (* case M \<noteq> Ax y a*)
    apply(rule impI)
    apply(subgoal_tac "N{x:=<a>.M}{y:=<c>.P} = N{y:=<c>.P}{x:=<a>.(M{y:=<c>.P})}")
    apply(simp)
    apply(rule c_redu.right)
    apply(rule not_fin_subst2)
    apply(simp)
    apply(simp add: subst_fresh)
    apply(simp add: subst_fresh)
    apply(simp add: abs_fresh fresh_atm)
    apply(rule subst_subst3)
    apply(simp_all add: fresh_atm fresh_prod)
    done
qed

lemma c_redu_subst2:
  assumes a: "M \<longrightarrow>\<^sub>c M'" "c\<sharp>P" "y\<sharp>M"
  shows "M{c:=(y).P} \<longrightarrow>\<^sub>c M'{c:=(y).P}"
using a
proof(nominal_induct avoiding: y c P rule: c_redu.strong_induct)
  case (right N x a M)
  then show ?case
    apply -
    apply(simp)
    apply(rule conjI)
    apply(force)
    apply(auto)
    apply(subgoal_tac "N{x:=<a>.M}{c:=(y).P} = N{c:=(y).P}{x:=<a>.(M{c:=(y).P})}")(*A*)
    apply(simp)
    apply(rule c_redu.intros)
    apply(rule not_fin_subst1)
    apply(simp)
    apply(simp add: subst_fresh)
    apply(simp add: subst_fresh)
    apply(simp add: abs_fresh fresh_atm)
    apply(rule subst_subst1)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp)
    done
next
  case (left M a N x)
  then show ?case
    apply -
    apply(simp)
    apply(rule conjI)
    (* case N = Ax x c *)
    apply(rule impI)
    apply(subgoal_tac "M{a:=(x).Ax x c}{c:=(y).P} = M{c:=(y).P}{a:=(y).P}")
    apply(simp)
    apply(rule c_redu.left)
    apply(rule not_fic_subst2)
    apply(simp)
    apply(simp)
    apply(rule subst_fresh)
    apply(simp add: abs_fresh)
    apply(rule sym)
    apply(rule interesting_subst2')
    apply(simp add: fresh_atm)
    apply(simp)
    apply(simp)
    (* case M \<noteq> Ax y a*)
    apply(rule impI)
    apply(subgoal_tac "M{a:=(x).N}{c:=(y).P} = M{c:=(y).P}{a:=(x).(N{c:=(y).P})}")
    apply(simp)
    apply(rule c_redu.left)
    apply(rule not_fic_subst2)
    apply(simp)
    apply(simp add: subst_fresh)
    apply(simp add: subst_fresh)
    apply(simp add: abs_fresh fresh_atm)
    apply(rule subst_subst4)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp)
    done
qed

lemma c_redu_subst1':
  assumes a: "M \<longrightarrow>\<^sub>c M'" 
  shows "M{y:=<c>.P} \<longrightarrow>\<^sub>c M'{y:=<c>.P}"
using a
proof -
  obtain y'::"name"   where fs1: "y'\<sharp>(M,M',P,P,y)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain c'::"coname" where fs2: "c'\<sharp>(M,M',P,P,c)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "M{y:=<c>.P} = ([(y',y)]\<bullet>M){y':=<c'>.([(c',c)]\<bullet>P)}" using fs1 fs2
    apply -
    apply(rule trans)
    apply(rule_tac y="y'" in subst_rename(3))
    apply(simp)
    apply(rule subst_rename(4))
    apply(simp)
    done
  also have "\<dots> \<longrightarrow>\<^sub>c ([(y',y)]\<bullet>M'){y':=<c'>.([(c',c)]\<bullet>P)}" using fs1 fs2
    apply -
    apply(rule c_redu_subst1)
    apply(simp add: c_redu.eqvt a)
    apply(simp_all add: fresh_left calc_atm fresh_prod)
    done
  also have "\<dots> = M'{y:=<c>.P}" using fs1 fs2
    apply -
    apply(rule sym)
    apply(rule trans)
    apply(rule_tac y="y'" in subst_rename(3))
    apply(simp)
    apply(rule subst_rename(4))
    apply(simp)
    done
  finally show ?thesis by simp
qed

lemma c_redu_subst2':
  assumes a: "M \<longrightarrow>\<^sub>c M'" 
  shows "M{c:=(y).P} \<longrightarrow>\<^sub>c M'{c:=(y).P}"
using a
proof -
  obtain y'::"name"   where fs1: "y'\<sharp>(M,M',P,P,y)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain c'::"coname" where fs2: "c'\<sharp>(M,M',P,P,c)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "M{c:=(y).P} = ([(c',c)]\<bullet>M){c':=(y').([(y',y)]\<bullet>P)}" using fs1 fs2
    apply -
    apply(rule trans)
    apply(rule_tac c="c'" in subst_rename(1))
    apply(simp)
    apply(rule subst_rename(2))
    apply(simp)
    done
  also have "\<dots> \<longrightarrow>\<^sub>c ([(c',c)]\<bullet>M'){c':=(y').([(y',y)]\<bullet>P)}" using fs1 fs2
    apply -
    apply(rule c_redu_subst2)
    apply(simp add: c_redu.eqvt a)
    apply(simp_all add: fresh_left calc_atm fresh_prod)
    done
  also have "\<dots> = M'{c:=(y).P}" using fs1 fs2
    apply -
    apply(rule sym)
    apply(rule trans)
    apply(rule_tac c="c'" in subst_rename(1))
    apply(simp)
    apply(rule subst_rename(2))
    apply(simp)
    done

  finally show ?thesis by simp
qed

lemma aux1:
  assumes a: "M = M'" "M' \<longrightarrow>\<^sub>l M''"
  shows "M \<longrightarrow>\<^sub>l M''"
using a by simp
  
lemma aux2:
  assumes a: "M \<longrightarrow>\<^sub>l M'" "M' = M''"
  shows "M \<longrightarrow>\<^sub>l M''"
using a by simp

lemma aux3:
  assumes a: "M = M'" "M' \<longrightarrow>\<^sub>a* M''"
  shows "M \<longrightarrow>\<^sub>a* M''"
using a by simp

lemma aux4:
  assumes a: "M = M'"
  shows "M \<longrightarrow>\<^sub>a* M'"
using a by blast

lemma l_redu_subst1:
  assumes a: "M \<longrightarrow>\<^sub>l M'" 
  shows "M{y:=<c>.P} \<longrightarrow>\<^sub>a* M'{y:=<c>.P}"
using a
proof(nominal_induct M M' avoiding: y c P rule: l_redu.strong_induct)
  case LAxR
  then show ?case
    apply -
    apply(rule aux3)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: fresh_atm)
    apply(auto)
    apply(rule aux4)
    apply(simp add: trm.inject alpha calc_atm fresh_atm)
    apply(rule rtranclp_trans)
    apply(rule a_starI)
    apply(rule al_redu)
    apply(rule l_redu.intros)
    apply(simp add: subst_fresh)
    apply(simp add: fresh_atm)
    apply(rule fic_subst2)
    apply(simp_all)
    apply(rule aux4)
    apply(rule subst_comm')
    apply(simp_all)
    done
next
  case LAxL
  then show ?case
    apply -
    apply(rule aux3)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: trm.inject fresh_atm)
    apply(auto)
    apply(rule aux4)
    apply(rule sym)
    apply(rule fin_substn_nrename)
    apply(simp_all)
    apply(rule a_starI)
    apply(rule al_redu)
    apply(rule aux2)
    apply(rule l_redu.intros)
    apply(simp add: subst_fresh)
    apply(simp add: fresh_atm)
    apply(rule fin_subst1)
    apply(simp_all)
    apply(rule subst_comm')
    apply(simp_all)
    done
next
  case (LNot v M N u a b)
  then show ?case
  proof -
    { assume asm: "N\<noteq>Ax y b"
      have "(Cut <a>.NotR (u).M a (v).NotL <b>.N v){y:=<c>.P} = 
        (Cut <a>.NotR (u).(M{y:=<c>.P}) a (v).NotL <b>.(N{y:=<c>.P}) v)" using LNot
        by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>l (Cut <b>.(N{y:=<c>.P}) (u).(M{y:=<c>.P}))" using LNot
        by (auto intro: l_redu.intros simp add: subst_fresh)
      also have "\<dots> = (Cut <b>.N (u).M){y:=<c>.P}" using LNot asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally have ?thesis by auto
    }
    moreover
    { assume asm: "N=Ax y b"
      have "(Cut <a>.NotR (u).M a (v).NotL <b>.N v){y:=<c>.P} = 
        (Cut <a>.NotR (u).(M{y:=<c>.P}) a (v).NotL <b>.(N{y:=<c>.P}) v)" using LNot
        by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* (Cut <b>.(N{y:=<c>.P}) (u).(M{y:=<c>.P}))" using LNot
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <b>.(Cut <c>.P (y).Ax y b) (u).(M{y:=<c>.P}))" using LNot asm
        by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* (Cut <b>.(P[c\<turnstile>c>b]) (u).(M{y:=<c>.P}))" 
      proof (cases "fic P c")
        case True 
        assume "fic P c"
        then show ?thesis using LNot
          apply -
          apply(rule a_starI)
          apply(rule better_CutL_intro)
          apply(rule al_redu)
          apply(rule better_LAxR_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fic P c" 
        then show ?thesis
          apply -
          apply(rule a_star_CutL)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_left)
          apply(simp)
          apply(simp add: subst_with_ax2)
          done
      qed
      also have "\<dots> = (Cut <b>.N (u).M){y:=<c>.P}" using LNot asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule crename_swap)
        apply(simp)
        done
      finally have "(Cut <a>.NotR (u).M a (v).NotL <b>.N v){y:=<c>.P} \<longrightarrow>\<^sub>a* (Cut <b>.N (u).M){y:=<c>.P}" 
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LAnd1 b a1 M1 a2 M2 N z u)
  then show ?case
  proof -
    { assume asm: "M1\<noteq>Ax y a1"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){y:=<c>.P} = 
        Cut <b>.AndR <a1>.(M1{y:=<c>.P}) <a2>.(M2{y:=<c>.P}) b (z).AndL1 (u).(N{y:=<c>.P}) z" 
        using LAnd1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a1>.(M1{y:=<c>.P}) (u).(N{y:=<c>.P})"
        using LAnd1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a1>.M1 (u).N){y:=<c>.P}" using LAnd1 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){y:=<c>.P} \<longrightarrow>\<^sub>a* (Cut <a1>.M1 (u).N){y:=<c>.P}"
        by simp
    } 
    moreover
    { assume asm: "M1=Ax y a1"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){y:=<c>.P} = 
        Cut <b>.AndR <a1>.(M1{y:=<c>.P}) <a2>.(M2{y:=<c>.P}) b (z).AndL1 (u).(N{y:=<c>.P}) z" 
        using LAnd1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a1>.(M1{y:=<c>.P}) (u).(N{y:=<c>.P})"
        using LAnd1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a1>.(Cut <c>.P (y). Ax y a1) (u).(N{y:=<c>.P})" 
        using LAnd1 asm by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a1>.P[c\<turnstile>c>a1] (u).(N{y:=<c>.P})"
      proof (cases "fic P c")
        case True 
        assume "fic P c"
        then show ?thesis using LAnd1
          apply -
          apply(rule a_starI)
          apply(rule better_CutL_intro)
          apply(rule al_redu)
          apply(rule better_LAxR_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fic P c" 
        then show ?thesis
          apply -
          apply(rule a_star_CutL)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_left)
          apply(simp)
          apply(simp add: subst_with_ax2)
          done
      qed
      also have "\<dots> = (Cut <a1>.M1 (u).N){y:=<c>.P}" using LAnd1 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule crename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){y:=<c>.P} \<longrightarrow>\<^sub>a* (Cut <a1>.M1 (u).N){y:=<c>.P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LAnd2 b a1 M1 a2 M2 N z u)
  then show ?case
  proof -
    { assume asm: "M2\<noteq>Ax y a2"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){y:=<c>.P} = 
        Cut <b>.AndR <a1>.(M1{y:=<c>.P}) <a2>.(M2{y:=<c>.P}) b (z).AndL2 (u).(N{y:=<c>.P}) z" 
        using LAnd2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a2>.(M2{y:=<c>.P}) (u).(N{y:=<c>.P})"
        using LAnd2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a2>.M2 (u).N){y:=<c>.P}" using LAnd2 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){y:=<c>.P} \<longrightarrow>\<^sub>a* (Cut <a2>.M2 (u).N){y:=<c>.P}"
        by simp
    } 
    moreover
    { assume asm: "M2=Ax y a2"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){y:=<c>.P} = 
        Cut <b>.AndR <a1>.(M1{y:=<c>.P}) <a2>.(M2{y:=<c>.P}) b (z).AndL2 (u).(N{y:=<c>.P}) z" 
        using LAnd2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a2>.(M2{y:=<c>.P}) (u).(N{y:=<c>.P})"
        using LAnd2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a2>.(Cut <c>.P (y). Ax y a2) (u).(N{y:=<c>.P})" 
        using LAnd2 asm by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a2>.P[c\<turnstile>c>a2] (u).(N{y:=<c>.P})"
      proof (cases "fic P c")
        case True 
        assume "fic P c"
        then show ?thesis using LAnd2 asm
          apply -
          apply(rule a_starI)
          apply(rule better_CutL_intro)
          apply(rule al_redu)
          apply(rule better_LAxR_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fic P c" 
        then show ?thesis
          apply -
          apply(rule a_star_CutL)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_left)
          apply(simp)
          apply(simp add: subst_with_ax2)
          done
      qed
      also have "\<dots> = (Cut <a2>.M2 (u).N){y:=<c>.P}" using LAnd2 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule crename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){y:=<c>.P} \<longrightarrow>\<^sub>a* (Cut <a2>.M2 (u).N){y:=<c>.P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LOr1 b a M N1 N2 z x1 x2 y c P)
  then show ?case
  proof -
    { assume asm: "M\<noteq>Ax y a"
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} = 
        Cut <b>.OrR1 <a>.(M{y:=<c>.P}) b (z).OrL (x1).(N1{y:=<c>.P}) (x2).(N2{y:=<c>.P}) z" 
        using LOr1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(M{y:=<c>.P}) (x1).(N1{y:=<c>.P})"
        using LOr1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a>.M (x1).N1){y:=<c>.P}" using LOr1 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} \<longrightarrow>\<^sub>a* (Cut <a>.M (x1).N1){y:=<c>.P}"
        by simp
    } 
    moreover
    { assume asm: "M=Ax y a"
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} = 
        Cut <b>.OrR1 <a>.(M{y:=<c>.P}) b (z).OrL (x1).(N1{y:=<c>.P}) (x2).(N2{y:=<c>.P}) z" 
        using LOr1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(M{y:=<c>.P}) (x1).(N1{y:=<c>.P})"
        using LOr1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(Cut <c>.P (y). Ax y a) (x1).(N1{y:=<c>.P})" 
        using LOr1 asm by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.P[c\<turnstile>c>a] (x1).(N1{y:=<c>.P})"
      proof (cases "fic P c")
        case True 
        assume "fic P c"
        then show ?thesis using LOr1
          apply -
          apply(rule a_starI)
          apply(rule better_CutL_intro)
          apply(rule al_redu)
          apply(rule better_LAxR_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fic P c" 
        then show ?thesis
          apply -
          apply(rule a_star_CutL)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_left)
          apply(simp)
          apply(simp add: subst_with_ax2)
          done
      qed
      also have "\<dots> = (Cut <a>.M (x1).N1){y:=<c>.P}" using LOr1 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule crename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} \<longrightarrow>\<^sub>a* (Cut <a>.M (x1).N1){y:=<c>.P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LOr2 b a M N1 N2 z x1 x2 y c P)
  then show ?case
  proof -
    { assume asm: "M\<noteq>Ax y a"
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} = 
        Cut <b>.OrR2 <a>.(M{y:=<c>.P}) b (z).OrL (x1).(N1{y:=<c>.P}) (x2).(N2{y:=<c>.P}) z" 
        using LOr2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(M{y:=<c>.P}) (x2).(N2{y:=<c>.P})"
        using LOr2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a>.M (x2).N2){y:=<c>.P}" using LOr2 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} \<longrightarrow>\<^sub>a* (Cut <a>.M (x2).N2){y:=<c>.P}"
        by simp
    } 
    moreover
    { assume asm: "M=Ax y a"
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} = 
        Cut <b>.OrR2 <a>.(M{y:=<c>.P}) b (z).OrL (x1).(N1{y:=<c>.P}) (x2).(N2{y:=<c>.P}) z" 
        using LOr2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(M{y:=<c>.P}) (x2).(N2{y:=<c>.P})"
        using LOr2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(Cut <c>.P (y). Ax y a) (x2).(N2{y:=<c>.P})" 
        using LOr2 asm by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.P[c\<turnstile>c>a] (x2).(N2{y:=<c>.P})"
      proof (cases "fic P c")
        case True 
        assume "fic P c"
        then show ?thesis using LOr2
          apply -
          apply(rule a_starI)
          apply(rule better_CutL_intro)
          apply(rule al_redu)
          apply(rule better_LAxR_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fic P c" 
        then show ?thesis
          apply -
          apply(rule a_star_CutL)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_left)
          apply(simp)
          apply(simp add: subst_with_ax2)
          done
      qed
      also have "\<dots> = (Cut <a>.M (x2).N2){y:=<c>.P}" using LOr2 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule crename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} \<longrightarrow>\<^sub>a* (Cut <a>.M (x2).N2){y:=<c>.P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LImp z N u Q x M b a d y c P)
  then show ?case
  proof -
    { assume asm: "N\<noteq>Ax y d"
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){y:=<c>.P} = 
        Cut <b>.ImpR (x).<a>.(M{y:=<c>.P}) b (z).ImpL <d>.(N{y:=<c>.P}) (u).(Q{y:=<c>.P}) z" 
        using LImp by (simp add: fresh_prod abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(Cut <d>.(N{y:=<c>.P})  (x).(M{y:=<c>.P})) (u).(Q{y:=<c>.P})"
        using LImp
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a>.(Cut <d>.N  (x).M) (u).Q){y:=<c>.P}" using LImp asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){y:=<c>.P} \<longrightarrow>\<^sub>a* 
                     (Cut <a>.(Cut <d>.N  (x).M) (u).Q){y:=<c>.P}"
        by simp
    } 
    moreover
    { assume asm: "N=Ax y d"
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){y:=<c>.P} = 
        Cut <b>.ImpR (x).<a>.(M{y:=<c>.P}) b (z).ImpL <d>.(N{y:=<c>.P}) (u).(Q{y:=<c>.P}) z" 
        using LImp by (simp add: subst_fresh abs_fresh fresh_atm fresh_prod)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(Cut <d>.(N{y:=<c>.P})  (x).(M{y:=<c>.P})) (u).(Q{y:=<c>.P})"
        using LImp
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(Cut <d>.(Cut <c>.P (y).Ax y d)  (x).(M{y:=<c>.P})) (u).(Q{y:=<c>.P})"
        using LImp asm by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(Cut <d>.(P[c\<turnstile>c>d]) (x).(M{y:=<c>.P})) (u).(Q{y:=<c>.P})"
      proof (cases "fic P c")
        case True 
        assume "fic P c"
        then show ?thesis using LImp
          apply -
          apply(rule a_starI)
          apply(rule better_CutL_intro)
          apply(rule a_Cut_l)
          apply(simp add: subst_fresh abs_fresh)
          apply(simp add: abs_fresh fresh_atm)
          apply(rule al_redu)
          apply(rule better_LAxR_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fic P c" 
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_CutL)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_left)
          apply(simp)
          apply(simp add: subst_with_ax2)
          done
      qed
      also have "\<dots> = (Cut <a>.(Cut <d>.N (x).M) (u).Q){y:=<c>.P}" using LImp asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(simp add: trm.inject)
        apply(simp add: alpha)
        apply(rule sym)
        apply(rule crename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){y:=<c>.P} \<longrightarrow>\<^sub>a* 
               (Cut <a>.(Cut <d>.N (x).M) (u).Q){y:=<c>.P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
qed

lemma l_redu_subst2:
  assumes a: "M \<longrightarrow>\<^sub>l M'" 
  shows "M{c:=(y).P} \<longrightarrow>\<^sub>a* M'{c:=(y).P}"
using a
proof(nominal_induct M M' avoiding: y c P rule: l_redu.strong_induct)
  case LAxR
  then show ?case
    apply -
    apply(rule aux3)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp add: trm.inject fresh_atm)
    apply(auto)
    apply(rule aux4)
    apply(rule sym)
    apply(rule fic_substc_crename)
    apply(simp_all)
    apply(rule a_starI)
    apply(rule al_redu)
    apply(rule aux2)
    apply(rule l_redu.intros)
    apply(simp add: subst_fresh)
    apply(simp add: fresh_atm)
    apply(rule fic_subst1)
    apply(simp_all)
    apply(rule subst_comm')
    apply(simp_all)
    done
next
  case LAxL
  then show ?case
    apply -
    apply(rule aux3)
    apply(rule better_Cut_substc)
    apply(simp)
    apply(simp add: abs_fresh)
    apply(simp add: fresh_atm)
    apply(auto)
    apply(rule aux4)
    apply(simp add: trm.inject alpha calc_atm fresh_atm)
    apply(rule rtranclp_trans)
    apply(rule a_starI)
    apply(rule al_redu)
    apply(rule l_redu.intros)
    apply(simp add: subst_fresh)
    apply(simp add: fresh_atm)
    apply(rule fin_subst2)
    apply(simp_all)
    apply(rule aux4)
    apply(rule subst_comm')
    apply(simp_all)
    done
next
  case (LNot v M N u a b)
  then show ?case
  proof -
    { assume asm: "M\<noteq>Ax u c"
      have "(Cut <a>.NotR (u).M a (v).NotL <b>.N v){c:=(y).P} = 
        (Cut <a>.NotR (u).(M{c:=(y).P}) a (v).NotL <b>.(N{c:=(y).P}) v)" using LNot
        by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>l (Cut <b>.(N{c:=(y).P}) (u).(M{c:=(y).P}))" using LNot
        by (auto intro: l_redu.intros simp add: subst_fresh)
      also have "\<dots> = (Cut <b>.N (u).M){c:=(y).P}" using LNot asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally have ?thesis by auto
    }
    moreover
    { assume asm: "M=Ax u c"
      have "(Cut <a>.NotR (u).M a (v).NotL <b>.N v){c:=(y).P} = 
        (Cut <a>.NotR (u).(M{c:=(y).P}) a (v).NotL <b>.(N{c:=(y).P}) v)" using LNot
        by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* (Cut <b>.(N{c:=(y).P}) (u).(M{c:=(y).P}))" using LNot
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <b>.(N{c:=(y).P}) (u).(Cut <c>.(Ax u c) (y).P))" using LNot asm
        by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* (Cut <b>.(N{c:=(y).P})  (u).(P[y\<turnstile>n>u]))" 
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LNot
          apply -
          apply(rule a_starI)
          apply(rule better_CutR_intro)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis
          apply -
          apply(rule a_star_CutR)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <b>.N (u).M){c:=(y).P}" using LNot asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule nrename_swap)
        apply(simp)
        done
      finally have "(Cut <a>.NotR (u).M a (v).NotL <b>.N v){c:=(y).P} \<longrightarrow>\<^sub>a* (Cut <b>.N (u).M){c:=(y).P}" 
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LAnd1 b a1 M1 a2 M2 N z u)
  then show ?case
  proof -
    { assume asm: "N\<noteq>Ax u c"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){c:=(y).P} = 
        Cut <b>.AndR <a1>.(M1{c:=(y).P}) <a2>.(M2{c:=(y).P}) b (z).AndL1 (u).(N{c:=(y).P}) z" 
        using LAnd1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a1>.(M1{c:=(y).P}) (u).(N{c:=(y).P})"
        using LAnd1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a1>.M1 (u).N){c:=(y).P}" using LAnd1 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){c:=(y).P} \<longrightarrow>\<^sub>a* (Cut <a1>.M1 (u).N){c:=(y).P}"
        by simp
    } 
    moreover
    { assume asm: "N=Ax u c"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){c:=(y).P} = 
        Cut <b>.AndR <a1>.(M1{c:=(y).P}) <a2>.(M2{c:=(y).P}) b (z).AndL1 (u).(N{c:=(y).P}) z" 
        using LAnd1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a1>.(M1{c:=(y).P}) (u).(N{c:=(y).P})"
        using LAnd1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a1>.(M1{c:=(y).P}) (u).(Cut <c>.(Ax u c) (y).P)" 
        using LAnd1 asm by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a1>.(M1{c:=(y).P}) (u).(P[y\<turnstile>n>u])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LAnd1
          apply -
          apply(rule a_starI)
          apply(rule better_CutR_intro)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis
          apply -
          apply(rule a_star_CutR)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a1>.M1 (u).N){c:=(y).P}" using LAnd1 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule nrename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){c:=(y).P} \<longrightarrow>\<^sub>a* (Cut <a1>.M1 (u).N){c:=(y).P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LAnd2 b a1 M1 a2 M2 N z u)
  then show ?case
  proof -
    { assume asm: "N\<noteq>Ax u c"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){c:=(y).P} = 
        Cut <b>.AndR <a1>.(M1{c:=(y).P}) <a2>.(M2{c:=(y).P}) b (z).AndL2 (u).(N{c:=(y).P}) z" 
        using LAnd2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a2>.(M2{c:=(y).P}) (u).(N{c:=(y).P})"
        using LAnd2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a2>.M2 (u).N){c:=(y).P}" using LAnd2 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){c:=(y).P} \<longrightarrow>\<^sub>a* (Cut <a2>.M2 (u).N){c:=(y).P}"
        by simp
    } 
    moreover
    { assume asm: "N=Ax u c"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){c:=(y).P} = 
        Cut <b>.AndR <a1>.(M1{c:=(y).P}) <a2>.(M2{c:=(y).P}) b (z).AndL2 (u).(N{c:=(y).P}) z" 
        using LAnd2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a2>.(M2{c:=(y).P}) (u).(N{c:=(y).P})"
        using LAnd2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a2>.(M2{c:=(y).P}) (u).(Cut <c>.(Ax u c) (y).P)" 
        using LAnd2 asm by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a2>.(M2{c:=(y).P}) (u).(P[y\<turnstile>n>u])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LAnd2
          apply -
          apply(rule a_starI)
          apply(rule better_CutR_intro)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis
          apply -
          apply(rule a_star_CutR)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a2>.M2 (u).N){c:=(y).P}" using LAnd2 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule nrename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){c:=(y).P} \<longrightarrow>\<^sub>a* (Cut <a2>.M2 (u).N){c:=(y).P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LOr1 b a M N1 N2 z x1 x2 y c P)
  then show ?case
  proof -
    { assume asm: "N1\<noteq>Ax x1 c"
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} = 
        Cut <b>.OrR1 <a>.(M{c:=(y).P}) b (z).OrL (x1).(N1{c:=(y).P}) (x2).(N2{c:=(y).P}) z" 
        using LOr1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(M{c:=(y).P}) (x1).(N1{c:=(y).P})"
        using LOr1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a>.M (x1).N1){c:=(y).P}" using LOr1 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} \<longrightarrow>\<^sub>a* (Cut <a>.M (x1).N1){c:=(y).P}"
        by simp
    } 
    moreover
    { assume asm: "N1=Ax x1 c"
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} = 
        Cut <b>.OrR1 <a>.(M{c:=(y).P}) b (z).OrL (x1).(N1{c:=(y).P}) (x2).(N2{c:=(y).P}) z" 
        using LOr1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(M{c:=(y).P}) (x1).(N1{c:=(y).P})"
        using LOr1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(M{c:=(y).P}) (x1).(Cut <c>.(Ax x1 c) (y).P)" 
        using LOr1 asm by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(M{c:=(y).P})   (x1).(P[y\<turnstile>n>x1])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LOr1
          apply -
          apply(rule a_starI)
          apply(rule better_CutR_intro)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis
          apply -
          apply(rule a_star_CutR)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a>.M (x1).N1){c:=(y).P}" using LOr1 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule nrename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} \<longrightarrow>\<^sub>a* (Cut <a>.M (x1).N1){c:=(y).P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LOr2 b a M N1 N2 z x1 x2 y c P)
  then show ?case
  proof -
    { assume asm: "N2\<noteq>Ax x2 c"
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} = 
        Cut <b>.OrR2 <a>.(M{c:=(y).P}) b (z).OrL (x1).(N1{c:=(y).P}) (x2).(N2{c:=(y).P}) z" 
        using LOr2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(M{c:=(y).P}) (x2).(N2{c:=(y).P})"
        using LOr2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a>.M (x2).N2){c:=(y).P}" using LOr2 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} \<longrightarrow>\<^sub>a* (Cut <a>.M (x2).N2){c:=(y).P}"
        by simp
    } 
    moreover
    { assume asm: "N2=Ax x2 c"
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} = 
        Cut <b>.OrR2 <a>.(M{c:=(y).P}) b (z).OrL (x1).(N1{c:=(y).P}) (x2).(N2{c:=(y).P}) z" 
        using LOr2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(M{c:=(y).P}) (x2).(N2{c:=(y).P})"
        using LOr2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(M{c:=(y).P}) (x2).(Cut <c>.(Ax x2 c) (y).P)" 
        using LOr2 asm by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(M{c:=(y).P}) (x2).(P[y\<turnstile>n>x2])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LOr2
          apply -
          apply(rule a_starI)
          apply(rule better_CutR_intro)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis
          apply -
          apply(rule a_star_CutR)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a>.M (x2).N2){c:=(y).P}" using LOr2 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule nrename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} \<longrightarrow>\<^sub>a* (Cut <a>.M (x2).N2){c:=(y).P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LImp z N u Q x M b a d y c P)
  then show ?case
  proof -
    { assume asm: "M\<noteq>Ax x c \<and> Q\<noteq>Ax u c"
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} = 
        Cut <b>.ImpR (x).<a>.(M{c:=(y).P}) b (z).ImpL <d>.(N{c:=(y).P}) (u).(Q{c:=(y).P}) z" 
        using LImp by (simp add: fresh_prod abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(M{c:=(y).P})) (u).(Q{c:=(y).P})"
        using LImp
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a>.(Cut <d>.N  (x).M) (u).Q){c:=(y).P}" using LImp asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} \<longrightarrow>\<^sub>a* 
                     (Cut <a>.(Cut <d>.N  (x).M) (u).Q){c:=(y).P}"
        by simp
    } 
    moreover
    { assume asm: "M=Ax x c \<and> Q\<noteq>Ax u c"
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} = 
        Cut <b>.ImpR (x).<a>.(M{c:=(y).P}) b (z).ImpL <d>.(N{c:=(y).P}) (u).(Q{c:=(y).P}) z" 
        using LImp by (simp add: subst_fresh abs_fresh fresh_atm fresh_prod)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(M{c:=(y).P})) (u).(Q{c:=(y).P})"
        using LImp
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(Cut <c>.Ax x c (y).P)) (u).(Q{c:=(y).P})"
        using LImp asm by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(P[y\<turnstile>n>x])) (u).(Q{c:=(y).P})"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_CutR)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_CutR)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a>.(Cut <d>.N (x).M) (u).Q){c:=(y).P}" using LImp asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(simp add: trm.inject)
        apply(simp add: alpha)
        apply(simp add: nrename_swap)
        done
      finally 
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} \<longrightarrow>\<^sub>a* 
               (Cut <a>.(Cut <d>.N (x).M) (u).Q){c:=(y).P}"
        by simp
    }
     moreover
    { assume asm: "M\<noteq>Ax x c \<and> Q=Ax u c"
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} = 
        Cut <b>.ImpR (x).<a>.(M{c:=(y).P}) b (z).ImpL <d>.(N{c:=(y).P}) (u).(Q{c:=(y).P}) z" 
        using LImp by (simp add: subst_fresh abs_fresh fresh_atm fresh_prod)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(M{c:=(y).P})) (u).(Q{c:=(y).P})"
        using LImp
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(M{c:=(y).P})) (u).(Cut <c>.Ax u c (y).P)"
        using LImp asm by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(M{c:=(y).P})) (u).(P[y\<turnstile>n>u])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutR)
          apply(rule a_starI)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutR)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a>.(Cut <d>.N (x).M) (u).Q){c:=(y).P}" using LImp asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(simp add: nrename_swap)
        done
      finally 
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} \<longrightarrow>\<^sub>a* 
               (Cut <a>.(Cut <d>.N (x).M) (u).Q){c:=(y).P}"
        by simp
    }
     moreover
    { assume asm: "M=Ax x c \<and> Q=Ax u c"
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} = 
        Cut <b>.ImpR (x).<a>.(M{c:=(y).P}) b (z).ImpL <d>.(N{c:=(y).P}) (u).(Q{c:=(y).P}) z" 
        using LImp by (simp add: subst_fresh abs_fresh fresh_atm fresh_prod)
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(M{c:=(y).P})) (u).(Q{c:=(y).P})"
        using LImp
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(Cut <c>.Ax x c (y).P)) (u).(Cut <c>.Ax u c (y).P)"
        using LImp asm by simp
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(Cut <c>.Ax x c (y).P)) (u).(P[y\<turnstile>n>u])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutR)
          apply(rule a_starI)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutR)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> \<longrightarrow>\<^sub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(P[y\<turnstile>n>x])) (u).(P[y\<turnstile>n>u])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_CutR)
          apply(rule a_starI)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_CutR)
          apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a>.(Cut <d>.N (x).M) (u).Q){c:=(y).P}" using LImp asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(rule conjI)
        apply(simp add: alpha fresh_atm trm.inject)
        apply(simp add: nrename_swap)
        apply(simp add: alpha fresh_atm trm.inject)
        apply(simp add: nrename_swap)
        done
      finally 
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} \<longrightarrow>\<^sub>a* 
               (Cut <a>.(Cut <d>.N (x).M) (u).Q){c:=(y).P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
qed

lemma a_redu_subst1:
  assumes a: "M \<longrightarrow>\<^sub>a M'"
  shows "M{y:=<c>.P} \<longrightarrow>\<^sub>a* M'{y:=<c>.P}"
using a
proof(nominal_induct avoiding: y c P rule: a_redu.strong_induct)
  case al_redu
  then show ?case by (simp only: l_redu_subst1)
next
  case ac_redu
  then show ?case
    apply -
    apply(rule a_starI)
    apply(rule a_redu.ac_redu)
    apply(simp only: c_redu_subst1')
    done
next
  case (a_Cut_l a N x M M' y c P)
  then show ?case
    apply(simp add: subst_fresh fresh_a_redu)
    apply(rule conjI)
    apply(rule impI)+
    apply(simp)
    apply(drule ax_do_not_a_reduce)
    apply(simp)
    apply(rule impI)
    apply(rule conjI)
    apply(rule impI)
    apply(simp)
    apply(drule_tac x="y" in meta_spec)
    apply(drule_tac x="c" in meta_spec)
    apply(drule_tac x="P" in meta_spec)
    apply(simp)
    apply(rule rtranclp_trans)
    apply(rule a_star_CutL)
    apply(assumption)
    apply(rule rtranclp_trans)
    apply(rule_tac M'="P[c\<turnstile>c>a]" in a_star_CutL)
    apply(case_tac "fic P c")
    apply(rule a_starI)
    apply(rule al_redu)
    apply(rule better_LAxR_intro)
    apply(simp)
    apply(rule rtranclp_trans)
    apply(rule a_starI)
    apply(rule ac_redu)
    apply(rule better_left)
    apply(simp)
    apply(rule subst_with_ax2)
    apply(rule aux4)
    apply(simp add: trm.inject)
    apply(simp add: alpha fresh_atm)
    apply(simp add: crename_swap)
    apply(rule impI)
    apply(rule a_star_CutL)
    apply(auto)
    done
next
  case (a_Cut_r a N x M M' y c P)
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_CutR)
    apply(auto)[1]
    apply(rule a_star_CutR)
    apply(auto)[1]
    done
next
  case a_NotL
  then show ?case 
    apply(auto)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_NotL)
    apply(auto)[1]
    apply(rule a_star_NotL)
    apply(auto)[1]
    done
next
  case a_NotR
  then show ?case 
    apply(auto)
    apply(rule a_star_NotR)
    apply(auto)[1]
    done
next
  case a_AndR_l
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_AndR)
    apply(auto)
    done
next
  case a_AndR_r
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_AndR)
    apply(auto)
    done
next
  case a_AndL1
  then show ?case 
    apply(auto)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_AndL1)
    apply(auto)[1]
    apply(rule a_star_AndL1)
    apply(auto)[1]
    done
next
  case a_AndL2
  then show ?case 
    apply(auto)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_AndL2)
    apply(auto)[1]
    apply(rule a_star_AndL2)
    apply(auto)[1]
    done
next
  case a_OrR1
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_OrR1)
    apply(auto)
    done
next
  case a_OrR2
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_OrR2)
    apply(auto)
    done
next
  case a_OrL_l
  then show ?case 
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_OrL)
    apply(auto)
    apply(rule a_star_OrL)
    apply(auto)
    done
next
  case a_OrL_r
  then show ?case 
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_OrL)
    apply(auto)
    apply(rule a_star_OrL)
    apply(auto)
    done
next
  case a_ImpR
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_ImpR)
    apply(auto)
    done
next
  case a_ImpL_r
  then show ?case 
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_ImpL)
    apply(auto)
    apply(rule a_star_ImpL)
    apply(auto)
    done
next
  case a_ImpL_l
  then show ?case 
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_ImpL)
    apply(auto)
    apply(rule a_star_ImpL)
    apply(auto)
    done
qed

lemma a_redu_subst2:
  assumes a: "M \<longrightarrow>\<^sub>a M'"
  shows "M{c:=(y).P} \<longrightarrow>\<^sub>a* M'{c:=(y).P}"
using a
proof(nominal_induct avoiding: y c P rule: a_redu.strong_induct)
  case al_redu
  then show ?case by (simp only: l_redu_subst2)
next
  case ac_redu
  then show ?case
    apply -
    apply(rule a_starI)
    apply(rule a_redu.ac_redu)
    apply(simp only: c_redu_subst2')
    done
next
  case (a_Cut_r a N x M M' y c P)
  then show ?case
    apply(simp add: subst_fresh fresh_a_redu)
    apply(rule conjI)
    apply(rule impI)+
    apply(simp)
    apply(drule ax_do_not_a_reduce)
    apply(simp)
    apply(rule impI)
    apply(rule conjI)
    apply(rule impI)
    apply(simp)
    apply(drule_tac x="c" in meta_spec)
    apply(drule_tac x="y" in meta_spec)
    apply(drule_tac x="P" in meta_spec)
    apply(simp)
    apply(rule rtranclp_trans)
    apply(rule a_star_CutR)
    apply(assumption)
    apply(rule rtranclp_trans)
    apply(rule_tac N'="P[y\<turnstile>n>x]" in a_star_CutR)
    apply(case_tac "fin P y")
    apply(rule a_starI)
    apply(rule al_redu)
    apply(rule better_LAxL_intro)
    apply(simp)
    apply(rule rtranclp_trans)
    apply(rule a_starI)
    apply(rule ac_redu)
    apply(rule better_right)
    apply(simp)
    apply(rule subst_with_ax1)
    apply(rule aux4)
    apply(simp add: trm.inject)
    apply(simp add: alpha fresh_atm)
    apply(simp add: nrename_swap)
    apply(rule impI)
    apply(rule a_star_CutR)
    apply(auto)
    done
next
  case (a_Cut_l a N x M M' y c P)
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_CutL)
    apply(auto)[1]
    apply(rule a_star_CutL)
    apply(auto)[1]
    done
next
  case a_NotR
  then show ?case 
    apply(auto)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutL)
    apply(rule a_star_NotR)
    apply(auto)[1]
    apply(rule a_star_NotR)
    apply(auto)[1]
    done
next
  case a_NotL
  then show ?case 
    apply(auto)
    apply(rule a_star_NotL)
    apply(auto)[1]
    done
next
  case a_AndR_l
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutL)
    apply(rule a_star_AndR)
    apply(auto)
    apply(rule a_star_AndR)
    apply(auto)
    done
next
  case a_AndR_r
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutL)
    apply(rule a_star_AndR)
    apply(auto)
    apply(rule a_star_AndR)
    apply(auto)
    done
next
  case a_AndL1
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_AndL1)
    apply(auto)
    done
next
  case a_AndL2
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_AndL2)
    apply(auto)
    done
next
  case a_OrR1
  then show ?case 
    apply(auto)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutL)
    apply(rule a_star_OrR1)
    apply(auto)[1]
    apply(rule a_star_OrR1)
    apply(auto)[1]
    done
next
  case a_OrR2
  then show ?case 
    apply(auto)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutL)
    apply(rule a_star_OrR2)
    apply(auto)[1]
    apply(rule a_star_OrR2)
    apply(auto)[1]
    done
next
  case a_OrL_l
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_OrL)
    apply(auto)
    done
next
  case a_OrL_r
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_OrL)
    apply(auto)
    done
next
  case a_ImpR
  then show ?case 
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutL)
    apply(rule a_star_ImpR)
    apply(auto)
    apply(rule a_star_ImpR)
    apply(auto)
    done
next
  case a_ImpL_l
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_ImpL)
    apply(auto)
    done
next
  case a_ImpL_r
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_ImpL)
    apply(auto)
    done
qed

lemma a_star_subst1:
  assumes a: "M \<longrightarrow>\<^sub>a* M'"
  shows "M{y:=<c>.P} \<longrightarrow>\<^sub>a* M'{y:=<c>.P}"
using a
apply(induct)
apply(blast)
apply(drule_tac y="y" and c="c" and P="P" in a_redu_subst1)
apply(auto)
done

lemma a_star_subst2:
  assumes a: "M \<longrightarrow>\<^sub>a* M'"
  shows "M{c:=(y).P} \<longrightarrow>\<^sub>a* M'{c:=(y).P}"
using a
apply(induct)
apply(blast)
apply(drule_tac y="y" and c="c" and P="P" in a_redu_subst2)
apply(auto)
done

text \<open>Candidates and SN\<close>

text \<open>SNa\<close>

inductive 
  SNa :: "trm \<Rightarrow> bool"
where
  SNaI: "(\<And>M'. M \<longrightarrow>\<^sub>a M' \<Longrightarrow> SNa M') \<Longrightarrow> SNa M"

lemma SNa_induct[consumes 1]:
  assumes major: "SNa M"
  assumes hyp: "\<And>M'. SNa M' \<Longrightarrow> (\<forall>M''. M'\<longrightarrow>\<^sub>a M'' \<longrightarrow> P M'' \<Longrightarrow> P M')"
  shows "P M"
  apply (rule major[THEN SNa.induct])
  apply (rule hyp)
  apply (rule SNaI)
  apply (blast)+
  done


lemma double_SNa_aux:
  assumes a_SNa: "SNa a"
  and b_SNa: "SNa b"
  and hyp: "\<And>x z.
    (\<And>y. x\<longrightarrow>\<^sub>a y \<Longrightarrow> SNa y) \<Longrightarrow>
    (\<And>y. x\<longrightarrow>\<^sub>a y \<Longrightarrow> P y z) \<Longrightarrow>
    (\<And>u. z\<longrightarrow>\<^sub>a u \<Longrightarrow> SNa u) \<Longrightarrow>
    (\<And>u. z\<longrightarrow>\<^sub>a u \<Longrightarrow> P x u) \<Longrightarrow> P x z"
  shows "P a b"
proof -
  from a_SNa
  have r: "\<And>b. SNa b \<Longrightarrow> P a b"
  proof (induct a rule: SNa.induct)
    case (SNaI x)
    note SNa' = this
    have "SNa b" by fact
    thus ?case
    proof (induct b rule: SNa.induct)
      case (SNaI y)
      show ?case
        apply (rule hyp)
        apply (erule SNa')
        apply (erule SNa')
        apply (rule SNa.SNaI)
        apply (erule SNaI)+
        done
    qed
  qed
  from b_SNa show ?thesis by (rule r)
qed

lemma double_SNa:
  "\<lbrakk>SNa a; SNa b; \<forall>x z. ((\<forall>y. x\<longrightarrow>\<^sub>ay \<longrightarrow> P y z) \<and> (\<forall>u. z\<longrightarrow>\<^sub>a u \<longrightarrow> P x u)) \<longrightarrow> P x z\<rbrakk> \<Longrightarrow> P a b"
apply(rule_tac double_SNa_aux)
apply(assumption)+
apply(blast)
done

lemma a_preserves_SNa:
  assumes a: "SNa M" "M\<longrightarrow>\<^sub>a M'"
  shows "SNa M'"
using a 
by (erule_tac SNa.cases) (simp)

lemma a_star_preserves_SNa:
  assumes a: "SNa M" and b: "M\<longrightarrow>\<^sub>a* M'"
  shows "SNa M'"
using b a
by (induct) (auto simp add: a_preserves_SNa)

lemma Ax_in_SNa:
  shows "SNa (Ax x a)"
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
done

lemma NotL_in_SNa:
  assumes a: "SNa M"
  shows "SNa (NotL <a>.M x)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha)
apply(rotate_tac 1)
apply(drule_tac x="[(a,aa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(subgoal_tac "NotL <a>.([(a,aa)]\<bullet>M'a) x = NotL <aa>.M'a x")
apply(simp)
apply(simp add: trm.inject alpha fresh_a_redu)
done

lemma NotR_in_SNa:
  assumes a: "SNa M"
  shows "SNa (NotR (x).M a)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha)
apply(rotate_tac 1)
apply(drule_tac x="[(x,xa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="NotR (x).([(x,xa)]\<bullet>M'a) a" in subst)
apply(simp add: trm.inject alpha fresh_a_redu)
apply(simp)
done

lemma AndL1_in_SNa:
  assumes a: "SNa M"
  shows "SNa (AndL1 (x).M y)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha)
apply(rotate_tac 1)
apply(drule_tac x="[(x,xa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="AndL1 x.([(x,xa)]\<bullet>M'a) y" in subst)
apply(simp add: trm.inject alpha fresh_a_redu)
apply(simp)
done

lemma AndL2_in_SNa:
  assumes a: "SNa M"
  shows "SNa (AndL2 (x).M y)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha)
apply(rotate_tac 1)
apply(drule_tac x="[(x,xa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="AndL2 x.([(x,xa)]\<bullet>M'a) y" in subst)
apply(simp add: trm.inject alpha fresh_a_redu)
apply(simp)
done

lemma OrR1_in_SNa:
  assumes a: "SNa M"
  shows "SNa (OrR1 <a>.M b)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha)
apply(rotate_tac 1)
apply(drule_tac x="[(a,aa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="OrR1 <a>.([(a,aa)]\<bullet>M'a) b" in subst)
apply(simp add: trm.inject alpha fresh_a_redu)
apply(simp)
done

lemma OrR2_in_SNa:
  assumes a: "SNa M"
  shows "SNa (OrR2 <a>.M b)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha)
apply(rotate_tac 1)
apply(drule_tac x="[(a,aa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="OrR2 <a>.([(a,aa)]\<bullet>M'a) b" in subst)
apply(simp add: trm.inject alpha fresh_a_redu)
apply(simp)
done

lemma ImpR_in_SNa:
  assumes a: "SNa M"
  shows "SNa (ImpR (x).<a>.M b)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha abs_fresh abs_perm calc_atm)
apply(rotate_tac 1)
apply(drule_tac x="[(a,aa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="ImpR (x).<a>.([(a,aa)]\<bullet>M'a) b" in subst)
apply(simp add: trm.inject alpha fresh_a_redu)
apply(simp)
apply(rotate_tac 1)
apply(drule_tac x="[(x,xa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="ImpR (x).<a>.([(x,xa)]\<bullet>M'a) b" in subst)
apply(simp add: trm.inject alpha fresh_a_redu abs_fresh abs_perm calc_atm)
apply(simp)
apply(rotate_tac 1)
apply(drule_tac x="[(a,aa)]\<bullet>[(x,xa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="ImpR (x).<a>.([(a,aa)]\<bullet>[(x,xa)]\<bullet>M'a) b" in subst)
apply(simp add: trm.inject alpha fresh_a_redu abs_fresh abs_perm calc_atm)
apply(simp add: fresh_left calc_atm fresh_a_redu)
apply(simp)
done

lemma AndR_in_SNa:
  assumes a: "SNa M" "SNa N"
  shows "SNa (AndR <a>.M <b>.N c)"
apply(rule_tac a="M" and b="N" in double_SNa)
apply(rule a)+
apply(auto)
apply(rule SNaI)
apply(drule a_redu_AndR_elim)
apply(auto)
done

lemma OrL_in_SNa:
  assumes a: "SNa M" "SNa N"
  shows "SNa (OrL (x).M (y).N z)"
apply(rule_tac a="M" and b="N" in double_SNa)
apply(rule a)+
apply(auto)
apply(rule SNaI)
apply(drule a_redu_OrL_elim)
apply(auto)
done

lemma ImpL_in_SNa:
  assumes a: "SNa M" "SNa N"
  shows "SNa (ImpL <a>.M (y).N z)"
apply(rule_tac a="M" and b="N" in double_SNa)
apply(rule a)+
apply(auto)
apply(rule SNaI)
apply(drule a_redu_ImpL_elim)
apply(auto)
done

lemma SNa_eqvt:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "SNa M \<Longrightarrow> SNa (pi1\<bullet>M)"
  and   "SNa M \<Longrightarrow> SNa (pi2\<bullet>M)"
apply -
apply(induct rule: SNa.induct)
apply(rule SNaI)
apply(drule_tac pi="(rev pi1)" in a_redu.eqvt(1))
apply(rotate_tac 1)
apply(drule_tac x="(rev pi1)\<bullet>M'" in meta_spec)
apply(perm_simp)
apply(induct rule: SNa.induct)
apply(rule SNaI)
apply(drule_tac pi="(rev pi2)" in a_redu.eqvt(2))
apply(rotate_tac 1)
apply(drule_tac x="(rev pi2)\<bullet>M'" in meta_spec)
apply(perm_simp)
done

text \<open>set operators\<close>

definition AXIOMSn :: "ty \<Rightarrow> ntrm set" where
  "AXIOMSn B \<equiv> { (x):(Ax y b) | x y b. True }"

definition AXIOMSc::"ty \<Rightarrow> ctrm set" where
  "AXIOMSc B \<equiv> { <a>:(Ax y b) | a y b. True }"

definition BINDINGn::"ty \<Rightarrow> ctrm set \<Rightarrow> ntrm set" where
  "BINDINGn B X \<equiv> { (x):M | x M. \<forall>a P. <a>:P\<in>X \<longrightarrow> SNa (M{x:=<a>.P})}"

definition BINDINGc::"ty \<Rightarrow> ntrm set \<Rightarrow> ctrm set" where
  "BINDINGc B X \<equiv> { <a>:M | a M. \<forall>x P. (x):P\<in>X \<longrightarrow> SNa (M{a:=(x).P})}"

lemma BINDINGn_decreasing:
  shows "X\<subseteq>Y \<Longrightarrow> BINDINGn B Y \<subseteq> BINDINGn B X"
by (simp add: BINDINGn_def) (blast) 

lemma BINDINGc_decreasing:
  shows "X\<subseteq>Y \<Longrightarrow> BINDINGc B Y \<subseteq> BINDINGc B X"
by (simp add: BINDINGc_def) (blast) 
  
nominal_primrec
  NOTRIGHT :: "ty \<Rightarrow> ntrm set \<Rightarrow> ctrm set"
where
 "NOTRIGHT (NOT B) X = { <a>:NotR (x).M a | a x M. fic (NotR (x).M a) a \<and> (x):M \<in> X }"
apply(rule TrueI)+
done

lemma NOTRIGHT_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(NOTRIGHT (NOT B) X)) = NOTRIGHT (NOT B) (pi\<bullet>X)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(1))
apply(simp)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>(<a>:NotR (xa).M a)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps)
done

lemma NOTRIGHT_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(NOTRIGHT (NOT B) X)) = NOTRIGHT (NOT B) (pi\<bullet>X)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(2))
apply(simp)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="<((rev pi)\<bullet>a)>:NotR ((rev pi)\<bullet>xa).((rev pi)\<bullet>M) ((rev pi)\<bullet>a)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps)
done
  
nominal_primrec
  NOTLEFT :: "ty \<Rightarrow> ctrm set \<Rightarrow> ntrm set"
where
 "NOTLEFT (NOT B) X = { (x):NotL <a>.M x | a x M. fin (NotL <a>.M x) x \<and> <a>:M \<in> X }"
apply(rule TrueI)+
done

lemma NOTLEFT_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(NOTLEFT (NOT B) X)) = NOTLEFT (NOT B) (pi\<bullet>X)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(1))
apply(simp)
apply(rule_tac x="<a>:M" in exI)
apply(simp)
apply(rule_tac x="(((rev pi)\<bullet>xa)):NotL <((rev pi)\<bullet>a)>.((rev pi)\<bullet>M) ((rev pi)\<bullet>xa)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps)
done

lemma NOTLEFT_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(NOTLEFT (NOT B) X)) = NOTLEFT (NOT B) (pi\<bullet>X)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(2))
apply(simp)
apply(rule_tac x="<a>:M" in exI)
apply(simp)
apply(rule_tac x="(((rev pi)\<bullet>xa)):NotL <((rev pi)\<bullet>a)>.((rev pi)\<bullet>M) ((rev pi)\<bullet>xa)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps)
done
  
nominal_primrec
  ANDRIGHT :: "ty \<Rightarrow> ctrm set \<Rightarrow> ctrm set \<Rightarrow> ctrm set"
where
 "ANDRIGHT (B AND C) X Y = 
            { <c>:AndR <a>.M <b>.N c | c a b M N. fic (AndR <a>.M <b>.N c) c \<and> <a>:M \<in> X \<and> <b>:N \<in> Y }"
apply(rule TrueI)+
done

lemma ANDRIGHT_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(ANDRIGHT (A AND B) X Y)) = ANDRIGHT (A AND B) (pi\<bullet>X) (pi\<bullet>Y)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>c" in exI)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(rule_tac x="pi\<bullet>N" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(1))
apply(simp)
apply(rule conjI)
apply(rule_tac x="<a>:M" in exI)
apply(simp)
apply(rule_tac x="<b>:N" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>(<c>:AndR <a>.M <b>.N c)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>c" in exI)
apply(rule_tac x="(rev pi)\<bullet>a" in exI)
apply(rule_tac x="(rev pi)\<bullet>b" in exI)
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(rule_tac x="(rev pi)\<bullet>N" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps)
done

lemma ANDRIGHT_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(ANDRIGHT (A AND B) X Y)) = ANDRIGHT (A AND B) (pi\<bullet>X) (pi\<bullet>Y)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>c" in exI)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(rule_tac x="pi\<bullet>N" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(2))
apply(simp)
apply(rule conjI)
apply(rule_tac x="<a>:M" in exI)
apply(simp)
apply(rule_tac x="<b>:N" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>(<c>:AndR <a>.M <b>.N c)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>c" in exI)
apply(rule_tac x="(rev pi)\<bullet>a" in exI)
apply(rule_tac x="(rev pi)\<bullet>b" in exI)
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(rule_tac x="(rev pi)\<bullet>N" in exI)
apply(simp)
apply(drule_tac pi="rev pi" in fic.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp)
done

nominal_primrec
  ANDLEFT1 :: "ty \<Rightarrow> ntrm set \<Rightarrow> ntrm set"
where
 "ANDLEFT1 (B AND C) X = { (y):AndL1 (x).M y | x y M. fin (AndL1 (x).M y) y \<and> (x):M \<in> X }"
apply(rule TrueI)+
done

lemma ANDLEFT1_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(ANDLEFT1 (A AND B) X)) = ANDLEFT1 (A AND B) (pi\<bullet>X)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>y" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(1))
apply(simp)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((y):AndL1 (xa).M y)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>y" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp)
apply(drule_tac pi="rev pi" in fin.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp)
done

lemma ANDLEFT1_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(ANDLEFT1 (A AND B) X)) = ANDLEFT1 (A AND B) (pi\<bullet>X)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>y" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(2))
apply(simp)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((y):AndL1 (xa).M y)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>y" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps)
done

nominal_primrec
  ANDLEFT2 :: "ty \<Rightarrow> ntrm set \<Rightarrow> ntrm set"
where
 "ANDLEFT2 (B AND C) X = { (y):AndL2 (x).M y | x y M. fin (AndL2 (x).M y) y \<and> (x):M \<in> X }"
apply(rule TrueI)+
done

lemma ANDLEFT2_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(ANDLEFT2 (A AND B) X)) = ANDLEFT2 (A AND B) (pi\<bullet>X)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>y" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(1))
apply(simp)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((y):AndL2 (xa).M y)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>y" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp)
apply(drule_tac pi="rev pi" in fin.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp)
done

lemma ANDLEFT2_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(ANDLEFT2 (A AND B) X)) = ANDLEFT2 (A AND B) (pi\<bullet>X)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>y" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(2))
apply(simp)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((y):AndL2 (xa).M y)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>y" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps)
done

nominal_primrec
  ORLEFT :: "ty \<Rightarrow> ntrm set \<Rightarrow> ntrm set \<Rightarrow> ntrm set"
where
 "ORLEFT (B OR C) X Y = 
            { (z):OrL (x).M (y).N z | x y z M N. fin (OrL (x).M (y).N z) z \<and> (x):M \<in> X \<and> (y):N \<in> Y }"
apply(rule TrueI)+
done

lemma ORLEFT_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(ORLEFT (A OR B) X Y)) = ORLEFT (A OR B) (pi\<bullet>X) (pi\<bullet>Y)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>xb" in exI)
apply(rule_tac x="pi\<bullet>y" in exI)
apply(rule_tac x="pi\<bullet>z" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(rule_tac x="pi\<bullet>N" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(1))
apply(simp)
apply(rule conjI)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(y):N" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((z):OrL (xa).M (y).N z)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI)
apply(rule_tac x="(rev pi)\<bullet>y" in exI)
apply(rule_tac x="(rev pi)\<bullet>z" in exI)
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(rule_tac x="(rev pi)\<bullet>N" in exI)
apply(simp)
apply(drule_tac pi="rev pi" in fin.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp)
done

lemma ORLEFT_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(ORLEFT (A OR B) X Y)) = ORLEFT (A OR B) (pi\<bullet>X) (pi\<bullet>Y)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>xb" in exI)
apply(rule_tac x="pi\<bullet>y" in exI)
apply(rule_tac x="pi\<bullet>z" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(rule_tac x="pi\<bullet>N" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(2))
apply(simp)
apply(rule conjI)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(y):N" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((z):OrL (xa).M (y).N z)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI)
apply(rule_tac x="(rev pi)\<bullet>y" in exI)
apply(rule_tac x="(rev pi)\<bullet>z" in exI)
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(rule_tac x="(rev pi)\<bullet>N" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps)
done

nominal_primrec
  ORRIGHT1 :: "ty \<Rightarrow> ctrm set \<Rightarrow> ctrm set"
where
 "ORRIGHT1 (B OR C) X = { <b>:OrR1 <a>.M b | a b M. fic (OrR1 <a>.M b) b \<and> <a>:M \<in> X }"
apply(rule TrueI)+
done

lemma ORRIGHT1_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(ORRIGHT1 (A OR B) X)) = ORRIGHT1 (A OR B) (pi\<bullet>X)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>b" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(1))
apply(simp)
apply(rule_tac x="<a>:M" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>(<b>:OrR1 <a>.M b)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>b" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps)
done

lemma ORRIGHT1_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(ORRIGHT1 (A OR B) X)) = ORRIGHT1 (A OR B) (pi\<bullet>X)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>b" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(2))
apply(simp)
apply(rule_tac x="<a>:M" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>(<b>:OrR1 <a>.M b)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>b" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp)
apply(drule_tac pi="rev pi" in fic.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp)
done

nominal_primrec
  ORRIGHT2 :: "ty \<Rightarrow> ctrm set \<Rightarrow> ctrm set"
where
 "ORRIGHT2 (B OR C) X = { <b>:OrR2 <a>.M b | a b M. fic (OrR2 <a>.M b) b \<and> <a>:M \<in> X }"
apply(rule TrueI)+
done

lemma ORRIGHT2_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(ORRIGHT2 (A OR B) X)) = ORRIGHT2 (A OR B) (pi\<bullet>X)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>b" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(1))
apply(simp)
apply(rule_tac x="<a>:M" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>(<b>:OrR2 <a>.M b)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>b" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps)
done

lemma ORRIGHT2_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(ORRIGHT2 (A OR B) X)) = ORRIGHT2 (A OR B) (pi\<bullet>X)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>b" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(2))
apply(simp)
apply(rule_tac x="<a>:M" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>(<b>:OrR2 <a>.M b)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>b" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp)
apply(drule_tac pi="rev pi" in fic.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp)
done

nominal_primrec
  IMPRIGHT :: "ty \<Rightarrow> ntrm set \<Rightarrow> ctrm set \<Rightarrow> ntrm set \<Rightarrow> ctrm set \<Rightarrow> ctrm set"
where
 "IMPRIGHT (B IMP C) X Y Z U= 
        { <b>:ImpR (x).<a>.M b | x a b M. fic (ImpR (x).<a>.M b) b 
                                        \<and> (\<forall>z P. x\<sharp>(z,P) \<and> (z):P \<in> Z \<longrightarrow> (x):(M{a:=(z).P}) \<in> X)
                                        \<and> (\<forall>c Q. a\<sharp>(c,Q) \<and> <c>:Q \<in> U \<longrightarrow> <a>:(M{x:=<c>.Q}) \<in> Y)}"
apply(rule TrueI)+
done

lemma IMPRIGHT_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(IMPRIGHT (A IMP B) X Y Z U)) = IMPRIGHT (A IMP B) (pi\<bullet>X) (pi\<bullet>Y) (pi\<bullet>Z) (pi\<bullet>U)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>xb" in exI)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(1))
apply(simp)
apply(rule conjI)
apply(auto)[1]
apply(rule_tac x="(xb):(M{a:=((rev pi)\<bullet>z).((rev pi)\<bullet>P)})" in exI)
apply(perm_simp add: csubst_eqvt)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp)
apply(simp add: fresh_right)
apply(auto)[1]
apply(rule_tac x="<a>:(M{xb:=<((rev pi)\<bullet>c)>.((rev pi)\<bullet>Q)})" in exI)
apply(perm_simp add: nsubst_eqvt)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps fresh_left)
apply(rule_tac x="(rev pi)\<bullet>(<b>:ImpR xa.<a>.M b)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI)
apply(rule_tac x="(rev pi)\<bullet>a" in exI)
apply(rule_tac x="(rev pi)\<bullet>b" in exI)
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(1))
apply(simp add: swap_simps)
apply(rule conjI)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>z" in spec)
apply(drule_tac x="pi\<bullet>P" in spec)
apply(drule mp)
apply(simp add: fresh_right)
apply(rule_tac x="(z):P" in exI)
apply(simp)
apply(auto)[1]
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: csubst_eqvt fresh_right)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>c" in spec)
apply(drule_tac x="pi\<bullet>Q" in spec)
apply(drule mp)
apply(simp add: swap_simps fresh_left)
apply(rule_tac x="<c>:Q" in exI)
apply(simp add: swap_simps)
apply(auto)[1]
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: nsubst_eqvt)
done

lemma IMPRIGHT_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(IMPRIGHT (A IMP B) X Y Z U)) = IMPRIGHT (A IMP B) (pi\<bullet>X) (pi\<bullet>Y) (pi\<bullet>Z) (pi\<bullet>U)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>xb" in exI)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(2))
apply(simp)
apply(rule conjI)
apply(auto)[1]
apply(rule_tac x="(xb):(M{a:=((rev pi)\<bullet>z).((rev pi)\<bullet>P)})" in exI)
apply(perm_simp add: csubst_eqvt)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps fresh_left)
apply(auto)[1]
apply(rule_tac x="<a>:(M{xb:=<((rev pi)\<bullet>c)>.((rev pi)\<bullet>Q)})" in exI)
apply(perm_simp add: nsubst_eqvt)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: fresh_right)
apply(rule_tac x="(rev pi)\<bullet>(<b>:ImpR xa.<a>.M b)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI)
apply(rule_tac x="(rev pi)\<bullet>a" in exI)
apply(rule_tac x="(rev pi)\<bullet>b" in exI)
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(2))
apply(simp add: swap_simps)
apply(rule conjI)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>z" in spec)
apply(drule_tac x="pi\<bullet>P" in spec)
apply(simp add: swap_simps fresh_left)
apply(drule mp)
apply(rule_tac x="(z):P" in exI)
apply(simp add: swap_simps)
apply(auto)[1]
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: csubst_eqvt fresh_right)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>c" in spec)
apply(drule_tac x="pi\<bullet>Q" in spec)
apply(simp add: fresh_right)
apply(drule mp)
apply(rule_tac x="<c>:Q" in exI)
apply(simp)
apply(auto)[1]
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: nsubst_eqvt fresh_right)
done

nominal_primrec
  IMPLEFT :: "ty \<Rightarrow> ctrm set \<Rightarrow> ntrm set \<Rightarrow> ntrm set"
where
 "IMPLEFT (B IMP C) X Y = 
        { (y):ImpL <a>.M (x).N y | x a y M N. fin (ImpL <a>.M (x).N y) y \<and> <a>:M \<in> X \<and> (x):N \<in> Y }"
apply(rule TrueI)+
done

lemma IMPLEFT_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(IMPLEFT (A IMP B) X Y)) = IMPLEFT (A IMP B) (pi\<bullet>X) (pi\<bullet>Y)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>y" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI) 
apply(rule_tac x="pi\<bullet>N" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(1))
apply(simp)
apply(rule conjI)
apply(rule_tac x="<a>:M" in exI)
apply(simp)
apply(rule_tac x="(xb):N" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((y):ImpL <a>.M (xa).N y)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>y" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(rule_tac x="(rev pi)\<bullet>N" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps)
done

lemma IMPLEFT_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(IMPLEFT (A IMP B) X Y)) = IMPLEFT (A IMP B) (pi\<bullet>X) (pi\<bullet>Y)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>y" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI) 
apply(rule_tac x="pi\<bullet>N" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(2))
apply(simp)
apply(rule conjI)
apply(rule_tac x="<a>:M" in exI)
apply(simp)
apply(rule_tac x="(xb):N" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((y):ImpL <a>.M (xa).N y)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>y" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(rule_tac x="(rev pi)\<bullet>N" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps)
done

lemma sum_cases:
 shows "(\<exists>y. x=Inl y) \<or> (\<exists>y. x=Inr y)"
apply(rule_tac s="x" in sumE)
apply(auto)
done

function
  NEGc::"ty \<Rightarrow> ntrm set \<Rightarrow> ctrm set"
and
  NEGn::"ty \<Rightarrow> ctrm set \<Rightarrow> ntrm set"
where
  "NEGc (PR A)    X = AXIOMSc (PR A) \<union> BINDINGc (PR A) X"  
| "NEGc (NOT C)   X = AXIOMSc (NOT C) \<union> BINDINGc (NOT C) X 
                         \<union> NOTRIGHT (NOT C) (lfp (NEGn C \<circ> NEGc C))"  
| "NEGc (C AND D) X = AXIOMSc (C AND D) \<union> BINDINGc (C AND D) X 
                     \<union> ANDRIGHT (C AND D) (NEGc C (lfp (NEGn C \<circ> NEGc C))) (NEGc D (lfp (NEGn D \<circ> NEGc D)))"
| "NEGc (C OR D)  X = AXIOMSc (C OR D) \<union> BINDINGc (C OR D) X  
                         \<union> ORRIGHT1 (C OR D) (NEGc C (lfp (NEGn C \<circ> NEGc C))) 
                         \<union> ORRIGHT2 (C OR D) (NEGc D (lfp (NEGn D \<circ> NEGc D)))"
| "NEGc (C IMP D) X = AXIOMSc (C IMP D) \<union> BINDINGc (C IMP D) X 
    \<union> IMPRIGHT (C IMP D) (lfp (NEGn C \<circ> NEGc C)) (NEGc D (lfp (NEGn D \<circ> NEGc D))) 
                          (lfp (NEGn D \<circ> NEGc D)) (NEGc C (lfp (NEGn C \<circ> NEGc C)))"
| "NEGn (PR A)    X = AXIOMSn (PR A) \<union> BINDINGn (PR A) X"   
| "NEGn (NOT C)   X = AXIOMSn (NOT C) \<union> BINDINGn (NOT C) X 
                         \<union> NOTLEFT (NOT C) (NEGc C (lfp (NEGn C \<circ> NEGc C)))"  
| "NEGn (C AND D) X = AXIOMSn (C AND D) \<union> BINDINGn (C AND D) X 
                         \<union> ANDLEFT1 (C AND D) (lfp (NEGn C \<circ> NEGc C)) 
                         \<union> ANDLEFT2 (C AND D) (lfp (NEGn D \<circ> NEGc D))"
| "NEGn (C OR D)  X = AXIOMSn (C OR D) \<union> BINDINGn (C OR D) X 
                         \<union> ORLEFT (C OR D) (lfp (NEGn C \<circ> NEGc C)) (lfp (NEGn D \<circ> NEGc D))"
| "NEGn (C IMP D) X = AXIOMSn (C IMP D) \<union> BINDINGn (C IMP D) X 
                         \<union> IMPLEFT (C IMP D) (NEGc C (lfp (NEGn C \<circ> NEGc C))) (lfp (NEGn D \<circ> NEGc D))"
using ty_cases sum_cases 
apply(auto simp add: ty.inject)
apply(drule_tac x="x" in meta_spec)
apply(fastforce simp add: ty.inject)
done

termination
apply(relation "measure (case_sum (size\<circ>fst) (size\<circ>fst))")
apply(simp_all)
done

text \<open>Candidates\<close>

lemma test1:
  shows "x\<in>(X\<union>Y) = (x\<in>X \<or> x\<in>Y)"
by blast

lemma test2:
  shows "x\<in>(X\<inter>Y) = (x\<in>X \<and> x\<in>Y)"
by blast

lemma big_inter_eqvt:
  fixes pi1::"name prm"
  and   X::"('a::pt_name) set set"
  and   pi2::"coname prm"
  and   Y::"('b::pt_coname) set set"
  shows "(pi1\<bullet>(\<Inter>X)) = \<Inter>(pi1\<bullet>X)"
  and   "(pi2\<bullet>(\<Inter>Y)) = \<Inter>(pi2\<bullet>Y)"
apply(auto simp add: perm_set_def)
apply(rule_tac x="(rev pi1)\<bullet>x" in exI)
apply(perm_simp)
apply(rule ballI)
apply(drule_tac x="pi1\<bullet>xa" in spec)
apply(auto)
apply(drule_tac x="xa" in spec)
apply(auto)[1]
apply(rule_tac x="(rev pi1)\<bullet>xb" in exI)
apply(perm_simp)
apply(simp add: pt_set_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: pt_set_bij[OF pt_name_inst, OF at_name_inst])
apply(simp add: pt_set_bij1[OF pt_name_inst, OF at_name_inst])
apply(rule_tac x="(rev pi2)\<bullet>x" in exI)
apply(perm_simp)
apply(rule ballI)
apply(drule_tac x="pi2\<bullet>xa" in spec)
apply(auto)
apply(drule_tac x="xa" in spec)
apply(auto)[1]
apply(rule_tac x="(rev pi2)\<bullet>xb" in exI)
apply(perm_simp)
apply(simp add: pt_set_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: pt_set_bij[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: pt_set_bij1[OF pt_coname_inst, OF at_coname_inst])
done

lemma lfp_eqvt:
  fixes pi1::"name prm"
  and   f::"'a set \<Rightarrow> ('a::pt_name) set"
  and   pi2::"coname prm"
  and   g::"'b set \<Rightarrow> ('b::pt_coname) set"
  shows "pi1\<bullet>(lfp f) = lfp (pi1\<bullet>f)"
  and   "pi2\<bullet>(lfp g) = lfp (pi2\<bullet>g)"
apply(simp add: lfp_def)
apply(simp add: big_inter_eqvt)
apply(simp add: pt_Collect_eqvt[OF pt_name_inst, OF at_name_inst])
apply(subgoal_tac "{u. (pi1\<bullet>f) u \<subseteq> u} = {u. ((rev pi1)\<bullet>((pi1\<bullet>f) u)) \<subseteq> ((rev pi1)\<bullet>u)}")
apply(perm_simp)
apply(rule Collect_cong)
apply(rule iffI)
apply(rule subseteq_eqvt(1)[THEN iffD1])
apply(simp add: perm_bool)
apply(drule subseteq_eqvt(1)[THEN iffD2])
apply(simp add: perm_bool)
apply(simp add: lfp_def)
apply(simp add: big_inter_eqvt)
apply(simp add: pt_Collect_eqvt[OF pt_coname_inst, OF at_coname_inst])
apply(subgoal_tac "{u. (pi2\<bullet>g) u \<subseteq> u} = {u. ((rev pi2)\<bullet>((pi2\<bullet>g) u)) \<subseteq> ((rev pi2)\<bullet>u)}")
apply(perm_simp)
apply(rule Collect_cong)
apply(rule iffI)
apply(rule subseteq_eqvt(2)[THEN iffD1])
apply(simp add: perm_bool)
apply(drule subseteq_eqvt(2)[THEN iffD2])
apply(simp add: perm_bool)
done

abbreviation
  CANDn::"ty \<Rightarrow> ntrm set"  (\<open>\<parallel>'(_')\<parallel>\<close> [60] 60) 
where
  "\<parallel>(B)\<parallel> \<equiv> lfp (NEGn B \<circ> NEGc B)" 

abbreviation
  CANDc::"ty \<Rightarrow> ctrm set"  (\<open>\<parallel><_>\<parallel>\<close> [60] 60)
where
  "\<parallel><B>\<parallel> \<equiv> NEGc B (\<parallel>(B)\<parallel>)"

lemma NEGn_decreasing:
  shows "X\<subseteq>Y \<Longrightarrow> NEGn B Y \<subseteq> NEGn B X"
by (nominal_induct B rule: ty.strong_induct)
   (auto dest: BINDINGn_decreasing)

lemma NEGc_decreasing:
  shows "X\<subseteq>Y \<Longrightarrow> NEGc B Y \<subseteq> NEGc B X"
by (nominal_induct B rule: ty.strong_induct)
   (auto dest: BINDINGc_decreasing)

lemma mono_NEGn_NEGc:
  shows "mono (NEGn B \<circ> NEGc B)"
  and   "mono (NEGc B \<circ> NEGn B)"
proof -
  have "\<forall>X Y. X\<subseteq>Y \<longrightarrow> NEGn B (NEGc B X) \<subseteq> NEGn B (NEGc B Y)"
  proof (intro strip)
    fix X::"ntrm set" and Y::"ntrm set"
    assume "X\<subseteq>Y"
    then have "NEGc B Y \<subseteq> NEGc B X" by (simp add: NEGc_decreasing)
    then show "NEGn B (NEGc B X) \<subseteq> NEGn B (NEGc B Y)" by (simp add: NEGn_decreasing)
  qed
  then show "mono (NEGn B \<circ> NEGc B)" by (simp add: mono_def)
next
  have "\<forall>X Y. X\<subseteq>Y \<longrightarrow> NEGc B (NEGn B X) \<subseteq> NEGc B (NEGn B Y)"
  proof (intro strip)
    fix X::"ctrm set" and Y::"ctrm set"
    assume "X\<subseteq>Y"
    then have "NEGn B Y \<subseteq> NEGn B X" by (simp add: NEGn_decreasing)
    then show "NEGc B (NEGn B X) \<subseteq> NEGc B (NEGn B Y)" by (simp add: NEGc_decreasing)
  qed
  then show "mono (NEGc B \<circ> NEGn B)" by (simp add: mono_def)
qed

lemma NEG_simp:
  shows "\<parallel><B>\<parallel> = NEGc B (\<parallel>(B)\<parallel>)"
  and   "\<parallel>(B)\<parallel> = NEGn B (\<parallel><B>\<parallel>)"
proof -
  show "\<parallel><B>\<parallel> = NEGc B (\<parallel>(B)\<parallel>)" by simp
next
  have "\<parallel>(B)\<parallel> \<equiv> lfp (NEGn B \<circ> NEGc B)" by simp
  then have "\<parallel>(B)\<parallel> = (NEGn B \<circ> NEGc B) (\<parallel>(B)\<parallel>)" using mono_NEGn_NEGc def_lfp_unfold by blast
  then show "\<parallel>(B)\<parallel> = NEGn B (\<parallel><B>\<parallel>)" by simp
qed

lemma NEG_elim:
  shows "M \<in> \<parallel><B>\<parallel> \<Longrightarrow> M \<in> NEGc B (\<parallel>(B)\<parallel>)"
  and   "N \<in> \<parallel>(B)\<parallel> \<Longrightarrow> N \<in> NEGn B (\<parallel><B>\<parallel>)"
using NEG_simp by (blast)+

lemma NEG_intro:
  shows "M \<in> NEGc B (\<parallel>(B)\<parallel>) \<Longrightarrow> M \<in> \<parallel><B>\<parallel>"
  and   "N \<in> NEGn B (\<parallel><B>\<parallel>) \<Longrightarrow> N \<in> \<parallel>(B)\<parallel>"
using NEG_simp by (blast)+

lemma NEGc_simps:
  shows "NEGc (PR A) (\<parallel>(PR A)\<parallel>) = AXIOMSc (PR A) \<union> BINDINGc (PR A) (\<parallel>(PR A)\<parallel>)"  
  and   "NEGc (NOT C) (\<parallel>(NOT C)\<parallel>) = AXIOMSc (NOT C) \<union> BINDINGc (NOT C) (\<parallel>(NOT C)\<parallel>) 
                                        \<union> (NOTRIGHT (NOT C) (\<parallel>(C)\<parallel>))"  
  and   "NEGc (C AND D) (\<parallel>(C AND D)\<parallel>) = AXIOMSc (C AND D) \<union> BINDINGc (C AND D) (\<parallel>(C AND D)\<parallel>) 
                                        \<union> (ANDRIGHT (C AND D) (\<parallel><C>\<parallel>) (\<parallel><D>\<parallel>))"
  and   "NEGc (C OR D) (\<parallel>(C OR D)\<parallel>) = AXIOMSc (C OR D) \<union> BINDINGc (C OR D)  (\<parallel>(C OR D)\<parallel>)
                                        \<union> (ORRIGHT1 (C OR D) (\<parallel><C>\<parallel>)) \<union> (ORRIGHT2 (C OR D) (\<parallel><D>\<parallel>))"
  and   "NEGc (C IMP D) (\<parallel>(C IMP D)\<parallel>) = AXIOMSc (C IMP D) \<union> BINDINGc (C IMP D) (\<parallel>(C IMP D)\<parallel>) 
          \<union> (IMPRIGHT (C IMP D) (\<parallel>(C)\<parallel>) (\<parallel><D>\<parallel>) (\<parallel>(D)\<parallel>) (\<parallel><C>\<parallel>))"
by (simp_all only: NEGc.simps)

lemma AXIOMS_in_CANDs:
  shows "AXIOMSn B \<subseteq> (\<parallel>(B)\<parallel>)"
  and   "AXIOMSc B \<subseteq> (\<parallel><B>\<parallel>)"
proof -
  have "AXIOMSn B \<subseteq> NEGn B (\<parallel><B>\<parallel>)"
    by (nominal_induct B rule: ty.strong_induct) (auto)
  then show "AXIOMSn B \<subseteq> \<parallel>(B)\<parallel>" using NEG_simp by blast
next
  have "AXIOMSc B \<subseteq> NEGc B (\<parallel>(B)\<parallel>)"
    by (nominal_induct B rule: ty.strong_induct) (auto)
  then show "AXIOMSc B \<subseteq> \<parallel><B>\<parallel>" using NEG_simp by blast
qed

lemma Ax_in_CANDs:
  shows "(y):Ax x a \<in> \<parallel>(B)\<parallel>"
  and   "<b>:Ax x a \<in> \<parallel><B>\<parallel>"
proof -
  have "(y):Ax x a \<in> AXIOMSn B" by (auto simp add: AXIOMSn_def)
  also have "AXIOMSn B \<subseteq> \<parallel>(B)\<parallel>" by (rule AXIOMS_in_CANDs)
  finally show "(y):Ax x a \<in> \<parallel>(B)\<parallel>" by simp
next
  have "<b>:Ax x a \<in> AXIOMSc B" by (auto simp add: AXIOMSc_def)
  also have "AXIOMSc B \<subseteq> \<parallel><B>\<parallel>" by (rule AXIOMS_in_CANDs)
  finally show "<b>:Ax x a \<in> \<parallel><B>\<parallel>" by simp
qed

lemma AXIOMS_eqvt_aux_name:
  fixes pi::"name prm"
  shows "M \<in> AXIOMSn B \<Longrightarrow> (pi\<bullet>M) \<in> AXIOMSn B" 
  and   "N \<in> AXIOMSc B \<Longrightarrow> (pi\<bullet>N) \<in> AXIOMSc B"
apply(auto simp add: AXIOMSn_def AXIOMSc_def)
apply(rule_tac x="pi\<bullet>x" in exI)
apply(rule_tac x="pi\<bullet>y" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(simp)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>y" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(simp)
done

lemma AXIOMS_eqvt_aux_coname:
  fixes pi::"coname prm"
  shows "M \<in> AXIOMSn B \<Longrightarrow> (pi\<bullet>M) \<in> AXIOMSn B" 
  and   "N \<in> AXIOMSc B \<Longrightarrow> (pi\<bullet>N) \<in> AXIOMSc B"
apply(auto simp add: AXIOMSn_def AXIOMSc_def)
apply(rule_tac x="pi\<bullet>x" in exI)
apply(rule_tac x="pi\<bullet>y" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(simp)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>y" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(simp)
done

lemma AXIOMS_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>AXIOMSn B) = AXIOMSn B" 
  and   "(pi\<bullet>AXIOMSc B) = AXIOMSc B"
apply(auto)
apply(simp add: pt_set_bij1a[OF pt_name_inst, OF at_name_inst])
apply(drule_tac pi="pi" in AXIOMS_eqvt_aux_name(1))
apply(perm_simp)
apply(drule_tac pi="rev pi" in AXIOMS_eqvt_aux_name(1))
apply(simp add: pt_set_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: pt_set_bij1a[OF pt_name_inst, OF at_name_inst])
apply(drule_tac pi="pi" in AXIOMS_eqvt_aux_name(2))
apply(perm_simp)
apply(drule_tac pi="rev pi" in AXIOMS_eqvt_aux_name(2))
apply(simp add: pt_set_bij1[OF pt_name_inst, OF at_name_inst])
done

lemma AXIOMS_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>AXIOMSn B) = AXIOMSn B" 
  and   "(pi\<bullet>AXIOMSc B) = AXIOMSc B"
apply(auto)
apply(simp add: pt_set_bij1a[OF pt_coname_inst, OF at_coname_inst])
apply(drule_tac pi="pi" in AXIOMS_eqvt_aux_coname(1))
apply(perm_simp)
apply(drule_tac pi="rev pi" in AXIOMS_eqvt_aux_coname(1))
apply(simp add: pt_set_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: pt_set_bij1a[OF pt_coname_inst, OF at_coname_inst])
apply(drule_tac pi="pi" in AXIOMS_eqvt_aux_coname(2))
apply(perm_simp)
apply(drule_tac pi="rev pi" in AXIOMS_eqvt_aux_coname(2))
apply(simp add: pt_set_bij1[OF pt_coname_inst, OF at_coname_inst])
done

lemma BINDING_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(BINDINGn B X)) = BINDINGn B (pi\<bullet>X)" 
  and   "(pi\<bullet>(BINDINGc B Y)) = BINDINGc B (pi\<bullet>Y)" 
apply(auto simp add: BINDINGn_def BINDINGc_def perm_set_def)
apply(rule_tac x="pi\<bullet>xb" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(auto)[1]
apply(drule_tac x="(rev pi)\<bullet>a" in spec)
apply(drule_tac x="(rev pi)\<bullet>P" in spec)
apply(drule mp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp)
apply(drule_tac ?pi1.0="pi" in SNa_eqvt(1))
apply(perm_simp add: nsubst_eqvt)
apply(rule_tac x="(rev pi\<bullet>xa):(rev pi\<bullet>M)" in exI)
apply(perm_simp)
apply(rule_tac x="rev pi\<bullet>xa" in exI)
apply(rule_tac x="rev pi\<bullet>M" in exI)
apply(simp)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>a" in spec)
apply(drule_tac x="pi\<bullet>P" in spec)
apply(drule mp)
apply(force)
apply(drule_tac ?pi1.0="rev pi" in SNa_eqvt(1))
apply(perm_simp add: nsubst_eqvt)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(auto)[1]
apply(drule_tac x="(rev pi)\<bullet>x" in spec)
apply(drule_tac x="(rev pi)\<bullet>P" in spec)
apply(drule mp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp)
apply(drule_tac ?pi1.0="pi" in SNa_eqvt(1))
apply(perm_simp add: csubst_eqvt)
apply(rule_tac x="<(rev pi\<bullet>a)>:(rev pi\<bullet>M)" in exI)
apply(perm_simp)
apply(rule_tac x="rev pi\<bullet>a" in exI)
apply(rule_tac x="rev pi\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>x" in spec)
apply(drule_tac x="pi\<bullet>P" in spec)
apply(drule mp)
apply(force)
apply(drule_tac ?pi1.0="rev pi" in SNa_eqvt(1))
apply(perm_simp add: csubst_eqvt)
done

lemma BINDING_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(BINDINGn B X)) = BINDINGn B (pi\<bullet>X)" 
  and   "(pi\<bullet>(BINDINGc B Y)) = BINDINGc B (pi\<bullet>Y)" 
apply(auto simp add: BINDINGn_def BINDINGc_def perm_set_def)
apply(rule_tac x="pi\<bullet>xb" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(auto)[1]
apply(drule_tac x="(rev pi)\<bullet>a" in spec)
apply(drule_tac x="(rev pi)\<bullet>P" in spec)
apply(drule mp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp)
apply(drule_tac ?pi2.0="pi" in SNa_eqvt(2))
apply(perm_simp add: nsubst_eqvt)
apply(rule_tac x="(rev pi\<bullet>xa):(rev pi\<bullet>M)" in exI)
apply(perm_simp)
apply(rule_tac x="rev pi\<bullet>xa" in exI)
apply(rule_tac x="rev pi\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>a" in spec)
apply(drule_tac x="pi\<bullet>P" in spec)
apply(drule mp)
apply(force)
apply(drule_tac ?pi2.0="rev pi" in SNa_eqvt(2))
apply(perm_simp add: nsubst_eqvt)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(auto)[1]
apply(drule_tac x="(rev pi)\<bullet>x" in spec)
apply(drule_tac x="(rev pi)\<bullet>P" in spec)
apply(drule mp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp)
apply(drule_tac ?pi2.0="pi" in SNa_eqvt(2))
apply(perm_simp add: csubst_eqvt)
apply(rule_tac x="<(rev pi\<bullet>a)>:(rev pi\<bullet>M)" in exI)
apply(perm_simp)
apply(rule_tac x="rev pi\<bullet>a" in exI)
apply(rule_tac x="rev pi\<bullet>M" in exI)
apply(simp)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>x" in spec)
apply(drule_tac x="pi\<bullet>P" in spec)
apply(drule mp)
apply(force)
apply(drule_tac ?pi2.0="rev pi" in SNa_eqvt(2))
apply(perm_simp add: csubst_eqvt)
done

lemma CAND_eqvt_name:
  fixes pi::"name prm"
  shows   "(pi\<bullet>(\<parallel>(B)\<parallel>)) = (\<parallel>(B)\<parallel>)"
  and     "(pi\<bullet>(\<parallel><B>\<parallel>)) = (\<parallel><B>\<parallel>)"
proof (nominal_induct B rule: ty.strong_induct)
  case (PR X)
  { case 1 show ?case 
      apply -
      apply(simp add: lfp_eqvt)
      apply(simp add: perm_fun_def)
      apply(simp add: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name)
      apply(perm_simp)
    done
  next
    case 2 show ?case
      apply -
      apply(simp only: NEGc_simps)
      apply(simp add: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name)
      apply(simp add: lfp_eqvt)
      apply(simp add: comp_def)
      apply(simp add: perm_fun_def)
      apply(simp add: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name)
      apply(perm_simp)
      done
  }
next
  case (NOT B)
  have ih1: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(NOT B)\<parallel>) = (\<parallel>(NOT B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name NOTRIGHT_eqvt_name NOTLEFT_eqvt_name)
    apply(perm_simp add: ih1 ih2)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name NOTRIGHT_eqvt_name ih1 ih2 g)
  }
next
  case (AND A B)
  have ih1: "pi\<bullet>(\<parallel>(A)\<parallel>) = (\<parallel>(A)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><A>\<parallel>) = (\<parallel><A>\<parallel>)" by fact
  have ih3: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih4: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(A AND B)\<parallel>) = (\<parallel>(A AND B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name ANDRIGHT_eqvt_name 
                     ANDLEFT2_eqvt_name ANDLEFT1_eqvt_name)
    apply(perm_simp add: ih1 ih2 ih3 ih4)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name 
                     ANDRIGHT_eqvt_name ANDLEFT1_eqvt_name ANDLEFT2_eqvt_name ih1 ih2 ih3 ih4 g)
  }
next
  case (OR A B)
  have ih1: "pi\<bullet>(\<parallel>(A)\<parallel>) = (\<parallel>(A)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><A>\<parallel>) = (\<parallel><A>\<parallel>)" by fact
  have ih3: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih4: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(A OR B)\<parallel>) = (\<parallel>(A OR B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name ORRIGHT1_eqvt_name 
                     ORRIGHT2_eqvt_name ORLEFT_eqvt_name)
    apply(perm_simp add: ih1 ih2 ih3 ih4)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name 
                     ORRIGHT1_eqvt_name ORRIGHT2_eqvt_name ORLEFT_eqvt_name ih1 ih2 ih3 ih4 g)
  }
next
  case (IMP A B)
  have ih1: "pi\<bullet>(\<parallel>(A)\<parallel>) = (\<parallel>(A)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><A>\<parallel>) = (\<parallel><A>\<parallel>)" by fact
  have ih3: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih4: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(A IMP B)\<parallel>) = (\<parallel>(A IMP B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name IMPRIGHT_eqvt_name IMPLEFT_eqvt_name)
    apply(perm_simp add: ih1 ih2 ih3 ih4)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name 
                     IMPRIGHT_eqvt_name IMPLEFT_eqvt_name ih1 ih2 ih3 ih4 g)
  }
qed

lemma CAND_eqvt_coname:
  fixes pi::"coname prm"
  shows   "(pi\<bullet>(\<parallel>(B)\<parallel>)) = (\<parallel>(B)\<parallel>)"
  and     "(pi\<bullet>(\<parallel><B>\<parallel>)) = (\<parallel><B>\<parallel>)"
proof (nominal_induct B rule: ty.strong_induct)
  case (PR X)
  { case 1 show ?case 
      apply -
      apply(simp add: lfp_eqvt)
      apply(simp add: perm_fun_def)
      apply(simp add: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname)
      apply(perm_simp)
    done
  next
    case 2 show ?case
      apply -
      apply(simp only: NEGc_simps)
      apply(simp add: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname)
      apply(simp add: lfp_eqvt)
      apply(simp add: comp_def)
      apply(simp add: perm_fun_def)
      apply(simp add: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname)
      apply(perm_simp)
      done
  }
next
  case (NOT B)
  have ih1: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(NOT B)\<parallel>) = (\<parallel>(NOT B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname 
            NOTRIGHT_eqvt_coname NOTLEFT_eqvt_coname)
    apply(perm_simp add: ih1 ih2)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname 
              NOTRIGHT_eqvt_coname ih1 ih2 g)
  }
next
  case (AND A B)
  have ih1: "pi\<bullet>(\<parallel>(A)\<parallel>) = (\<parallel>(A)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><A>\<parallel>) = (\<parallel><A>\<parallel>)" by fact
  have ih3: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih4: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(A AND B)\<parallel>) = (\<parallel>(A AND B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname ANDRIGHT_eqvt_coname 
                     ANDLEFT2_eqvt_coname ANDLEFT1_eqvt_coname)
    apply(perm_simp add: ih1 ih2 ih3 ih4)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname 
                     ANDRIGHT_eqvt_coname ANDLEFT1_eqvt_coname ANDLEFT2_eqvt_coname ih1 ih2 ih3 ih4 g)
  }
next
  case (OR A B)
  have ih1: "pi\<bullet>(\<parallel>(A)\<parallel>) = (\<parallel>(A)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><A>\<parallel>) = (\<parallel><A>\<parallel>)" by fact
  have ih3: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih4: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(A OR B)\<parallel>) = (\<parallel>(A OR B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname ORRIGHT1_eqvt_coname 
                     ORRIGHT2_eqvt_coname ORLEFT_eqvt_coname)
    apply(perm_simp add: ih1 ih2 ih3 ih4)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname 
                     ORRIGHT1_eqvt_coname ORRIGHT2_eqvt_coname ORLEFT_eqvt_coname ih1 ih2 ih3 ih4 g)
  }
next
  case (IMP A B)
  have ih1: "pi\<bullet>(\<parallel>(A)\<parallel>) = (\<parallel>(A)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><A>\<parallel>) = (\<parallel><A>\<parallel>)" by fact
  have ih3: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih4: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(A IMP B)\<parallel>) = (\<parallel>(A IMP B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname IMPRIGHT_eqvt_coname 
         IMPLEFT_eqvt_coname)
    apply(perm_simp add: ih1 ih2 ih3 ih4)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname 
                     IMPRIGHT_eqvt_coname IMPLEFT_eqvt_coname ih1 ih2 ih3 ih4 g)
  }
qed

text \<open>Elimination rules for the set-operators\<close>

lemma BINDINGc_elim:
  assumes a: "<a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>)"
  shows "\<forall>x P. ((x):P)\<in>(\<parallel>(B)\<parallel>) \<longrightarrow> SNa (M{a:=(x).P})"
using a
apply(auto simp add: BINDINGc_def)
apply(auto simp add: ctrm.inject alpha)
apply(drule_tac x="[(a,aa)]\<bullet>x" in spec)
apply(drule_tac x="[(a,aa)]\<bullet>P" in spec)
apply(drule mp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname)
apply(drule_tac ?pi2.0="[(a,aa)]" in SNa_eqvt(2))
apply(perm_simp add: csubst_eqvt)
done

lemma BINDINGn_elim:
  assumes a: "(x):M \<in> BINDINGn B (\<parallel><B>\<parallel>)"
  shows "\<forall>c P. (<c>:P)\<in>(\<parallel><B>\<parallel>) \<longrightarrow> SNa (M{x:=<c>.P})"
using a
apply(auto simp add: BINDINGn_def)
apply(auto simp add: ntrm.inject alpha)
apply(drule_tac x="[(x,xa)]\<bullet>c" in spec)
apply(drule_tac x="[(x,xa)]\<bullet>P" in spec)
apply(drule mp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name)
apply(drule_tac ?pi1.0="[(x,xa)]" in SNa_eqvt(1))
apply(perm_simp add: nsubst_eqvt)
done

lemma NOTRIGHT_elim:
  assumes a: "<a>:M \<in> NOTRIGHT (NOT B) (\<parallel>(B)\<parallel>)"
  obtains x' M' where "M = NotR (x').M' a" and "fic (NotR (x').M' a) a" and "(x'):M' \<in> (\<parallel>(B)\<parallel>)"
using a
apply(auto simp add: ctrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
done

lemma NOTLEFT_elim:
  assumes a: "(x):M \<in> NOTLEFT (NOT B) (\<parallel><B>\<parallel>)"
  obtains a' M' where "M = NotL <a'>.M' x" and "fin (NotL <a'>.M' x) x" and "<a'>:M' \<in> (\<parallel><B>\<parallel>)"
using a
apply(auto simp add: ntrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
done

lemma ANDRIGHT_elim:
  assumes a: "<a>:M \<in> ANDRIGHT (B AND C) (\<parallel><B>\<parallel>) (\<parallel><C>\<parallel>)"
  obtains d' M' e' N' where "M = AndR <d'>.M' <e'>.N' a" and "fic (AndR <d'>.M' <e'>.N' a) a" 
                      and "<d'>:M' \<in> (\<parallel><B>\<parallel>)" and "<e'>:N' \<in> (\<parallel><C>\<parallel>)"
using a
apply(auto simp add: ctrm.inject alpha abs_fresh calc_atm fresh_atm)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" and x="<a>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(case_tac "a=b")
apply(simp)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(b,c)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(b,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "c=b")
apply(simp)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(aa,c)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(aa,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,c)]" and x="<aa>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "c=aa")
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" and x="<a>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" and x="<a>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(case_tac "a=aa")
apply(simp)
apply(case_tac "aa=b")
apply(simp)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(b,c)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(b,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "c=b")
apply(simp)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(aa,b)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(aa,b)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(aa,c)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(aa,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,c)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "c=aa")
apply(simp)
apply(case_tac "a=b")
apply(simp)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(b,aa)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(b,aa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(b,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(b,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(b,aa)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "aa=b")
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "a=b")
apply(simp)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(b,c)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(b,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "c=b")
apply(simp)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
done 

lemma ANDLEFT1_elim:
  assumes a: "(x):M \<in> ANDLEFT1 (B AND C) (\<parallel>(B)\<parallel>)"
  obtains x' M' where "M = AndL1 (x').M' x" and "fin (AndL1 (x').M' x) x" and "(x'):M' \<in> (\<parallel>(B)\<parallel>)"
using a [[ hypsubst_thin = true ]]
apply(auto simp add: ntrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(xa,y)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "y=xa")
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
done

lemma ANDLEFT2_elim:
  assumes a: "(x):M \<in> ANDLEFT2 (B AND C) (\<parallel>(C)\<parallel>)"
  obtains x' M' where "M = AndL2 (x').M' x" and "fin (AndL2 (x').M' x) x" and "(x'):M' \<in> (\<parallel>(C)\<parallel>)"
using a [[ hypsubst_thin = true ]]
apply(auto simp add: ntrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(xa,y)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "y=xa")
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
done

lemma ORRIGHT1_elim:
  assumes a: "<a>:M \<in> ORRIGHT1 (B OR C) (\<parallel><B>\<parallel>)"
  obtains a' M' where "M = OrR1 <a'>.M' a" and "fic (OrR1 <a'>.M' a) a" and "<a'>:M' \<in> (\<parallel><B>\<parallel>)"
using a
apply(auto simp add: ctrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(aa,b)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "b=aa")
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
done

lemma ORRIGHT2_elim:
  assumes a: "<a>:M \<in> ORRIGHT2 (B OR C) (\<parallel><C>\<parallel>)"
  obtains a' M' where "M = OrR2 <a'>.M' a" and "fic (OrR2 <a'>.M' a) a" and "<a'>:M' \<in> (\<parallel><C>\<parallel>)"
using a
apply(auto simp add: ctrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(aa,b)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "b=aa")
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
done

lemma ORLEFT_elim:
  assumes a: "(x):M \<in> ORLEFT (B OR C) (\<parallel>(B)\<parallel>) (\<parallel>(C)\<parallel>)"
  obtains y' M' z' N' where "M = OrL (y').M' (z').N' x" and "fin (OrL (y').M' (z').N' x) x" 
                      and "(y'):M' \<in> (\<parallel>(B)\<parallel>)" and "(z'):N' \<in> (\<parallel>(C)\<parallel>)"
using a
apply(auto simp add: ntrm.inject alpha abs_fresh calc_atm fresh_atm)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" and x="(x):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(case_tac "x=y")
apply(simp)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(y,z)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(y,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "z=y")
apply(simp)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(xa,z)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(xa,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,z)]" and x="(xa):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "z=xa")
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" and x="(x):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" and x="(x):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(case_tac "x=xa")
apply(simp)
apply(case_tac "xa=y")
apply(simp)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(y,z)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(y,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "z=y")
apply(simp)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(xa,y)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(xa,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(xa,z)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(xa,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,z)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "z=xa")
apply(simp)
apply(case_tac "x=y")
apply(simp)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(y,xa)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(y,xa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(y,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(y,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(y,xa)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "xa=y")
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "x=y")
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(y,z)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(y,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "z=y")
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
done

lemma IMPRIGHT_elim:
  assumes a: "<a>:M \<in> IMPRIGHT (B IMP C) (\<parallel>(B)\<parallel>) (\<parallel><C>\<parallel>) (\<parallel>(C)\<parallel>) (\<parallel><B>\<parallel>)"
  obtains x' a' M' where "M = ImpR (x').<a'>.M' a" and "fic (ImpR (x').<a'>.M' a) a" 
                   and "\<forall>z P. x'\<sharp>(z,P) \<and> (z):P \<in> \<parallel>(C)\<parallel> \<longrightarrow> (x'):(M'{a':=(z).P}) \<in> \<parallel>(B)\<parallel>" 
                   and "\<forall>c Q. a'\<sharp>(c,Q) \<and> <c>:Q \<in> \<parallel><B>\<parallel> \<longrightarrow> <a'>:(M'{x':=<c>.Q}) \<in> \<parallel><C>\<parallel>"
using a
apply(auto simp add: ctrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule_tac x="z" in spec)
apply(drule_tac x="[(a,b)]\<bullet>P" in spec)
apply(simp add: fresh_prod fresh_left calc_atm)
apply(drule_tac pi="[(a,b)]" and x="(x):Ma{a:=(z).([(a,b)]\<bullet>P)}" 
                                     in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: calc_atm csubst_eqvt CAND_eqvt_coname)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add:  CAND_eqvt_coname)
apply(rotate_tac 2)
apply(drule_tac x="[(a,b)]\<bullet>c" in spec)
apply(drule_tac x="[(a,b)]\<bullet>Q" in spec)
apply(simp add: fresh_prod fresh_left)
apply(drule mp)
apply(simp add: calc_atm)
apply(drule_tac pi="[(a,b)]" and x="<a>:Ma{x:=<([(a,b)]\<bullet>c)>.([(a,b)]\<bullet>Q)}" 
                                        in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: nsubst_eqvt CAND_eqvt_coname)
apply(simp add: calc_atm)
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(aa,b)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule_tac x="z" in spec)
apply(drule_tac x="[(a,b)]\<bullet>P" in spec)
apply(simp add: fresh_prod fresh_left calc_atm)
apply(drule_tac pi="[(a,b)]" and x="(x):Ma{a:=(z).([(a,b)]\<bullet>P)}" 
                                     in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: calc_atm csubst_eqvt  CAND_eqvt_coname)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname)
apply(drule_tac x="[(a,b)]\<bullet>c" in spec)
apply(drule_tac x="[(a,b)]\<bullet>Q" in spec)
apply(simp)
apply(simp add: fresh_prod fresh_left)
apply(drule mp)
apply(simp add: calc_atm)
apply(drule_tac pi="[(a,b)]" and x="<a>:Ma{x:=<([(a,b)]\<bullet>c)>.([(a,b)]\<bullet>Q)}" 
                                      in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: nsubst_eqvt CAND_eqvt_coname)
apply(simp add: calc_atm)
apply(simp)
apply(case_tac "b=aa")
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule_tac x="z" in spec)
apply(drule_tac x="[(a,aa)]\<bullet>P" in spec)
apply(simp add: fresh_prod fresh_left calc_atm)
apply(drule_tac pi="[(a,aa)]" and x="(x):Ma{aa:=(z).([(a,aa)]\<bullet>P)}" 
                                    in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: calc_atm csubst_eqvt  CAND_eqvt_coname)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add:  CAND_eqvt_coname)
apply(drule_tac x="[(a,aa)]\<bullet>c" in spec)
apply(drule_tac x="[(a,aa)]\<bullet>Q" in spec)
apply(simp)
apply(simp add: fresh_prod fresh_left)
apply(drule mp)
apply(simp add: calc_atm)
apply(drule_tac pi="[(a,aa)]" and x="<aa>:Ma{x:=<([(a,aa)]\<bullet>c)>.([(a,aa)]\<bullet>Q)}" 
                                    in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: nsubst_eqvt  CAND_eqvt_coname)
apply(simp add: calc_atm)
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>Ma" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm  CAND_eqvt_coname)
apply(drule_tac x="z" in spec)
apply(drule_tac x="[(a,b)]\<bullet>P" in spec)
apply(simp add: fresh_prod fresh_left calc_atm)
apply(drule_tac pi="[(a,b)]" and x="(x):Ma{aa:=(z).([(a,b)]\<bullet>P)}" 
                                          in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: calc_atm csubst_eqvt  CAND_eqvt_coname)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add:  CAND_eqvt_coname)
apply(drule_tac x="[(a,b)]\<bullet>c" in spec)
apply(drule_tac x="[(a,b)]\<bullet>Q" in spec)
apply(simp add: fresh_prod fresh_left)
apply(drule mp)
apply(simp add: calc_atm)
apply(drule_tac pi="[(a,b)]" and x="<aa>:Ma{x:=<([(a,b)]\<bullet>c)>.([(a,b)]\<bullet>Q)}" 
                                        in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: nsubst_eqvt  CAND_eqvt_coname)
apply(simp add: calc_atm)
done

lemma IMPLEFT_elim:
  assumes a: "(x):M \<in> IMPLEFT (B IMP C) (\<parallel><B>\<parallel>) (\<parallel>(C)\<parallel>)"
  obtains x' a' M' N' where "M = ImpL <a'>.M' (x').N' x" and "fin (ImpL <a'>.M' (x').N' x) x" 
                   and "<a'>:M' \<in> \<parallel><B>\<parallel>" and "(x'):N' \<in> \<parallel>(C)\<parallel>"
using a
apply(auto simp add: ntrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" and x="(x):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: calc_atm  CAND_eqvt_name)
apply(simp)
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(xa,y)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(xa,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" and x="(xa):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "y=xa")
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" and x="<a>:Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm  CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" and x="(xa):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>Ma" in meta_spec)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" and x="(xa):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
done

lemma CANDs_alpha:
  shows "<a>:M \<in> (\<parallel><B>\<parallel>) \<Longrightarrow> [a].M = [b].N \<Longrightarrow> <b>:N \<in> (\<parallel><B>\<parallel>)"
  and   "(x):M \<in> (\<parallel>(B)\<parallel>) \<Longrightarrow> [x].M = [y].N \<Longrightarrow> (y):N \<in> (\<parallel>(B)\<parallel>)"
apply(auto simp add: alpha)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: CAND_eqvt_coname calc_atm)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name calc_atm)
done

lemma CAND_NotR_elim:
  assumes a: "<a>:NotR (x).M a \<in> (\<parallel><B>\<parallel>)" "<a>:NotR (x).M a \<notin> BINDINGc B (\<parallel>(B)\<parallel>)"
  shows "\<exists>B'. B = NOT B' \<and> (x):M \<in> (\<parallel>(B')\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSc_def ctrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
done

lemma CAND_NotL_elim_aux:
  assumes a: "(x):NotL <a>.M x \<in> NEGn B (\<parallel><B>\<parallel>)" "(x):NotL <a>.M x \<notin> BINDINGn B (\<parallel><B>\<parallel>)"
  shows "\<exists>B'. B = NOT B' \<and> <a>:M \<in> (\<parallel><B'>\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSn_def ntrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
done

lemmas CAND_NotL_elim = CAND_NotL_elim_aux[OF NEG_elim(2)]

lemma CAND_AndR_elim:
  assumes a: "<a>:AndR <b>.M <c>.N a \<in> (\<parallel><B>\<parallel>)" "<a>:AndR <b>.M <c>.N a \<notin> BINDINGc B (\<parallel>(B)\<parallel>)"
  shows "\<exists>B1 B2. B = B1 AND B2 \<and> <b>:M \<in> (\<parallel><B1>\<parallel>) \<and> <c>:N \<in> (\<parallel><B2>\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSc_def ctrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(a,ca)]" and x="<a>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(a,ca)]" and x="<a>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(a,ca)]" and x="<a>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "a=ba")
apply(simp)
apply(drule_tac pi="[(ba,ca)]" and x="<ba>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "ca=ba")
apply(simp)
apply(drule_tac pi="[(a,ba)]" and x="<ba>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(a,ca)]" and x="<ba>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac pi="[(aa,ca)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "ca=aa")
apply(simp)
apply(drule_tac pi="[(a,aa)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(a,ca)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(a,ca)]" and x="<a>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac pi="[(aa,ca)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "ca=aa")
apply(simp)
apply(drule_tac pi="[(a,aa)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(a,ca)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "a=ba")
apply(simp)
apply(drule_tac pi="[(ba,ca)]" and x="<ba>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "ca=ba")
apply(simp)
apply(drule_tac pi="[(a,ba)]" and x="<ba>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(a,ca)]" and x="<ba>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
done

lemma CAND_OrR1_elim:
  assumes a: "<a>:OrR1 <b>.M a \<in> (\<parallel><B>\<parallel>)" "<a>:OrR1 <b>.M a \<notin> BINDINGc B (\<parallel>(B)\<parallel>)"
  shows "\<exists>B1 B2. B = B1 OR B2 \<and> <b>:M \<in> (\<parallel><B1>\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSc_def ctrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(a,ba)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac pi="[(aa,ba)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
apply(case_tac "ba=aa")
apply(simp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
apply(drule_tac pi="[(a,ba)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
done

lemma CAND_OrR2_elim:
  assumes a: "<a>:OrR2 <b>.M a \<in> (\<parallel><B>\<parallel>)" "<a>:OrR2 <b>.M a \<notin> BINDINGc B (\<parallel>(B)\<parallel>)"
  shows "\<exists>B1 B2. B = B1 OR B2 \<and> <b>:M \<in> (\<parallel><B2>\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSc_def ctrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(a,ba)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac pi="[(aa,ba)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
apply(case_tac "ba=aa")
apply(simp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
apply(drule_tac pi="[(a,ba)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
done

lemma CAND_OrL_elim_aux:
  assumes a: "(x):(OrL (y).M (z).N x) \<in> NEGn B (\<parallel><B>\<parallel>)" "(x):(OrL (y).M (z).N x) \<notin> BINDINGn B (\<parallel><B>\<parallel>)"
  shows "\<exists>B1 B2. B = B1 OR B2 \<and> (y):M \<in> (\<parallel>(B1)\<parallel>) \<and> (z):N \<in> (\<parallel>(B2)\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSn_def ntrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(x,za)]" and x="(x):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(x,za)]" and x="(x):Na" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(x,za)]" and x="(x):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "x=ya")
apply(simp)
apply(drule_tac pi="[(ya,za)]" and x="(ya):Na" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "za=ya")
apply(simp)
apply(drule_tac pi="[(x,ya)]" and x="(ya):Na" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(x,za)]" and x="(ya):Na" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac pi="[(xa,za)]" and x="(xa):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "za=xa")
apply(simp)
apply(drule_tac pi="[(x,xa)]" and x="(xa):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(x,za)]" and x="(xa):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(x,za)]" and x="(x):Na" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac pi="[(xa,za)]" and x="(xa):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "za=xa")
apply(simp)
apply(drule_tac pi="[(x,xa)]" and x="(xa):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(x,za)]" and x="(xa):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "x=ya")
apply(simp)
apply(drule_tac pi="[(ya,za)]" and x="(ya):Na" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "za=ya")
apply(simp)
apply(drule_tac pi="[(x,ya)]" and x="(ya):Na" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(x,za)]" and x="(ya):Na" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
done

lemmas CAND_OrL_elim = CAND_OrL_elim_aux[OF NEG_elim(2)]

lemma CAND_AndL1_elim_aux:
  assumes a: "(x):(AndL1 (y).M x) \<in> NEGn B (\<parallel><B>\<parallel>)" "(x):(AndL1 (y).M x) \<notin> BINDINGn B (\<parallel><B>\<parallel>)"
  shows "\<exists>B1 B2. B = B1 AND B2 \<and> (y):M \<in> (\<parallel>(B1)\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSn_def ntrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(x,ya)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac pi="[(xa,ya)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
apply(case_tac "ya=xa")
apply(simp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
apply(drule_tac pi="[(x,ya)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
done

lemmas CAND_AndL1_elim = CAND_AndL1_elim_aux[OF NEG_elim(2)]

lemma CAND_AndL2_elim_aux:
  assumes a: "(x):(AndL2 (y).M x) \<in> NEGn B (\<parallel><B>\<parallel>)" "(x):(AndL2 (y).M x) \<notin> BINDINGn B (\<parallel><B>\<parallel>)"
  shows "\<exists>B1 B2. B = B1 AND B2 \<and> (y):M \<in> (\<parallel>(B2)\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSn_def ntrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(x,ya)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac pi="[(xa,ya)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
apply(case_tac "ya=xa")
apply(simp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
apply(drule_tac pi="[(x,ya)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
done

lemmas CAND_AndL2_elim = CAND_AndL2_elim_aux[OF NEG_elim(2)]

lemma CAND_ImpL_elim_aux:
  assumes a: "(x):(ImpL <a>.M (z).N x) \<in> NEGn B (\<parallel><B>\<parallel>)" "(x):(ImpL <a>.M (z).N x) \<notin> BINDINGn B (\<parallel><B>\<parallel>)"
  shows "\<exists>B1 B2. B = B1 IMP B2 \<and> <a>:M \<in> (\<parallel><B1>\<parallel>) \<and> (z):N \<in> (\<parallel>(B2)\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSn_def ntrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(x,y)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(x,y)]" and x="(x):Na" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(x,y)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac pi="[(xa,y)]" and x="(xa):Na" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "y=xa")
apply(simp)
apply(drule_tac pi="[(x,xa)]" and x="(xa):Na" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(x,y)]" and x="(xa):Na" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
done

lemmas CAND_ImpL_elim = CAND_ImpL_elim_aux[OF NEG_elim(2)]

lemma CAND_ImpR_elim:
  assumes a: "<a>:ImpR (x).<b>.M a \<in> (\<parallel><B>\<parallel>)" "<a>:ImpR (x).<b>.M a \<notin> BINDINGc B (\<parallel>(B)\<parallel>)"
  shows "\<exists>B1 B2. B = B1 IMP B2 \<and> 
                 (\<forall>z P. x\<sharp>(z,P) \<and> (z):P \<in> \<parallel>(B2)\<parallel> \<longrightarrow> (x):(M{b:=(z).P}) \<in> \<parallel>(B1)\<parallel>) \<and>
                 (\<forall>c Q. b\<sharp>(c,Q) \<and> <c>:Q \<in> \<parallel><B1>\<parallel> \<longrightarrow> <b>:(M{x:=<c>.Q}) \<in> \<parallel><B2>\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSc_def ctrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm fresh_prod fresh_bij)
apply(generate_fresh "name") 
apply(generate_fresh "coname")
apply(drule_tac a="ca" and z="c" in alpha_name_coname)
apply(simp) 
apply(simp) 
apply(simp) 
apply(drule_tac x="[(xa,c)]\<bullet>[(aa,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>z" in spec)
apply(drule_tac x="[(xa,c)]\<bullet>[(aa,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>P" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(aa,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="cb" and z="ca" in alpha_name_coname)
apply(simp)
apply(simp)
apply(simp)
apply(drule_tac x="[(xa,ca)]\<bullet>[(aa,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>c" in spec)
apply(drule_tac x="[(xa,ca)]\<bullet>[(aa,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>Q" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(aa,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="ca" and z="c" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,c)]\<bullet>[(ba,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>z" in spec)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,c)]\<bullet>[(ba,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>P" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(ba,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(ba,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="cb" and z="ca" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,ca)]\<bullet>[(ba,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>c" in spec)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,ca)]\<bullet>[(ba,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>Q" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(ba,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(ba,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(case_tac "a=aa")
apply(simp)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="ca" and z="c" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(aa,ba)]\<bullet>[(xa,c)]\<bullet>[(ba,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>z" in spec)
apply(drule_tac x="[(aa,ba)]\<bullet>[(xa,c)]\<bullet>[(ba,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>P" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(ba,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,ba)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,ba)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(ba,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(simp)
apply(case_tac "ba=aa")
apply(simp)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="ca" and z="c" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(a,aa)]\<bullet>[(xa,c)]\<bullet>[(a,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>z" in spec)
apply(drule_tac x="[(a,aa)]\<bullet>[(xa,c)]\<bullet>[(a,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>P" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,aa)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,aa)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(a,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(simp)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="ca" and z="c" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,c)]\<bullet>[(aa,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>z" in spec)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,c)]\<bullet>[(aa,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>P" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(aa,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(case_tac "a=aa")
apply(simp)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="cb" and z="ca" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(aa,ba)]\<bullet>[(xa,ca)]\<bullet>[(ba,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>c" in spec)
apply(drule_tac x="[(aa,ba)]\<bullet>[(xa,ca)]\<bullet>[(ba,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>Q" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(ba,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,ba)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,ba)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(ba,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(simp)
apply(case_tac "ba=aa")
apply(simp)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="cb" and z="ca" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(a,aa)]\<bullet>[(xa,ca)]\<bullet>[(a,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>c" in spec)
apply(drule_tac x="[(a,aa)]\<bullet>[(xa,ca)]\<bullet>[(a,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>Q" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,aa)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,aa)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(a,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(simp)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="cb" and z="ca" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,ca)]\<bullet>[(aa,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>c" in spec)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,ca)]\<bullet>[(aa,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>Q" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(aa,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
done

text \<open>Main lemma 1\<close>

lemma AXIOMS_imply_SNa:
  shows "<a>:M \<in> AXIOMSc B \<Longrightarrow> SNa M"
  and   "(x):M \<in> AXIOMSn B \<Longrightarrow> SNa M"
apply -
apply(auto simp add: AXIOMSn_def AXIOMSc_def ntrm.inject ctrm.inject alpha)
apply(rule Ax_in_SNa)+
done

lemma BINDING_imply_SNa:
  shows "<a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>) \<Longrightarrow> SNa M"
  and   "(x):M \<in> BINDINGn B (\<parallel><B>\<parallel>) \<Longrightarrow> SNa M"
apply -
apply(auto simp add: BINDINGn_def BINDINGc_def ntrm.inject ctrm.inject alpha)
apply(drule_tac x="x" in spec)
apply(drule_tac x="Ax x a" in spec)
apply(drule mp)
apply(rule Ax_in_CANDs)
apply(drule a_star_preserves_SNa)
apply(rule subst_with_ax2)
apply(simp add: crename_id)
apply(drule_tac x="x" in spec)
apply(drule_tac x="Ax x aa" in spec)
apply(drule mp)
apply(rule Ax_in_CANDs)
apply(drule a_star_preserves_SNa)
apply(rule subst_with_ax2)
apply(simp add: crename_id SNa_eqvt)
apply(drule_tac x="a" in spec)
apply(drule_tac x="Ax x a" in spec)
apply(drule mp)
apply(rule Ax_in_CANDs)
apply(drule a_star_preserves_SNa)
apply(rule subst_with_ax1)
apply(simp add: nrename_id)
apply(drule_tac x="a" in spec)
apply(drule_tac x="Ax xa a" in spec)
apply(drule mp)
apply(rule Ax_in_CANDs)
apply(drule a_star_preserves_SNa)
apply(rule subst_with_ax1)
apply(simp add: nrename_id SNa_eqvt)
done

lemma CANDs_imply_SNa:
  shows "<a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> SNa M"
  and   "(x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> SNa M"
proof(induct B arbitrary: a x M rule: ty.induct)
  case (PR X)
  { case 1 
    have "<a>:M \<in> \<parallel><PR X>\<parallel>" by fact
    then have "<a>:M \<in> NEGc (PR X) (\<parallel>(PR X)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (PR X) \<union> BINDINGc (PR X) (\<parallel>(PR X)\<parallel>)" by simp
    moreover
    { assume "<a>:M \<in> AXIOMSc (PR X)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (PR X) (\<parallel>(PR X)\<parallel>)"
      then have "SNa M" by (simp add: BINDING_imply_SNa)
    }
    ultimately show "SNa M" by blast 
  next
    case 2
    have "(x):M \<in> (\<parallel>(PR X)\<parallel>)" by fact
    then have "(x):M \<in> NEGn (PR X) (\<parallel><PR X>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (PR X) \<union> BINDINGn (PR X) (\<parallel><PR X>\<parallel>)" by simp
    moreover
    { assume "(x):M \<in> AXIOMSn (PR X)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (PR X) (\<parallel><PR X>\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
    ultimately show "SNa M" by blast
  }
next
  case (NOT B)
  have ih1: "\<And>a M. <a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih2: "\<And>x M. (x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> SNa M" by fact
  { case 1
    have "<a>:M \<in> (\<parallel><NOT B>\<parallel>)" by fact
    then have "<a>:M \<in> NEGc (NOT B) (\<parallel>(NOT B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (NOT B) \<union> BINDINGc (NOT B) (\<parallel>(NOT B)\<parallel>) \<union> NOTRIGHT (NOT B) (\<parallel>(B)\<parallel>)" by simp
     moreover
    { assume "<a>:M \<in> AXIOMSc (NOT B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (NOT B) (\<parallel>(NOT B)\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "<a>:M \<in> NOTRIGHT (NOT B) (\<parallel>(B)\<parallel>)"
      then obtain x' M' where eq: "M = NotR (x').M' a" and "(x'):M' \<in> (\<parallel>(B)\<parallel>)"
        using NOTRIGHT_elim by blast
      then have "SNa M'" using ih2 by blast
      then have "SNa M" using eq by (simp add: NotR_in_SNa)
    }
    ultimately show "SNa M" by blast
  next
    case 2
    have "(x):M \<in> (\<parallel>(NOT B)\<parallel>)" by fact
    then have "(x):M \<in> NEGn (NOT B) (\<parallel><NOT B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (NOT B) \<union> BINDINGn (NOT B) (\<parallel><NOT B>\<parallel>) \<union> NOTLEFT (NOT B) (\<parallel><B>\<parallel>)" 
      by (simp only: NEGn.simps)
     moreover
    { assume "(x):M \<in> AXIOMSn (NOT B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (NOT B) (\<parallel><NOT B>\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "(x):M \<in> NOTLEFT (NOT B) (\<parallel><B>\<parallel>)"
      then obtain a' M' where eq: "M = NotL <a'>.M' x" and "<a'>:M' \<in> (\<parallel><B>\<parallel>)"
        using NOTLEFT_elim by blast
      then have "SNa M'" using ih1 by blast
      then have "SNa M" using eq by (simp add: NotL_in_SNa)
    }
    ultimately show "SNa M" by blast
  }
next
  case (AND A B)
  have ih1: "\<And>a M. <a>:M \<in> \<parallel><A>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih2: "\<And>x M. (x):M \<in> \<parallel>(A)\<parallel> \<Longrightarrow> SNa M" by fact
  have ih3: "\<And>a M. <a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih4: "\<And>x M. (x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> SNa M" by fact
  { case 1
    have "<a>:M \<in> (\<parallel><A AND B>\<parallel>)" by fact
    then have "<a>:M \<in> NEGc (A AND B) (\<parallel>(A AND B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (A AND B) \<union> BINDINGc (A AND B) (\<parallel>(A AND B)\<parallel>) 
                                  \<union> ANDRIGHT (A AND B) (\<parallel><A>\<parallel>) (\<parallel><B>\<parallel>)" by simp
     moreover
    { assume "<a>:M \<in> AXIOMSc (A AND B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (A AND B) (\<parallel>(A AND B)\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "<a>:M \<in> ANDRIGHT (A AND B) (\<parallel><A>\<parallel>) (\<parallel><B>\<parallel>)"
      then obtain a' M' b' N' where eq: "M = AndR <a'>.M' <b'>.N' a" 
                                and "<a'>:M' \<in> (\<parallel><A>\<parallel>)" and "<b'>:N' \<in> (\<parallel><B>\<parallel>)"
        by (erule_tac ANDRIGHT_elim, blast)
      then have "SNa M'" and "SNa N'" using ih1 ih3 by blast+
      then have "SNa M" using eq by (simp add: AndR_in_SNa)
    }
    ultimately show "SNa M" by blast
  next
    case 2
    have "(x):M \<in> (\<parallel>(A AND B)\<parallel>)" by fact
    then have "(x):M \<in> NEGn (A AND B) (\<parallel><A AND B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (A AND B) \<union> BINDINGn (A AND B) (\<parallel><A AND B>\<parallel>) 
                       \<union> ANDLEFT1 (A AND B) (\<parallel>(A)\<parallel>) \<union> ANDLEFT2 (A AND B) (\<parallel>(B)\<parallel>)" 
      by (simp only: NEGn.simps)
     moreover
    { assume "(x):M \<in> AXIOMSn (A AND B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (A AND B) (\<parallel><A AND B>\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "(x):M \<in> ANDLEFT1 (A AND B) (\<parallel>(A)\<parallel>)"
      then obtain x' M' where eq: "M = AndL1 (x').M' x" and "(x'):M' \<in> (\<parallel>(A)\<parallel>)"
        using ANDLEFT1_elim by blast
      then have "SNa M'" using ih2 by blast
      then have "SNa M" using eq by (simp add: AndL1_in_SNa)
    }
    moreover
    { assume "(x):M \<in> ANDLEFT2 (A AND B) (\<parallel>(B)\<parallel>)"
      then obtain x' M' where eq: "M = AndL2 (x').M' x" and "(x'):M' \<in> (\<parallel>(B)\<parallel>)"
        using ANDLEFT2_elim by blast
      then have "SNa M'" using ih4 by blast
      then have "SNa M" using eq by (simp add: AndL2_in_SNa)
    }
    ultimately show "SNa M" by blast
  }
next
  case (OR A B)
  have ih1: "\<And>a M. <a>:M \<in> \<parallel><A>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih2: "\<And>x M. (x):M \<in> \<parallel>(A)\<parallel> \<Longrightarrow> SNa M" by fact
  have ih3: "\<And>a M. <a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih4: "\<And>x M. (x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> SNa M" by fact
  { case 1
    have "<a>:M \<in> (\<parallel><A OR B>\<parallel>)" by fact
    then have "<a>:M \<in> NEGc (A OR B) (\<parallel>(A OR B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (A OR B) \<union> BINDINGc (A OR B) (\<parallel>(A OR B)\<parallel>) 
                                  \<union> ORRIGHT1 (A OR B) (\<parallel><A>\<parallel>) \<union> ORRIGHT2 (A OR B) (\<parallel><B>\<parallel>)" by simp
     moreover
    { assume "<a>:M \<in> AXIOMSc (A OR B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (A OR B) (\<parallel>(A OR B)\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "<a>:M \<in> ORRIGHT1 (A OR B) (\<parallel><A>\<parallel>)"
      then obtain a' M' where eq: "M = OrR1 <a'>.M' a" 
                                and "<a'>:M' \<in> (\<parallel><A>\<parallel>)" 
        by (erule_tac ORRIGHT1_elim, blast)
      then have "SNa M'" using ih1 by blast
      then have "SNa M" using eq by (simp add: OrR1_in_SNa)
    }
     moreover
    { assume "<a>:M \<in> ORRIGHT2 (A OR B) (\<parallel><B>\<parallel>)"
      then obtain a' M' where eq: "M = OrR2 <a'>.M' a" and "<a'>:M' \<in> (\<parallel><B>\<parallel>)" 
        using ORRIGHT2_elim by blast
      then have "SNa M'" using ih3 by blast
      then have "SNa M" using eq by (simp add: OrR2_in_SNa)
    }
    ultimately show "SNa M" by blast
  next
    case 2
    have "(x):M \<in> (\<parallel>(A OR B)\<parallel>)" by fact
    then have "(x):M \<in> NEGn (A OR B) (\<parallel><A OR B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (A OR B) \<union> BINDINGn (A OR B) (\<parallel><A OR B>\<parallel>) 
                       \<union> ORLEFT (A OR B) (\<parallel>(A)\<parallel>) (\<parallel>(B)\<parallel>)" 
      by (simp only: NEGn.simps)
     moreover
    { assume "(x):M \<in> AXIOMSn (A OR B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (A OR B) (\<parallel><A OR B>\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "(x):M \<in> ORLEFT (A OR B) (\<parallel>(A)\<parallel>) (\<parallel>(B)\<parallel>)"
      then obtain x' M' y' N' where eq: "M = OrL (x').M' (y').N' x" 
                                and "(x'):M' \<in> (\<parallel>(A)\<parallel>)" and  "(y'):N' \<in> (\<parallel>(B)\<parallel>)"
        by (erule_tac ORLEFT_elim, blast)
      then have "SNa M'" and "SNa N'" using ih2 ih4 by blast+
      then have "SNa M" using eq by (simp add: OrL_in_SNa)
    }
    ultimately show "SNa M" by blast
  }
next 
  case (IMP A B)
  have ih1: "\<And>a M. <a>:M \<in> \<parallel><A>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih2: "\<And>x M. (x):M \<in> \<parallel>(A)\<parallel> \<Longrightarrow> SNa M" by fact
  have ih3: "\<And>a M. <a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih4: "\<And>x M. (x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> SNa M" by fact
  { case 1
    have "<a>:M \<in> (\<parallel><A IMP B>\<parallel>)" by fact
    then have "<a>:M \<in> NEGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (A IMP B) \<union> BINDINGc (A IMP B) (\<parallel>(A IMP B)\<parallel>) 
                                  \<union> IMPRIGHT (A IMP B) (\<parallel>(A)\<parallel>) (\<parallel><B>\<parallel>) (\<parallel>(B)\<parallel>) (\<parallel><A>\<parallel>)" by simp
     moreover
    { assume "<a>:M \<in> AXIOMSc (A IMP B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "<a>:M \<in> IMPRIGHT (A IMP B) (\<parallel>(A)\<parallel>) (\<parallel><B>\<parallel>) (\<parallel>(B)\<parallel>) (\<parallel><A>\<parallel>)"
      then obtain x' a' M' where eq: "M = ImpR (x').<a'>.M' a" 
                           and imp: "\<forall>z P. x'\<sharp>(z,P) \<and> (z):P \<in> \<parallel>(B)\<parallel> \<longrightarrow> (x'):(M'{a':=(z).P}) \<in> \<parallel>(A)\<parallel>"    
        by (erule_tac IMPRIGHT_elim, blast)
      obtain z::"name" where fs: "z\<sharp>x'" by (rule_tac exists_fresh, rule fin_supp, blast)
      have "(z):Ax z a'\<in> \<parallel>(B)\<parallel>" by (simp add: Ax_in_CANDs)
      with imp fs have "(x'):(M'{a':=(z).Ax z a'}) \<in> \<parallel>(A)\<parallel>" by (simp add: fresh_prod fresh_atm)
      then have "SNa (M'{a':=(z).Ax z a'})" using ih2 by blast
      moreover 
      have "M'{a':=(z).Ax z a'} \<longrightarrow>\<^sub>a* M'[a'\<turnstile>c>a']" by (simp add: subst_with_ax2)
      ultimately have "SNa (M'[a'\<turnstile>c>a'])" by (simp add: a_star_preserves_SNa)
      then have "SNa M'" by (simp add: crename_id)
      then have "SNa M" using eq by (simp add: ImpR_in_SNa)
    }
    ultimately show "SNa M" by blast
  next
    case 2
    have "(x):M \<in> (\<parallel>(A IMP B)\<parallel>)" by fact
    then have "(x):M \<in> NEGn (A IMP B) (\<parallel><A IMP B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (A IMP B) \<union> BINDINGn (A IMP B) (\<parallel><A IMP B>\<parallel>) 
                       \<union> IMPLEFT (A IMP B) (\<parallel><A>\<parallel>) (\<parallel>(B)\<parallel>)" 
      by (simp only: NEGn.simps)
     moreover
    { assume "(x):M \<in> AXIOMSn (A IMP B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (A IMP B) (\<parallel><A IMP B>\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "(x):M \<in> IMPLEFT (A IMP B) (\<parallel><A>\<parallel>) (\<parallel>(B)\<parallel>)"
      then obtain a' M' y' N' where eq: "M = ImpL <a'>.M' (y').N' x" 
                                and "<a'>:M' \<in> (\<parallel><A>\<parallel>)" and  "(y'):N' \<in> (\<parallel>(B)\<parallel>)"
        by (erule_tac IMPLEFT_elim, blast)
      then have "SNa M'" and "SNa N'" using ih1 ih4 by blast+
      then have "SNa M" using eq by (simp add: ImpL_in_SNa)
    }
    ultimately show "SNa M" by blast
  }
qed 

text \<open>Main lemma 2\<close>

lemma AXIOMS_preserved:
  shows "<a>:M \<in> AXIOMSc B \<Longrightarrow> M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> <a>:M' \<in> AXIOMSc B"
  and   "(x):M \<in> AXIOMSn B \<Longrightarrow> M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> (x):M' \<in> AXIOMSn B"
  apply(simp_all add: AXIOMSc_def AXIOMSn_def)
  apply(auto simp add: ntrm.inject ctrm.inject alpha)
  apply(drule ax_do_not_a_star_reduce)
  apply(auto)
  apply(drule ax_do_not_a_star_reduce)
  apply(auto)
  apply(drule ax_do_not_a_star_reduce)
  apply(auto)
  apply(drule ax_do_not_a_star_reduce)
  apply(auto)
  done  

lemma BINDING_preserved:
  shows "<a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>) \<Longrightarrow> M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> <a>:M' \<in> BINDINGc B (\<parallel>(B)\<parallel>)"
  and   "(x):M \<in> BINDINGn B (\<parallel><B>\<parallel>) \<Longrightarrow> M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> (x):M' \<in> BINDINGn B (\<parallel><B>\<parallel>)"
proof -
  assume red: "M \<longrightarrow>\<^sub>a* M'"
  assume asm: "<a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>)"
  {
    fix x::"name" and  P::"trm"
    from asm have "((x):P) \<in> (\<parallel>(B)\<parallel>) \<Longrightarrow> SNa (M{a:=(x).P})" by (simp add: BINDINGc_elim)
    moreover
    have "M{a:=(x).P} \<longrightarrow>\<^sub>a* M'{a:=(x).P}" using red by (simp add: a_star_subst2)
    ultimately 
    have "((x):P) \<in> (\<parallel>(B)\<parallel>) \<Longrightarrow> SNa (M'{a:=(x).P})" by (simp add: a_star_preserves_SNa)
  }
  then show "<a>:M' \<in> BINDINGc B (\<parallel>(B)\<parallel>)" by (auto simp add: BINDINGc_def)
next
  assume red: "M \<longrightarrow>\<^sub>a* M'"
  assume asm: "(x):M \<in> BINDINGn B (\<parallel><B>\<parallel>)"
  {
    fix c::"coname" and  P::"trm"
    from asm have "(<c>:P) \<in> (\<parallel><B>\<parallel>) \<Longrightarrow> SNa (M{x:=<c>.P})" by (simp add: BINDINGn_elim)
    moreover
    have "M{x:=<c>.P} \<longrightarrow>\<^sub>a* M'{x:=<c>.P}" using red by (simp add: a_star_subst1)
    ultimately 
    have "(<c>:P) \<in> (\<parallel><B>\<parallel>) \<Longrightarrow> SNa (M'{x:=<c>.P})" by (simp add: a_star_preserves_SNa)
  }
  then show "(x):M' \<in> BINDINGn B (\<parallel><B>\<parallel>)" by (auto simp add: BINDINGn_def)
qed
    
lemma CANDs_preserved:
  shows "<a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> <a>:M' \<in> \<parallel><B>\<parallel>"
  and   "(x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> M \<longrightarrow>\<^sub>a* M' \<Longrightarrow> (x):M' \<in> \<parallel>(B)\<parallel>" 
proof(nominal_induct B arbitrary: a x M M' rule: ty.strong_induct) 
  case (PR X)
  { case 1 
    have asm: "M \<longrightarrow>\<^sub>a* M'" by fact
    have "<a>:M \<in> \<parallel><PR X>\<parallel>" by fact
    then have "<a>:M \<in> NEGc (PR X) (\<parallel>(PR X)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (PR X) \<union> BINDINGc (PR X) (\<parallel>(PR X)\<parallel>)" by simp
    moreover
    { assume "<a>:M \<in> AXIOMSc (PR X)"
      then have "<a>:M' \<in> AXIOMSc (PR X)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (PR X) (\<parallel>(PR X)\<parallel>)"
      then have "<a>:M' \<in> BINDINGc (PR X) (\<parallel>(PR X)\<parallel>)" using asm by (simp add: BINDING_preserved)
    }
    ultimately have "<a>:M' \<in> AXIOMSc (PR X) \<union> BINDINGc (PR X) (\<parallel>(PR X)\<parallel>)" by blast
    then have "<a>:M' \<in> NEGc (PR X) (\<parallel>(PR X)\<parallel>)" by simp
    then show "<a>:M' \<in> (\<parallel><PR X>\<parallel>)" using NEG_simp by blast
  next
    case 2
    have asm: "M \<longrightarrow>\<^sub>a* M'" by fact
    have "(x):M \<in> \<parallel>(PR X)\<parallel>" by fact
    then have "(x):M \<in> NEGn (PR X) (\<parallel><PR X>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (PR X) \<union> BINDINGn (PR X) (\<parallel><PR X>\<parallel>)" by simp
    moreover
    { assume "(x):M \<in> AXIOMSn (PR X)"
      then have "(x):M' \<in> AXIOMSn (PR X)" using asm by (simp only: AXIOMS_preserved) 
    }
    moreover
    { assume "(x):M \<in> BINDINGn (PR X) (\<parallel><PR X>\<parallel>)"
      then have "(x):M' \<in> BINDINGn (PR X) (\<parallel><PR X>\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    ultimately have "(x):M' \<in> AXIOMSn (PR X) \<union> BINDINGn (PR X) (\<parallel><PR X>\<parallel>)" by blast
    then have "(x):M' \<in> NEGn (PR X) (\<parallel><PR X>\<parallel>)" by simp
    then show "(x):M' \<in> (\<parallel>(PR X)\<parallel>)" using NEG_simp by blast
  }
next
  case (IMP A B)
  have ih1: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><A>\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><A>\<parallel>" by fact
  have ih2: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(A)\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(A)\<parallel>" by fact
  have ih3: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><B>\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><B>\<parallel>" by fact
  have ih4: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(B)\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(B)\<parallel>" by fact
  { case 1 
    have asm: "M \<longrightarrow>\<^sub>a* M'" by fact
    have "<a>:M \<in> \<parallel><A IMP B>\<parallel>" by fact
    then have "<a>:M \<in> NEGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (A IMP B) \<union> BINDINGc (A IMP B) (\<parallel>(A IMP B)\<parallel>) 
                            \<union> IMPRIGHT (A IMP B) (\<parallel>(A)\<parallel>) (\<parallel><B>\<parallel>) (\<parallel>(B)\<parallel>) (\<parallel><A>\<parallel>)" by simp
    moreover
    { assume "<a>:M \<in> AXIOMSc (A IMP B)"
      then have "<a>:M' \<in> AXIOMSc (A IMP B)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)"
      then have "<a>:M' \<in> BINDINGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "<a>:M \<in> IMPRIGHT (A IMP B) (\<parallel>(A)\<parallel>) (\<parallel><B>\<parallel>) (\<parallel>(B)\<parallel>) (\<parallel><A>\<parallel>)"
      then obtain x' a' N' where eq: "M = ImpR (x').<a'>.N' a" and fic: "fic (ImpR (x').<a'>.N' a) a"
                           and imp1: "\<forall>z P. x'\<sharp>(z,P) \<and> (z):P \<in> \<parallel>(B)\<parallel> \<longrightarrow> (x'):(N'{a':=(z).P}) \<in> \<parallel>(A)\<parallel>" 
                           and imp2: "\<forall>c Q. a'\<sharp>(c,Q) \<and> <c>:Q \<in> \<parallel><A>\<parallel> \<longrightarrow> <a'>:(N'{x':=<c>.Q}) \<in> \<parallel><B>\<parallel>"
        using IMPRIGHT_elim by blast
      from eq asm obtain N'' where eq': "M' = ImpR (x').<a'>.N'' a" and red: "N' \<longrightarrow>\<^sub>a* N''" 
        using a_star_redu_ImpR_elim by (blast)
      from imp1 have "\<forall>z P. x'\<sharp>(z,P) \<and> (z):P \<in> \<parallel>(B)\<parallel> \<longrightarrow> (x'):(N''{a':=(z).P}) \<in> \<parallel>(A)\<parallel>" using red ih2
        apply(auto)
        apply(drule_tac x="z" in spec)
        apply(drule_tac x="P" in spec)
        apply(simp)
        apply(drule_tac a_star_subst2)
        apply(blast)
        done
      moreover
      from imp2 have "\<forall>c Q. a'\<sharp>(c,Q) \<and> <c>:Q \<in> \<parallel><A>\<parallel> \<longrightarrow> <a'>:(N''{x':=<c>.Q}) \<in> \<parallel><B>\<parallel>" using red ih3
        apply(auto)
        apply(drule_tac x="c" in spec)
        apply(drule_tac x="Q" in spec)
        apply(simp)
        apply(drule_tac a_star_subst1)
        apply(blast)
        done
      moreover
      from fic have "fic M' a" using eq asm by (simp add: fic_a_star_reduce)
      ultimately have "<a>:M' \<in> IMPRIGHT (A IMP B) (\<parallel>(A)\<parallel>) (\<parallel><B>\<parallel>) (\<parallel>(B)\<parallel>) (\<parallel><A>\<parallel>)" using eq' by auto
    }
    ultimately have "<a>:M' \<in> AXIOMSc (A IMP B) \<union> BINDINGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)
                                            \<union> IMPRIGHT (A IMP B) (\<parallel>(A)\<parallel>) (\<parallel><B>\<parallel>) (\<parallel>(B)\<parallel>) (\<parallel><A>\<parallel>)" by blast
    then have "<a>:M' \<in> NEGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)" by simp
    then show "<a>:M' \<in> (\<parallel><A IMP B>\<parallel>)" using NEG_simp by blast
  next
    case 2
    have asm: "M \<longrightarrow>\<^sub>a* M'" by fact
    have "(x):M \<in> \<parallel>(A IMP B)\<parallel>" by fact
    then have "(x):M \<in> NEGn (A IMP B) (\<parallel><A IMP B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (A IMP B) \<union> BINDINGn (A IMP B) (\<parallel><A IMP B>\<parallel>) 
                                              \<union> IMPLEFT (A IMP B) (\<parallel><A>\<parallel>) (\<parallel>(B)\<parallel>)" by simp
    moreover
    { assume "(x):M \<in> AXIOMSn (A IMP B)"
      then have "(x):M' \<in> AXIOMSn (A IMP B)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (A IMP B) (\<parallel><A IMP B>\<parallel>)"
      then have "(x):M' \<in> BINDINGn (A IMP B) (\<parallel><A IMP B>\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "(x):M \<in> IMPLEFT (A IMP B) (\<parallel><A>\<parallel>) (\<parallel>(B)\<parallel>)"
      then obtain a' T' y' N' where eq: "M = ImpL <a'>.T' (y').N' x" 
                             and fin: "fin (ImpL <a'>.T' (y').N' x) x"
                             and imp1: "<a'>:T' \<in> \<parallel><A>\<parallel>" and imp2: "(y'):N' \<in> \<parallel>(B)\<parallel>"
        by (erule_tac IMPLEFT_elim, blast)
      from eq asm obtain T'' N'' where eq': "M' = ImpL <a'>.T'' (y').N'' x" 
                                 and red1: "T' \<longrightarrow>\<^sub>a* T''"  and red2: "N' \<longrightarrow>\<^sub>a* N''"
        using a_star_redu_ImpL_elim by blast
      from fin have "fin M' x" using eq asm by (simp add: fin_a_star_reduce)
      moreover
      from imp1 red1 have "<a'>:T'' \<in> \<parallel><A>\<parallel>" using ih1 by simp
      moreover
      from imp2 red2 have "(y'):N'' \<in> \<parallel>(B)\<parallel>" using ih4 by simp
      ultimately have "(x):M' \<in> IMPLEFT (A IMP B) (\<parallel><A>\<parallel>) (\<parallel>(B)\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "(x):M' \<in> AXIOMSn (A IMP B) \<union> BINDINGn (A IMP B) (\<parallel><A IMP B>\<parallel>)
                                              \<union> IMPLEFT (A IMP B) (\<parallel><A>\<parallel>) (\<parallel>(B)\<parallel>)" by blast
    then have "(x):M' \<in> NEGn (A IMP B) (\<parallel><A IMP B>\<parallel>)" by simp
    then show "(x):M' \<in> (\<parallel>(A IMP B)\<parallel>)" using NEG_simp by blast
  }
next
  case (AND A B)
  have ih1: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><A>\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><A>\<parallel>" by fact
  have ih2: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(A)\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(A)\<parallel>" by fact
  have ih3: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><B>\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><B>\<parallel>" by fact
  have ih4: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(B)\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(B)\<parallel>" by fact
  { case 1 
    have asm: "M \<longrightarrow>\<^sub>a* M'" by fact
    have "<a>:M \<in> \<parallel><A AND B>\<parallel>" by fact
    then have "<a>:M \<in> NEGc (A AND B) (\<parallel>(A AND B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (A AND B) \<union> BINDINGc (A AND B) (\<parallel>(A AND B)\<parallel>) 
                                              \<union> ANDRIGHT (A AND B) (\<parallel><A>\<parallel>) (\<parallel><B>\<parallel>)" by simp
    moreover
    { assume "<a>:M \<in> AXIOMSc (A AND B)"
      then have "<a>:M' \<in> AXIOMSc (A AND B)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (A AND B) (\<parallel>(A AND B)\<parallel>)"
      then have "<a>:M' \<in> BINDINGc (A AND B) (\<parallel>(A AND B)\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "<a>:M \<in> ANDRIGHT (A AND B) (\<parallel><A>\<parallel>) (\<parallel><B>\<parallel>)"
      then obtain a' T' b' N' where eq: "M = AndR <a'>.T' <b'>.N' a" 
                              and fic: "fic (AndR <a'>.T' <b'>.N' a) a"
                           and imp1: "<a'>:T' \<in> \<parallel><A>\<parallel>" and imp2: "<b'>:N' \<in> \<parallel><B>\<parallel>"
        using ANDRIGHT_elim by blast
      from eq asm obtain T'' N'' where eq': "M' = AndR <a'>.T'' <b'>.N'' a" 
                          and red1: "T' \<longrightarrow>\<^sub>a* T''" and red2: "N' \<longrightarrow>\<^sub>a* N''" 
        using a_star_redu_AndR_elim by blast
      from fic have "fic M' a" using eq asm by (simp add: fic_a_star_reduce)
      moreover
      from imp1 red1 have "<a'>:T'' \<in> \<parallel><A>\<parallel>" using ih1 by simp
      moreover
      from imp2 red2 have "<b'>:N'' \<in> \<parallel><B>\<parallel>" using ih3 by simp
      ultimately have "<a>:M' \<in> ANDRIGHT (A AND B) (\<parallel><A>\<parallel>) (\<parallel><B>\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "<a>:M' \<in> AXIOMSc (A AND B) \<union> BINDINGc (A AND B) (\<parallel>(A AND B)\<parallel>)
                                              \<union> ANDRIGHT (A AND B) (\<parallel><A>\<parallel>) (\<parallel><B>\<parallel>)" by blast
    then have "<a>:M' \<in> NEGc (A AND B) (\<parallel>(A AND B)\<parallel>)" by simp
    then show "<a>:M' \<in> (\<parallel><A AND B>\<parallel>)" using NEG_simp by blast
  next
    case 2
    have asm: "M \<longrightarrow>\<^sub>a* M'" by fact
    have "(x):M \<in> \<parallel>(A AND B)\<parallel>" by fact
    then have "(x):M \<in> NEGn (A AND B) (\<parallel><A AND B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (A AND B) \<union> BINDINGn (A AND B) (\<parallel><A AND B>\<parallel>) 
                                     \<union> ANDLEFT1 (A AND B) (\<parallel>(A)\<parallel>) \<union> ANDLEFT2 (A AND B) (\<parallel>(B)\<parallel>)" by simp
    moreover
    { assume "(x):M \<in> AXIOMSn (A AND B)"
      then have "(x):M' \<in> AXIOMSn (A AND B)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (A AND B) (\<parallel><A AND B>\<parallel>)"
      then have "(x):M' \<in> BINDINGn (A AND B) (\<parallel><A AND B>\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "(x):M \<in> ANDLEFT1 (A AND B) (\<parallel>(A)\<parallel>)"
      then obtain y' N' where eq: "M = AndL1 (y').N' x" 
                             and fin: "fin (AndL1 (y').N' x) x" and imp: "(y'):N' \<in> \<parallel>(A)\<parallel>"
        by (erule_tac ANDLEFT1_elim, blast)
      from eq asm obtain N'' where eq': "M' = AndL1 (y').N'' x" and red1: "N' \<longrightarrow>\<^sub>a* N''"
        using a_star_redu_AndL1_elim by blast
      from fin have "fin M' x" using eq asm by (simp add: fin_a_star_reduce)
      moreover
      from imp red1 have "(y'):N'' \<in> \<parallel>(A)\<parallel>" using ih2 by simp
      ultimately have "(x):M' \<in> ANDLEFT1 (A AND B) (\<parallel>(A)\<parallel>)" using eq' by (simp, blast) 
    }
     moreover
    { assume "(x):M \<in> ANDLEFT2 (A AND B) (\<parallel>(B)\<parallel>)"
      then obtain y' N' where eq: "M = AndL2 (y').N' x" 
                             and fin: "fin (AndL2 (y').N' x) x" and imp: "(y'):N' \<in> \<parallel>(B)\<parallel>"
        by (erule_tac ANDLEFT2_elim, blast)
      from eq asm obtain N'' where eq': "M' = AndL2 (y').N'' x" and red1: "N' \<longrightarrow>\<^sub>a* N''"
        using a_star_redu_AndL2_elim by blast
      from fin have "fin M' x" using eq asm by (simp add: fin_a_star_reduce)
      moreover
      from imp red1 have "(y'):N'' \<in> \<parallel>(B)\<parallel>" using ih4 by simp
      ultimately have "(x):M' \<in> ANDLEFT2 (A AND B) (\<parallel>(B)\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "(x):M' \<in> AXIOMSn (A AND B) \<union> BINDINGn (A AND B) (\<parallel><A AND B>\<parallel>)
                               \<union> ANDLEFT1 (A AND B) (\<parallel>(A)\<parallel>) \<union> ANDLEFT2 (A AND B) (\<parallel>(B)\<parallel>)" by blast
    then have "(x):M' \<in> NEGn (A AND B) (\<parallel><A AND B>\<parallel>)" by simp
    then show "(x):M' \<in> (\<parallel>(A AND B)\<parallel>)" using NEG_simp by blast
  }
next    
 case (OR A B)
  have ih1: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><A>\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><A>\<parallel>" by fact
  have ih2: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(A)\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(A)\<parallel>" by fact
  have ih3: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><B>\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><B>\<parallel>" by fact
  have ih4: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(B)\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(B)\<parallel>" by fact
  { case 1 
    have asm: "M \<longrightarrow>\<^sub>a* M'" by fact
    have "<a>:M \<in> \<parallel><A OR B>\<parallel>" by fact
    then have "<a>:M \<in> NEGc (A OR B) (\<parallel>(A OR B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (A OR B) \<union> BINDINGc (A OR B) (\<parallel>(A OR B)\<parallel>) 
                          \<union> ORRIGHT1 (A OR B) (\<parallel><A>\<parallel>) \<union> ORRIGHT2 (A OR B) (\<parallel><B>\<parallel>)" by simp
    moreover
    { assume "<a>:M \<in> AXIOMSc (A OR B)"
      then have "<a>:M' \<in> AXIOMSc (A OR B)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (A OR B) (\<parallel>(A OR B)\<parallel>)"
      then have "<a>:M' \<in> BINDINGc (A OR B) (\<parallel>(A OR B)\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "<a>:M \<in> ORRIGHT1 (A OR B) (\<parallel><A>\<parallel>)"
      then obtain a' N' where eq: "M = OrR1 <a'>.N' a" 
                              and fic: "fic (OrR1 <a'>.N' a) a" and imp1: "<a'>:N' \<in> \<parallel><A>\<parallel>"
        using ORRIGHT1_elim by blast
      from eq asm obtain N'' where eq': "M' = OrR1 <a'>.N'' a" and red1: "N' \<longrightarrow>\<^sub>a* N''" 
        using a_star_redu_OrR1_elim by blast
      from fic have "fic M' a" using eq asm by (simp add: fic_a_star_reduce)
      moreover
      from imp1 red1 have "<a'>:N'' \<in> \<parallel><A>\<parallel>" using ih1 by simp
      ultimately have "<a>:M' \<in> ORRIGHT1 (A OR B) (\<parallel><A>\<parallel>)" using eq' by (simp, blast) 
    }
    moreover
    { assume "<a>:M \<in> ORRIGHT2 (A OR B) (\<parallel><B>\<parallel>)"
      then obtain a' N' where eq: "M = OrR2 <a'>.N' a" 
                              and fic: "fic (OrR2 <a'>.N' a) a" and imp1: "<a'>:N' \<in> \<parallel><B>\<parallel>"
        using ORRIGHT2_elim by blast
      from eq asm obtain N'' where eq': "M' = OrR2 <a'>.N'' a" and red1: "N' \<longrightarrow>\<^sub>a* N''" 
        using a_star_redu_OrR2_elim by blast
      from fic have "fic M' a" using eq asm by (simp add: fic_a_star_reduce)
      moreover
      from imp1 red1 have "<a'>:N'' \<in> \<parallel><B>\<parallel>" using ih3 by simp
      ultimately have "<a>:M' \<in> ORRIGHT2 (A OR B) (\<parallel><B>\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "<a>:M' \<in> AXIOMSc (A OR B) \<union> BINDINGc (A OR B) (\<parallel>(A OR B)\<parallel>)
                                \<union> ORRIGHT1 (A OR B) (\<parallel><A>\<parallel>) \<union> ORRIGHT2 (A OR B) (\<parallel><B>\<parallel>)" by blast
    then have "<a>:M' \<in> NEGc (A OR B) (\<parallel>(A OR B)\<parallel>)" by simp
    then show "<a>:M' \<in> (\<parallel><A OR B>\<parallel>)" using NEG_simp by blast
  next
    case 2
    have asm: "M \<longrightarrow>\<^sub>a* M'" by fact
    have "(x):M \<in> \<parallel>(A OR B)\<parallel>" by fact
    then have "(x):M \<in> NEGn (A OR B) (\<parallel><A OR B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (A OR B) \<union> BINDINGn (A OR B) (\<parallel><A OR B>\<parallel>) 
                                     \<union> ORLEFT (A OR B) (\<parallel>(A)\<parallel>) (\<parallel>(B)\<parallel>)" by simp
    moreover
    { assume "(x):M \<in> AXIOMSn (A OR B)"
      then have "(x):M' \<in> AXIOMSn (A OR B)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (A OR B) (\<parallel><A OR B>\<parallel>)"
      then have "(x):M' \<in> BINDINGn (A OR B) (\<parallel><A OR B>\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "(x):M \<in> ORLEFT (A OR B) (\<parallel>(A)\<parallel>) (\<parallel>(B)\<parallel>)"
      then obtain y' T' z' N' where eq: "M = OrL (y').T' (z').N' x" 
                             and fin: "fin (OrL (y').T' (z').N' x) x" 
                             and imp1: "(y'):T' \<in> \<parallel>(A)\<parallel>" and imp2: "(z'):N' \<in> \<parallel>(B)\<parallel>"
        by (erule_tac ORLEFT_elim, blast)
      from eq asm obtain T'' N'' where eq': "M' = OrL (y').T'' (z').N'' x" 
                and red1: "T' \<longrightarrow>\<^sub>a* T''" and red2: "N' \<longrightarrow>\<^sub>a* N''"
        using a_star_redu_OrL_elim by blast
      from fin have "fin M' x" using eq asm by (simp add: fin_a_star_reduce)
      moreover
      from imp1 red1 have "(y'):T'' \<in> \<parallel>(A)\<parallel>" using ih2 by simp
      moreover
      from imp2 red2 have "(z'):N'' \<in> \<parallel>(B)\<parallel>" using ih4 by simp
      ultimately have "(x):M' \<in> ORLEFT (A OR B) (\<parallel>(A)\<parallel>) (\<parallel>(B)\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "(x):M' \<in> AXIOMSn (A OR B) \<union> BINDINGn (A OR B) (\<parallel><A OR B>\<parallel>)
                               \<union> ORLEFT (A OR B) (\<parallel>(A)\<parallel>) (\<parallel>(B)\<parallel>)" by blast
    then have "(x):M' \<in> NEGn (A OR B) (\<parallel><A OR B>\<parallel>)" by simp
    then show "(x):M' \<in> (\<parallel>(A OR B)\<parallel>)" using NEG_simp by blast
  }
next
  case (NOT A)
  have ih1: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><A>\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><A>\<parallel>" by fact
  have ih2: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(A)\<parallel>; M \<longrightarrow>\<^sub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(A)\<parallel>" by fact
  { case 1 
    have asm: "M \<longrightarrow>\<^sub>a* M'" by fact
    have "<a>:M \<in> \<parallel><NOT A>\<parallel>" by fact
    then have "<a>:M \<in> NEGc (NOT A) (\<parallel>(NOT A)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (NOT A) \<union> BINDINGc (NOT A) (\<parallel>(NOT A)\<parallel>) 
                                              \<union> NOTRIGHT (NOT A) (\<parallel>(A)\<parallel>)" by simp
    moreover
    { assume "<a>:M \<in> AXIOMSc (NOT A)"
      then have "<a>:M' \<in> AXIOMSc (NOT A)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (NOT A) (\<parallel>(NOT A)\<parallel>)"
      then have "<a>:M' \<in> BINDINGc (NOT A) (\<parallel>(NOT A)\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "<a>:M \<in> NOTRIGHT (NOT A) (\<parallel>(A)\<parallel>)"
      then obtain y' N' where eq: "M = NotR (y').N' a" 
                              and fic: "fic (NotR (y').N' a) a" and imp: "(y'):N' \<in> \<parallel>(A)\<parallel>"
        using NOTRIGHT_elim by blast
      from eq asm obtain N'' where eq': "M' = NotR (y').N'' a" and red: "N' \<longrightarrow>\<^sub>a* N''" 
        using a_star_redu_NotR_elim by blast
      from fic have "fic M' a" using eq asm by (simp add: fic_a_star_reduce)
      moreover
      from imp red have "(y'):N'' \<in> \<parallel>(A)\<parallel>" using ih2 by simp
      ultimately have "<a>:M' \<in> NOTRIGHT (NOT A) (\<parallel>(A)\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "<a>:M' \<in> AXIOMSc (NOT A) \<union> BINDINGc (NOT A) (\<parallel>(NOT A)\<parallel>)
                                              \<union> NOTRIGHT (NOT A) (\<parallel>(A)\<parallel>)" by blast
    then have "<a>:M' \<in> NEGc (NOT A) (\<parallel>(NOT A)\<parallel>)" by simp
    then show "<a>:M' \<in> (\<parallel><NOT A>\<parallel>)" using NEG_simp by blast
  next
    case 2
    have asm: "M \<longrightarrow>\<^sub>a* M'" by fact
    have "(x):M \<in> \<parallel>(NOT A)\<parallel>" by fact
    then have "(x):M \<in> NEGn (NOT A) (\<parallel><NOT A>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (NOT A) \<union> BINDINGn (NOT A) (\<parallel><NOT A>\<parallel>) 
                                     \<union> NOTLEFT (NOT A) (\<parallel><A>\<parallel>)" by simp
    moreover
    { assume "(x):M \<in> AXIOMSn (NOT A)"
      then have "(x):M' \<in> AXIOMSn (NOT A)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (NOT A) (\<parallel><NOT A>\<parallel>)"
      then have "(x):M' \<in> BINDINGn (NOT A) (\<parallel><NOT A>\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "(x):M \<in> NOTLEFT (NOT A) (\<parallel><A>\<parallel>)"
      then obtain a' N' where eq: "M = NotL <a'>.N' x" 
                             and fin: "fin (NotL <a'>.N' x) x" and imp: "<a'>:N' \<in> \<parallel><A>\<parallel>"
        by (erule_tac NOTLEFT_elim, blast)
      from eq asm obtain N'' where eq': "M' = NotL <a'>.N'' x" and red1: "N' \<longrightarrow>\<^sub>a* N''"
        using a_star_redu_NotL_elim by blast
      from fin have "fin M' x" using eq asm by (simp add: fin_a_star_reduce)
      moreover
      from imp red1 have "<a'>:N'' \<in> \<parallel><A>\<parallel>" using ih1 by simp
      ultimately have "(x):M' \<in> NOTLEFT (NOT A) (\<parallel><A>\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "(x):M' \<in> AXIOMSn (NOT A) \<union> BINDINGn (NOT A) (\<parallel><NOT A>\<parallel>)
                               \<union> NOTLEFT (NOT A) (\<parallel><A>\<parallel>)" by blast
    then have "(x):M' \<in> NEGn (NOT A) (\<parallel><NOT A>\<parallel>)" by simp
    then show "(x):M' \<in> (\<parallel>(NOT A)\<parallel>)" using NEG_simp by blast
  }
qed

lemma CANDs_preserved_single:
  shows "<a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> M \<longrightarrow>\<^sub>a M' \<Longrightarrow> <a>:M' \<in> \<parallel><B>\<parallel>"
  and   "(x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> M \<longrightarrow>\<^sub>a M' \<Longrightarrow> (x):M' \<in> \<parallel>(B)\<parallel>"
by (auto simp add: a_starI CANDs_preserved)

lemma fic_CANDS:
  assumes a: "\<not>fic M a"
  and     b: "<a>:M \<in> \<parallel><B>\<parallel>"
  shows "<a>:M \<in> AXIOMSc B \<or> <a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>)"
using a b
apply(nominal_induct B rule: ty.strong_induct)
apply(simp)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ctrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(auto simp add: calc_atm)[1]
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ctrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(a,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ctrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ctrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
done

lemma fin_CANDS_aux:
  assumes a: "\<not>fin M x"
  and     b: "(x):M \<in> (NEGn B (\<parallel><B>\<parallel>))"
  shows "(x):M \<in> AXIOMSn B \<or> (x):M \<in> BINDINGn B (\<parallel><B>\<parallel>)"
using a b
apply(nominal_induct B rule: ty.strong_induct)
apply(simp)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ntrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(auto simp add: calc_atm)[1]
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ntrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ntrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(x,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ntrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
done

lemma fin_CANDS:
  assumes a: "\<not>fin M x"
  and     b: "(x):M \<in> (\<parallel>(B)\<parallel>)"
  shows "(x):M \<in> AXIOMSn B \<or> (x):M \<in> BINDINGn B (\<parallel><B>\<parallel>)"
apply(rule fin_CANDS_aux)
apply(rule a)
apply(rule NEG_elim)
apply(rule b)
done

lemma BINDING_implies_CAND:
  shows "<c>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>) \<Longrightarrow> <c>:M \<in> (\<parallel><B>\<parallel>)"
  and   "(x):N \<in> BINDINGn B (\<parallel><B>\<parallel>) \<Longrightarrow> (x):N \<in> (\<parallel>(B)\<parallel>)"
apply -
apply(nominal_induct B rule: ty.strong_induct)
apply(auto)
apply(rule NEG_intro)
apply(nominal_induct B rule: ty.strong_induct)
apply(auto)
done

text \<open>3rd Main Lemma\<close>

lemma Cut_a_redu_elim:
  assumes a: "Cut <a>.M (x).N \<longrightarrow>\<^sub>a R"
  shows "(\<exists>M'. R = Cut <a>.M' (x).N \<and> M \<longrightarrow>\<^sub>a M') \<or>
         (\<exists>N'. R = Cut <a>.M (x).N' \<and> N \<longrightarrow>\<^sub>a N') \<or>
         (Cut <a>.M (x).N \<longrightarrow>\<^sub>c R) \<or>
         (Cut <a>.M (x).N \<longrightarrow>\<^sub>l R)"
  using a
  apply(erule_tac a_redu.cases)
                  apply(simp_all)
   apply(simp_all add: trm.inject)
   apply(rule disjI1)
   apply(auto simp add: alpha)[1]
    apply(rule_tac x="[(a,aa)]\<bullet>M'" in exI)
    apply(perm_simp add: fresh_left calc_atm a_redu.eqvt fresh_a_redu)
   apply(rule_tac x="[(a,aa)]\<bullet>M'" in exI)
   apply(perm_simp add: fresh_left calc_atm a_redu.eqvt fresh_a_redu)
  apply(rule disjI2)
  apply(rule disjI1)
  apply(auto simp add: alpha)[1]
   apply(rule_tac x="[(x,xa)]\<bullet>N'" in exI)
   apply(perm_simp add: fresh_left calc_atm a_redu.eqvt fresh_a_redu)
  apply(rule_tac x="[(x,xa)]\<bullet>N'" in exI)
  apply(perm_simp add: fresh_left calc_atm a_redu.eqvt fresh_a_redu)
  done

lemma Cut_c_redu_elim:
  assumes a: "Cut <a>.M (x).N \<longrightarrow>\<^sub>c R"
  shows "(R = M{a:=(x).N} \<and> \<not>fic M a) \<or>
         (R = N{x:=<a>.M} \<and> \<not>fin N x)"
  using a
  apply(erule_tac c_redu.cases)
   apply(simp_all)
   apply(simp_all add: trm.inject)
   apply(rule disjI1)
   apply(auto simp add: alpha)[1]
       apply(simp add: subst_rename fresh_atm)
      apply(simp add: subst_rename fresh_atm)
     apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
     apply(perm_simp)
    apply(simp add: subst_rename fresh_atm fresh_prod)
   apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
   apply(perm_simp)
  apply(rule disjI2)
  apply(auto simp add: alpha)[1]
      apply(simp add: subst_rename fresh_atm)
     apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
     apply(perm_simp)
    apply(simp add: subst_rename fresh_atm fresh_prod)
   apply(simp add: subst_rename fresh_atm fresh_prod)
  apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
  apply(perm_simp)
  done

lemma not_fic_crename_aux:
  assumes a: "fic M c" "c\<sharp>(a,b)"
  shows "fic (M[a\<turnstile>c>b]) c" 
  using a
  apply(nominal_induct M avoiding: c a b rule: trm.strong_induct)
             apply(auto dest!: fic_elims intro!: fic.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh)
  done

lemma not_fic_crename:
  assumes a: "\<not>(fic (M[a\<turnstile>c>b]) c)" "c\<sharp>(a,b)"
  shows "\<not>(fic M c)" 
  using a
  apply(auto dest:  not_fic_crename_aux)
  done

lemma not_fin_crename_aux:
  assumes a: "fin M y"
  shows "fin (M[a\<turnstile>c>b]) y" 
  using a
  apply(nominal_induct M avoiding: a b rule: trm.strong_induct)
             apply(auto dest!: fin_elims intro!: fin.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh)
  done

lemma not_fin_crename:
  assumes a: "\<not>(fin (M[a\<turnstile>c>b]) y)" 
  shows "\<not>(fin M y)" 
  using a
  apply(auto dest:  not_fin_crename_aux)
  done

lemma crename_fresh_interesting1:
  fixes c::"coname"
  assumes a: "c\<sharp>(M[a\<turnstile>c>b])" "c\<sharp>(a,b)"
  shows "c\<sharp>M"
  using a
  apply(nominal_induct M avoiding: c a b rule: trm.strong_induct)
             apply(auto split: if_splits simp add: abs_fresh)
  done

lemma crename_fresh_interesting2:
  fixes x::"name"
  assumes a: "x\<sharp>(M[a\<turnstile>c>b])" 
  shows "x\<sharp>M"
  using a
  apply(nominal_induct M avoiding: x a b rule: trm.strong_induct)
             apply(auto split: if_splits simp add: abs_fresh abs_supp fin_supp fresh_atm)
  done


lemma fic_crename:
  assumes a: "fic (M[a\<turnstile>c>b]) c" "c\<sharp>(a,b)"
  shows "fic M c" 
  using a
  apply(nominal_induct M avoiding: c a b rule: trm.strong_induct)
             apply(auto dest!: fic_elims intro!: fic.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh
      split: if_splits)
       apply(auto dest: crename_fresh_interesting1 simp add: fresh_prod fresh_atm)
  done

lemma fin_crename:
  assumes a: "fin (M[a\<turnstile>c>b]) x"
  shows "fin M x" 
  using a
  apply(nominal_induct M avoiding: x a b rule: trm.strong_induct)
             apply(auto dest!: fin_elims intro!: fin.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh
      split: if_splits)
        apply(auto dest: crename_fresh_interesting2 simp add: fresh_prod fresh_atm)
  done

lemma crename_Cut:
  assumes a: "R[a\<turnstile>c>b] = Cut <c>.M (x).N" "c\<sharp>(a,b,N,R)" "x\<sharp>(M,R)"
  shows "\<exists>M' N'. R = Cut <c>.M' (x).N' \<and> M'[a\<turnstile>c>b] = M \<and> N'[a\<turnstile>c>b] = N \<and> c\<sharp>N' \<and> x\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: a b c x M N rule: trm.strong_induct)
             apply(auto split: if_splits)
  apply(simp add: trm.inject)
  apply(auto simp add: alpha)
    apply(rule_tac x="[(name,x)]\<bullet>trm2" in exI)
    apply(perm_simp)
    apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
    apply(drule sym)
    apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
    apply(simp add: eqvts calc_atm)
   apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
   apply(auto simp add: fresh_atm)[1]
  apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule_tac x="[(name,x)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  apply(auto simp add: fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_NotR:
  assumes a: "R[a\<turnstile>c>b] = NotR (x).N c" "x\<sharp>R" "c\<sharp>(a,b)"
  shows "\<exists>N'. (R = NotR (x).N' c) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b c x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(name,x)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_NotR':
  assumes a: "R[a\<turnstile>c>b] = NotR (x).N c" "x\<sharp>R" "c\<sharp>a"
  shows "(\<exists>N'. (R = NotR (x).N' c) \<and> N'[a\<turnstile>c>b] = N) \<or> (\<exists>N'. (R = NotR (x).N' a) \<and> b=c \<and> N'[a\<turnstile>c>b] = N)"
  using a
  apply(nominal_induct R avoiding: a b c x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_fresh alpha trm.inject)
   apply(rule_tac x="[(name,x)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(name,x)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_NotR_aux:
  assumes a: "R[a\<turnstile>c>b] = NotR (x).N c" 
  shows "(a=c \<and> a=b) \<or> (a\<noteq>c)" 
  using a
  apply(nominal_induct R avoiding: a b c x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma crename_NotL:
  assumes a: "R[a\<turnstile>c>b] = NotL <c>.N y" "c\<sharp>(R,a,b)"
  shows "\<exists>N'. (R = NotL <c>.N' y) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b c y N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(coname,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_AndL1:
  assumes a: "R[a\<turnstile>c>b] = AndL1 (x).N y" "x\<sharp>R"
  shows "\<exists>N'. (R = AndL1 (x).N' y) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b x y N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(name1,x)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_AndL2:
  assumes a: "R[a\<turnstile>c>b] = AndL2 (x).N y" "x\<sharp>R"
  shows "\<exists>N'. (R = AndL2 (x).N' y) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b x y N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(name1,x)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_AndR_aux:
  assumes a: "R[a\<turnstile>c>b] = AndR <c>.M <d>.N e" 
  shows "(a=e \<and> a=b) \<or> (a\<noteq>e)" 
  using a
  apply(nominal_induct R avoiding: a b c d e M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma crename_AndR:
  assumes a: "R[a\<turnstile>c>b] = AndR <c>.M <d>.N e" "c\<sharp>(a,b,d,e,N,R)" "d\<sharp>(a,b,c,e,M,R)" "e\<sharp>(a,b)"
  shows "\<exists>M' N'. R = AndR <c>.M' <d>.N' e \<and> M'[a\<turnstile>c>b] = M \<and> N'[a\<turnstile>c>b] = N \<and> c\<sharp>N' \<and> d\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: a b c d e M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha)
        apply(simp add: fresh_atm fresh_prod)
       apply(rule_tac x="[(coname2,d)]\<bullet>trm2" in exI)
       apply(perm_simp)
       apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
      apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
      apply(perm_simp)
      apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
     apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
     apply(perm_simp)
     apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
    apply(rule_tac x="[(coname2,d)]\<bullet>trm2" in exI)
    apply(perm_simp)
    apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(coname2,d)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[a\<turnstile>c>b]" in  sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_AndR':
  assumes a: "R[a\<turnstile>c>b] = AndR <c>.M <d>.N e" "c\<sharp>(a,b,d,e,N,R)" "d\<sharp>(a,b,c,e,M,R)" "e\<sharp>a"
  shows "(\<exists>M' N'. R = AndR <c>.M' <d>.N' e \<and> M'[a\<turnstile>c>b] = M \<and> N'[a\<turnstile>c>b] = N \<and> c\<sharp>N' \<and> d\<sharp>M') \<or>
         (\<exists>M' N'. R = AndR <c>.M' <d>.N' a \<and> b=e \<and> M'[a\<turnstile>c>b] = M \<and> N'[a\<turnstile>c>b] = N \<and> c\<sharp>N' \<and> d\<sharp>M')"
  using a [[simproc del: defined_all]]
  apply(nominal_induct R avoiding: a b c d e M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha)[1]
            apply(auto split: if_splits simp add: trm.inject alpha)[1]
           apply(auto split: if_splits simp add: trm.inject alpha)[1]
          apply(auto split: if_splits simp add: trm.inject alpha)[1]
         apply(simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm trm.inject alpha)[1]
         apply(case_tac "coname3=a")
          apply(simp)
          apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
          apply(perm_simp)
          apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
          apply(rule_tac x="[(coname2,d)]\<bullet>trm2" in exI)
          apply(perm_simp)
          apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm trm.inject alpha split: if_splits)[1]
           apply(drule sym)
           apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
           apply(simp add: eqvts calc_atm)
          apply(drule_tac s="trm2[a\<turnstile>c>e]" in  sym)
          apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
          apply(simp add: eqvts calc_atm)
         apply(simp)
         apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
         apply(perm_simp)
         apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
         apply(rule_tac x="[(coname2,d)]\<bullet>trm2" in exI)
         apply(perm_simp)
         apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm trm.inject alpha split: if_splits)[1]
          apply(drule sym)
          apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
          apply(simp add: eqvts calc_atm)
         apply(drule_tac s="trm2[a\<turnstile>c>b]" in  sym)
         apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
         apply(simp add: eqvts calc_atm)
        apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma crename_OrR1_aux:
  assumes a: "R[a\<turnstile>c>b] = OrR1 <c>.M e" 
  shows "(a=e \<and> a=b) \<or> (a\<noteq>e)" 
  using a
  apply(nominal_induct R avoiding: a b c e M rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma crename_OrR1:
  assumes a: "R[a\<turnstile>c>b] = OrR1 <c>.N d" "c\<sharp>(R,a,b)" "d\<sharp>(a,b)"
  shows "\<exists>N'. (R = OrR1 <c>.N' d) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_OrR1':
  assumes a: "R[a\<turnstile>c>b] = OrR1 <c>.N d" "c\<sharp>(R,a,b)" "d\<sharp>a"
  shows "(\<exists>N'. (R = OrR1 <c>.N' d) \<and> N'[a\<turnstile>c>b] = N) \<or>
         (\<exists>N'. (R = OrR1 <c>.N' a) \<and> b=d \<and> N'[a\<turnstile>c>b] = N)" 
  using a
  apply(nominal_induct R avoiding: a b c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
   apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_OrR2_aux:
  assumes a: "R[a\<turnstile>c>b] = OrR2 <c>.M e" 
  shows "(a=e \<and> a=b) \<or> (a\<noteq>e)" 
  using a
  apply(nominal_induct R avoiding: a b c e M rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma crename_OrR2:
  assumes a: "R[a\<turnstile>c>b] = OrR2 <c>.N d" "c\<sharp>(R,a,b)" "d\<sharp>(a,b)"
  shows "\<exists>N'. (R = OrR2 <c>.N' d) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_OrR2':
  assumes a: "R[a\<turnstile>c>b] = OrR2 <c>.N d" "c\<sharp>(R,a,b)" "d\<sharp>a"
  shows "(\<exists>N'. (R = OrR2 <c>.N' d) \<and> N'[a\<turnstile>c>b] = N) \<or>
         (\<exists>N'. (R = OrR2 <c>.N' a) \<and> b=d \<and> N'[a\<turnstile>c>b] = N)" 
  using a
  apply(nominal_induct R avoiding: a b c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
   apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_OrL:
  assumes a: "R[a\<turnstile>c>b] = OrL (x).M (y).N z" "x\<sharp>(y,z,N,R)" "y\<sharp>(x,z,M,R)"
  shows "\<exists>M' N'. R = OrL (x).M' (y).N' z \<and> M'[a\<turnstile>c>b] = M \<and> N'[a\<turnstile>c>b] = N \<and> x\<sharp>N' \<and> y\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: a b x y z M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha)
    apply(rule_tac x="[(name2,y)]\<bullet>trm2" in exI)
    apply(perm_simp)
    apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(rule_tac x="[(name1,x)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(name1,x)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(name2,y)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[a\<turnstile>c>b]" in  sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_ImpL:
  assumes a: "R[a\<turnstile>c>b] = ImpL <c>.M (y).N z" "c\<sharp>(a,b,N,R)" "y\<sharp>(z,M,R)"
  shows "\<exists>M' N'. R = ImpL <c>.M' (y).N' z \<and> M'[a\<turnstile>c>b] = M \<and> N'[a\<turnstile>c>b] = N \<and> c\<sharp>N' \<and> y\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: a b c y z M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha)
    apply(rule_tac x="[(name1,y)]\<bullet>trm2" in exI)
    apply(perm_simp)
    apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(name1,y)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[a\<turnstile>c>b]" in  sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_ImpR_aux:
  assumes a: "R[a\<turnstile>c>b] = ImpR (x).<c>.M e" 
  shows "(a=e \<and> a=b) \<or> (a\<noteq>e)" 
  using a
  apply(nominal_induct R avoiding: x a b c e M rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma crename_ImpR:
  assumes a: "R[a\<turnstile>c>b] = ImpR (x).<c>.N d" "c\<sharp>(R,a,b)" "d\<sharp>(a,b)" "x\<sharp>R" 
  shows "\<exists>N'. (R = ImpR (x).<c>.N' d) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b x c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_perm alpha abs_fresh trm.inject)
   apply(rule_tac x="[(name,x)]\<bullet>trm" in exI)
   apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule_tac x="[(name,x)]\<bullet>[(coname1, c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_supp fin_supp abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_ImpR':
  assumes a: "R[a\<turnstile>c>b] = ImpR (x).<c>.N d" "c\<sharp>(R,a,b)" "x\<sharp>R" "d\<sharp>a"
  shows "(\<exists>N'. (R = ImpR (x).<c>.N' d) \<and> N'[a\<turnstile>c>b] = N) \<or>
         (\<exists>N'. (R = ImpR (x).<c>.N' a) \<and> b=d \<and> N'[a\<turnstile>c>b] = N)" 
  using a
  apply(nominal_induct R avoiding: x a b c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject abs_perm calc_atm)
   apply(rule_tac x="[(name,x)]\<bullet>[(coname1,c)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod abs_supp fin_supp)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(name,x)]\<bullet>[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod abs_supp fin_supp)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_ax2:
  assumes a: "N[a\<turnstile>c>b] = Ax x c"
  shows "\<exists>d. N = Ax x d"
  using a
  apply(nominal_induct N avoiding: a b rule: trm.strong_induct)
             apply(auto split: if_splits)
  apply(simp add: trm.inject)
  done

lemma crename_interesting1:
  assumes a: "distinct [a,b,c]"
  shows "M[a\<turnstile>c>c][c\<turnstile>c>b] = M[c\<turnstile>c>b][a\<turnstile>c>b]"
  using a
  apply(nominal_induct M avoiding: a c b rule: trm.strong_induct)
             apply(auto simp add: rename_fresh simp add: trm.inject alpha)
     apply(blast)
    apply(rotate_tac 12)
    apply(drule_tac x="a" in meta_spec)
    apply(rotate_tac 15)
    apply(drule_tac x="c" in meta_spec)
    apply(rotate_tac 15)
    apply(drule_tac x="b" in meta_spec)
    apply(blast)
   apply(blast)
  apply(blast)
  done

lemma crename_interesting2:
  assumes a: "a\<noteq>c" "a\<noteq>d" "a\<noteq>b" "c\<noteq>d" "b\<noteq>c"
  shows "M[a\<turnstile>c>b][c\<turnstile>c>d] = M[c\<turnstile>c>d][a\<turnstile>c>b]"
  using a
  apply(nominal_induct M avoiding: a c b d rule: trm.strong_induct)
             apply(auto simp add: rename_fresh simp add: trm.inject alpha)
  done

lemma crename_interesting3:
  shows "M[a\<turnstile>c>c][x\<turnstile>n>y] = M[x\<turnstile>n>y][a\<turnstile>c>c]"
  apply(nominal_induct M avoiding: a c x y rule: trm.strong_induct)
             apply(auto simp add: rename_fresh simp add: trm.inject alpha)
  done

lemma crename_credu:
  assumes a: "(M[a\<turnstile>c>b]) \<longrightarrow>\<^sub>c M'"
  shows "\<exists>M0. M0[a\<turnstile>c>b]=M' \<and> M \<longrightarrow>\<^sub>c M0"
  using a
  apply(nominal_induct M\<equiv>"M[a\<turnstile>c>b]" M' avoiding: M a b rule: c_redu.strong_induct)
   apply(drule sym)
   apply(drule crename_Cut)
     apply(simp)
    apply(simp)
   apply(auto)
   apply(rule_tac x="M'{a:=(x).N'}" in exI)
   apply(rule conjI)
    apply(simp add: fresh_atm abs_fresh subst_comm fresh_prod)
   apply(rule c_redu.intros)
     apply(auto dest: not_fic_crename)[1]
    apply(simp add: abs_fresh)
   apply(simp add: abs_fresh)
  apply(drule sym)
  apply(drule crename_Cut)
    apply(simp)
   apply(simp)
  apply(auto)
  apply(rule_tac x="N'{x:=<a>.M'}" in exI)
  apply(rule conjI)
   apply(simp add: fresh_atm abs_fresh subst_comm fresh_prod)
  apply(rule c_redu.intros)
    apply(auto dest: not_fin_crename)[1]
   apply(simp add: abs_fresh)
  apply(simp add: abs_fresh)
  done

lemma crename_lredu:
  assumes a: "(M[a\<turnstile>c>b]) \<longrightarrow>\<^sub>l M'"
  shows "\<exists>M0. M0[a\<turnstile>c>b]=M' \<and> M \<longrightarrow>\<^sub>l M0"
  using a
  apply(nominal_induct M\<equiv>"M[a\<turnstile>c>b]" M' avoiding: M a b rule: l_redu.strong_induct)
         apply(drule sym)
         apply(drule crename_Cut)
           apply(simp add: fresh_prod fresh_atm)
          apply(simp)
         apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
         apply(case_tac "aa=ba")
          apply(simp add: crename_id)
          apply(rule l_redu.intros)
            apply(simp)
           apply(simp add: fresh_atm)
          apply(assumption)
         apply(frule crename_ax2)
         apply(auto)[1]
         apply(case_tac "d=aa")
          apply(simp add: trm.inject)
          apply(rule_tac x="M'[a\<turnstile>c>aa]" in exI)
          apply(rule conjI)
           apply(rule crename_interesting1)
           apply(simp)
          apply(rule l_redu.intros)
            apply(simp)
           apply(simp add: fresh_atm)
          apply(auto dest: fic_crename simp add: fresh_prod fresh_atm)[1]
         apply(simp add: trm.inject)
         apply(rule_tac x="M'[a\<turnstile>c>b]" in exI)
         apply(rule conjI)
          apply(rule crename_interesting2)
              apply(simp)
             apply(simp)
            apply(simp)
           apply(simp)
          apply(simp)
         apply(rule l_redu.intros)
           apply(simp)
          apply(simp add: fresh_atm)
         apply(auto dest: fic_crename simp add: fresh_prod fresh_atm)[1]
        apply(drule sym)
        apply(drule crename_Cut)
          apply(simp add: fresh_prod fresh_atm)
         apply(simp add: fresh_prod fresh_atm)
        apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
        apply(case_tac "aa=b")
         apply(simp add: crename_id)
         apply(rule l_redu.intros)
           apply(simp)
          apply(simp add: fresh_atm)
         apply(assumption)
        apply(frule crename_ax2)
        apply(auto)[1]
        apply(case_tac "d=aa")
         apply(simp add: trm.inject)
        apply(simp add: trm.inject)
        apply(rule_tac x="N'[x\<turnstile>n>y]" in exI)
        apply(rule conjI)
         apply(rule sym)
         apply(rule crename_interesting3)
        apply(rule l_redu.intros)
          apply(simp)
         apply(simp add: fresh_atm)
        apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
    (* LNot *)
       apply(drule sym)
       apply(drule crename_Cut)
         apply(simp add: fresh_prod abs_fresh fresh_atm)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
       apply(drule crename_NotR)
         apply(simp add: fresh_prod abs_fresh fresh_atm)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
       apply(drule crename_NotL)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
       apply(rule_tac x="Cut <b>.N'b (x).N'a" in exI)
       apply(simp add: fresh_atm)[1]
       apply(rule l_redu.intros)
            apply(auto simp add: fresh_prod intro: crename_fresh_interesting2)[1]
           apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting2)[1]
          apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
         apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
        apply(simp add: fresh_atm)
       apply(simp add: fresh_atm)
    (* LAnd1 *)
      apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
      apply(drule sym)
      apply(drule crename_Cut)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(auto)[1]
      apply(drule crename_AndR)
         apply(simp add: fresh_prod abs_fresh fresh_atm)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
      apply(drule crename_AndL1)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
      apply(rule_tac x="Cut <a1>.M'a (x).N'a" in exI)
      apply(simp add: fresh_atm)[1]
      apply(rule l_redu.intros)
           apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: crename_fresh_interesting1)[1]
          apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting2)[1]
         apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
        apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
       apply(simp add: fresh_atm)
      apply(simp add: fresh_atm)
    (* LAnd2 *)
     apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
     apply(drule sym)
     apply(drule crename_Cut)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(auto)[1]
     apply(drule crename_AndR)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
     apply(drule crename_AndL2)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
     apply(rule_tac x="Cut <a2>.N'b (x).N'a" in exI)
     apply(simp add: fresh_atm)[1]
     apply(rule l_redu.intros)
          apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: crename_fresh_interesting1)[1]
         apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting2)[1]
        apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
       apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
      apply(simp add: fresh_atm)
     apply(simp add: fresh_atm)
    (* LOr1 *)
    apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
    apply(drule sym)
    apply(drule crename_Cut)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(auto)[1]
    apply(drule crename_OrL)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
    apply(drule crename_OrR1)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
    apply(auto)
    apply(rule_tac x="Cut <a>.N' (x1).M'a" in exI)
    apply(rule conjI)
     apply(simp add: abs_fresh fresh_atm)[1]
    apply(rule l_redu.intros)
         apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: crename_fresh_interesting1)[1]
        apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting2)[1]
       apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
      apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
     apply(simp add: fresh_atm)
    apply(simp add: fresh_atm)
    (* LOr2 *)
   apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule crename_Cut)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(auto)[1]
   apply(drule crename_OrL)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
   apply(drule crename_OrR2)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
   apply(auto)
   apply(rule_tac x="Cut <a>.N' (x2).N'a" in exI)
   apply(rule conjI)
    apply(simp add: abs_fresh fresh_atm)[1]
   apply(rule l_redu.intros)
        apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: crename_fresh_interesting1)[1]
       apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting2)[1]
      apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
     apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
    apply(simp add: fresh_atm)
   apply(simp add: fresh_atm)
    (* ImpL *)
  apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
  apply(drule sym)
  apply(drule crename_Cut)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(simp add: fresh_prod abs_fresh fresh_atm abs_supp fin_supp)
  apply(auto)[1]
  apply(drule crename_ImpL)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(simp add: fresh_prod abs_fresh fresh_atm)
  apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
  apply(drule crename_ImpR)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(simp)
  apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
  apply(rule_tac x="Cut <a>.(Cut <c>.M'a (x).N') (y).N'a" in exI)
  apply(rule conjI)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
  apply(rule l_redu.intros)
       apply(auto simp add: fresh_atm abs_fresh abs_supp fin_supp fresh_prod intro: crename_fresh_interesting2)[1]
      apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: crename_fresh_interesting1)[1]
     apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: crename_fresh_interesting2)[1]
    apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: crename_fresh_interesting1)[1]
   apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: crename_fresh_interesting1)[1]
  apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: crename_fresh_interesting1)[1]
  done

lemma crename_aredu:
  assumes a: "(M[a\<turnstile>c>b]) \<longrightarrow>\<^sub>a M'" "a\<noteq>b"
  shows "\<exists>M0. M0[a\<turnstile>c>b]=M' \<and> M \<longrightarrow>\<^sub>a M0"
  using a
  apply(nominal_induct "M[a\<turnstile>c>b]" M' avoiding: M a b rule: a_redu.strong_induct)
                  apply(drule  crename_lredu)
                  apply(blast)
                 apply(drule  crename_credu)
                 apply(blast)
    (* Cut *)
                apply(drule sym)
                apply(drule crename_Cut)
                  apply(simp)
                 apply(simp)
                apply(auto)[1]
                apply(drule_tac x="M'a" in meta_spec)
                apply(drule_tac x="aa" in meta_spec)
                apply(drule_tac x="b" in meta_spec)
                apply(auto)[1]
                apply(rule_tac x="Cut <a>.M0 (x).N'" in exI)
                apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
                apply(rule conjI)
                 apply(rule trans)
                  apply(rule crename.simps)
                   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
                  apply(drule crename_fresh_interesting2)
                  apply(simp add: fresh_a_redu)
                 apply(simp)
                apply(auto)[1]
               apply(drule sym)
               apply(drule crename_Cut)
                 apply(simp)
                apply(simp)
               apply(auto)[1]
               apply(drule_tac x="N'a" in meta_spec)
               apply(drule_tac x="aa" in meta_spec)
               apply(drule_tac x="b" in meta_spec)
               apply(auto)[1]
               apply(rule_tac x="Cut <a>.M' (x).M0" in exI)
               apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
               apply(rule conjI)
                apply(rule trans)
                 apply(rule crename.simps)
                  apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
                  apply(drule crename_fresh_interesting1)
                   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
                  apply(simp add: fresh_a_redu)
                 apply(simp)
                apply(simp)
               apply(auto)[1]
    (* NotL *)
              apply(drule sym)
              apply(drule crename_NotL)
               apply(simp)
              apply(auto)[1]
              apply(drule_tac x="N'" in meta_spec)
              apply(drule_tac x="aa" in meta_spec)
              apply(drule_tac x="b" in meta_spec)
              apply(auto)[1]
              apply(rule_tac x="NotL <a>.M0 x" in exI)
              apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
              apply(auto)[1]
    (* NotR *)
             apply(drule sym)
             apply(frule crename_NotR_aux)
             apply(erule disjE)
              apply(auto)[1]
             apply(drule crename_NotR')
               apply(simp)
              apply(simp add: fresh_atm)
             apply(erule disjE)
              apply(auto)[1]
              apply(drule_tac x="N'" in meta_spec)
              apply(drule_tac x="aa" in meta_spec)
              apply(drule_tac x="b" in meta_spec)
              apply(auto)[1]
              apply(rule_tac x="NotR (x).M0 a" in exI)
              apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
              apply(auto)[1]
             apply(auto)[1]
             apply(drule_tac x="N'" in meta_spec)
             apply(drule_tac x="aa" in meta_spec)
             apply(drule_tac x="a" in meta_spec)
             apply(auto)[1]
             apply(rule_tac x="NotR (x).M0 aa" in exI)
             apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
             apply(auto)[1]
    (* AndR *)
            apply(drule sym)
            apply(frule crename_AndR_aux)
            apply(erule disjE)
             apply(auto)[1]
            apply(drule crename_AndR')
               apply(simp add: fresh_prod fresh_atm)
              apply(simp add: fresh_atm)
             apply(simp add: fresh_atm)
            apply(erule disjE)
             apply(auto)[1]
             apply(drule_tac x="M'a" in meta_spec)
             apply(drule_tac x="aa" in meta_spec)
             apply(drule_tac x="ba" in meta_spec)
             apply(auto)[1]
             apply(rule_tac x="AndR <a>.M0 <b>.N' c" in exI)
             apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
             apply(auto)[1]
             apply(rule trans)
              apply(rule crename.simps)
                apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
               apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
               apply(auto intro: fresh_a_redu)[1]
              apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
             apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(auto)[1]
            apply(drule_tac x="M'a" in meta_spec)
            apply(drule_tac x="aa" in meta_spec)
            apply(drule_tac x="c" in meta_spec)
            apply(auto)[1]
            apply(rule_tac x="AndR <a>.M0 <b>.N' aa" in exI)
            apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(auto)[1]
            apply(rule trans)
             apply(rule crename.simps)
               apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
              apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
              apply(auto intro: fresh_a_redu)[1]
             apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(drule sym)
           apply(frule crename_AndR_aux)
           apply(erule disjE)
            apply(auto)[1]
           apply(drule crename_AndR')
              apply(simp add: fresh_prod fresh_atm)
             apply(simp add: fresh_atm)
            apply(simp add: fresh_atm)
           apply(erule disjE)
            apply(auto)[1]
            apply(drule_tac x="N'a" in meta_spec)
            apply(drule_tac x="aa" in meta_spec)
            apply(drule_tac x="ba" in meta_spec)
            apply(auto)[1]
            apply(rule_tac x="AndR <a>.M' <b>.M0 c" in exI)
            apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(auto)[1]
            apply(rule trans)
             apply(rule crename.simps)
               apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
               apply(auto intro: fresh_a_redu)[1]
              apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
             apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(auto)[1]
           apply(drule_tac x="N'a" in meta_spec)
           apply(drule_tac x="aa" in meta_spec)
           apply(drule_tac x="c" in meta_spec)
           apply(auto)[1]
           apply(rule_tac x="AndR <a>.M' <b>.M0 aa" in exI)
           apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(auto)[1]
           apply(rule trans)
            apply(rule crename.simps)
              apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
              apply(auto intro: fresh_a_redu)[1]
             apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(simp)
    (* AndL1 *)
          apply(drule sym)
          apply(drule crename_AndL1)
           apply(simp)
          apply(auto)[1]
          apply(drule_tac x="N'" in meta_spec)
          apply(drule_tac x="a" in meta_spec)
          apply(drule_tac x="b" in meta_spec)
          apply(auto)[1]
          apply(rule_tac x="AndL1 (x).M0 y" in exI)
          apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
          apply(auto)[1]
    (* AndL2 *)
         apply(drule sym)
         apply(drule crename_AndL2)
          apply(simp)
         apply(auto)[1]
         apply(drule_tac x="N'" in meta_spec)
         apply(drule_tac x="a" in meta_spec)
         apply(drule_tac x="b" in meta_spec)
         apply(auto)[1]
         apply(rule_tac x="AndL2 (x).M0 y" in exI)
         apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
         apply(auto)[1]
    (* OrL *)
        apply(drule sym)
        apply(drule crename_OrL)
          apply(simp)
          apply(auto simp add: fresh_atm fresh_prod)[1]
         apply(auto simp add: fresh_atm fresh_prod)[1]
        apply(auto)[1]
        apply(drule_tac x="M'a" in meta_spec)
        apply(drule_tac x="a" in meta_spec)
        apply(drule_tac x="b" in meta_spec)
        apply(auto)[1]
        apply(rule_tac x="OrL (x).M0 (y).N' z" in exI)
        apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(auto)[1]
        apply(rule trans)
         apply(rule crename.simps)
           apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
          apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
          apply(auto intro: fresh_a_redu)[1]
         apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(simp)
       apply(drule sym)
       apply(drule crename_OrL)
         apply(simp)
         apply(auto simp add: fresh_atm fresh_prod)[1]
        apply(auto simp add: fresh_atm fresh_prod)[1]
       apply(auto)[1]
       apply(drule_tac x="N'a" in meta_spec)
       apply(drule_tac x="a" in meta_spec)
       apply(drule_tac x="b" in meta_spec)
       apply(auto)[1]
       apply(rule_tac x="OrL (x).M' (y).M0 z" in exI)
       apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
       apply(auto)[1]
       apply(rule trans)
        apply(rule crename.simps)
          apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
          apply(auto intro: fresh_a_redu)[1]
         apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(simp)
       apply(simp)
    (* OrR1 *)
      apply(drule sym)
      apply(frule crename_OrR1_aux)
      apply(erule disjE)
       apply(auto)[1]
      apply(drule crename_OrR1')
        apply(simp)
       apply(simp add: fresh_atm)
      apply(erule disjE)
       apply(auto)[1]
       apply(drule_tac x="N'" in meta_spec)
       apply(drule_tac x="aa" in meta_spec)
       apply(drule_tac x="ba" in meta_spec)
       apply(auto)[1]
       apply(rule_tac x="OrR1 <a>.M0 b" in exI)
       apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
       apply(auto)[1]
      apply(auto)[1]
      apply(drule_tac x="N'" in meta_spec)
      apply(drule_tac x="aa" in meta_spec)
      apply(drule_tac x="b" in meta_spec)
      apply(auto)[1]
      apply(rule_tac x="OrR1 <a>.M0 aa" in exI)
      apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
      apply(auto)[1]
    (* OrR2 *)
     apply(drule sym)
     apply(frule crename_OrR2_aux)
     apply(erule disjE)
      apply(auto)[1]
     apply(drule crename_OrR2')
       apply(simp)
      apply(simp add: fresh_atm)
     apply(erule disjE)
      apply(auto)[1]
      apply(drule_tac x="N'" in meta_spec)
      apply(drule_tac x="aa" in meta_spec)
      apply(drule_tac x="ba" in meta_spec)
      apply(auto)[1]
      apply(rule_tac x="OrR2 <a>.M0 b" in exI)
      apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
      apply(auto)[1]
     apply(auto)[1]
     apply(drule_tac x="N'" in meta_spec)
     apply(drule_tac x="aa" in meta_spec)
     apply(drule_tac x="b" in meta_spec)
     apply(auto)[1]
     apply(rule_tac x="OrR2 <a>.M0 aa" in exI)
     apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
     apply(auto)[1]
    (* ImpL *)
    apply(drule sym)
    apply(drule crename_ImpL)
      apply(simp)
     apply(simp)
    apply(auto)[1]
    apply(drule_tac x="M'a" in meta_spec)
    apply(drule_tac x="aa" in meta_spec)
    apply(drule_tac x="b" in meta_spec)
    apply(auto)[1]
    apply(rule_tac x="ImpL <a>.M0 (x).N' y" in exI)
    apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
    apply(auto)[1]
    apply(rule trans)
     apply(rule crename.simps)
      apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
     apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
     apply(auto intro: fresh_a_redu)[1]
    apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(drule sym)
   apply(drule crename_ImpL)
     apply(simp)
    apply(simp)
   apply(auto)[1]
   apply(drule_tac x="N'a" in meta_spec)
   apply(drule_tac x="aa" in meta_spec)
   apply(drule_tac x="b" in meta_spec)
   apply(auto)[1]
   apply(rule_tac x="ImpL <a>.M' (x).M0 y" in exI)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(auto)[1]
   apply(rule trans)
    apply(rule crename.simps)
     apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
     apply(auto intro: fresh_a_redu)[1]
    apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(simp)
    (* ImpR *)
  apply(drule sym)
  apply(frule crename_ImpR_aux)
  apply(erule disjE)
   apply(auto)[1]
  apply(drule crename_ImpR')
     apply(simp)
    apply(simp add: fresh_atm)
   apply(simp add: fresh_atm)
  apply(erule disjE)
   apply(auto)[1]
   apply(drule_tac x="N'" in meta_spec)
   apply(drule_tac x="aa" in meta_spec)
   apply(drule_tac x="ba" in meta_spec)
   apply(auto)[1]
   apply(rule_tac x="ImpR (x).<a>.M0 b" in exI)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(auto)[1]
  apply(auto)[1]
  apply(drule_tac x="N'" in meta_spec)
  apply(drule_tac x="aa" in meta_spec)
  apply(drule_tac x="b" in meta_spec)
  apply(auto)[1]
  apply(rule_tac x="ImpR (x).<a>.M0 aa" in exI)
  apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
  apply(auto)[1]
  done

lemma SNa_preserved_renaming1:
  assumes a: "SNa M"
  shows "SNa (M[a\<turnstile>c>b])"
  using a
  apply(induct rule: SNa_induct)
  apply(case_tac "a=b")
   apply(simp add: crename_id)
  apply(rule SNaI)
  apply(drule crename_aredu)
   apply(blast)+
  done

lemma nrename_interesting1:
  assumes a: "distinct [x,y,z]"
  shows "M[x\<turnstile>n>z][z\<turnstile>n>y] = M[z\<turnstile>n>y][x\<turnstile>n>y]"
  using a
  apply(nominal_induct M avoiding: x y z rule: trm.strong_induct)
             apply(auto simp add: rename_fresh simp add: trm.inject alpha)
     apply(blast)
    apply(blast)
   apply(rotate_tac 12)
   apply(drule_tac x="x" in meta_spec)
   apply(rotate_tac 15)
   apply(drule_tac x="y" in meta_spec)
   apply(rotate_tac 15)
   apply(drule_tac x="z" in meta_spec)
   apply(blast)
  apply(rotate_tac 11)
  apply(drule_tac x="x" in meta_spec)
  apply(rotate_tac 14)
  apply(drule_tac x="y" in meta_spec)
  apply(rotate_tac 14)
  apply(drule_tac x="z" in meta_spec)
  apply(blast)
  done

lemma nrename_interesting2:
  assumes a: "x\<noteq>z" "x\<noteq>u" "x\<noteq>y" "z\<noteq>u" "y\<noteq>z"
  shows "M[x\<turnstile>n>y][z\<turnstile>n>u] = M[z\<turnstile>n>u][x\<turnstile>n>y]"
  using a
  apply(nominal_induct M avoiding: x y z u rule: trm.strong_induct)
             apply(auto simp add: rename_fresh simp add: trm.inject alpha)
  done

lemma not_fic_nrename_aux:
  assumes a: "fic M c" 
  shows "fic (M[x\<turnstile>n>y]) c" 
  using a
  apply(nominal_induct M avoiding: c x y rule: trm.strong_induct)
             apply(auto dest!: fic_elims intro!: fic.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh)
  done

lemma not_fic_nrename:
  assumes a: "\<not>(fic (M[x\<turnstile>n>y]) c)" 
  shows "\<not>(fic M c)" 
  using a
  apply(auto dest:  not_fic_nrename_aux)
  done

lemma fin_nrename:
  assumes a: "fin M z" "z\<sharp>(x,y)"
  shows "fin (M[x\<turnstile>n>y]) z" 
  using a
  apply(nominal_induct M avoiding: x y z rule: trm.strong_induct)
             apply(auto dest!: fin_elims intro!: fin.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh
      split: if_splits)
  done

lemma nrename_fresh_interesting1:
  fixes z::"name"
  assumes a: "z\<sharp>(M[x\<turnstile>n>y])" "z\<sharp>(x,y)"
  shows "z\<sharp>M"
  using a
  apply(nominal_induct M avoiding: x y z rule: trm.strong_induct)
             apply(auto split: if_splits simp add: abs_fresh abs_supp fin_supp)
  done

lemma nrename_fresh_interesting2:
  fixes c::"coname"
  assumes a: "c\<sharp>(M[x\<turnstile>n>y])" 
  shows "c\<sharp>M"
  using a
  apply(nominal_induct M avoiding: x y c rule: trm.strong_induct)
             apply(auto split: if_splits simp add: abs_fresh abs_supp fin_supp fresh_atm)
  done

lemma fin_nrename2:
  assumes a: "fin (M[x\<turnstile>n>y]) z" "z\<sharp>(x,y)"
  shows "fin M z" 
  using a
  apply(nominal_induct M avoiding: x y z rule: trm.strong_induct)
             apply(auto dest!: fin_elims intro!: fin.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh
      split: if_splits)
        apply(auto dest: nrename_fresh_interesting1 simp add: fresh_atm fresh_prod)
  done

lemma nrename_Cut:
  assumes a: "R[x\<turnstile>n>y] = Cut <c>.M (z).N" "c\<sharp>(N,R)" "z\<sharp>(x,y,M,R)"
  shows "\<exists>M' N'. R = Cut <c>.M' (z).N' \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N \<and> c\<sharp>N' \<and> z\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: c y x z M N rule: trm.strong_induct)
             apply(auto split: if_splits)
  apply(simp add: trm.inject)
  apply(auto simp add: alpha fresh_atm)
  apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule_tac x="[(name,z)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule conjI)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(auto simp add: fresh_atm)[1]
  apply(drule sym)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_NotR:
  assumes a: "R[x\<turnstile>n>y] = NotR (z).N c" "z\<sharp>(R,x,y)" 
  shows "\<exists>N'. (R = NotR (z).N' c) \<and> N'[x\<turnstile>n>y] = N" 
  using a
  apply(nominal_induct R avoiding: x y c z N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(name,z)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_NotL:
  assumes a: "R[x\<turnstile>n>y] = NotL <c>.N z" "c\<sharp>R" "z\<sharp>(x,y)"
  shows "\<exists>N'. (R = NotL <c>.N' z) \<and> N'[x\<turnstile>n>y] = N" 
  using a
  apply(nominal_induct R avoiding: x y c z N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(coname,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_NotL':
  assumes a: "R[x\<turnstile>n>y] = NotL <c>.N u" "c\<sharp>R" "x\<noteq>y" 
  shows "(\<exists>N'. (R = NotL <c>.N' u) \<and> N'[x\<turnstile>n>y] = N) \<or> (\<exists>N'. (R = NotL <c>.N' x) \<and> y=u \<and> N'[x\<turnstile>n>y] = N)"
  using a
  apply(nominal_induct R avoiding: y u c x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_fresh alpha trm.inject)
   apply(rule_tac x="[(coname,c)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(coname,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_NotL_aux:
  assumes a: "R[x\<turnstile>n>y] = NotL <c>.N u" 
  shows "(x=u \<and> x=y) \<or> (x\<noteq>u)" 
  using a
  apply(nominal_induct R avoiding: y u c x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma nrename_AndL1:
  assumes a: "R[x\<turnstile>n>y] = AndL1 (z).N u" "z\<sharp>(R,x,y)" "u\<sharp>(x,y)"
  shows "\<exists>N'. (R = AndL1 (z).N' u) \<and> N'[x\<turnstile>n>y] = N" 
  using a
  apply(nominal_induct R avoiding: z u x y N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(name1,z)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_AndL1':
  assumes a: "R[x\<turnstile>n>y] = AndL1 (v).N u" "v\<sharp>(R,u,x,y)" "x\<noteq>y" 
  shows "(\<exists>N'. (R = AndL1 (v).N' u) \<and> N'[x\<turnstile>n>y] = N) \<or> (\<exists>N'. (R = AndL1 (v).N' x) \<and> y=u \<and> N'[x\<turnstile>n>y] = N)"
  using a
  apply(nominal_induct R avoiding: y u v x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_fresh alpha trm.inject)
   apply(rule_tac x="[(name1,v)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(name1,v)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_AndL1_aux:
  assumes a: "R[x\<turnstile>n>y] = AndL1 (v).N u" 
  shows "(x=u \<and> x=y) \<or> (x\<noteq>u)" 
  using a
  apply(nominal_induct R avoiding: y u v x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma nrename_AndL2:
  assumes a: "R[x\<turnstile>n>y] = AndL2 (z).N u" "z\<sharp>(R,x,y)" "u\<sharp>(x,y)"
  shows "\<exists>N'. (R = AndL2 (z).N' u) \<and> N'[x\<turnstile>n>y] = N" 
  using a
  apply(nominal_induct R avoiding: z u x y N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(name1,z)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_AndL2':
  assumes a: "R[x\<turnstile>n>y] = AndL2 (v).N u" "v\<sharp>(R,u,x,y)" "x\<noteq>y" 
  shows "(\<exists>N'. (R = AndL2 (v).N' u) \<and> N'[x\<turnstile>n>y] = N) \<or> (\<exists>N'. (R = AndL2 (v).N' x) \<and> y=u \<and> N'[x\<turnstile>n>y] = N)"
  using a
  apply(nominal_induct R avoiding: y u v x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_fresh alpha trm.inject)
   apply(rule_tac x="[(name1,v)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(name1,v)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_AndL2_aux:
  assumes a: "R[x\<turnstile>n>y] = AndL2 (v).N u" 
  shows "(x=u \<and> x=y) \<or> (x\<noteq>u)" 
  using a
  apply(nominal_induct R avoiding: y u v x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma nrename_AndR:
  assumes a: "R[x\<turnstile>n>y] = AndR <c>.M <d>.N e" "c\<sharp>(d,e,N,R)" "d\<sharp>(c,e,M,R)" 
  shows "\<exists>M' N'. R = AndR <c>.M' <d>.N' e \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N \<and> c\<sharp>N' \<and> d\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: x y c d e M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha)
    apply(simp add: fresh_atm fresh_prod)
   apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(coname2,d)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[x\<turnstile>n>y]" in  sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_OrR1:
  assumes a: "R[x\<turnstile>n>y] = OrR1 <c>.N d" "c\<sharp>(R,d)" 
  shows "\<exists>N'. (R = OrR1 <c>.N' d) \<and> N'[x\<turnstile>n>y] = N" 
  using a
  apply(nominal_induct R avoiding: x y c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_OrR2:
  assumes a: "R[x\<turnstile>n>y] = OrR2 <c>.N d" "c\<sharp>(R,d)" 
  shows "\<exists>N'. (R = OrR2 <c>.N' d) \<and> N'[x\<turnstile>n>y] = N" 
  using a
  apply(nominal_induct R avoiding: x y c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_OrL:
  assumes a: "R[u\<turnstile>n>v] = OrL (x).M (y).N z" "x\<sharp>(y,z,u,v,N,R)" "y\<sharp>(x,z,u,v,M,R)" "z\<sharp>(u,v)"
  shows "\<exists>M' N'. R = OrL (x).M' (y).N' z \<and> M'[u\<turnstile>n>v] = M \<and> N'[u\<turnstile>n>v] = N \<and> x\<sharp>N' \<and> y\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: u v x y z M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha fresh_prod fresh_atm)
  apply(rule_tac x="[(name1,x)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(name2,y)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[u\<turnstile>n>v]" in  sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_OrL':
  assumes a: "R[x\<turnstile>n>y] = OrL (v).M (w).N u" "v\<sharp>(R,N,u,x,y)" "w\<sharp>(R,M,u,x,y)" "x\<noteq>y" 
  shows "(\<exists>M' N'. (R = OrL (v).M' (w).N' u) \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N) \<or> 
         (\<exists>M' N'. (R = OrL (v).M' (w).N' x) \<and> y=u \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N)"
  using a [[simproc del: defined_all]]
  apply(nominal_induct R avoiding: y x u v w M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_fresh alpha trm.inject)
   apply(rule_tac x="[(name1,v)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(rule_tac x="[(name2,w)]\<bullet>trm2" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(rule conjI)
    apply(drule sym)
    apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
    apply(simp add: eqvts calc_atm)
   apply(drule_tac s="trm2[x\<turnstile>n>u]" in sym)
   apply(drule_tac pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(name1,v)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule_tac x="[(name2,w)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule conjI)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[x\<turnstile>n>y]" in sym)
  apply(drule_tac pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_OrL_aux:
  assumes a: "R[x\<turnstile>n>y] = OrL (v).M (w).N u" 
  shows "(x=u \<and> x=y) \<or> (x\<noteq>u)" 
  using a
  apply(nominal_induct R avoiding: y x w u v M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma nrename_ImpL:
  assumes a: "R[x\<turnstile>n>y] = ImpL <c>.M (u).N z" "c\<sharp>(N,R)" "u\<sharp>(y,x,z,M,R)" "z\<sharp>(x,y)"
  shows "\<exists>M' N'. R = ImpL <c>.M' (u).N' z \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N \<and> c\<sharp>N' \<and> u\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: u x c y z M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha fresh_prod fresh_atm)
  apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(name1,u)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[x\<turnstile>n>y]" in  sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm fresh_prod fresh_atm)
  done

lemma nrename_ImpL':
  assumes a: "R[x\<turnstile>n>y] = ImpL <c>.M (w).N u" "c\<sharp>(R,N)" "w\<sharp>(R,M,u,x,y)" "x\<noteq>y" 
  shows "(\<exists>M' N'. (R = ImpL <c>.M' (w).N' u) \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N) \<or> 
         (\<exists>M' N'. (R = ImpL <c>.M' (w).N' x) \<and> y=u \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N)"
  using a [[simproc del: defined_all]]
  apply(nominal_induct R avoiding: y x u c w M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_fresh alpha trm.inject)
   apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(rule_tac x="[(name1,w)]\<bullet>trm2" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(rule conjI)
    apply(drule sym)
    apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
    apply(simp add: eqvts calc_atm)
   apply(drule_tac s="trm2[x\<turnstile>n>u]" in sym)
   apply(drule_tac pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule_tac x="[(name1,w)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule conjI)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[x\<turnstile>n>y]" in sym)
  apply(drule_tac pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_ImpL_aux:
  assumes a: "R[x\<turnstile>n>y] = ImpL <c>.M (w).N u" 
  shows "(x=u \<and> x=y) \<or> (x\<noteq>u)" 
  using a
  apply(nominal_induct R avoiding: y x w u c M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma nrename_ImpR:
  assumes a: "R[u\<turnstile>n>v] = ImpR (x).<c>.N d" "c\<sharp>(R,d)" "x\<sharp>(R,u,v)" 
  shows "\<exists>N'. (R = ImpR (x).<c>.N' d) \<and> N'[u\<turnstile>n>v] = N" 
  using a
  apply(nominal_induct R avoiding: u v x c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_perm alpha abs_fresh trm.inject)
   apply(rule_tac x="[(name,x)]\<bullet>trm" in exI)
   apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule_tac x="[(name,x)]\<bullet>[(coname1, c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_supp fin_supp abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_credu:
  assumes a: "(M[x\<turnstile>n>y]) \<longrightarrow>\<^sub>c M'"
  shows "\<exists>M0. M0[x\<turnstile>n>y]=M' \<and> M \<longrightarrow>\<^sub>c M0"
  using a
  apply(nominal_induct M\<equiv>"M[x\<turnstile>n>y]" M' avoiding: M x y rule: c_redu.strong_induct)
   apply(drule sym)
   apply(drule nrename_Cut)
     apply(simp)
    apply(simp)
   apply(auto)
   apply(rule_tac x="M'{a:=(x).N'}" in exI)
   apply(rule conjI)
    apply(simp add: fresh_atm abs_fresh subst_comm fresh_prod)
   apply(rule c_redu.intros)
     apply(auto dest: not_fic_nrename)[1]
    apply(simp add: abs_fresh)
   apply(simp add: abs_fresh)
  apply(drule sym)
  apply(drule nrename_Cut)
    apply(simp)
   apply(simp)
  apply(auto)
  apply(rule_tac x="N'{x:=<a>.M'}" in exI)
  apply(rule conjI)
   apply(simp add: fresh_atm abs_fresh subst_comm fresh_prod)
  apply(rule c_redu.intros)
    apply(auto)
  apply(drule_tac x="xa" and y="y" in fin_nrename)
   apply(auto simp add: fresh_prod abs_fresh)
  done

lemma nrename_ax2:
  assumes a: "N[x\<turnstile>n>y] = Ax z c"
  shows "\<exists>z. N = Ax z c"
  using a
  apply(nominal_induct N avoiding: x y rule: trm.strong_induct)
             apply(auto split: if_splits)
  apply(simp add: trm.inject)
  done

lemma fic_nrename:
  assumes a: "fic (M[x\<turnstile>n>y]) c" 
  shows "fic M c" 
  using a
  apply(nominal_induct M avoiding: c x y rule: trm.strong_induct)
             apply(auto dest!: fic_elims intro!: fic.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh
      split: if_splits)
       apply(auto dest: nrename_fresh_interesting2 simp add: fresh_prod fresh_atm)
  done

lemma nrename_lredu:
  assumes a: "(M[x\<turnstile>n>y]) \<longrightarrow>\<^sub>l M'"
  shows "\<exists>M0. M0[x\<turnstile>n>y]=M' \<and> M \<longrightarrow>\<^sub>l M0"
  using a
  apply(nominal_induct M\<equiv>"M[x\<turnstile>n>y]" M' avoiding: M x y rule: l_redu.strong_induct)
         apply(drule sym)
         apply(drule nrename_Cut)
           apply(simp add: fresh_prod fresh_atm)
          apply(simp)
         apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
         apply(case_tac "xa=y")
          apply(simp add: nrename_id)
          apply(rule l_redu.intros)
            apply(simp)
           apply(simp add: fresh_atm)
          apply(assumption)
         apply(frule nrename_ax2)
         apply(auto)[1]
         apply(case_tac "z=xa")
          apply(simp add: trm.inject)
         apply(simp)
         apply(rule_tac x="M'[a\<turnstile>c>b]" in exI)
         apply(rule conjI)
          apply(rule crename_interesting3)
         apply(rule l_redu.intros)
           apply(simp)
          apply(simp add: fresh_atm)
         apply(auto dest: fic_nrename simp add: fresh_prod fresh_atm)[1]
        apply(drule sym)
        apply(drule nrename_Cut)
          apply(simp add: fresh_prod fresh_atm)
         apply(simp add: fresh_prod fresh_atm)
        apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
        apply(case_tac "xa=ya")
         apply(simp add: nrename_id)
         apply(rule l_redu.intros)
           apply(simp)
          apply(simp add: fresh_atm)
         apply(assumption)
        apply(frule nrename_ax2)
        apply(auto)[1]
        apply(case_tac "z=xa")
         apply(simp add: trm.inject)
         apply(rule_tac x="N'[x\<turnstile>n>xa]" in exI)
         apply(rule conjI)
          apply(rule nrename_interesting1)
          apply(auto)[1]
         apply(rule l_redu.intros)
           apply(simp)
          apply(simp add: fresh_atm)
         apply(auto dest: fin_nrename2 simp add: fresh_prod fresh_atm)[1]
        apply(simp add: trm.inject)
        apply(rule_tac x="N'[x\<turnstile>n>y]" in exI)
        apply(rule conjI)
         apply(rule nrename_interesting2)
             apply(simp_all)
        apply(rule l_redu.intros)
          apply(simp)
         apply(simp add: fresh_atm)
        apply(auto dest: fin_nrename2 simp add: fresh_prod fresh_atm)[1]
    (* LNot *)
       apply(drule sym)
       apply(drule nrename_Cut)
         apply(simp add: fresh_prod abs_fresh fresh_atm)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
       apply(drule nrename_NotR)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
       apply(drule nrename_NotL)
         apply(simp add: fresh_prod abs_fresh fresh_atm)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
       apply(rule_tac x="Cut <b>.N'b (x).N'a" in exI)
       apply(simp add: fresh_atm)[1]
       apply(rule l_redu.intros)
            apply(auto simp add: fresh_prod fresh_atm intro: nrename_fresh_interesting1)[1]
           apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
          apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting2)[1]
         apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting2)[1]
        apply(simp add: fresh_atm)
       apply(simp add: fresh_atm)
    (* LAnd1 *)
      apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
      apply(drule sym)
      apply(drule nrename_Cut)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(auto)[1]
      apply(drule nrename_AndR)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
      apply(drule nrename_AndL1)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
      apply(rule_tac x="Cut <a1>.M'a (x).N'b" in exI)
      apply(simp add: fresh_atm)[1]
      apply(rule l_redu.intros)
           apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: nrename_fresh_interesting2)[1]
          apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
         apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
        apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
       apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
      apply(simp add: fresh_atm)
    (* LAnd2 *)
     apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
     apply(drule sym)
     apply(drule nrename_Cut)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(auto)[1]
     apply(drule nrename_AndR)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
     apply(drule nrename_AndL2)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
     apply(rule_tac x="Cut <a2>.N'a (x).N'b" in exI)
     apply(simp add: fresh_atm)[1]
     apply(rule l_redu.intros)
          apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: nrename_fresh_interesting2)[1]
         apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
        apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
       apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
      apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
     apply(simp add: fresh_atm)
    (* LOr1 *)
    apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
    apply(drule sym)
    apply(drule nrename_Cut)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(auto)[1]
    apply(drule nrename_OrL)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(simp add: fresh_prod fresh_atm)
    apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
    apply(drule nrename_OrR1)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
    apply(rule_tac x="Cut <a>.N' (x1).M'a" in exI)
    apply(rule conjI)
     apply(simp add: abs_fresh fresh_atm)[1]
    apply(rule l_redu.intros)
         apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: nrename_fresh_interesting2)[1]
        apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
       apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
      apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
     apply(simp add: fresh_atm)
    apply(simp add: fresh_atm)
    (* LOr2 *)
   apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule nrename_Cut)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(auto)[1]
   apply(drule nrename_OrL)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
   apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
   apply(drule nrename_OrR2)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
   apply(rule_tac x="Cut <a>.N' (x2).N'a" in exI)
   apply(rule conjI)
    apply(simp add: abs_fresh fresh_atm)[1]
   apply(rule l_redu.intros)
        apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: nrename_fresh_interesting2)[1]
       apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
      apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
     apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
    apply(simp add: fresh_atm)
   apply(simp add: fresh_atm)
    (* ImpL *)
  apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
  apply(drule sym) 
  apply(drule nrename_Cut)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(simp add: fresh_prod abs_fresh fresh_atm abs_supp fin_supp)
  apply(auto)[1]
  apply(drule nrename_ImpL)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(simp add: fresh_prod fresh_atm)
  apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
  apply(drule nrename_ImpR)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(simp add: fresh_prod abs_fresh fresh_atm)
  apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
  apply(rule_tac x="Cut <a>.(Cut <c>.M'a (x).N') (y).N'a" in exI)
  apply(rule conjI)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
  apply(rule l_redu.intros)
       apply(auto simp add: fresh_atm abs_fresh abs_supp fin_supp fresh_prod intro: nrename_fresh_interesting1)[1]
      apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: nrename_fresh_interesting2)[1]
     apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: nrename_fresh_interesting1)[1]
    apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: nrename_fresh_interesting2)[1]
   apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: nrename_fresh_interesting2)[1]
  apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: nrename_fresh_interesting2)[1]
  done

lemma nrename_aredu:
  assumes a: "(M[x\<turnstile>n>y]) \<longrightarrow>\<^sub>a M'" "x\<noteq>y"
  shows "\<exists>M0. M0[x\<turnstile>n>y]=M' \<and> M \<longrightarrow>\<^sub>a M0"
  using a
  apply(nominal_induct "M[x\<turnstile>n>y]" M' avoiding: M x y rule: a_redu.strong_induct)
                  apply(drule  nrename_lredu)
                  apply(blast)
                 apply(drule  nrename_credu)
                 apply(blast)
    (* Cut *)
                apply(drule sym)
                apply(drule nrename_Cut)
                  apply(simp)
                 apply(simp)
                apply(auto)[1]
                apply(drule_tac x="M'a" in meta_spec)
                apply(drule_tac x="xa" in meta_spec)
                apply(drule_tac x="y" in meta_spec)
                apply(auto)[1]
                apply(rule_tac x="Cut <a>.M0 (x).N'" in exI)
                apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
                apply(rule conjI)
                 apply(rule trans)
                  apply(rule nrename.simps)
                   apply(drule nrename_fresh_interesting2)
                   apply(simp add: fresh_a_redu)
                  apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
                  apply(drule nrename_fresh_interesting1)
                   apply(simp add: fresh_prod fresh_atm)
                  apply(simp add: fresh_a_redu)
                 apply(simp)
                apply(auto)[1]
               apply(drule sym)
               apply(drule nrename_Cut)
                 apply(simp)
                apply(simp)
               apply(auto)[1]
               apply(drule_tac x="N'a" in meta_spec)
               apply(drule_tac x="xa" in meta_spec)
               apply(drule_tac x="y" in meta_spec)
               apply(auto)[1]
               apply(rule_tac x="Cut <a>.M' (x).M0" in exI)
               apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
               apply(rule conjI)
                apply(rule trans)
                 apply(rule nrename.simps)
                  apply(simp add: fresh_a_redu)
                 apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
                apply(simp)
               apply(auto)[1]
    (* NotL *)
              apply(drule sym)
              apply(frule nrename_NotL_aux)
              apply(erule disjE)
               apply(auto)[1]
              apply(drule nrename_NotL')
                apply(simp)
               apply(simp add: fresh_atm)
              apply(erule disjE)
               apply(auto)[1]
               apply(drule_tac x="N'" in meta_spec)
               apply(drule_tac x="xa" in meta_spec)
               apply(drule_tac x="y" in meta_spec)
               apply(auto)[1]
               apply(rule_tac x="NotL <a>.M0 x" in exI)
               apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
               apply(auto)[1]
              apply(auto)[1]
              apply(drule_tac x="N'" in meta_spec)
              apply(drule_tac x="xa" in meta_spec)
              apply(drule_tac x="x" in meta_spec)
              apply(auto)[1]
              apply(rule_tac x="NotL <a>.M0 xa" in exI)
              apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
              apply(auto)[1]
    (* NotR *)
             apply(drule sym)
             apply(drule nrename_NotR)
              apply(simp)
             apply(auto)[1]
             apply(drule_tac x="N'" in meta_spec)
             apply(drule_tac x="xa" in meta_spec)
             apply(drule_tac x="y" in meta_spec)
             apply(auto)[1]
             apply(rule_tac x="NotR (x).M0 a" in exI)
             apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
             apply(auto)[1]
    (* AndR *)
            apply(drule sym)
            apply(drule nrename_AndR)
              apply(simp)
              apply(auto simp add: fresh_atm fresh_prod)[1]
             apply(auto simp add: fresh_atm fresh_prod)[1]
            apply(auto)[1]
            apply(drule_tac x="M'a" in meta_spec)
            apply(drule_tac x="x" in meta_spec)
            apply(drule_tac x="y" in meta_spec)
            apply(auto)[1]
            apply(rule_tac x="AndR <a>.M0 <b>.N' c" in exI)
            apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(auto)[1]
            apply(rule trans)
             apply(rule nrename.simps)
               apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
              apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
              apply(auto intro: fresh_a_redu)[1]
             apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(simp)
           apply(drule sym)
           apply(drule nrename_AndR)
             apply(simp)
             apply(auto simp add: fresh_atm fresh_prod)[1]
            apply(auto simp add: fresh_atm fresh_prod)[1]
           apply(auto)[1]
           apply(drule_tac x="N'a" in meta_spec)
           apply(drule_tac x="x" in meta_spec)
           apply(drule_tac x="y" in meta_spec)
           apply(auto)[1]
           apply(rule_tac x="AndR <a>.M' <b>.M0 c" in exI)
           apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(auto)[1]
           apply(rule trans)
            apply(rule nrename.simps)
              apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
              apply(auto intro: fresh_a_redu)[1]
             apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(simp)
           apply(simp)
    (* AndL1 *)
          apply(drule sym)
          apply(frule nrename_AndL1_aux)
          apply(erule disjE)
           apply(auto)[1]
          apply(drule nrename_AndL1')
            apply(simp)
           apply(simp add: fresh_atm)
          apply(erule disjE)
           apply(auto)[1]
           apply(drule_tac x="N'" in meta_spec)
           apply(drule_tac x="xa" in meta_spec)
           apply(drule_tac x="ya" in meta_spec)
           apply(auto)[1]
           apply(rule_tac x="AndL1 (x).M0 y" in exI)
           apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(auto)[1]
          apply(auto)[1]
          apply(drule_tac x="N'" in meta_spec)
          apply(drule_tac x="xa" in meta_spec)
          apply(drule_tac x="y" in meta_spec)
          apply(auto)[1]
          apply(rule_tac x="AndL1 (x).M0 xa" in exI)
          apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
          apply(auto)[1]
    (* AndL2 *)
         apply(drule sym)
         apply(frule nrename_AndL2_aux)
         apply(erule disjE)
          apply(auto)[1]
         apply(drule nrename_AndL2')
           apply(simp)
          apply(simp add: fresh_atm)
         apply(erule disjE)
          apply(auto)[1]
          apply(drule_tac x="N'" in meta_spec)
          apply(drule_tac x="xa" in meta_spec)
          apply(drule_tac x="ya" in meta_spec)
          apply(auto)[1]
          apply(rule_tac x="AndL2 (x).M0 y" in exI)
          apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
          apply(auto)[1]
         apply(auto)[1]
         apply(drule_tac x="N'" in meta_spec)
         apply(drule_tac x="xa" in meta_spec)
         apply(drule_tac x="y" in meta_spec)
         apply(auto)[1]
         apply(rule_tac x="AndL2 (x).M0 xa" in exI)
         apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
         apply(auto)[1]
    (* OrL *)
        apply(drule sym)
        apply(frule nrename_OrL_aux)
        apply(erule disjE)
         apply(auto)[1]
        apply(drule nrename_OrL')
           apply(simp add: fresh_prod fresh_atm)
          apply(simp add: fresh_atm)
         apply(simp add: fresh_atm)
        apply(erule disjE)
         apply(auto)[1]
         apply(drule_tac x="M'a" in meta_spec)
         apply(drule_tac x="xa" in meta_spec)
         apply(drule_tac x="ya" in meta_spec)
         apply(auto)[1]
         apply(rule_tac x="OrL (x).M0 (y).N' z" in exI)
         apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
         apply(auto)[1]
         apply(rule trans)
          apply(rule nrename.simps)
            apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(auto intro: fresh_a_redu)[1]
          apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
         apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(auto)[1]
        apply(drule_tac x="M'a" in meta_spec)
        apply(drule_tac x="xa" in meta_spec)
        apply(drule_tac x="z" in meta_spec)
        apply(auto)[1]
        apply(rule_tac x="OrL (x).M0 (y).N' xa" in exI)
        apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(auto)[1]
        apply(rule trans)
         apply(rule nrename.simps)
           apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
          apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
          apply(auto intro: fresh_a_redu)[1]
         apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
       apply(drule sym)
       apply(frule nrename_OrL_aux)
       apply(erule disjE)
        apply(auto)[1]
       apply(drule nrename_OrL')
          apply(simp add: fresh_prod fresh_atm)
         apply(simp add: fresh_atm)
        apply(simp add: fresh_atm)
       apply(erule disjE)
        apply(auto)[1]
        apply(drule_tac x="N'a" in meta_spec)
        apply(drule_tac x="xa" in meta_spec)
        apply(drule_tac x="ya" in meta_spec)
        apply(auto)[1]
        apply(rule_tac x="OrL (x).M' (y).M0 z" in exI)
        apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(auto)[1]
        apply(rule trans)
         apply(rule nrename.simps)
           apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
           apply(auto intro: fresh_a_redu)[1]
          apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
         apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
       apply(auto)[1]
       apply(drule_tac x="N'a" in meta_spec)
       apply(drule_tac x="xa" in meta_spec)
       apply(drule_tac x="z" in meta_spec)
       apply(auto)[1]
       apply(rule_tac x="OrL (x).M' (y).M0 xa" in exI)
       apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
       apply(auto)[1]
       apply(rule trans)
        apply(rule nrename.simps)
          apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
          apply(auto intro: fresh_a_redu)[1]
         apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(simp)
       apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
    (* OrR1 *)
      apply(drule sym)
      apply(drule nrename_OrR1)
       apply(simp)
      apply(auto)[1]
      apply(drule_tac x="N'" in meta_spec)
      apply(drule_tac x="x" in meta_spec)
      apply(drule_tac x="y" in meta_spec)
      apply(auto)[1]
      apply(rule_tac x="OrR1 <a>.M0 b" in exI)
      apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
      apply(auto)[1]
    (* OrR2 *)
     apply(drule sym)
     apply(drule nrename_OrR2)
      apply(simp)
     apply(auto)[1]
     apply(drule_tac x="N'" in meta_spec)
     apply(drule_tac x="x" in meta_spec)
     apply(drule_tac x="y" in meta_spec)
     apply(auto)[1]
     apply(rule_tac x="OrR2 <a>.M0 b" in exI)
     apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
     apply(auto)[1]
    (* ImpL *)
    apply(drule sym)
    apply(frule nrename_ImpL_aux)
    apply(erule disjE)
     apply(auto)[1]
    apply(drule nrename_ImpL')
       apply(simp add: fresh_prod fresh_atm)
      apply(simp add: fresh_atm)
     apply(simp add: fresh_atm)
    apply(erule disjE)
     apply(auto)[1]
     apply(drule_tac x="M'a" in meta_spec)
     apply(drule_tac x="xa" in meta_spec)
     apply(drule_tac x="ya" in meta_spec)
     apply(auto)[1]
     apply(rule_tac x="ImpL <a>.M0 (x).N' y" in exI)
     apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
     apply(auto)[1]
     apply(rule trans)
      apply(rule nrename.simps)
       apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
      apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
      apply(auto intro: fresh_a_redu)[1]
     apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
    apply(auto)[1]
    apply(drule_tac x="M'a" in meta_spec)
    apply(drule_tac x="xa" in meta_spec)
    apply(drule_tac x="y" in meta_spec)
    apply(auto)[1]
    apply(rule_tac x="ImpL <a>.M0 (x).N' xa" in exI)
    apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
    apply(auto)[1]
    apply(rule trans)
     apply(rule nrename.simps)
      apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
     apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
     apply(auto intro: fresh_a_redu)[1]
    apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(drule sym)
   apply(frule nrename_ImpL_aux)
   apply(erule disjE)
    apply(auto)[1]
   apply(drule nrename_ImpL')
      apply(simp add: fresh_prod fresh_atm)
     apply(simp add: fresh_atm)
    apply(simp add: fresh_atm)
   apply(erule disjE)
    apply(auto)[1]
    apply(drule_tac x="N'a" in meta_spec)
    apply(drule_tac x="xa" in meta_spec)
    apply(drule_tac x="ya" in meta_spec)
    apply(auto)[1]
    apply(rule_tac x="ImpL <a>.M' (x).M0 y" in exI)
    apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
    apply(auto)[1]
    apply(rule trans)
     apply(rule nrename.simps)
      apply(auto intro: fresh_a_redu)[1]
     apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
    apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(auto)[1]
   apply(drule_tac x="N'a" in meta_spec)
   apply(drule_tac x="xa" in meta_spec)
   apply(drule_tac x="y" in meta_spec)
   apply(auto)[1]
   apply(rule_tac x="ImpL <a>.M' (x).M0 xa" in exI)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(auto)[1]
   apply(rule trans)
    apply(rule nrename.simps)
     apply(auto intro: fresh_a_redu)[1]
    apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
    (* ImpR *)
  apply(drule sym)
  apply(drule nrename_ImpR)
    apply(simp)
   apply(simp)
  apply(auto)[1]
  apply(drule_tac x="N'" in meta_spec)
  apply(drule_tac x="xa" in meta_spec)
  apply(drule_tac x="y" in meta_spec)
  apply(auto)[1]
  apply(rule_tac x="ImpR (x).<a>.M0 b" in exI)
  apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
  apply(auto)[1]
  done

lemma SNa_preserved_renaming2:
  assumes a: "SNa N"
  shows "SNa (N[x\<turnstile>n>y])"
  using a
  apply(induct rule: SNa_induct)
  apply(case_tac "x=y")
   apply(simp add: nrename_id)
  apply(rule SNaI)
  apply(drule nrename_aredu)
   apply(blast)+
  done

text \<open>helper-stuff to set up the induction\<close>

abbreviation
  SNa_set :: "trm set"
  where
    "SNa_set \<equiv> {M. SNa M}"

abbreviation
  A_Redu_set :: "(trm\<times>trm) set"
  where
    "A_Redu_set \<equiv> {(N,M)| M N. M \<longrightarrow>\<^sub>a N}"

lemma SNa_elim:
  assumes a: "SNa M"
  shows "(\<forall>M. (\<forall>N. M \<longrightarrow>\<^sub>a N \<longrightarrow> P N)\<longrightarrow> P M) \<longrightarrow> P M"
  using a
  by (induct rule: SNa.induct) (blast)

lemma wf_SNa_restricted:
  shows "wf (A_Redu_set \<inter> (UNIV \<times> SNa_set))"
  apply(unfold wf_def)
  apply(intro strip)
  apply(case_tac "SNa x")
   apply(simp (no_asm_use))
   apply(drule_tac P="P" in SNa_elim)
   apply(erule mp)
   apply(blast)
    (* other case *)
  apply(drule_tac x="x" in spec)
  apply(erule mp)
  apply(fast)
  done

definition SNa_Redu :: "(trm \<times> trm) set" where
  "SNa_Redu \<equiv> A_Redu_set \<inter> (UNIV \<times> SNa_set)"

lemma wf_SNa_Redu:
  shows "wf SNa_Redu"
  apply(unfold SNa_Redu_def)
  apply(rule wf_SNa_restricted)
  done

lemma wf_measure_triple:
  shows "wf ((measure size) <*lex*> SNa_Redu <*lex*> SNa_Redu)"
  by (auto intro: wf_SNa_Redu)

lemma my_wf_induct_triple: 
  assumes a: " wf(r1 <*lex*> r2 <*lex*> r3)"           
    and     b: "\<And>x. \<lbrakk>\<And>y. ((fst y,fst (snd y),snd (snd y)),(fst x,fst (snd x), snd (snd x))) 
                                    \<in> (r1 <*lex*> r2 <*lex*> r3) \<longrightarrow> P y\<rbrakk> \<Longrightarrow> P x"  
  shows "P x"
  using a
  apply(induct x rule: wf_induct_rule)
  apply(rule b)
  apply(simp)
  done

lemma my_wf_induct_triple': 
  assumes a: " wf(r1 <*lex*> r2 <*lex*> r3)"           
    and    b: "\<And>x1 x2 x3. \<lbrakk>\<And>y1 y2 y3. ((y1,y2,y3),(x1,x2,x3)) \<in> (r1 <*lex*> r2 <*lex*> r3) \<longrightarrow> P (y1,y2,y3)\<rbrakk> 
             \<Longrightarrow> P (x1,x2,x3)"  
  shows "P (x1,x2,x3)"
  apply(rule_tac my_wf_induct_triple[OF a])
  apply(case_tac x rule: prod.exhaust)
  apply(simp)
  apply(rename_tac p a b)
  apply(case_tac b)
  apply(simp)
  apply(rule b)
  apply(blast)
  done

lemma my_wf_induct_triple'': 
  assumes a: " wf(r1 <*lex*> r2 <*lex*> r3)"           
    and     b: "\<And>x1 x2 x3. \<lbrakk>\<And>y1 y2 y3. ((y1,y2,y3),(x1,x2,x3)) \<in> (r1 <*lex*> r2 <*lex*> r3) \<longrightarrow> P y1 y2 y3\<rbrakk>
               \<Longrightarrow> P x1 x2 x3"  
  shows "P x1 x2 x3"
  apply(rule_tac my_wf_induct_triple'[where P="\<lambda>(x1,x2,x3). P x1 x2 x3", simplified])
   apply(rule a)
  apply(rule b)
  apply(auto)
  done

lemma excluded_m:
  assumes a: "<a>:M \<in> (\<parallel><B>\<parallel>)" "(x):N \<in> (\<parallel>(B)\<parallel>)"
  shows "(<a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>) \<or> (x):N \<in> BINDINGn B (\<parallel><B>\<parallel>))
      \<or>\<not>(<a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>) \<or> (x):N \<in> BINDINGn B (\<parallel><B>\<parallel>))"
  by (blast)

text \<open>The following two simplification rules are necessary because of the 
      new definition of lexicographic ordering\<close>
lemma ne_and_SNa_Redu[simp]: "M \<noteq> x \<and> (M,x) \<in> SNa_Redu \<longleftrightarrow> (M,x) \<in> SNa_Redu"
  using wf_SNa_Redu by auto

lemma ne_and_less_size [simp]: "A \<noteq> B \<and> size A < size B \<longleftrightarrow> size A < size B"
  by auto

lemma tricky_subst:
  assumes a1: "b\<sharp>(c,N)"
    and     a2: "z\<sharp>(x,P)"
    and     a3: "M\<noteq>Ax z b"
  shows "(Cut <c>.N (z).M){b:=(x).P} = Cut <c>.N (z).(M{b:=(x).P})"
  using a1 a2 a3
  apply -
  apply(generate_fresh "coname")
  apply(subgoal_tac "Cut <c>.N (z).M = Cut <ca>.([(ca,c)]\<bullet>N) (z).M")
   apply(simp)
   apply(rule trans)
    apply(rule better_Cut_substc)
     apply(simp)
    apply(simp add: abs_fresh)
   apply(simp)
   apply(subgoal_tac "b\<sharp>([(ca,c)]\<bullet>N)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
   apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
  apply(simp add: trm.inject)
  apply(rule sym)
  apply(simp add: alpha fresh_prod fresh_atm)
  done

text \<open>3rd lemma\<close>

lemma CUT_SNa_aux:
  assumes a1: "<a>:M \<in> (\<parallel><B>\<parallel>)"
    and     a2: "SNa M"
    and     a3: "(x):N \<in> (\<parallel>(B)\<parallel>)"
    and     a4: "SNa N"
  shows   "SNa (Cut <a>.M (x).N)"
  using a1 a2 a3 a4 [[simproc del: defined_all]]
  apply(induct B M N arbitrary: a x rule: my_wf_induct_triple''[OF wf_measure_triple])
  apply(rule SNaI)
  apply(drule Cut_a_redu_elim)
  apply(erule disjE)
    (* left-inner reduction *)
   apply(erule exE)
   apply(erule conjE)+
   apply(simp)
   apply(drule_tac x="x1" in meta_spec)
   apply(drule_tac x="M'a" in meta_spec)
   apply(drule_tac x="x3" in meta_spec)
   apply(drule conjunct2)
   apply(drule mp)
    apply(rule conjI)
     apply(simp)
    apply(rule disjI1)
    apply(simp add: SNa_Redu_def)
   apply(drule_tac x="a" in spec)
   apply(drule mp)
    apply(simp add: CANDs_preserved_single)
   apply(drule mp)
    apply(simp add: a_preserves_SNa)
   apply(drule_tac x="x" in spec)
   apply(simp)
  apply(erule disjE)
    (* right-inner reduction *)
   apply(erule exE)
   apply(erule conjE)+
   apply(simp)
   apply(drule_tac x="x1" in meta_spec)
   apply(drule_tac x="x2" in meta_spec)
   apply(drule_tac x="N'" in meta_spec)
   apply(drule conjunct2)
   apply(drule mp)
    apply(rule conjI)
     apply(simp)
    apply(rule disjI2)
    apply(simp add: SNa_Redu_def)
   apply(drule_tac x="a" in spec)
   apply(drule mp)
    apply(simp add: CANDs_preserved_single)
   apply(drule mp)
    apply(assumption)
   apply(drule_tac x="x" in spec)
   apply(drule mp)
    apply(simp add: CANDs_preserved_single)
   apply(drule mp)
    apply(simp add: a_preserves_SNa)
   apply(assumption)
  apply(erule disjE)
    (******** c-reduction *********)
   apply(drule Cut_c_redu_elim)
    (* c-left reduction*)
   apply(erule disjE)
    apply(erule conjE)
    apply(frule_tac B="x1" in fic_CANDS)
     apply(simp)
    apply(erule disjE)
    (* in AXIOMSc *)
     apply(simp add: AXIOMSc_def)
     apply(erule exE)+
     apply(simp add: ctrm.inject)
     apply(simp add: alpha)
     apply(erule disjE)
      apply(simp)
      apply(rule impI)
      apply(simp)
      apply(subgoal_tac "fic (Ax y b) b")(*A*)
       apply(simp)
    (*A*)
      apply(auto)[1]
     apply(simp)
     apply(rule impI)
     apply(simp)
     apply(subgoal_tac "fic (Ax ([(a,aa)]\<bullet>y) a) a")(*B*)
      apply(simp)
    (*B*)
     apply(auto)[1]
    (* in BINDINGc *)
    apply(simp)
    apply(drule BINDINGc_elim)
    apply(simp)
    (* c-right reduction*)
   apply(erule conjE)
   apply(frule_tac B="x1" in fin_CANDS)
    apply(simp)
   apply(erule disjE)
    (* in AXIOMSc *)
    apply(simp add: AXIOMSn_def)
    apply(erule exE)+
    apply(simp add: ntrm.inject)
    apply(simp add: alpha)
    apply(erule disjE)
     apply(simp)
     apply(rule impI)
     apply(simp)
     apply(subgoal_tac "fin (Ax xa b) xa")(*A*)
      apply(simp)
    (*A*)
     apply(auto)[1]
    apply(simp)
    apply(rule impI)
    apply(simp)
    apply(subgoal_tac "fin (Ax x ([(x,xa)]\<bullet>b)) x")(*B*)
     apply(simp)
    (*B*)
    apply(auto)[1]
    (* in BINDINGc *)
   apply(simp)
   apply(drule BINDINGn_elim)
   apply(simp)
    (*********** l-reductions ************)
  apply(drule Cut_l_redu_elim)
  apply(erule disjE)
    (* ax1 *)
   apply(erule exE)
   apply(simp)
   apply(simp add: SNa_preserved_renaming1)
  apply(erule disjE)
    (* ax2 *)
   apply(erule exE)
   apply(simp add: SNa_preserved_renaming2)
  apply(erule disjE)
    (* LNot *)
   apply(erule exE)+
   apply(auto)[1]
   apply(frule_tac excluded_m)
    apply(assumption)
   apply(erule disjE)
    (* one of them in BINDING *)
    apply(erule disjE)
     apply(drule fin_elims)
     apply(drule fic_elims)
     apply(simp)
     apply(drule BINDINGc_elim)
     apply(drule_tac x="x" in spec)
     apply(drule_tac x="NotL <b>.N' x" in spec)
     apply(simp)
     apply(simp add: better_NotR_substc)
     apply(generate_fresh "coname")
     apply(subgoal_tac "fresh_fun (\<lambda>a'. Cut <a'>.NotR (y).M'a a' (x).NotL <b>.N' x) 
                   =  Cut <c>.NotR (y).M'a c (x).NotL <b>.N' x")
      apply(simp)
      apply(subgoal_tac "Cut <c>.NotR (y).M'a c (x).NotL <b>.N' x \<longrightarrow>\<^sub>a Cut <b>.N' (y).M'a")
       apply(simp only: a_preserves_SNa)
      apply(rule al_redu)
      apply(rule better_LNot_intro)
       apply(simp)
      apply(simp)
     apply(fresh_fun_simp (no_asm))
     apply(simp)
    (* other case of in BINDING *)
    apply(drule fin_elims)
    apply(drule fic_elims)
    apply(simp)
    apply(drule BINDINGn_elim)
    apply(drule_tac x="a" in spec)
    apply(drule_tac x="NotR (y).M'a a" in spec)
    apply(simp)
    apply(simp add: better_NotL_substn)
    apply(generate_fresh "name")
    apply(subgoal_tac "fresh_fun (\<lambda>x'. Cut <a>.NotR (y).M'a a (x').NotL <b>.N' x') 
                   = Cut <a>.NotR (y).M'a a (c).NotL <b>.N' c")
     apply(simp)
     apply(subgoal_tac "Cut <a>.NotR (y).M'a a (c).NotL <b>.N' c \<longrightarrow>\<^sub>a Cut <b>.N' (y).M'a")
      apply(simp only: a_preserves_SNa)
     apply(rule al_redu)
     apply(rule better_LNot_intro)
      apply(simp)
     apply(simp)
    apply(fresh_fun_simp (no_asm))
    apply(simp)
    (* none of them in BINDING *)
   apply(simp)
   apply(erule conjE)
   apply(frule CAND_NotR_elim)
    apply(assumption)
   apply(erule exE)
   apply(frule CAND_NotL_elim)
    apply(assumption)
   apply(erule exE)
   apply(simp only: ty.inject)
   apply(drule_tac x="B'" in meta_spec)
   apply(drule_tac x="N'" in meta_spec)
   apply(drule_tac x="M'a" in meta_spec)
   apply(erule conjE)+
   apply(drule mp)
    apply(simp)
   apply(drule_tac x="b" in spec)
   apply(rotate_tac 13)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 13)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(drule_tac x="y" in spec)
   apply(rotate_tac 13)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 13)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* LAnd1 case *)
  apply(erule disjE)
   apply(erule exE)+
   apply(auto)[1]
   apply(frule_tac excluded_m)
    apply(assumption)
   apply(erule disjE)
    (* one of them in BINDING *)
    apply(erule disjE)
     apply(drule fin_elims)
     apply(drule fic_elims)
     apply(simp)
     apply(drule BINDINGc_elim)
     apply(drule_tac x="x" in spec)
     apply(drule_tac x="AndL1 (y).N' x" in spec)
     apply(simp)
     apply(simp add: better_AndR_substc)
     apply(generate_fresh "coname")
     apply(subgoal_tac "fresh_fun (\<lambda>a'. Cut <a'>.AndR <b>.M1 <c>.M2 a' (x).AndL1 (y).N' x) 
                   = Cut <ca>.AndR <b>.M1 <c>.M2 ca (x).AndL1 (y).N' x")
      apply(simp)
      apply(subgoal_tac "Cut <ca>.AndR <b>.M1 <c>.M2 ca (x).AndL1 (y).N' x \<longrightarrow>\<^sub>a Cut <b>.M1 (y).N'")
       apply(auto intro: a_preserves_SNa)[1]
      apply(rule al_redu)
      apply(rule better_LAnd1_intro)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
      apply(simp)
     apply(fresh_fun_simp (no_asm))
     apply(simp)
    (* other case of in BINDING *)
    apply(drule fin_elims)
    apply(drule fic_elims)
    apply(simp)
    apply(drule BINDINGn_elim)
    apply(drule_tac x="a" in spec)
    apply(drule_tac x="AndR <b>.M1 <c>.M2 a" in spec)
    apply(simp)
    apply(simp add: better_AndL1_substn)
    apply(generate_fresh "name")
    apply(subgoal_tac "fresh_fun (\<lambda>z'. Cut <a>.AndR <b>.M1 <c>.M2 a (z').AndL1 (y).N' z') 
                   = Cut <a>.AndR <b>.M1 <c>.M2 a (ca).AndL1 (y).N' ca")
     apply(simp)
     apply(subgoal_tac "Cut <a>.AndR <b>.M1 <c>.M2 a (ca).AndL1 (y).N' ca \<longrightarrow>\<^sub>a Cut <b>.M1 (y).N'")
      apply(auto intro: a_preserves_SNa)[1]
     apply(rule al_redu)
     apply(rule better_LAnd1_intro)
      apply(simp add: abs_fresh fresh_prod fresh_atm) 
     apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(fresh_fun_simp (no_asm))
    apply(simp)
    (* none of them in BINDING *)
   apply(simp)
   apply(erule conjE)
   apply(frule CAND_AndR_elim)
    apply(assumption)
   apply(erule exE)
   apply(frule CAND_AndL1_elim)
    apply(assumption)
   apply(erule exE)+
   apply(simp only: ty.inject)
   apply(drule_tac x="B1" in meta_spec)
   apply(drule_tac x="M1" in meta_spec)
   apply(drule_tac x="N'" in meta_spec)
   apply(erule conjE)+
   apply(drule mp)
    apply(simp)
   apply(drule_tac x="b" in spec)
   apply(rotate_tac 14)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 14)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(drule_tac x="y" in spec)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* LAnd2 case *)
  apply(erule disjE)
   apply(erule exE)+
   apply(auto)[1]
   apply(frule_tac excluded_m)
    apply(assumption)
   apply(erule disjE)
    (* one of them in BINDING *)
    apply(erule disjE)
     apply(drule fin_elims)
     apply(drule fic_elims)
     apply(simp)
     apply(drule BINDINGc_elim)
     apply(drule_tac x="x" in spec)
     apply(drule_tac x="AndL2 (y).N' x" in spec)
     apply(simp)
     apply(simp add: better_AndR_substc)
     apply(generate_fresh "coname")
     apply(subgoal_tac "fresh_fun (\<lambda>a'. Cut <a'>.AndR <b>.M1 <c>.M2 a' (x).AndL2 (y).N' x) 
                   = Cut <ca>.AndR <b>.M1 <c>.M2 ca (x).AndL2 (y).N' x")
      apply(simp)
      apply(subgoal_tac "Cut <ca>.AndR <b>.M1 <c>.M2 ca (x).AndL2 (y).N' x \<longrightarrow>\<^sub>a Cut <c>.M2 (y).N'")
       apply(auto intro: a_preserves_SNa)[1]
      apply(rule al_redu)
      apply(rule better_LAnd2_intro)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
      apply(simp)
     apply(fresh_fun_simp (no_asm))
     apply(simp)
    (* other case of in BINDING *)
    apply(drule fin_elims)
    apply(drule fic_elims)
    apply(simp)
    apply(drule BINDINGn_elim)
    apply(drule_tac x="a" in spec)
    apply(drule_tac x="AndR <b>.M1 <c>.M2 a" in spec)
    apply(simp)
    apply(simp add: better_AndL2_substn)
    apply(generate_fresh "name")
    apply(subgoal_tac "fresh_fun (\<lambda>z'. Cut <a>.AndR <b>.M1 <c>.M2 a (z').AndL2 (y).N' z') 
                   = Cut <a>.AndR <b>.M1 <c>.M2 a (ca).AndL2 (y).N' ca")
     apply(simp)
     apply(subgoal_tac "Cut <a>.AndR <b>.M1 <c>.M2 a (ca).AndL2 (y).N' ca \<longrightarrow>\<^sub>a Cut <c>.M2 (y).N'")
      apply(auto intro: a_preserves_SNa)[1]
     apply(rule al_redu)
     apply(rule better_LAnd2_intro)
      apply(simp add: abs_fresh fresh_prod fresh_atm) 
     apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(fresh_fun_simp (no_asm))
    apply(simp)
    (* none of them in BINDING *)
   apply(simp)
   apply(erule conjE)
   apply(frule CAND_AndR_elim)
    apply(assumption)
   apply(erule exE)
   apply(frule CAND_AndL2_elim)
    apply(assumption)
   apply(erule exE)+
   apply(simp only: ty.inject)
   apply(drule_tac x="B2" in meta_spec)
   apply(drule_tac x="M2" in meta_spec)
   apply(drule_tac x="N'" in meta_spec)
   apply(erule conjE)+
   apply(drule mp)
    apply(simp)
   apply(drule_tac x="c" in spec)
   apply(rotate_tac 14)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 14)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(drule_tac x="y" in spec)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* LOr1 case *)
  apply(erule disjE)
   apply(erule exE)+
   apply(auto)[1]
   apply(frule_tac excluded_m)
    apply(assumption)
   apply(erule disjE)
    (* one of them in BINDING *)
    apply(erule disjE)
     apply(drule fin_elims)
     apply(drule fic_elims)
     apply(simp)
     apply(drule BINDINGc_elim)
     apply(drule_tac x="x" in spec)
     apply(drule_tac x="OrL (z).M1 (y).M2 x" in spec)
     apply(simp)
     apply(simp add: better_OrR1_substc)
     apply(generate_fresh "coname")
     apply(subgoal_tac "fresh_fun (\<lambda>a'. Cut <a'>.OrR1 <b>.N' a' (x).OrL (z).M1 (y).M2 x) 
                   = Cut <c>.OrR1 <b>.N' c (x).OrL (z).M1 (y).M2 x")
      apply(simp)
      apply(subgoal_tac "Cut <c>.OrR1 <b>.N' c (x).OrL (z).M1 (y).M2 x \<longrightarrow>\<^sub>a Cut <b>.N' (z).M1")
       apply(auto intro: a_preserves_SNa)[1]
      apply(rule al_redu)
      apply(rule better_LOr1_intro)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
      apply(simp add: abs_fresh)
     apply(fresh_fun_simp (no_asm))
     apply(simp)
    (* other case of in BINDING *)
    apply(drule fin_elims)
    apply(drule fic_elims)
    apply(simp)
    apply(drule BINDINGn_elim)
    apply(drule_tac x="a" in spec)
    apply(drule_tac x="OrR1 <b>.N' a" in spec)
    apply(simp)
    apply(simp add: better_OrL_substn)
    apply(generate_fresh "name")
    apply(subgoal_tac "fresh_fun (\<lambda>z'. Cut <a>.OrR1 <b>.N' a (z').OrL (z).M1 (y).M2 z') 
                   = Cut <a>.OrR1 <b>.N' a (c).OrL (z).M1 (y).M2 c")
     apply(simp)
     apply(subgoal_tac "Cut <a>.OrR1 <b>.N' a (c).OrL (z).M1 (y).M2 c \<longrightarrow>\<^sub>a Cut <b>.N' (z).M1")
      apply(auto intro: a_preserves_SNa)[1]
     apply(rule al_redu)
     apply(rule better_LOr1_intro)
      apply(simp add: abs_fresh fresh_prod fresh_atm) 
     apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(fresh_fun_simp (no_asm))
    apply(simp)
    (* none of them in BINDING *)
   apply(simp)
   apply(erule conjE)
   apply(frule CAND_OrR1_elim)
    apply(assumption)
   apply(erule exE)+
   apply(frule CAND_OrL_elim)
    apply(assumption)
   apply(erule exE)+
   apply(simp only: ty.inject)
   apply(drule_tac x="B1" in meta_spec)
   apply(drule_tac x="N'" in meta_spec)
   apply(drule_tac x="M1" in meta_spec)
   apply(erule conjE)+
   apply(drule mp)
    apply(simp)
   apply(drule_tac x="b" in spec)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(drule_tac x="z" in spec)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* LOr2 case *)
  apply(erule disjE)
   apply(erule exE)+
   apply(auto)[1]
   apply(frule_tac excluded_m)
    apply(assumption)
   apply(erule disjE)
    (* one of them in BINDING *)
    apply(erule disjE)
     apply(drule fin_elims)
     apply(drule fic_elims)
     apply(simp)
     apply(drule BINDINGc_elim)
     apply(drule_tac x="x" in spec)
     apply(drule_tac x="OrL (z).M1 (y).M2 x" in spec)
     apply(simp)
     apply(simp add: better_OrR2_substc)
     apply(generate_fresh "coname")
     apply(subgoal_tac "fresh_fun (\<lambda>a'. Cut <a'>.OrR2 <b>.N' a' (x).OrL (z).M1 (y).M2 x) 
                   = Cut <c>.OrR2 <b>.N' c (x).OrL (z).M1 (y).M2 x")
      apply(simp)
      apply(subgoal_tac "Cut <c>.OrR2 <b>.N' c (x).OrL (z).M1 (y).M2 x \<longrightarrow>\<^sub>a Cut <b>.N' (y).M2")
       apply(auto intro: a_preserves_SNa)[1]
      apply(rule al_redu)
      apply(rule better_LOr2_intro)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
      apply(simp add: abs_fresh)
     apply(fresh_fun_simp (no_asm))
     apply(simp)
    (* other case of in BINDING *)
    apply(drule fin_elims)
    apply(drule fic_elims)
    apply(simp)
    apply(drule BINDINGn_elim)
    apply(drule_tac x="a" in spec)
    apply(drule_tac x="OrR2 <b>.N' a" in spec)
    apply(simp)
    apply(simp add: better_OrL_substn)
    apply(generate_fresh "name")
    apply(subgoal_tac "fresh_fun (\<lambda>z'. Cut <a>.OrR2 <b>.N' a (z').OrL (z).M1 (y).M2 z') 
                   = Cut <a>.OrR2 <b>.N' a (c).OrL (z).M1 (y).M2 c")
     apply(simp)
     apply(subgoal_tac "Cut <a>.OrR2 <b>.N' a (c).OrL (z).M1 (y).M2 c \<longrightarrow>\<^sub>a Cut <b>.N' (y).M2")
      apply(auto intro: a_preserves_SNa)[1]
     apply(rule al_redu)
     apply(rule better_LOr2_intro)
      apply(simp add: abs_fresh fresh_prod fresh_atm) 
     apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(fresh_fun_simp (no_asm))
    apply(simp)
    (* none of them in BINDING *)
   apply(simp)
   apply(erule conjE)
   apply(frule CAND_OrR2_elim)
    apply(assumption)
   apply(erule exE)+
   apply(frule CAND_OrL_elim)
    apply(assumption)
   apply(erule exE)+
   apply(simp only: ty.inject)
   apply(drule_tac x="B2" in meta_spec)
   apply(drule_tac x="N'" in meta_spec)
   apply(drule_tac x="M2" in meta_spec)
   apply(erule conjE)+
   apply(drule mp)
    apply(simp)
   apply(drule_tac x="b" in spec)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(drule_tac x="y" in spec)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* LImp case *)
  apply(erule exE)+
  apply(auto)[1]
  apply(frule_tac excluded_m)
   apply(assumption)
  apply(erule disjE)
    (* one of them in BINDING *)
   apply(erule disjE)
    apply(drule fin_elims)
    apply(drule fic_elims)
    apply(simp)
    apply(drule BINDINGc_elim)
    apply(drule_tac x="x" in spec)
    apply(drule_tac x="ImpL <c>.N1 (y).N2 x" in spec)
    apply(simp)
    apply(simp add: better_ImpR_substc)
    apply(generate_fresh "coname")
    apply(subgoal_tac "fresh_fun (\<lambda>a'. Cut <a'>.ImpR (z).<b>.M'a a' (x).ImpL <c>.N1 (y).N2 x)
                   = Cut <ca>.ImpR (z).<b>.M'a ca (x).ImpL <c>.N1 (y).N2 x")
     apply(simp)
     apply(subgoal_tac "Cut <ca>.ImpR (z).<b>.M'a ca (x).ImpL <c>.N1 (y).N2 x \<longrightarrow>\<^sub>a 
                                                          Cut <b>.Cut <c>.N1 (z).M'a (y).N2")
      apply(auto intro: a_preserves_SNa)[1]
     apply(rule al_redu)
     apply(rule better_LImp_intro)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
      apply(simp add: abs_fresh)
     apply(simp)
    apply(fresh_fun_simp (no_asm))
    apply(simp)
    (* other case of in BINDING *)
   apply(drule fin_elims)
   apply(drule fic_elims)
   apply(simp)
   apply(drule BINDINGn_elim)
   apply(drule_tac x="a" in spec)
   apply(drule_tac x="ImpR (z).<b>.M'a a" in spec)
   apply(simp)
   apply(simp add: better_ImpL_substn)
   apply(generate_fresh "name")
   apply(subgoal_tac "fresh_fun (\<lambda>z'. Cut <a>.ImpR (z).<b>.M'a a (z').ImpL <c>.N1 (y).N2 z')
                   = Cut <a>.ImpR (z).<b>.M'a a (ca).ImpL <c>.N1 (y).N2 ca")
    apply(simp)
    apply(subgoal_tac "Cut <a>.ImpR (z).<b>.M'a a (ca).ImpL <c>.N1 (y).N2 ca \<longrightarrow>\<^sub>a 
                                                          Cut <b>.Cut <c>.N1 (z).M'a (y).N2")
     apply(auto intro: a_preserves_SNa)[1]
    apply(rule al_redu)
    apply(rule better_LImp_intro)
      apply(simp add: abs_fresh fresh_prod fresh_atm) 
     apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(simp)
   apply(fresh_fun_simp (no_asm))
    apply(simp add: abs_fresh abs_supp fin_supp)
   apply(simp add: abs_fresh abs_supp fin_supp)
  apply(simp)
    (* none of them in BINDING *)
  apply(erule conjE)
  apply(frule CAND_ImpL_elim)
   apply(assumption)
  apply(erule exE)+
  apply(frule CAND_ImpR_elim) (* check here *)
   apply(assumption)
  apply(erule exE)+
  apply(erule conjE)+
  apply(simp only: ty.inject)
  apply(erule conjE)+
  apply(case_tac "M'a=Ax z b")
    (* case Ma = Ax z b *)
   apply(rule_tac t="Cut <b>.(Cut <c>.N1 (z).M'a) (y).N2" and s="Cut <b>.(M'a{z:=<c>.N1}) (y).N2" in subst)
    apply(simp)
   apply(drule_tac x="c" in spec)
   apply(drule_tac x="N1" in spec)
   apply(drule mp)
    apply(simp)
   apply(drule_tac x="B2" in meta_spec)
   apply(drule_tac x="M'a{z:=<c>.N1}" in meta_spec)
   apply(drule_tac x="N2" in meta_spec)
   apply(drule conjunct1)
   apply(drule mp)
    apply(simp)
   apply(rotate_tac 17)
   apply(drule_tac x="b" in spec)
   apply(drule mp)
    apply(assumption)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(rotate_tac 17)
   apply(drule_tac x="y" in spec)
   apply(drule mp)
    apply(assumption)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* case Ma \<noteq> Ax z b *)
  apply(subgoal_tac "<b>:Cut <c>.N1 (z).M'a \<in> \<parallel><B2>\<parallel>") (* lemma *)
   apply(frule_tac meta_spec)
   apply(drule_tac x="B2" in meta_spec)
   apply(drule_tac x="Cut <c>.N1 (z).M'a" in meta_spec)
   apply(drule_tac x="N2" in meta_spec)
   apply(erule conjE)+
   apply(drule mp)
    apply(simp)
   apply(rotate_tac 20)
   apply(drule_tac x="b" in spec)
   apply(rotate_tac 20)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 20)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(rotate_tac 20)
   apply(drule_tac x="y" in spec)
   apply(rotate_tac 20)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 20)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* lemma *)
  apply(subgoal_tac "<b>:Cut <c>.N1 (z).M'a \<in> BINDINGc B2 (\<parallel>(B2)\<parallel>)") (* second lemma *)
   apply(simp add: BINDING_implies_CAND)
    (* second lemma *)
  apply(simp (no_asm) add: BINDINGc_def)
  apply(rule exI)+
  apply(rule conjI)
   apply(rule refl)
  apply(rule allI)+
  apply(rule impI)
  apply(generate_fresh "name")
  apply(rule_tac t="Cut <c>.N1 (z).M'a" and s="Cut <c>.N1 (ca).([(ca,z)]\<bullet>M'a)" in subst)
   apply(simp add: trm.inject alpha fresh_prod fresh_atm)
  apply(rule_tac t="(Cut <c>.N1 (ca).([(ca,z)]\<bullet>M'a)){b:=(xa).P}" 
      and s="Cut <c>.N1 (ca).(([(ca,z)]\<bullet>M'a){b:=(xa).P})" in subst)
   apply(rule sym)
   apply(rule tricky_subst)
     apply(simp)
    apply(simp)
   apply(clarify)
   apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
   apply(simp add: calc_atm)
  apply(drule_tac x="B1" in meta_spec)
  apply(drule_tac x="N1" in meta_spec)
  apply(drule_tac x="([(ca,z)]\<bullet>M'a){b:=(xa).P}" in meta_spec)
  apply(drule conjunct1)
  apply(drule mp)
   apply(simp)
  apply(rotate_tac 19)
  apply(drule_tac x="c" in spec)
  apply(drule mp)
   apply(assumption)
  apply(drule mp)
   apply(simp add: CANDs_imply_SNa)
  apply(rotate_tac 19)
  apply(drule_tac x="ca" in spec)
  apply(subgoal_tac "(ca):([(ca,z)]\<bullet>M'a){b:=(xa).P} \<in> \<parallel>(B1)\<parallel>")(*A*)
   apply(drule mp)
    apply(assumption)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (*A*)
  apply(drule_tac x="[(ca,z)]\<bullet>xa" in spec)
  apply(drule_tac x="[(ca,z)]\<bullet>P" in spec)
  apply(rotate_tac 19)
  apply(simp add: fresh_prod fresh_left)
  apply(drule mp)
   apply(rule conjI)
    apply(auto simp add: calc_atm)[1]
   apply(rule conjI)
    apply(auto simp add: calc_atm)[1]
   apply(drule_tac pi="[(ca,z)]" and x="(xa):P" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
   apply(simp add: CAND_eqvt_name)
  apply(drule_tac pi="[(ca,z)]" and X="\<parallel>(B1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
  apply(simp add: CAND_eqvt_name csubst_eqvt)
  apply(perm_simp)
  done


(* parallel substitution *)


lemma CUT_SNa:
  assumes a1: "<a>:M \<in> (\<parallel><B>\<parallel>)"
    and     a2: "(x):N \<in> (\<parallel>(B)\<parallel>)"
  shows   "SNa (Cut <a>.M (x).N)"
  using a1 a2
  apply -
  apply(rule CUT_SNa_aux[OF a1])
    apply(simp_all add: CANDs_imply_SNa)
  done 


fun 
  findn :: "(name\<times>coname\<times>trm) list\<Rightarrow>name\<Rightarrow>(coname\<times>trm) option"
  where
    "findn [] x = None"
  | "findn ((y,c,P)#\<theta>_n) x = (if y=x then Some (c,P) else findn \<theta>_n x)"

lemma findn_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>findn \<theta>_n x) = findn (pi1\<bullet>\<theta>_n) (pi1\<bullet>x)" 
    and   "(pi2\<bullet>findn \<theta>_n x) = findn (pi2\<bullet>\<theta>_n) (pi2\<bullet>x)"
   apply(induct \<theta>_n)
     apply(auto simp add: perm_bij) 
  done

lemma findn_fresh:
  assumes a: "x\<sharp>\<theta>_n"
  shows "findn \<theta>_n x = None"
  using a
  apply(induct \<theta>_n)
   apply(auto simp add: fresh_list_cons fresh_atm fresh_prod)
  done

fun 
  findc :: "(coname\<times>name\<times>trm) list\<Rightarrow>coname\<Rightarrow>(name\<times>trm) option"
  where
    "findc [] x = None"
  | "findc ((c,y,P)#\<theta>_c) a = (if a=c then Some (y,P) else findc \<theta>_c a)"

lemma findc_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>findc \<theta>_c a) = findc (pi1\<bullet>\<theta>_c) (pi1\<bullet>a)" 
    and   "(pi2\<bullet>findc \<theta>_c a) = findc (pi2\<bullet>\<theta>_c) (pi2\<bullet>a)"
   apply(induct \<theta>_c)
     apply(auto simp add: perm_bij) 
  done

lemma findc_fresh:
  assumes a: "a\<sharp>\<theta>_c"
  shows "findc \<theta>_c a = None"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_list_cons fresh_atm fresh_prod)
  done

abbreviation 
  nmaps :: "(name\<times>coname\<times>trm) list \<Rightarrow> name \<Rightarrow> (coname\<times>trm) option \<Rightarrow> bool" (\<open>_ nmaps _ to _\<close> [55,55,55] 55) 
  where
    "\<theta>_n nmaps x to P \<equiv> (findn \<theta>_n x) = P"

abbreviation 
  cmaps :: "(coname\<times>name\<times>trm) list \<Rightarrow> coname \<Rightarrow> (name\<times>trm) option \<Rightarrow> bool" (\<open>_ cmaps _ to _\<close> [55,55,55] 55) 
  where
    "\<theta>_c cmaps a to P \<equiv> (findc \<theta>_c a) = P"

lemma nmaps_fresh:
  shows "\<theta>_n nmaps x to Some (c,P) \<Longrightarrow> a\<sharp>\<theta>_n \<Longrightarrow> a\<sharp>(c,P)"
  apply(induct \<theta>_n)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
   apply(case_tac "aa=x")
    apply(auto)
  apply(case_tac "aa=x")
   apply(auto)
  done

lemma cmaps_fresh:
  shows "\<theta>_c cmaps a to Some (y,P) \<Longrightarrow> x\<sharp>\<theta>_c \<Longrightarrow> x\<sharp>(y,P)"
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
   apply(case_tac "a=aa")
    apply(auto)
  apply(case_tac "a=aa")
   apply(auto)
  done

lemma nmaps_false:
  shows "\<theta>_n nmaps x to Some (c,P) \<Longrightarrow> x\<sharp>\<theta>_n \<Longrightarrow> False"
  apply(induct \<theta>_n)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

lemma cmaps_false:
  shows "\<theta>_c cmaps c to Some (x,P) \<Longrightarrow> c\<sharp>\<theta>_c \<Longrightarrow> False"
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

fun 
  lookupa :: "name\<Rightarrow>coname\<Rightarrow>(coname\<times>name\<times>trm) list\<Rightarrow>trm"
  where
    "lookupa x a [] = Ax x a"
  | "lookupa x a ((c,y,P)#\<theta>_c) = (if a=c then Cut <a>.Ax x a (y).P else lookupa x a \<theta>_c)"

lemma lookupa_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(lookupa x a \<theta>_c)) = lookupa (pi1\<bullet>x) (pi1\<bullet>a) (pi1\<bullet>\<theta>_c)"
    and   "(pi2\<bullet>(lookupa x a \<theta>_c)) = lookupa (pi2\<bullet>x) (pi2\<bullet>a) (pi2\<bullet>\<theta>_c)"
   apply -
   apply(induct \<theta>_c)
    apply(auto simp add: eqvts)
  apply(induct \<theta>_c)
   apply(auto simp add: eqvts)
  done

lemma lookupa_fire:
  assumes a: "\<theta>_c cmaps a to Some (y,P)"
  shows "(lookupa x a \<theta>_c) = Cut <a>.Ax x a (y).P"
  using a
  apply(induct \<theta>_c arbitrary: x a y P)
   apply(auto)
  done

fun 
  lookupb :: "name\<Rightarrow>coname\<Rightarrow>(coname\<times>name\<times>trm) list\<Rightarrow>coname\<Rightarrow>trm\<Rightarrow>trm"
  where
    "lookupb x a [] c P = Cut <c>.P (x).Ax x a"
  | "lookupb x a ((d,y,N)#\<theta>_c) c P = (if a=d then Cut <c>.P (y).N  else lookupb x a \<theta>_c c P)"

lemma lookupb_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(lookupb x a \<theta>_c c P)) = lookupb (pi1\<bullet>x) (pi1\<bullet>a) (pi1\<bullet>\<theta>_c) (pi1\<bullet>c) (pi1\<bullet>P)"
    and   "(pi2\<bullet>(lookupb x a \<theta>_c c P)) = lookupb (pi2\<bullet>x) (pi2\<bullet>a) (pi2\<bullet>\<theta>_c) (pi2\<bullet>c) (pi2\<bullet>P)"
   apply -
   apply(induct \<theta>_c)
    apply(auto simp add: eqvts)
  apply(induct \<theta>_c)
   apply(auto simp add: eqvts)
  done

fun 
  lookup :: "name\<Rightarrow>coname\<Rightarrow>(name\<times>coname\<times>trm) list\<Rightarrow>(coname\<times>name\<times>trm) list\<Rightarrow>trm"
  where
    "lookup x a [] \<theta>_c = lookupa x a \<theta>_c"
  | "lookup x a ((y,c,P)#\<theta>_n) \<theta>_c = (if x=y then (lookupb x a \<theta>_c c P) else lookup x a \<theta>_n \<theta>_c)"

lemma lookup_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(lookup x a \<theta>_n \<theta>_c)) = lookup (pi1\<bullet>x) (pi1\<bullet>a) (pi1\<bullet>\<theta>_n) (pi1\<bullet>\<theta>_c)"
    and   "(pi2\<bullet>(lookup x a \<theta>_n \<theta>_c)) = lookup (pi2\<bullet>x) (pi2\<bullet>a) (pi2\<bullet>\<theta>_n) (pi2\<bullet>\<theta>_c)"
   apply -
   apply(induct \<theta>_n)
    apply(auto simp add: eqvts)
  apply(induct \<theta>_n)
   apply(auto simp add: eqvts)
  done

fun 
  lookupc :: "name\<Rightarrow>coname\<Rightarrow>(name\<times>coname\<times>trm) list\<Rightarrow>trm"
  where
    "lookupc x a [] = Ax x a"
  | "lookupc x a ((y,c,P)#\<theta>_n) = (if x=y then P[c\<turnstile>c>a] else lookupc x a \<theta>_n)"

lemma lookupc_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(lookupc x a \<theta>_n)) = lookupc (pi1\<bullet>x) (pi1\<bullet>a) (pi1\<bullet>\<theta>_n)"
    and   "(pi2\<bullet>(lookupc x a \<theta>_n)) = lookupc (pi2\<bullet>x) (pi2\<bullet>a) (pi2\<bullet>\<theta>_n)"
   apply -
   apply(induct \<theta>_n)
    apply(auto simp add: eqvts)
  apply(induct \<theta>_n)
   apply(auto simp add: eqvts)
  done

fun 
  lookupd :: "name\<Rightarrow>coname\<Rightarrow>(coname\<times>name\<times>trm) list\<Rightarrow>trm"
  where
    "lookupd x a [] = Ax x a"
  | "lookupd x a ((c,y,P)#\<theta>_c) = (if a=c then P[y\<turnstile>n>x] else lookupd x a \<theta>_c)"

lemma lookupd_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(lookupd x a \<theta>_n)) = lookupd (pi1\<bullet>x) (pi1\<bullet>a) (pi1\<bullet>\<theta>_n)"
    and   "(pi2\<bullet>(lookupd x a \<theta>_n)) = lookupd (pi2\<bullet>x) (pi2\<bullet>a) (pi2\<bullet>\<theta>_n)"
   apply -
   apply(induct \<theta>_n)
    apply(auto simp add: eqvts)
  apply(induct \<theta>_n)
   apply(auto simp add: eqvts)
  done

lemma lookupa_fresh:
  assumes a: "a\<sharp>\<theta>_c"
  shows "lookupa y a \<theta>_c = Ax y a"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_prod fresh_list_cons fresh_atm)
  done

lemma lookupa_csubst:
  assumes a: "a\<sharp>\<theta>_c"
  shows "Cut <a>.Ax y a (x).P = (lookupa y a \<theta>_c){a:=(x).P}"
  using a by (simp add: lookupa_fresh)

lemma lookupa_freshness:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(\<theta>_c,c) \<Longrightarrow> a\<sharp>lookupa y c \<theta>_c"
    and   "x\<sharp>(\<theta>_c,y) \<Longrightarrow> x\<sharp>lookupa y c \<theta>_c"
   apply(induct \<theta>_c)
     apply(auto simp add: fresh_prod fresh_list_cons abs_fresh fresh_atm)
  done

lemma lookupa_unicity:
  assumes a: "lookupa x a \<theta>_c= Ax y b" "b\<sharp>\<theta>_c" "y\<sharp>\<theta>_c"
  shows "x=y \<and> a=b"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: trm.inject fresh_list_cons fresh_prod fresh_atm)
   apply(case_tac "a=aa")
    apply(auto)
  apply(case_tac "a=aa")
   apply(auto)
  done

lemma lookupb_csubst:
  assumes a: "a\<sharp>(\<theta>_c,c,N)"
  shows "Cut <c>.N (x).P = (lookupb y a \<theta>_c c N){a:=(x).P}"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_list_cons fresh_atm fresh_prod)
  apply(rule sym)
  apply(generate_fresh "name")
  apply(generate_fresh "coname")
  apply(subgoal_tac "Cut <c>.N (y).Ax y a = Cut <caa>.([(caa,c)]\<bullet>N) (ca).Ax ca a")
   apply(simp)
   apply(rule trans)
    apply(rule better_Cut_substc)
     apply(simp)
    apply(simp add: abs_fresh)
   apply(simp)
   apply(subgoal_tac "a\<sharp>([(caa,c)]\<bullet>N)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
   apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
  apply(simp add: trm.inject)
  apply(rule conjI)
   apply(rule sym)
   apply(simp add: alpha fresh_prod fresh_atm)
  apply(simp add: alpha calc_atm fresh_prod fresh_atm)
  done

lemma lookupb_freshness:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(\<theta>_c,c,b,P) \<Longrightarrow> a\<sharp>lookupb y c \<theta>_c b P"
    and   "x\<sharp>(\<theta>_c,y,P) \<Longrightarrow> x\<sharp>lookupb y c \<theta>_c b P"
   apply(induct \<theta>_c)
     apply(auto simp add: fresh_prod fresh_list_cons abs_fresh fresh_atm)
  done

lemma lookupb_unicity:
  assumes a: "lookupb x a \<theta>_c c P = Ax y b" "b\<sharp>(\<theta>_c,c,P)" "y\<sharp>\<theta>_c"
  shows "x=y \<and> a=b"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
   apply(case_tac "a=aa")
    apply(auto)
  apply(case_tac "a=aa")
   apply(auto)
  done

lemma lookupb_lookupa:
  assumes a: "x\<sharp>\<theta>_c"
  shows "lookupb x c \<theta>_c a P = (lookupa x c \<theta>_c){x:=<a>.P}"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_list_cons fresh_prod)
  apply(generate_fresh "coname")
  apply(generate_fresh "name")
  apply(subgoal_tac "Cut <c>.Ax x c (aa).b = Cut <ca>.Ax x ca (caa).([(caa,aa)]\<bullet>b)")
   apply(simp)
   apply(rule sym)
   apply(rule trans)
    apply(rule better_Cut_substn)
     apply(simp add: abs_fresh)
    apply(simp)
   apply(simp)
   apply(subgoal_tac "x\<sharp>([(caa,aa)]\<bullet>b)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
   apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(simp add: trm.inject)
  apply(rule conjI)
   apply(simp add: alpha calc_atm fresh_atm fresh_prod)
  apply(rule sym)
  apply(simp add: alpha calc_atm fresh_atm fresh_prod)
  done

lemma lookup_csubst:
  assumes a: "a\<sharp>(\<theta>_n,\<theta>_c)"
  shows "lookup y c \<theta>_n ((a,x,P)#\<theta>_c) = (lookup y c \<theta>_n \<theta>_c){a:=(x).P}"
  using a
  apply(induct \<theta>_n)
   apply(auto simp add: fresh_prod fresh_list_cons)
     apply(simp add: lookupa_csubst)
    apply(simp add: lookupa_freshness forget fresh_atm fresh_prod)
   apply(rule lookupb_csubst)
   apply(simp)
  apply(auto simp add: lookupb_freshness forget fresh_atm fresh_prod)
  done

lemma lookup_fresh:
  assumes a: "x\<sharp>(\<theta>_n,\<theta>_c)"
  shows "lookup x c \<theta>_n \<theta>_c = lookupa x c \<theta>_c"
  using a
  apply(induct \<theta>_n)
   apply(auto simp add: fresh_prod fresh_list_cons fresh_atm)
  done

lemma lookup_unicity:
  assumes a: "lookup x a \<theta>_n \<theta>_c= Ax y b" "b\<sharp>(\<theta>_c,\<theta>_n)" "y\<sharp>(\<theta>_c,\<theta>_n)"
  shows "x=y \<and> a=b"
  using a
  apply(induct \<theta>_n)
   apply(auto simp add: trm.inject fresh_list_cons fresh_prod fresh_atm)
     apply(drule lookupa_unicity)
       apply(simp)+
    apply(drule lookupa_unicity)
      apply(simp)+
   apply(case_tac "x=aa")
    apply(auto)
   apply(drule lookupb_unicity)
     apply(simp add: fresh_atm)
    apply(simp)
   apply(simp)
  apply(case_tac "x=aa")
   apply(auto)
  apply(drule lookupb_unicity)
    apply(simp add: fresh_atm)
   apply(simp)
  apply(simp)
  done

lemma lookup_freshness:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(c,\<theta>_c,\<theta>_n) \<Longrightarrow> a\<sharp>lookup y c \<theta>_n \<theta>_c"
    and   "x\<sharp>(y,\<theta>_c,\<theta>_n) \<Longrightarrow> x\<sharp>lookup y c \<theta>_n \<theta>_c"   
   apply(induct \<theta>_n)
     apply(auto simp add: fresh_prod fresh_list_cons abs_fresh fresh_atm)
     apply(simp add: fresh_atm fresh_prod lookupa_freshness)
    apply(simp add: fresh_atm fresh_prod lookupa_freshness)
   apply(simp add: fresh_atm fresh_prod lookupb_freshness)
  apply(simp add: fresh_atm fresh_prod lookupb_freshness)
  done

lemma lookupc_freshness:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(\<theta>_c,c) \<Longrightarrow> a\<sharp>lookupc y c \<theta>_c"
    and   "x\<sharp>(\<theta>_c,y) \<Longrightarrow> x\<sharp>lookupc y c \<theta>_c"
   apply(induct \<theta>_c)
     apply(auto simp add: fresh_prod fresh_list_cons abs_fresh fresh_atm)
   apply(rule rename_fresh)
   apply(simp add: fresh_atm)
  apply(rule rename_fresh)
  apply(simp add: fresh_atm)
  done

lemma lookupc_fresh:
  assumes a: "y\<sharp>\<theta>_n"
  shows "lookupc y a \<theta>_n = Ax y a"
  using a
  apply(induct \<theta>_n)
   apply(auto simp add: fresh_prod fresh_list_cons fresh_atm)
  done

lemma lookupc_nmaps:
  assumes a: "\<theta>_n nmaps x to Some (c,P)"
  shows "lookupc x a \<theta>_n = P[c\<turnstile>c>a]"
  using a
  apply(induct \<theta>_n)
   apply(auto)
  done 

lemma lookupc_unicity:
  assumes a: "lookupc y a \<theta>_n = Ax x b" "x\<sharp>\<theta>_n"
  shows "y=x"
  using a
  apply(induct \<theta>_n)
   apply(auto simp add: trm.inject fresh_list_cons fresh_prod)
  apply(case_tac "y=aa")
   apply(auto)
  apply(subgoal_tac "x\<sharp>(ba[aa\<turnstile>c>a])")
   apply(simp add: fresh_atm)
  apply(rule rename_fresh)
  apply(simp)
  done

lemma lookupd_fresh:
  assumes a: "a\<sharp>\<theta>_c"
  shows "lookupd y a \<theta>_c = Ax y a"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_prod fresh_list_cons fresh_atm)
  done 

lemma lookupd_unicity:
  assumes a: "lookupd y a \<theta>_c = Ax y b" "b\<sharp>\<theta>_c"
  shows "a=b"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: trm.inject fresh_list_cons fresh_prod)
  apply(case_tac "a=aa")
   apply(auto)
  apply(subgoal_tac "b\<sharp>(ba[aa\<turnstile>n>y])")
   apply(simp add: fresh_atm)
  apply(rule rename_fresh)
  apply(simp)
  done

lemma lookupd_freshness:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(\<theta>_c,c) \<Longrightarrow> a\<sharp>lookupd y c \<theta>_c"
    and   "x\<sharp>(\<theta>_c,y) \<Longrightarrow> x\<sharp>lookupd y c \<theta>_c"
   apply(induct \<theta>_c)
     apply(auto simp add: fresh_prod fresh_list_cons abs_fresh fresh_atm)
   apply(rule rename_fresh)
   apply(simp add: fresh_atm)
  apply(rule rename_fresh)
  apply(simp add: fresh_atm)
  done

lemma lookupd_cmaps:
  assumes a: "\<theta>_c cmaps a to Some (x,P)"
  shows "lookupd y a \<theta>_c = P[x\<turnstile>n>y]"
  using a
  apply(induct \<theta>_c)
   apply(auto)
  done 

nominal_primrec (freshness_context: "\<theta>_n::(name\<times>coname\<times>trm)")
  stn :: "trm\<Rightarrow>(name\<times>coname\<times>trm) list\<Rightarrow>trm" 
  where
    "stn (Ax x a) \<theta>_n = lookupc x a \<theta>_n"
  | "\<lbrakk>a\<sharp>(N,\<theta>_n);x\<sharp>(M,\<theta>_n)\<rbrakk> \<Longrightarrow> stn (Cut <a>.M (x).N) \<theta>_n = (Cut <a>.M (x).N)" 
  | "x\<sharp>\<theta>_n \<Longrightarrow> stn (NotR (x).M a) \<theta>_n = (NotR (x).M a)"
  | "a\<sharp>\<theta>_n \<Longrightarrow>stn (NotL <a>.M x) \<theta>_n = (NotL <a>.M x)"
  | "\<lbrakk>a\<sharp>(N,d,b,\<theta>_n);b\<sharp>(M,d,a,\<theta>_n)\<rbrakk> \<Longrightarrow> stn (AndR <a>.M <b>.N d) \<theta>_n = (AndR <a>.M <b>.N d)"
  | "x\<sharp>(z,\<theta>_n) \<Longrightarrow> stn (AndL1 (x).M z) \<theta>_n = (AndL1 (x).M z)"
  | "x\<sharp>(z,\<theta>_n) \<Longrightarrow> stn (AndL2 (x).M z) \<theta>_n = (AndL2 (x).M z)"
  | "a\<sharp>(b,\<theta>_n) \<Longrightarrow> stn (OrR1 <a>.M b) \<theta>_n = (OrR1 <a>.M b)"
  | "a\<sharp>(b,\<theta>_n) \<Longrightarrow> stn (OrR2 <a>.M b) \<theta>_n = (OrR2 <a>.M b)"
  | "\<lbrakk>x\<sharp>(N,z,u,\<theta>_n);u\<sharp>(M,z,x,\<theta>_n)\<rbrakk> \<Longrightarrow> stn (OrL (x).M (u).N z) \<theta>_n = (OrL (x).M (u).N z)"
  | "\<lbrakk>a\<sharp>(b,\<theta>_n);x\<sharp>\<theta>_n\<rbrakk> \<Longrightarrow> stn (ImpR (x).<a>.M b) \<theta>_n = (ImpR (x).<a>.M b)"
  | "\<lbrakk>a\<sharp>(N,\<theta>_n);x\<sharp>(M,z,\<theta>_n)\<rbrakk> \<Longrightarrow> stn (ImpL <a>.M (x).N z) \<theta>_n = (ImpL <a>.M (x).N z)"
                       apply(finite_guess)+
                       apply(rule TrueI)+
                       apply(simp add: abs_fresh abs_supp fin_supp)+
                       apply(fresh_guess)+
  done

nominal_primrec (freshness_context: "\<theta>_c::(coname\<times>name\<times>trm)")
  stc :: "trm\<Rightarrow>(coname\<times>name\<times>trm) list\<Rightarrow>trm" 
  where
    "stc (Ax x a) \<theta>_c = lookupd x a \<theta>_c"
  | "\<lbrakk>a\<sharp>(N,\<theta>_c);x\<sharp>(M,\<theta>_c)\<rbrakk> \<Longrightarrow> stc (Cut <a>.M (x).N) \<theta>_c = (Cut <a>.M (x).N)" 
  | "x\<sharp>\<theta>_c \<Longrightarrow> stc (NotR (x).M a) \<theta>_c = (NotR (x).M a)"
  | "a\<sharp>\<theta>_c \<Longrightarrow> stc (NotL <a>.M x) \<theta>_c = (NotL <a>.M x)"
  | "\<lbrakk>a\<sharp>(N,d,b,\<theta>_c);b\<sharp>(M,d,a,\<theta>_c)\<rbrakk> \<Longrightarrow> stc (AndR <a>.M <b>.N d) \<theta>_c = (AndR <a>.M <b>.N d)"
  | "x\<sharp>(z,\<theta>_c) \<Longrightarrow> stc (AndL1 (x).M z) \<theta>_c = (AndL1 (x).M z)"
  | "x\<sharp>(z,\<theta>_c) \<Longrightarrow> stc (AndL2 (x).M z) \<theta>_c = (AndL2 (x).M z)"
  | "a\<sharp>(b,\<theta>_c) \<Longrightarrow> stc (OrR1 <a>.M b) \<theta>_c = (OrR1 <a>.M b)"
  | "a\<sharp>(b,\<theta>_c) \<Longrightarrow> stc (OrR2 <a>.M b) \<theta>_c = (OrR2 <a>.M b)"
  | "\<lbrakk>x\<sharp>(N,z,u,\<theta>_c);u\<sharp>(M,z,x,\<theta>_c)\<rbrakk> \<Longrightarrow> stc (OrL (x).M (u).N z) \<theta>_c = (OrL (x).M (u).N z)"
  | "\<lbrakk>a\<sharp>(b,\<theta>_c);x\<sharp>\<theta>_c\<rbrakk> \<Longrightarrow> stc (ImpR (x).<a>.M b) \<theta>_c = (ImpR (x).<a>.M b)"
  | "\<lbrakk>a\<sharp>(N,\<theta>_c);x\<sharp>(M,z,\<theta>_c)\<rbrakk> \<Longrightarrow> stc (ImpL <a>.M (x).N z) \<theta>_c = (ImpL <a>.M (x).N z)"
                       apply(finite_guess)+
                       apply(rule TrueI)+
                       apply(simp add: abs_fresh abs_supp fin_supp)+
                       apply(fresh_guess)+
  done

lemma stn_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(stn M \<theta>_n)) = stn (pi1\<bullet>M) (pi1\<bullet>\<theta>_n)"
    and   "(pi2\<bullet>(stn M \<theta>_n)) = stn (pi2\<bullet>M) (pi2\<bullet>\<theta>_n)"
   apply -
   apply(nominal_induct M avoiding: \<theta>_n rule: trm.strong_induct)
              apply(auto simp add: eqvts fresh_bij fresh_prod eq_bij fresh_atm)
  apply(nominal_induct M avoiding: \<theta>_n rule: trm.strong_induct)
             apply(auto simp add: eqvts fresh_bij fresh_prod eq_bij fresh_atm)
  done

lemma stc_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(stc M \<theta>_c)) = stc (pi1\<bullet>M) (pi1\<bullet>\<theta>_c)"
    and   "(pi2\<bullet>(stc M \<theta>_c)) = stc (pi2\<bullet>M) (pi2\<bullet>\<theta>_c)"
   apply -
   apply(nominal_induct M avoiding: \<theta>_c rule: trm.strong_induct)
              apply(auto simp add: eqvts fresh_bij fresh_prod eq_bij fresh_atm)
  apply(nominal_induct M avoiding: \<theta>_c rule: trm.strong_induct)
             apply(auto simp add: eqvts fresh_bij fresh_prod eq_bij fresh_atm)
  done

lemma stn_fresh:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(\<theta>_n,M) \<Longrightarrow> a\<sharp>stn M \<theta>_n"
    and   "x\<sharp>(\<theta>_n,M) \<Longrightarrow> x\<sharp>stn M \<theta>_n"
   apply(nominal_induct M avoiding: \<theta>_n a x rule: trm.strong_induct)
                       apply(auto simp add: abs_fresh fresh_prod fresh_atm)
   apply(rule lookupc_freshness)
   apply(simp add: fresh_atm)
  apply(rule lookupc_freshness)
  apply(simp add: fresh_atm)
  done

lemma stc_fresh:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(\<theta>_c,M) \<Longrightarrow> a\<sharp>stc M \<theta>_c"
    and   "x\<sharp>(\<theta>_c,M) \<Longrightarrow> x\<sharp>stc M \<theta>_c"
   apply(nominal_induct M avoiding: \<theta>_c a x rule: trm.strong_induct)
                       apply(auto simp add: abs_fresh fresh_prod fresh_atm)
   apply(rule lookupd_freshness)
   apply(simp add: fresh_atm)
  apply(rule lookupd_freshness)
  apply(simp add: fresh_atm)
  done

lemma case_option_eqvt1[eqvt_force]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
    and   B::"(name\<times>trm) option"
    and   r::"trm"
  shows "(pi1\<bullet>(case B of Some (x,P) \<Rightarrow> s x P | None \<Rightarrow> r)) = 
              (case (pi1\<bullet>B) of Some (x,P) \<Rightarrow> (pi1\<bullet>s) x P | None \<Rightarrow> (pi1\<bullet>r))"
    and   "(pi2\<bullet>(case B of Some (x,P) \<Rightarrow> s x P| None \<Rightarrow> r)) = 
              (case (pi2\<bullet>B) of Some (x,P) \<Rightarrow> (pi2\<bullet>s) x P | None \<Rightarrow> (pi2\<bullet>r))"
   apply(cases "B")
    apply(auto)
   apply(perm_simp)
  apply(cases "B")
   apply(auto)
  apply(perm_simp)
  done

lemma case_option_eqvt2[eqvt_force]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
    and   B::"(coname\<times>trm) option"
    and   r::"trm"
  shows "(pi1\<bullet>(case B of Some (x,P) \<Rightarrow> s x P | None \<Rightarrow> r)) = 
              (case (pi1\<bullet>B) of Some (x,P) \<Rightarrow> (pi1\<bullet>s) x P | None \<Rightarrow> (pi1\<bullet>r))"
    and   "(pi2\<bullet>(case B of Some (x,P) \<Rightarrow> s x P| None \<Rightarrow> r)) = 
              (case (pi2\<bullet>B) of Some (x,P) \<Rightarrow> (pi2\<bullet>s) x P | None \<Rightarrow> (pi2\<bullet>r))"
   apply(cases "B")
    apply(auto)
   apply(perm_simp)
  apply(cases "B")
   apply(auto)
  apply(perm_simp)
  done

nominal_primrec (freshness_context: "(\<theta>_n::(name\<times>coname\<times>trm) list,\<theta>_c::(coname\<times>name\<times>trm) list)")
  psubst :: "(name\<times>coname\<times>trm) list\<Rightarrow>(coname\<times>name\<times>trm) list\<Rightarrow>trm\<Rightarrow>trm" (\<open>_,_<_>\<close> [100,100,100] 100) 
  where
    "\<theta>_n,\<theta>_c<Ax x a> = lookup x a \<theta>_n \<theta>_c" 
  | "\<lbrakk>a\<sharp>(N,\<theta>_n,\<theta>_c);x\<sharp>(M,\<theta>_n,\<theta>_c)\<rbrakk> \<Longrightarrow> \<theta>_n,\<theta>_c<Cut <a>.M (x).N> = 
   Cut <a>.(if \<exists>x. M=Ax x a then stn M \<theta>_n else \<theta>_n,\<theta>_c<M>) 
       (x).(if \<exists>a. N=Ax x a then stc N \<theta>_c else \<theta>_n,\<theta>_c<N>)" 
  | "x\<sharp>(\<theta>_n,\<theta>_c) \<Longrightarrow> \<theta>_n,\<theta>_c<NotR (x).M a> = 
  (case (findc \<theta>_c a) of 
       Some (u,P) \<Rightarrow> fresh_fun (\<lambda>a'. Cut <a'>.NotR (x).(\<theta>_n,\<theta>_c<M>) a' (u).P) 
     | None \<Rightarrow> NotR (x).(\<theta>_n,\<theta>_c<M>) a)"
  | "a\<sharp>(\<theta>_n,\<theta>_c) \<Longrightarrow> \<theta>_n,\<theta>_c<NotL <a>.M x> = 
  (case (findn \<theta>_n x) of 
       Some (c,P) \<Rightarrow> fresh_fun (\<lambda>x'. Cut <c>.P (x').(NotL <a>.(\<theta>_n,\<theta>_c<M>) x')) 
     | None \<Rightarrow> NotL <a>.(\<theta>_n,\<theta>_c<M>) x)"
  | "\<lbrakk>a\<sharp>(N,c,\<theta>_n,\<theta>_c);b\<sharp>(M,c,\<theta>_n,\<theta>_c);b\<noteq>a\<rbrakk> \<Longrightarrow> (\<theta>_n,\<theta>_c<AndR <a>.M <b>.N c>) = 
  (case (findc \<theta>_c c) of 
       Some (x,P) \<Rightarrow> fresh_fun (\<lambda>a'. Cut <a'>.(AndR <a>.(\<theta>_n,\<theta>_c<M>) <b>.(\<theta>_n,\<theta>_c<N>) a') (x).P)
     | None \<Rightarrow> AndR <a>.(\<theta>_n,\<theta>_c<M>) <b>.(\<theta>_n,\<theta>_c<N>) c)"
  | "x\<sharp>(z,\<theta>_n,\<theta>_c) \<Longrightarrow> (\<theta>_n,\<theta>_c<AndL1 (x).M z>) = 
  (case (findn \<theta>_n z) of 
       Some (c,P) \<Rightarrow> fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL1 (x).(\<theta>_n,\<theta>_c<M>) z') 
     | None \<Rightarrow> AndL1 (x).(\<theta>_n,\<theta>_c<M>) z)"
  | "x\<sharp>(z,\<theta>_n,\<theta>_c) \<Longrightarrow> (\<theta>_n,\<theta>_c<AndL2 (x).M z>) = 
  (case (findn \<theta>_n z) of 
       Some (c,P) \<Rightarrow> fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL2 (x).(\<theta>_n,\<theta>_c<M>) z') 
     | None \<Rightarrow> AndL2 (x).(\<theta>_n,\<theta>_c<M>) z)"
  | "\<lbrakk>x\<sharp>(N,z,\<theta>_n,\<theta>_c);u\<sharp>(M,z,\<theta>_n,\<theta>_c);x\<noteq>u\<rbrakk> \<Longrightarrow> (\<theta>_n,\<theta>_c<OrL (x).M (u).N z>) =
  (case (findn \<theta>_n z) of  
       Some (c,P) \<Rightarrow> fresh_fun (\<lambda>z'. Cut <c>.P (z').OrL (x).(\<theta>_n,\<theta>_c<M>) (u).(\<theta>_n,\<theta>_c<N>) z') 
     | None \<Rightarrow> OrL (x).(\<theta>_n,\<theta>_c<M>) (u).(\<theta>_n,\<theta>_c<N>) z)"
  | "a\<sharp>(b,\<theta>_n,\<theta>_c) \<Longrightarrow> (\<theta>_n,\<theta>_c<OrR1 <a>.M b>) = 
  (case (findc \<theta>_c b) of
       Some (x,P) \<Rightarrow> fresh_fun (\<lambda>a'. Cut <a'>.OrR1 <a>.(\<theta>_n,\<theta>_c<M>) a' (x).P) 
     | None \<Rightarrow> OrR1 <a>.(\<theta>_n,\<theta>_c<M>) b)"
  | "a\<sharp>(b,\<theta>_n,\<theta>_c) \<Longrightarrow> (\<theta>_n,\<theta>_c<OrR2 <a>.M b>) = 
  (case (findc \<theta>_c b) of
       Some (x,P) \<Rightarrow> fresh_fun (\<lambda>a'. Cut <a'>.OrR2 <a>.(\<theta>_n,\<theta>_c<M>) a' (x).P) 
     | None \<Rightarrow> OrR2 <a>.(\<theta>_n,\<theta>_c<M>) b)"
  | "\<lbrakk>a\<sharp>(b,\<theta>_n,\<theta>_c); x\<sharp>(\<theta>_n,\<theta>_c)\<rbrakk> \<Longrightarrow> (\<theta>_n,\<theta>_c<ImpR (x).<a>.M b>) = 
  (case (findc \<theta>_c b) of
       Some (z,P) \<Rightarrow> fresh_fun (\<lambda>a'. Cut <a'>.ImpR (x).<a>.(\<theta>_n,\<theta>_c<M>) a' (z).P)
     | None \<Rightarrow> ImpR (x).<a>.(\<theta>_n,\<theta>_c<M>) b)"
  | "\<lbrakk>a\<sharp>(N,\<theta>_n,\<theta>_c); x\<sharp>(z,M,\<theta>_n,\<theta>_c)\<rbrakk> \<Longrightarrow> (\<theta>_n,\<theta>_c<ImpL <a>.M (x).N z>) = 
  (case (findn \<theta>_n z) of
       Some (c,P) \<Rightarrow> fresh_fun (\<lambda>z'. Cut <c>.P (z').ImpL <a>.(\<theta>_n,\<theta>_c<M>) (x).(\<theta>_n,\<theta>_c<N>) z') 
     | None \<Rightarrow> ImpL <a>.(\<theta>_n,\<theta>_c<M>) (x).(\<theta>_n,\<theta>_c<N>) z)"
                       apply(finite_guess)+
                       apply(rule TrueI)+
                       apply(simp add: abs_fresh stc_fresh)
                       apply(simp add: abs_fresh stn_fresh)
                       apply(case_tac "findc \<theta>_c x3")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findn \<theta>_n x3")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findc \<theta>_c x5")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findc \<theta>_c x5")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule_tac x="x3" in cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findn \<theta>_n x3")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findn \<theta>_n x3")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findc \<theta>_c x3")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findc \<theta>_c x3")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findn \<theta>_n x5")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findn \<theta>_n x5")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule_tac a="x3" in nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findc \<theta>_c x4")
                       apply(simp add: abs_fresh abs_supp fin_supp)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm abs_supp fin_supp)
                       apply(case_tac "findc \<theta>_c x4")
                       apply(simp add: abs_fresh abs_supp fin_supp)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule_tac x="x2" in cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm abs_supp fin_supp)
                       apply(case_tac "findn \<theta>_n x5")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findn \<theta>_n x5")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule_tac a="x3" in nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(fresh_guess)+
  done

lemma case_cong:
  assumes a: "B1=B2" "x1=x2" "y1=y2"
  shows "(case B1 of None \<Rightarrow> x1 | Some (x,P) \<Rightarrow> y1 x P) = (case B2 of None \<Rightarrow> x2 | Some (x,P) \<Rightarrow> y2 x P)"
  using a
  apply(auto)
  done

lemma find_maps:
  shows "\<theta>_c cmaps a to (findc \<theta>_c a)"
    and   "\<theta>_n nmaps x to (findn \<theta>_n x)"
   apply(auto)
  done

lemma psubst_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "pi1\<bullet>(\<theta>_n,\<theta>_c<M>) = (pi1\<bullet>\<theta>_n),(pi1\<bullet>\<theta>_c)<(pi1\<bullet>M)>"
    and   "pi2\<bullet>(\<theta>_n,\<theta>_c<M>) = (pi2\<bullet>\<theta>_n),(pi2\<bullet>\<theta>_c)<(pi2\<bullet>M)>"
   apply(nominal_induct M avoiding: \<theta>_n \<theta>_c rule: trm.strong_induct)
                       apply(auto simp add: eq_bij fresh_bij eqvts perm_pi_simp)
                     apply(rule case_cong)
                       apply(rule find_maps)
                      apply(simp)
                     apply(perm_simp add: eqvts)
                    apply(rule case_cong)
                      apply(rule find_maps)
                     apply(simp)
                    apply(perm_simp add: eqvts)
                   apply(rule case_cong)
                     apply(rule find_maps)
                    apply(simp)
                   apply(perm_simp add: eqvts)
                  apply(rule case_cong)
                    apply(rule find_maps)
                   apply(simp)
                  apply(perm_simp add: eqvts)
                 apply(rule case_cong)
                   apply(rule find_maps)
                  apply(simp)
                 apply(perm_simp add: eqvts)
                apply(rule case_cong)
                  apply(rule find_maps)
                 apply(simp)
                apply(perm_simp add: eqvts)
               apply(rule case_cong)
                 apply(rule find_maps)
                apply(simp)
               apply(perm_simp add: eqvts)
              apply(rule case_cong)
                apply(rule find_maps)
               apply(simp)
              apply(perm_simp add: eqvts)
             apply(rule case_cong)
               apply(rule find_maps)
              apply(simp)
             apply(perm_simp add: eqvts)
            apply(rule case_cong)
              apply(rule find_maps)
             apply(simp)
            apply(perm_simp add: eqvts)
           apply(rule case_cong)
             apply(rule find_maps)
            apply(simp)
           apply(perm_simp add: eqvts)
          apply(rule case_cong)
            apply(rule find_maps)
           apply(simp)
          apply(perm_simp add: eqvts)
         apply(rule case_cong)
           apply(rule find_maps)
          apply(simp)
         apply(perm_simp add: eqvts)
        apply(rule case_cong)
          apply(rule find_maps)
         apply(simp)
        apply(perm_simp add: eqvts)
       apply(rule case_cong)
         apply(rule find_maps)
        apply(simp)
       apply(perm_simp add: eqvts)
      apply(rule case_cong)
        apply(rule find_maps)
       apply(simp)
      apply(perm_simp add: eqvts)
     apply(rule case_cong)
       apply(rule find_maps)
      apply(simp)
     apply(perm_simp add: eqvts)
    apply(rule case_cong)
      apply(rule find_maps)
     apply(simp)
    apply(perm_simp add: eqvts)
   apply(rule case_cong)
     apply(rule find_maps)
    apply(simp)
   apply(perm_simp add: eqvts)
  apply(rule case_cong)
    apply(rule find_maps)
   apply(simp)
  apply(perm_simp add: eqvts)
  done

lemma ax_psubst:
  assumes a: "\<theta>_n,\<theta>_c<M> = Ax x a"
    and     b: "a\<sharp>(\<theta>_n,\<theta>_c)" "x\<sharp>(\<theta>_n,\<theta>_c)"
  shows "M = Ax x a"
  using a b
  apply(nominal_induct M avoiding: \<theta>_n \<theta>_c rule: trm.strong_induct)
             apply(auto)
            apply(drule lookup_unicity)
              apply(simp)+
           apply(case_tac "findc \<theta>_c coname")
            apply(simp)
           apply(auto)[1]
           apply(generate_fresh "coname")
           apply(fresh_fun_simp)
           apply(simp)
          apply(case_tac "findn \<theta>_n name")
           apply(simp)
          apply(auto)[1]
          apply(generate_fresh "name")
          apply(fresh_fun_simp)
          apply(simp)
         apply(case_tac "findc \<theta>_c coname3")
          apply(simp)
         apply(auto)[1]
         apply(generate_fresh "coname")
         apply(fresh_fun_simp)
         apply(simp)
        apply(case_tac "findn \<theta>_n name2")
         apply(simp)
        apply(auto)[1]
        apply(generate_fresh "name")
        apply(fresh_fun_simp)
        apply(simp)
       apply(case_tac "findn \<theta>_n name2")
        apply(simp)
       apply(auto)[1]
       apply(generate_fresh "name")
       apply(fresh_fun_simp)
       apply(simp)
      apply(case_tac "findc \<theta>_c coname2")
       apply(simp)
      apply(auto)[1]
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(simp)
     apply(case_tac "findc \<theta>_c coname2")
      apply(simp)
     apply(auto)[1]
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(simp)
    apply(case_tac "findn \<theta>_n name3")
     apply(simp)
    apply(auto)[1]
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(simp)
   apply(case_tac "findc \<theta>_c coname2")
    apply(simp)
   apply(auto)[1]
   apply(generate_fresh "coname")
   apply(fresh_fun_simp)
   apply(simp)
  apply(case_tac "findn \<theta>_n name2")
   apply(simp)
  apply(auto)[1]
  apply(generate_fresh "name")
  apply(fresh_fun_simp)
  apply(simp)
  done

lemma better_Cut_substc1:
  assumes a: "a\<sharp>(P,b)" "b\<sharp>N" 
  shows "(Cut <a>.M (x).N){b:=(y).P} = Cut <a>.(M{b:=(y).P}) (x).N"
  using a
  apply -
  apply(generate_fresh "coname")
  apply(generate_fresh "name")
  apply(subgoal_tac "Cut <a>.M (x).N = Cut <c>.([(c,a)]\<bullet>M) (ca).([(ca,x)]\<bullet>N)")
   apply(simp)
   apply(rule trans)
    apply(rule better_Cut_substc)
     apply(simp)
    apply(simp add: abs_fresh)
   apply(auto)[1]
    apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
    apply(simp add: calc_atm fresh_atm)
   apply(subgoal_tac"b\<sharp>([(ca,x)]\<bullet>N)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
    apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
    apply(perm_simp)
   apply(simp add: fresh_left calc_atm)
  apply(simp add: trm.inject)
  apply(rule conjI)
   apply(rule sym)
   apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  apply(rule sym)
  apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  done

lemma better_Cut_substc2:
  assumes a: "x\<sharp>(y,P)" "b\<sharp>(a,M)" "N\<noteq>Ax x b"
  shows "(Cut <a>.M (x).N){b:=(y).P} = Cut <a>.M (x).(N{b:=(y).P})"
  using a
  apply -
  apply(generate_fresh "coname")
  apply(generate_fresh "name")
  apply(subgoal_tac "Cut <a>.M (x).N = Cut <c>.([(c,a)]\<bullet>M) (ca).([(ca,x)]\<bullet>N)")
   apply(simp)
   apply(rule trans)
    apply(rule better_Cut_substc)
     apply(simp)
    apply(simp add: abs_fresh)
   apply(auto)[1]
    apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
    apply(simp add: calc_atm fresh_atm fresh_prod)
   apply(subgoal_tac"b\<sharp>([(c,a)]\<bullet>M)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
    apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
    apply(perm_simp)
   apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(simp add: trm.inject)
  apply(rule conjI)
   apply(rule sym)
   apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  apply(rule sym)
  apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  done

lemma better_Cut_substn1:
  assumes a: "y\<sharp>(x,N)" "a\<sharp>(b,P)" "M\<noteq>Ax y a"
  shows "(Cut <a>.M (x).N){y:=<b>.P} = Cut <a>.(M{y:=<b>.P}) (x).N"
  using a
  apply -
  apply(generate_fresh "coname")
  apply(generate_fresh "name")
  apply(subgoal_tac "Cut <a>.M (x).N = Cut <c>.([(c,a)]\<bullet>M) (ca).([(ca,x)]\<bullet>N)")
   apply(simp)
   apply(rule trans)
    apply(rule better_Cut_substn)
     apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
   apply(auto)[1]
    apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
    apply(simp add: calc_atm fresh_atm fresh_prod)
   apply(subgoal_tac"y\<sharp>([(ca,x)]\<bullet>N)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
    apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
    apply(perm_simp)
   apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(simp add: trm.inject)
  apply(rule conjI)
   apply(rule sym)
   apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  apply(rule sym)
  apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  done

lemma better_Cut_substn2:
  assumes a: "x\<sharp>(P,y)" "y\<sharp>M" 
  shows "(Cut <a>.M (x).N){y:=<b>.P} = Cut <a>.M (x).(N{y:=<b>.P})"
  using a
  apply -
  apply(generate_fresh "coname")
  apply(generate_fresh "name")
  apply(subgoal_tac "Cut <a>.M (x).N = Cut <c>.([(c,a)]\<bullet>M) (ca).([(ca,x)]\<bullet>N)")
   apply(simp)
   apply(rule trans)
    apply(rule better_Cut_substn)
     apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
   apply(auto)[1]
    apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
    apply(simp add: calc_atm fresh_atm)
   apply(subgoal_tac"y\<sharp>([(c,a)]\<bullet>M)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
    apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
    apply(perm_simp)
   apply(simp add: fresh_left calc_atm)
  apply(simp add: trm.inject)
  apply(rule conjI)
   apply(rule sym)
   apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  apply(rule sym)
  apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  done

lemma psubst_fresh_name:
  fixes x::"name"
  assumes a: "x\<sharp>\<theta>_n" "x\<sharp>\<theta>_c" "x\<sharp>M"
  shows "x\<sharp>\<theta>_n,\<theta>_c<M>"
  using a
  apply(nominal_induct M avoiding: x \<theta>_n \<theta>_c rule: trm.strong_induct)
             apply(simp add: lookup_freshness)
            apply(auto simp add: abs_fresh)[1]
                 apply(simp add: lookupc_freshness)
                apply(simp add: lookupc_freshness)
               apply(simp add: lookupc_freshness)
              apply(simp add: lookupd_freshness)
             apply(simp add: lookupd_freshness)
            apply(simp add: lookupc_freshness)
           apply(simp)
           apply(case_tac "findc \<theta>_c coname")
            apply(auto simp add: abs_fresh)[1]
           apply(auto)[1]
           apply(generate_fresh "coname")
           apply(fresh_fun_simp)
           apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
          apply(simp)
          apply(case_tac "findn \<theta>_n name")
           apply(auto simp add: abs_fresh)[1]
          apply(auto)[1]
          apply(generate_fresh "name")
          apply(fresh_fun_simp)
          apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
         apply(simp)
         apply(case_tac "findc \<theta>_c coname3")
          apply(auto simp add: abs_fresh)[1]
         apply(auto)[1]
         apply(generate_fresh "coname")
         apply(fresh_fun_simp)
         apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
        apply(simp)
        apply(case_tac "findn \<theta>_n name2")
         apply(auto simp add: abs_fresh)[1]
        apply(auto)[1]
        apply(generate_fresh "name")
        apply(fresh_fun_simp)
        apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
       apply(simp)
       apply(case_tac "findn \<theta>_n name2")
        apply(auto simp add: abs_fresh)[1]
       apply(auto)[1]
       apply(generate_fresh "name")
       apply(fresh_fun_simp)
       apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
      apply(simp)
      apply(case_tac "findc \<theta>_c coname2")
       apply(auto simp add: abs_fresh)[1]
      apply(auto)[1]
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
     apply(simp)
     apply(case_tac "findc \<theta>_c coname2")
      apply(auto simp add: abs_fresh)[1]
     apply(auto)[1]
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
    apply(simp)
    apply(case_tac "findn \<theta>_n name3")
     apply(auto simp add: abs_fresh)[1]
    apply(auto)[1]
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
   apply(simp)
   apply(case_tac "findc \<theta>_c coname2")
    apply(auto simp add: abs_fresh abs_supp fin_supp)[1]
   apply(auto)[1]
   apply(generate_fresh "coname")
   apply(fresh_fun_simp)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_prod fresh_atm cmaps_fresh)
  apply(simp)
  apply(case_tac "findn \<theta>_n name2")
   apply(auto simp add: abs_fresh)[1]
  apply(auto)[1]
  apply(generate_fresh "name")
  apply(fresh_fun_simp)
  apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
  done

lemma psubst_fresh_coname:
  fixes a::"coname"
  assumes a: "a\<sharp>\<theta>_n" "a\<sharp>\<theta>_c" "a\<sharp>M"
  shows "a\<sharp>\<theta>_n,\<theta>_c<M>"
  using a
  apply(nominal_induct M avoiding: a \<theta>_n \<theta>_c rule: trm.strong_induct)
             apply(simp add: lookup_freshness)
            apply(auto simp add: abs_fresh)[1]
                 apply(simp add: lookupd_freshness)
                apply(simp add: lookupd_freshness)
               apply(simp add: lookupc_freshness)
              apply(simp add: lookupd_freshness)
             apply(simp add: lookupc_freshness)
            apply(simp add: lookupd_freshness)
           apply(simp)
           apply(case_tac "findc \<theta>_c coname")
            apply(auto simp add: abs_fresh)[1]
           apply(auto)[1]
           apply(generate_fresh "coname")
           apply(fresh_fun_simp)
           apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
          apply(simp)
          apply(case_tac "findn \<theta>_n name")
           apply(auto simp add: abs_fresh)[1]
          apply(auto)[1]
          apply(generate_fresh "name")
          apply(fresh_fun_simp)
          apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
         apply(simp)
         apply(case_tac "findc \<theta>_c coname3")
          apply(auto simp add: abs_fresh)[1]
         apply(auto)[1]
         apply(generate_fresh "coname")
         apply(fresh_fun_simp)
         apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
        apply(simp)
        apply(case_tac "findn \<theta>_n name2")
         apply(auto simp add: abs_fresh)[1]
        apply(auto)[1]
        apply(generate_fresh "name")
        apply(fresh_fun_simp)
        apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
       apply(simp)
       apply(case_tac "findn \<theta>_n name2")
        apply(auto simp add: abs_fresh)[1]
       apply(auto)[1]
       apply(generate_fresh "name")
       apply(fresh_fun_simp)
       apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
      apply(simp)
      apply(case_tac "findc \<theta>_c coname2")
       apply(auto simp add: abs_fresh)[1]
      apply(auto)[1]
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
     apply(simp)
     apply(case_tac "findc \<theta>_c coname2")
      apply(auto simp add: abs_fresh)[1]
     apply(auto)[1]
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
    apply(simp)
    apply(case_tac "findn \<theta>_n name3")
     apply(auto simp add: abs_fresh)[1]
    apply(auto)[1]
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
   apply(simp)
   apply(case_tac "findc \<theta>_c coname2")
    apply(auto simp add: abs_fresh abs_supp fin_supp)[1]
   apply(auto)[1]
   apply(generate_fresh "coname")
   apply(fresh_fun_simp)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_prod fresh_atm cmaps_fresh)
  apply(simp)
  apply(case_tac "findn \<theta>_n name2")
   apply(auto simp add: abs_fresh)[1]
  apply(auto)[1]
  apply(generate_fresh "name")
  apply(fresh_fun_simp)
  apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
  done

lemma psubst_csubst:
  assumes a: "a\<sharp>(\<theta>_n,\<theta>_c)"
  shows "\<theta>_n,((a,x,P)#\<theta>_c)<M> = ((\<theta>_n,\<theta>_c<M>){a:=(x).P})"
  using a
  apply(nominal_induct M avoiding: a x \<theta>_n \<theta>_c P rule: trm.strong_induct)
             apply(auto simp add: fresh_list_cons fresh_prod)[1]
             apply(simp add: lookup_csubst)
            apply(simp add: fresh_list_cons fresh_prod)
            apply(auto)[1]
                 apply(rule sym)
                 apply(rule trans)
                  apply(rule better_Cut_substc)
                   apply(simp)
                  apply(simp add: abs_fresh fresh_atm)
                 apply(simp add: lookupd_fresh)
                 apply(subgoal_tac "a\<sharp>lookupc xa coname \<theta>_n")
                  apply(simp add: forget)
                  apply(simp add: trm.inject)
                  apply(rule sym)
                  apply(simp add: alpha nrename_swap fresh_atm)
                 apply(rule lookupc_freshness)
                 apply(simp add: fresh_atm)
                apply(rule sym)
                apply(rule trans)
                 apply(rule better_Cut_substc)
                  apply(simp)
                 apply(simp add: abs_fresh fresh_atm)
                apply(simp)
                apply(rule conjI)
                 apply(rule impI)
                 apply(simp add: lookupd_unicity)
                apply(rule impI)
                apply(subgoal_tac "a\<sharp>lookupc xa coname \<theta>_n")
                 apply(subgoal_tac "a\<sharp>lookupd name aa \<theta>_c")
                  apply(simp add: forget)
                 apply(rule lookupd_freshness)
                 apply(simp add: fresh_atm)
                apply(rule lookupc_freshness)
                apply(simp add: fresh_atm)
               apply(rule sym)
               apply(rule trans)
                apply(rule better_Cut_substc)
                 apply(simp)
                apply(simp add: abs_fresh fresh_atm)
               apply(simp)
               apply(rule conjI)
                apply(rule impI)
                apply(drule ax_psubst)
                  apply(simp)
                 apply(simp)
                apply(blast)
               apply(rule impI)
               apply(subgoal_tac "a\<sharp>lookupc xa coname \<theta>_n")
                apply(simp add: forget)
               apply(rule lookupc_freshness)
               apply(simp add: fresh_atm)
              apply(rule sym)
              apply(rule trans)
               apply(rule better_Cut_substc)
                apply(simp)
               apply(simp add: abs_fresh fresh_atm)
              apply(simp)
              apply(rule conjI)
               apply(rule impI)
               apply(simp add: trm.inject)
               apply(rule sym)
               apply(simp add: alpha)
               apply(simp add: alpha nrename_swap fresh_atm)
              apply(simp add: lookupd_fresh)
             apply(rule sym)
             apply(rule trans)
              apply(rule better_Cut_substc)
               apply(simp)
              apply(simp add: abs_fresh fresh_atm)
             apply(simp)
             apply(rule conjI)
              apply(rule impI)
              apply(simp add: lookupd_unicity)
             apply(rule impI)
             apply(subgoal_tac "a\<sharp>lookupd name aa \<theta>_c")
              apply(simp add: forget)
             apply(rule lookupd_freshness)
             apply(simp add: fresh_atm)
            apply(rule sym)
            apply(rule trans)
             apply(rule better_Cut_substc)
              apply(simp)
             apply(simp add: abs_fresh fresh_atm)
            apply(simp)
            apply(rule impI)
            apply(drule ax_psubst)
              apply(simp)
             apply(simp)
            apply(blast)
    (* NotR *)
           apply(simp)
           apply(case_tac "findc \<theta>_c coname")
            apply(simp)
            apply(auto simp add: fresh_list_cons fresh_prod)[1]
           apply(simp)
           apply(auto simp add: fresh_list_cons fresh_prod)[1]
            apply(drule cmaps_false)
             apply(assumption)
            apply(simp)
           apply(generate_fresh "coname")
           apply(fresh_fun_simp)
           apply(fresh_fun_simp)
           apply(rule sym)
           apply(rule trans)
            apply(rule better_Cut_substc1)
             apply(simp)
            apply(simp add: cmaps_fresh)
           apply(auto simp add: fresh_prod fresh_atm)[1]
    (* NotL *)
          apply(simp)
          apply(case_tac "findn \<theta>_n name")
           apply(simp)
           apply(auto simp add: fresh_list_cons fresh_prod)[1]
          apply(simp)
          apply(auto simp add: fresh_list_cons fresh_prod)[1]
          apply(generate_fresh "name")
          apply(fresh_fun_simp)
          apply(fresh_fun_simp)
          apply(drule_tac a="a" in nmaps_fresh)
           apply(assumption)
          apply(rule sym)
          apply(rule trans)
           apply(rule better_Cut_substc2)
             apply(simp)
            apply(simp)
           apply(simp)
          apply(simp)
    (* AndR *)
         apply(simp)
         apply(case_tac "findc \<theta>_c coname3")
          apply(simp)
          apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
         apply(simp)
         apply(auto simp add: fresh_list_cons fresh_prod)[1]
          apply(drule cmaps_false)
           apply(assumption)
          apply(simp)
         apply(generate_fresh "coname")
         apply(fresh_fun_simp)
         apply(fresh_fun_simp)
         apply(rule sym)
         apply(rule trans)
          apply(rule better_Cut_substc1)
           apply(simp)
          apply(simp add: cmaps_fresh)
         apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* AndL1 *)
        apply(simp)
        apply(case_tac "findn \<theta>_n name2")
         apply(simp)
         apply(auto simp add: fresh_list_cons fresh_prod)[1]
        apply(simp)
        apply(auto simp add: fresh_list_cons fresh_prod)[1]
        apply(generate_fresh "name")
        apply(fresh_fun_simp)
        apply(fresh_fun_simp)
        apply(drule_tac a="a" in nmaps_fresh)
         apply(assumption)
        apply(rule sym)
        apply(rule trans)
         apply(rule better_Cut_substc2)
           apply(simp)
          apply(simp)
         apply(simp)
        apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* AndL2 *)
       apply(simp)
       apply(case_tac "findn \<theta>_n name2")
        apply(simp)
        apply(auto simp add: fresh_list_cons fresh_prod)[1]
       apply(simp)
       apply(auto simp add: fresh_list_cons fresh_prod)[1]
       apply(generate_fresh "name")
       apply(fresh_fun_simp)
       apply(fresh_fun_simp)
       apply(drule_tac a="a" in nmaps_fresh)
        apply(assumption)
       apply(rule sym)
       apply(rule trans)
        apply(rule better_Cut_substc2)
          apply(simp)
         apply(simp)
        apply(simp)
       apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* OrR1 *)
      apply(simp)
      apply(case_tac "findc \<theta>_c coname2")
       apply(simp)
       apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
      apply(simp)
      apply(auto simp add: fresh_list_cons fresh_prod)[1]
       apply(drule cmaps_false)
        apply(assumption)
       apply(simp)
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(fresh_fun_simp)
      apply(rule sym)
      apply(rule trans)
       apply(rule better_Cut_substc1)
        apply(simp)
       apply(simp add: cmaps_fresh)
      apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* OrR2 *)
     apply(simp)
     apply(case_tac "findc \<theta>_c coname2")
      apply(simp)
      apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
     apply(simp)
     apply(auto simp add: fresh_list_cons fresh_prod)[1]
      apply(drule cmaps_false)
       apply(assumption)
      apply(simp)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(fresh_fun_simp)
     apply(rule sym)
     apply(rule trans)
      apply(rule better_Cut_substc1)
       apply(simp)
      apply(simp add: cmaps_fresh)
     apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* OrL *)
    apply(simp)
    apply(case_tac "findn \<theta>_n name3")
     apply(simp)
     apply(auto simp add: fresh_list_cons psubst_fresh_name fresh_atm fresh_prod)[1]
    apply(simp)
    apply(auto simp add: fresh_list_cons fresh_prod)[1]
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(drule_tac a="a" in nmaps_fresh)
     apply(assumption)
    apply(rule sym)
    apply(rule trans)
     apply(rule better_Cut_substc2)
       apply(simp)
      apply(simp)
     apply(simp)
    apply(auto simp add:  psubst_fresh_name fresh_prod fresh_atm)[1]
    (* ImpR *)
   apply(simp)
   apply(case_tac "findc \<theta>_c coname2")
    apply(simp)
    apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
   apply(simp)
   apply(auto simp add: fresh_list_cons fresh_prod)[1]
    apply(drule cmaps_false)
     apply(assumption)
    apply(simp)
   apply(generate_fresh "coname")
   apply(fresh_fun_simp)
   apply(fresh_fun_simp)
   apply(rule sym)
   apply(rule trans)
    apply(rule better_Cut_substc1)
     apply(simp)
    apply(simp add: cmaps_fresh)
   apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* ImpL *)
  apply(simp)
  apply(case_tac "findn \<theta>_n name2")
   apply(simp)
   apply(auto simp add: fresh_list_cons psubst_fresh_coname psubst_fresh_name fresh_atm fresh_prod)[1]
  apply(simp)
  apply(auto simp add: fresh_list_cons fresh_prod)[1]
  apply(generate_fresh "name")
  apply(fresh_fun_simp)
  apply(fresh_fun_simp)
  apply(simp add: abs_fresh subst_fresh)
  apply(drule_tac a="a" in nmaps_fresh)
   apply(assumption)
  apply(rule sym)
  apply(rule trans)
   apply(rule better_Cut_substc2)
     apply(simp)
    apply(simp)
   apply(simp)
  apply(auto simp add: psubst_fresh_coname psubst_fresh_name fresh_prod fresh_atm)[1]
  done

lemma psubst_nsubst:
  assumes a: "x\<sharp>(\<theta>_n,\<theta>_c)"
  shows "((x,a,P)#\<theta>_n),\<theta>_c<M> = ((\<theta>_n,\<theta>_c<M>){x:=<a>.P})"
  using a
  apply(nominal_induct M avoiding: a x \<theta>_n \<theta>_c P rule: trm.strong_induct)
             apply(auto simp add: fresh_list_cons fresh_prod)[1]
              apply(simp add: lookup_fresh)
              apply(rule lookupb_lookupa)
              apply(simp)
             apply(rule sym)
             apply(rule forget)
             apply(rule lookup_freshness)
             apply(simp add: fresh_atm)
            apply(auto simp add: lookupc_freshness fresh_list_cons fresh_prod)[1]
                 apply(simp add: lookupc_fresh)
                 apply(rule sym)
                 apply(rule trans)
                  apply(rule better_Cut_substn)
                   apply(simp add: abs_fresh)
                  apply(simp add: abs_fresh fresh_atm)
                 apply(simp add: lookupd_fresh)
                 apply(subgoal_tac "x\<sharp>lookupd name aa \<theta>_c")
                  apply(simp add: forget)
                  apply(simp add: trm.inject)
                  apply(rule sym)
                  apply(simp add: alpha crename_swap fresh_atm)
                 apply(rule lookupd_freshness)
                 apply(simp add: fresh_atm)
                apply(rule sym)
                apply(rule trans)
                 apply(rule better_Cut_substn)
                  apply(simp add: abs_fresh) 
                 apply(simp add: abs_fresh fresh_atm)
                apply(simp)
                apply(rule conjI)
                 apply(rule impI)
                 apply(simp add: lookupc_unicity)
                apply(rule impI)
                apply(subgoal_tac "x\<sharp>lookupc xa coname \<theta>_n")
                 apply(subgoal_tac "x\<sharp>lookupd name aa \<theta>_c")
                  apply(simp add: forget)
                 apply(rule lookupd_freshness)
                 apply(simp add: fresh_atm)
                apply(rule lookupc_freshness)
                apply(simp add: fresh_atm)
               apply(rule sym)
               apply(rule trans)
                apply(rule better_Cut_substn)
                 apply(simp add: abs_fresh)
                apply(simp add: abs_fresh fresh_atm)
               apply(simp)
               apply(rule conjI)
                apply(rule impI)
                apply(simp add: trm.inject)
                apply(rule sym)
                apply(simp add: alpha crename_swap fresh_atm)
               apply(rule impI)
               apply(simp add: lookupc_fresh)
              apply(rule sym)
              apply(rule trans)
               apply(rule better_Cut_substn)
                apply(simp add: abs_fresh)
               apply(simp add: abs_fresh fresh_atm)
              apply(simp)
              apply(rule conjI)
               apply(rule impI)
               apply(simp add: lookupc_unicity)
              apply(rule impI)
              apply(subgoal_tac "x\<sharp>lookupc xa coname \<theta>_n")
               apply(simp add: forget)
              apply(rule lookupc_freshness)
              apply(simp add: fresh_prod fresh_atm)
             apply(rule sym)
             apply(rule trans)
              apply(rule better_Cut_substn)
               apply(simp add: abs_fresh)
              apply(simp add: abs_fresh fresh_atm)
             apply(simp)
             apply(rule conjI)
              apply(rule impI)
              apply(drule ax_psubst)
                apply(simp)
               apply(simp)
              apply(simp)
              apply(blast)
             apply(rule impI)
             apply(subgoal_tac "x\<sharp>lookupd name aa \<theta>_c")
              apply(simp add: forget)
             apply(rule lookupd_freshness)
             apply(simp add: fresh_atm)
            apply(rule sym)
            apply(rule trans)
             apply(rule better_Cut_substn)
              apply(simp add: abs_fresh)
             apply(simp add: abs_fresh fresh_atm)
            apply(simp)
            apply(rule impI)
            apply(drule ax_psubst)
              apply(simp)
             apply(simp)
            apply(blast)
    (* NotR *)
           apply(simp)
           apply(case_tac "findc \<theta>_c coname")
            apply(simp)
            apply(auto simp add: fresh_list_cons fresh_prod)[1]
           apply(simp)
           apply(auto simp add: fresh_list_cons fresh_prod)[1]
           apply(generate_fresh "coname")
           apply(fresh_fun_simp)
           apply(fresh_fun_simp)
           apply(rule sym)
           apply(rule trans)
            apply(rule better_Cut_substn1)
              apply(simp add: cmaps_fresh)
             apply(simp)
            apply(simp)
           apply(simp)
    (* NotL *)
          apply(simp)
          apply(case_tac "findn \<theta>_n name")
           apply(simp)
           apply(auto simp add: fresh_list_cons fresh_prod)[1]
          apply(simp)
          apply(auto simp add: fresh_list_cons fresh_prod)[1]
           apply(drule nmaps_false)
            apply(simp)
           apply(simp)
          apply(generate_fresh "name")
          apply(fresh_fun_simp)
          apply(fresh_fun_simp)
          apply(rule sym)
          apply(rule trans)
           apply(rule better_Cut_substn2)
            apply(simp)
           apply(simp add: nmaps_fresh)
          apply(simp add: fresh_prod fresh_atm)
    (* AndR *)
         apply(simp)
         apply(case_tac "findc \<theta>_c coname3")
          apply(simp)
          apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
         apply(simp)
         apply(auto simp add: fresh_list_cons fresh_prod)[1]
         apply(generate_fresh "coname")
         apply(fresh_fun_simp)
         apply(fresh_fun_simp)
         apply(rule sym)
         apply(rule trans)
          apply(rule better_Cut_substn1)
            apply(simp add: cmaps_fresh)
           apply(simp)
          apply(simp)
         apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* AndL1 *)
        apply(simp)
        apply(case_tac "findn \<theta>_n name2")
         apply(simp)
         apply(auto simp add: fresh_list_cons fresh_prod)[1]
        apply(simp)
        apply(auto simp add: fresh_list_cons fresh_prod)[1]
         apply(drule nmaps_false)
          apply(simp)
         apply(simp)
        apply(generate_fresh "name")
        apply(fresh_fun_simp)
        apply(fresh_fun_simp)
        apply(rule sym)
        apply(rule trans)
         apply(rule better_Cut_substn2)
          apply(simp)
         apply(simp add: nmaps_fresh)
        apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* AndL2 *)
       apply(simp)
       apply(case_tac "findn \<theta>_n name2")
        apply(simp)
        apply(auto simp add: fresh_list_cons fresh_prod)[1]
       apply(simp)
       apply(auto simp add: fresh_list_cons fresh_prod)[1]
        apply(drule nmaps_false)
         apply(simp)
        apply(simp)
       apply(generate_fresh "name")
       apply(fresh_fun_simp)
       apply(fresh_fun_simp)
       apply(rule sym)
       apply(rule trans)
        apply(rule better_Cut_substn2)
         apply(simp)
        apply(simp add: nmaps_fresh)
       apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* OrR1 *)
      apply(simp)
      apply(case_tac "findc \<theta>_c coname2")
       apply(simp)
       apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
      apply(simp)
      apply(auto simp add: fresh_list_cons fresh_prod)[1]
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(fresh_fun_simp)
      apply(rule sym)
      apply(rule trans)
       apply(rule better_Cut_substn1)
         apply(simp add: cmaps_fresh)
        apply(simp)
       apply(simp)
      apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* OrR2 *)
     apply(simp)
     apply(case_tac "findc \<theta>_c coname2")
      apply(simp)
      apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
     apply(simp)
     apply(auto simp add: fresh_list_cons fresh_prod)[1]
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(fresh_fun_simp)
     apply(rule sym)
     apply(rule trans)
      apply(rule better_Cut_substn1)
        apply(simp add: cmaps_fresh)
       apply(simp)
      apply(simp)
     apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* OrL *)
    apply(simp)
    apply(case_tac "findn \<theta>_n name3")
     apply(simp)
     apply(auto simp add: fresh_list_cons psubst_fresh_name fresh_atm fresh_prod)[1]
    apply(simp)
    apply(auto simp add: fresh_list_cons fresh_prod)[1]
     apply(drule nmaps_false)
      apply(simp)
     apply(simp)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(rule sym)
    apply(rule trans)
     apply(rule better_Cut_substn2)
      apply(simp)
     apply(simp add: nmaps_fresh)
    apply(auto simp add:  psubst_fresh_name fresh_prod fresh_atm)[1]
    (* ImpR *)
   apply(simp)
   apply(case_tac "findc \<theta>_c coname2")
    apply(simp)
    apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
   apply(simp)
   apply(auto simp add: fresh_list_cons fresh_prod)[1]
   apply(generate_fresh "coname")
   apply(fresh_fun_simp)
   apply(fresh_fun_simp)
   apply(rule sym)
   apply(rule trans)
    apply(rule better_Cut_substn1)
      apply(simp add: cmaps_fresh)
     apply(simp)
    apply(simp)
   apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* ImpL *)
  apply(simp)
  apply(case_tac "findn \<theta>_n name2")
   apply(simp)
   apply(auto simp add: fresh_list_cons psubst_fresh_coname psubst_fresh_name fresh_atm fresh_prod)[1]
  apply(simp)
  apply(auto simp add: fresh_list_cons fresh_prod)[1]
   apply(drule nmaps_false)
    apply(simp)
   apply(simp)
  apply(generate_fresh "name")
  apply(fresh_fun_simp)
  apply(fresh_fun_simp)
  apply(rule sym)
  apply(rule trans)
   apply(rule better_Cut_substn2)
    apply(simp)
   apply(simp add: nmaps_fresh)
  apply(auto simp add: psubst_fresh_coname psubst_fresh_name fresh_prod fresh_atm)[1]
  done

definition 
  ncloses :: "(name\<times>coname\<times>trm) list\<Rightarrow>(name\<times>ty) list \<Rightarrow> bool" (\<open>_ ncloses _\<close> [55,55] 55) 
  where
    "\<theta>_n ncloses \<Gamma> \<equiv> \<forall>x B. ((x,B) \<in> set \<Gamma> \<longrightarrow> (\<exists>c P. \<theta>_n nmaps x to Some (c,P) \<and> <c>:P \<in> (\<parallel><B>\<parallel>)))"

definition 
  ccloses :: "(coname\<times>name\<times>trm) list\<Rightarrow>(coname\<times>ty) list \<Rightarrow> bool" (\<open>_ ccloses _\<close> [55,55] 55) 
  where
    "\<theta>_c ccloses \<Delta> \<equiv> \<forall>a B. ((a,B) \<in> set \<Delta> \<longrightarrow> (\<exists>x P. \<theta>_c cmaps a to Some (x,P) \<and> (x):P \<in> (\<parallel>(B)\<parallel>)))"

lemma ncloses_elim:
  assumes a: "(x,B) \<in> set \<Gamma>"
    and     b: "\<theta>_n ncloses \<Gamma>"
  shows "\<exists>c P. \<theta>_n nmaps x to Some (c,P) \<and> <c>:P \<in> (\<parallel><B>\<parallel>)"
  using a b by (auto simp add: ncloses_def)

lemma ccloses_elim:
  assumes a: "(a,B) \<in> set \<Delta>"
    and     b: "\<theta>_c ccloses \<Delta>"
  shows "\<exists>x P. \<theta>_c cmaps a to Some (x,P) \<and> (x):P \<in> (\<parallel>(B)\<parallel>)"
  using a b by (auto simp add: ccloses_def)

lemma ncloses_subset:
  assumes a: "\<theta>_n ncloses \<Gamma>"
    and     b: "set \<Gamma>' \<subseteq> set \<Gamma>"
  shows "\<theta>_n ncloses \<Gamma>'"
  using a b by (auto  simp add: ncloses_def)

lemma ccloses_subset:
  assumes a: "\<theta>_c ccloses \<Delta>"
    and     b: "set \<Delta>' \<subseteq> set \<Delta>"
  shows "\<theta>_c ccloses \<Delta>'"
  using a b by (auto  simp add: ccloses_def)

lemma validc_fresh:
  fixes a::"coname"
    and   \<Delta>::"(coname\<times>ty) list"
  assumes a: "a\<sharp>\<Delta>"
  shows "\<not>(\<exists>B. (a,B)\<in>set \<Delta>)"
  using a
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

lemma validn_fresh:
  fixes x::"name"
    and   \<Gamma>::"(name\<times>ty) list"
  assumes a: "x\<sharp>\<Gamma>"
  shows "\<not>(\<exists>B. (x,B)\<in>set \<Gamma>)"
  using a
  apply(induct \<Gamma>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

lemma ccloses_extend:
  assumes a: "\<theta>_c ccloses \<Delta>" "a\<sharp>\<Delta>" "a\<sharp>\<theta>_c" "(x):P\<in>\<parallel>(B)\<parallel>"
  shows "(a,x,P)#\<theta>_c ccloses (a,B)#\<Delta>"
  using a
  apply(simp add: ccloses_def)
  apply(drule validc_fresh)
  apply(auto)
  done

lemma ncloses_extend:
  assumes a: "\<theta>_n ncloses \<Gamma>" "x\<sharp>\<Gamma>" "x\<sharp>\<theta>_n" "<a>:P\<in>\<parallel><B>\<parallel>"
  shows "(x,a,P)#\<theta>_n ncloses (x,B)#\<Gamma>"
  using a
  apply(simp add: ncloses_def)
  apply(drule validn_fresh)
  apply(auto)
  done


text \<open>typing relation\<close>

inductive
  typing :: "ctxtn \<Rightarrow> trm \<Rightarrow> ctxtc \<Rightarrow> bool" (\<open>_ \<turnstile> _ \<turnstile> _\<close> [100,100,100] 100)
  where
    TAx:    "\<lbrakk>validn \<Gamma>;validc \<Delta>; (x,B)\<in>set \<Gamma>; (a,B)\<in>set \<Delta>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Ax x a \<turnstile> \<Delta>"
  | TNotR:  "\<lbrakk>x\<sharp>\<Gamma>; ((x,B)#\<Gamma>) \<turnstile> M \<turnstile> \<Delta>; set \<Delta>' = {(a,NOT B)}\<union>set \<Delta>; validc \<Delta>'\<rbrakk> 
           \<Longrightarrow> \<Gamma> \<turnstile> NotR (x).M a \<turnstile> \<Delta>'"
  | TNotL:  "\<lbrakk>a\<sharp>\<Delta>; \<Gamma> \<turnstile> M \<turnstile> ((a,B)#\<Delta>); set \<Gamma>' = {(x,NOT B)} \<union> set \<Gamma>; validn \<Gamma>'\<rbrakk>  
           \<Longrightarrow> \<Gamma>' \<turnstile> NotL <a>.M x \<turnstile> \<Delta>"
  | TAndL1: "\<lbrakk>x\<sharp>(\<Gamma>,y); ((x,B1)#\<Gamma>) \<turnstile> M \<turnstile> \<Delta>; set \<Gamma>' = {(y,B1 AND B2)} \<union> set \<Gamma>; validn \<Gamma>'\<rbrakk> 
           \<Longrightarrow> \<Gamma>' \<turnstile> AndL1 (x).M y \<turnstile> \<Delta>"
  | TAndL2: "\<lbrakk>x\<sharp>(\<Gamma>,y); ((x,B2)#\<Gamma>) \<turnstile> M \<turnstile> \<Delta>; set \<Gamma>' = {(y,B1 AND B2)} \<union> set \<Gamma>; validn \<Gamma>'\<rbrakk> 
           \<Longrightarrow> \<Gamma>' \<turnstile> AndL2 (x).M y \<turnstile> \<Delta>"
  | TAndR:  "\<lbrakk>a\<sharp>(\<Delta>,N,c); b\<sharp>(\<Delta>,M,c); a\<noteq>b; \<Gamma> \<turnstile> M \<turnstile> ((a,B)#\<Delta>); \<Gamma> \<turnstile> N \<turnstile> ((b,C)#\<Delta>); 
           set \<Delta>' = {(c,B AND C)}\<union>set \<Delta>; validc \<Delta>'\<rbrakk> 
           \<Longrightarrow> \<Gamma> \<turnstile> AndR <a>.M <b>.N c \<turnstile> \<Delta>'"
  | TOrL:   "\<lbrakk>x\<sharp>(\<Gamma>,N,z); y\<sharp>(\<Gamma>,M,z); x\<noteq>y; ((x,B)#\<Gamma>) \<turnstile> M \<turnstile> \<Delta>; ((y,C)#\<Gamma>) \<turnstile> N \<turnstile> \<Delta>;
           set \<Gamma>' = {(z,B OR C)} \<union> set \<Gamma>; validn \<Gamma>'\<rbrakk> 
           \<Longrightarrow> \<Gamma>' \<turnstile> OrL (x).M (y).N z \<turnstile> \<Delta>"
  | TOrR1:  "\<lbrakk>a\<sharp>(\<Delta>,b); \<Gamma> \<turnstile> M \<turnstile> ((a,B1)#\<Delta>); set \<Delta>' = {(b,B1 OR B2)}\<union>set \<Delta>; validc \<Delta>'\<rbrakk> 
           \<Longrightarrow> \<Gamma> \<turnstile> OrR1 <a>.M b \<turnstile> \<Delta>'"
  | TOrR2:  "\<lbrakk>a\<sharp>(\<Delta>,b); \<Gamma> \<turnstile> M \<turnstile> ((a,B2)#\<Delta>); set \<Delta>' = {(b,B1 OR B2)}\<union>set \<Delta>; validc \<Delta>'\<rbrakk> 
           \<Longrightarrow> \<Gamma> \<turnstile> OrR2 <a>.M b \<turnstile> \<Delta>'"
  | TImpL:  "\<lbrakk>a\<sharp>(\<Delta>,N); x\<sharp>(\<Gamma>,M,y); \<Gamma> \<turnstile> M \<turnstile> ((a,B)#\<Delta>); ((x,C)#\<Gamma>) \<turnstile> N \<turnstile> \<Delta>;
           set \<Gamma>' = {(y,B IMP C)} \<union> set \<Gamma>; validn \<Gamma>'\<rbrakk> 
           \<Longrightarrow> \<Gamma>' \<turnstile> ImpL <a>.M (x).N y \<turnstile> \<Delta>"
  | TImpR:  "\<lbrakk>a\<sharp>(\<Delta>,b); x\<sharp>\<Gamma>; ((x,B)#\<Gamma>) \<turnstile> M \<turnstile> ((a,C)#\<Delta>); set \<Delta>' = {(b,B IMP C)}\<union>set \<Delta>; validc \<Delta>'\<rbrakk> 
           \<Longrightarrow> \<Gamma> \<turnstile> ImpR (x).<a>.M b \<turnstile> \<Delta>'"
  | TCut:   "\<lbrakk>a\<sharp>(\<Delta>,N); x\<sharp>(\<Gamma>,M); \<Gamma> \<turnstile> M \<turnstile> ((a,B)#\<Delta>); ((x,B)#\<Gamma>) \<turnstile> N \<turnstile> \<Delta>\<rbrakk> 
           \<Longrightarrow> \<Gamma> \<turnstile> Cut <a>.M (x).N \<turnstile> \<Delta>"

equivariance typing

lemma fresh_set_member:
  fixes x::"name"
    and   a::"coname"
  shows "x\<sharp>L \<Longrightarrow> e\<in>set L \<Longrightarrow> x\<sharp>e"
    and   "a\<sharp>L \<Longrightarrow> e\<in>set L \<Longrightarrow> a\<sharp>e"   
  by (induct L) (auto simp add: fresh_list_cons) 

lemma fresh_subset:
  fixes x::"name"
    and   a::"coname"
  shows "x\<sharp>L \<Longrightarrow> set L' \<subseteq> set L \<Longrightarrow> x\<sharp>L'"
    and   "a\<sharp>L \<Longrightarrow> set L' \<subseteq> set L \<Longrightarrow> a\<sharp>L'"   
   apply(induct L' arbitrary: L) 
     apply(auto simp add: fresh_list_cons fresh_list_nil intro: fresh_set_member)
  done

lemma fresh_subset_ext:
  fixes x::"name"
    and   a::"coname"
  shows "x\<sharp>L \<Longrightarrow> x\<sharp>e \<Longrightarrow> set L' \<subseteq> set (e#L) \<Longrightarrow> x\<sharp>L'"
    and   "a\<sharp>L \<Longrightarrow> a\<sharp>e \<Longrightarrow> set L' \<subseteq> set (e#L) \<Longrightarrow> a\<sharp>L'"   
   apply(induct L' arbitrary: L) 
     apply(auto simp add: fresh_list_cons fresh_list_nil intro: fresh_set_member)
  done

lemma fresh_under_insert:
  fixes x::"name"
    and   a::"coname"
    and   \<Gamma>::"ctxtn"
    and   \<Delta>::"ctxtc"
  shows "x\<sharp>\<Gamma> \<Longrightarrow> x\<noteq>y \<Longrightarrow> set \<Gamma>' = insert (y,B) (set \<Gamma>) \<Longrightarrow> x\<sharp>\<Gamma>'"
    and   "a\<sharp>\<Delta> \<Longrightarrow> a\<noteq>c \<Longrightarrow> set \<Delta>' = insert (c,B) (set \<Delta>) \<Longrightarrow> a\<sharp>\<Delta>'"   
   apply(rule fresh_subset_ext(1))
     apply(auto simp add: fresh_prod fresh_atm fresh_ty)
  apply(rule fresh_subset_ext(2))
    apply(auto simp add: fresh_prod fresh_atm fresh_ty)
  done

nominal_inductive typing
                       apply (simp_all add: abs_fresh fresh_atm fresh_list_cons fresh_prod fresh_ty fresh_ctxt 
      fresh_list_append abs_supp fin_supp)
           apply(auto intro: fresh_under_insert)
  done

lemma validn_elim:
  assumes a: "validn ((x,B)#\<Gamma>)"
  shows "validn \<Gamma> \<and> x\<sharp>\<Gamma>"
  using a
  apply(erule_tac validn.cases)
   apply(auto)
  done

lemma validc_elim:
  assumes a: "validc ((a,B)#\<Delta>)"
  shows "validc \<Delta> \<and> a\<sharp>\<Delta>"
  using a
  apply(erule_tac validc.cases)
   apply(auto)
  done

lemma context_fresh:
  fixes x::"name"
    and   a::"coname"
  shows "x\<sharp>\<Gamma> \<Longrightarrow> \<not>(\<exists>B. (x,B)\<in>set \<Gamma>)"
    and   "a\<sharp>\<Delta> \<Longrightarrow> \<not>(\<exists>B. (a,B)\<in>set \<Delta>)"
   apply -
   apply(induct \<Gamma>)
    apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

lemma typing_implies_valid:
  assumes a: "\<Gamma> \<turnstile> M \<turnstile> \<Delta>"
  shows "validn \<Gamma> \<and> validc \<Delta>"
  using a
  apply(nominal_induct rule: typing.strong_induct)
             apply(auto dest: validn_elim validc_elim)
  done

lemma ty_perm:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
    and   B::"ty"
  shows "pi1\<bullet>B=B" and "pi2\<bullet>B=B"
   apply(nominal_induct B rule: ty.strong_induct)
           apply(auto simp add: perm_string)
  done

lemma ctxt_perm:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
    and   \<Gamma>::"ctxtn"
    and   \<Delta>::"ctxtc"
  shows "pi2\<bullet>\<Gamma>=\<Gamma>" and "pi1\<bullet>\<Delta>=\<Delta>"
   apply -
   apply(induct \<Gamma>)
    apply(auto simp add: calc_atm ty_perm)
  apply(induct \<Delta>)
   apply(auto simp add: calc_atm ty_perm)
  done

lemma typing_Ax_elim1: 
  assumes a: "\<Gamma> \<turnstile> Ax x a \<turnstile> ((a,B)#\<Delta>)"
  shows "(x,B)\<in>set \<Gamma>"
  using a
  apply(erule_tac typing.cases)
             apply(simp_all add: trm.inject)
  apply(auto)
  apply(auto dest: validc_elim context_fresh)
  done

lemma typing_Ax_elim2: 
  assumes a: "((x,B)#\<Gamma>) \<turnstile> Ax x a \<turnstile> \<Delta>"
  shows "(a,B)\<in>set \<Delta>"
  using a
  apply(erule_tac typing.cases)
             apply(simp_all add: trm.inject)
  apply(auto  dest!: validn_elim context_fresh)
  done

lemma psubst_Ax_aux: 
  assumes a: "\<theta>_c cmaps a to Some (y,N)"
  shows "lookupb x a \<theta>_c c P = Cut <c>.P (y).N"
  using a
  apply(induct \<theta>_c)
   apply(auto)
  done

lemma psubst_Ax:
  assumes a: "\<theta>_n nmaps x to Some (c,P)"
    and     b: "\<theta>_c cmaps a to Some (y,N)"
  shows "\<theta>_n,\<theta>_c<Ax x a> = Cut <c>.P (y).N"
  using a b
  apply(induct \<theta>_n)
   apply(auto simp add: psubst_Ax_aux)
  done

lemma psubst_Cut:
  assumes a: "\<forall>x. M\<noteq>Ax x c"
    and     b: "\<forall>a. N\<noteq>Ax x a"
    and     c: "c\<sharp>(\<theta>_n,\<theta>_c,N)" "x\<sharp>(\<theta>_n,\<theta>_c,M)"
  shows "\<theta>_n,\<theta>_c<Cut <c>.M (x).N> = Cut <c>.(\<theta>_n,\<theta>_c<M>) (x).(\<theta>_n,\<theta>_c<N>)"
  using a b c
  apply(simp)
  done

lemma all_CAND: 
  assumes a: "\<Gamma> \<turnstile> M \<turnstile> \<Delta>"
    and     b: "\<theta>_n ncloses \<Gamma>"
    and     c: "\<theta>_c ccloses \<Delta>"
  shows "SNa (\<theta>_n,\<theta>_c<M>)"
  using a b c
proof(nominal_induct avoiding: \<theta>_n \<theta>_c rule: typing.strong_induct)
  case (TAx \<Gamma> \<Delta> x B a \<theta>_n \<theta>_c)
  then show ?case
    apply -
    apply(drule ncloses_elim)
     apply(assumption)
    apply(drule ccloses_elim)
     apply(assumption)
    apply(erule exE)+
    apply(erule conjE)+
    apply(rule_tac s="Cut <c>.P (xa).Pa" and t="\<theta>_n,\<theta>_c<Ax x a>" in subst)
     apply(rule sym)
     apply(simp only: psubst_Ax)
    apply(simp add: CUT_SNa)
    done
next
  case (TNotR x \<Gamma> B M \<Delta> \<Delta>' a \<theta>_n \<theta>_c) 
  then show ?case 
    apply(simp)
    apply(subgoal_tac "(a,NOT B) \<in> set \<Delta>'")
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(simp)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(rule_tac B="NOT B" in CUT_SNa)
      apply(simp)
      apply(rule disjI2)
      apply(rule disjI2)
      apply(rule_tac x="c" in exI)
      apply(rule_tac x="x" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule conjI)
       apply(rule fic.intros)
       apply(rule psubst_fresh_coname)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGn_def)
      apply(simp)
      apply(rule_tac x="x" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule allI)+
      apply(rule impI)
      apply(simp add: psubst_nsubst[symmetric])
      apply(drule_tac x="(x,aa,Pa)#\<theta>_n" in meta_spec)
      apply(drule_tac x="\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(rule ncloses_extend)
          apply(assumption)
         apply(assumption)
        apply(assumption)
       apply(assumption)
      apply(drule meta_mp)
       apply(rule ccloses_subset)
        apply(assumption)
       apply(blast)
      apply(assumption)
     apply(simp)
    apply(blast)
    done
next
  case (TNotL a \<Delta> \<Gamma> M B \<Gamma>' x \<theta>_n \<theta>_c)
  then show ?case
    apply(simp)
    apply(subgoal_tac "(x,NOT B) \<in> set \<Gamma>'")
     apply(drule ncloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(simp del: NEGc.simps)
     apply(generate_fresh "name")
     apply(fresh_fun_simp)
     apply(rule_tac B="NOT B" in CUT_SNa)
      apply(simp)
     apply(rule NEG_intro)
     apply(simp (no_asm))
     apply(rule disjI2)
     apply(rule disjI2)
     apply(rule_tac x="a" in exI)
     apply(rule_tac x="ca" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule conjI)
      apply(rule fin.intros)
      apply(rule psubst_fresh_name)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(rule BINDING_implies_CAND)
     apply(unfold BINDINGc_def)
     apply(simp (no_asm))
     apply(rule_tac x="a" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(simp (no_asm))
     apply(rule allI)+
     apply(rule impI)
     apply(simp del: NEGc.simps add: psubst_csubst[symmetric])
     apply(drule_tac x="\<theta>_n" in meta_spec)
     apply(drule_tac x="(a,xa,Pa)#\<theta>_c" in meta_spec)
     apply(drule meta_mp)
      apply(rule ncloses_subset)
       apply(assumption)
      apply(blast)
     apply(drule meta_mp)
      apply(rule ccloses_extend)
         apply(assumption)
        apply(assumption)
       apply(assumption)
      apply(assumption)
     apply(assumption)
    apply(blast)
    done
next
  case (TAndL1 x \<Gamma> y B1 M \<Delta> \<Gamma>' B2 \<theta>_n \<theta>_c)
  then show ?case     
    apply(simp)
    apply(subgoal_tac "(y,B1 AND B2) \<in> set \<Gamma>'")
     apply(drule ncloses_elim)
      apply(assumption)
     apply(erule exE)+ 
     apply(simp del: NEGc.simps)
     apply(generate_fresh "name")
     apply(fresh_fun_simp)
     apply(rule_tac B="B1 AND B2" in CUT_SNa)
      apply(simp)
     apply(rule NEG_intro)
     apply(simp (no_asm))
     apply(rule disjI2)
     apply(rule disjI2)
     apply(rule disjI1)
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="ca" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule conjI)
      apply(rule fin.intros)
      apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
      apply(rule psubst_fresh_name)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(rule BINDING_implies_CAND)
     apply(unfold BINDINGn_def)
     apply(simp (no_asm))
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(simp (no_asm))
     apply(rule allI)+
     apply(rule impI)
     apply(simp del: NEGc.simps add: psubst_nsubst[symmetric])
     apply(drule_tac x="(x,a,Pa)#\<theta>_n" in meta_spec)
     apply(drule_tac x="\<theta>_c" in meta_spec)
     apply(drule meta_mp)
      apply(rule ncloses_extend)
         apply(rule ncloses_subset)
          apply(assumption)
         apply(blast)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(drule meta_mp)
      apply(assumption)
     apply(assumption)
    apply(blast)
    done
next
  case (TAndL2 x \<Gamma> y B2 M \<Delta> \<Gamma>' B1 \<theta>_n \<theta>_c)
  then show ?case 
    apply(simp)
    apply(subgoal_tac "(y,B1 AND B2) \<in> set \<Gamma>'")
     apply(drule ncloses_elim)
      apply(assumption)
     apply(erule exE)+ 
     apply(simp del: NEGc.simps)
     apply(generate_fresh "name")
     apply(fresh_fun_simp)
     apply(rule_tac B="B1 AND B2" in CUT_SNa)
      apply(simp)
     apply(rule NEG_intro)
     apply(simp (no_asm))
     apply(rule disjI2)
     apply(rule disjI2)
     apply(rule disjI2)
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="ca" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule conjI)
      apply(rule fin.intros)
      apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
      apply(rule psubst_fresh_name)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(rule BINDING_implies_CAND)
     apply(unfold BINDINGn_def)
     apply(simp (no_asm))
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(simp (no_asm))
     apply(rule allI)+
     apply(rule impI)
     apply(simp del: NEGc.simps add: psubst_nsubst[symmetric])
     apply(drule_tac x="(x,a,Pa)#\<theta>_n" in meta_spec)
     apply(drule_tac x="\<theta>_c" in meta_spec)
     apply(drule meta_mp)
      apply(rule ncloses_extend)
         apply(rule ncloses_subset)
          apply(assumption)
         apply(blast)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(drule meta_mp)
      apply(assumption)
     apply(assumption)
    apply(blast)
    done
next
  case (TAndR a \<Delta> N c b M \<Gamma> B C \<Delta>' \<theta>_n \<theta>_c)
  then show ?case 
    apply(simp)
    apply(subgoal_tac "(c,B AND C) \<in> set \<Delta>'")
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(simp)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(rule_tac B="B AND C" in CUT_SNa)
      apply(simp)
      apply(rule disjI2)
      apply(rule disjI2)
      apply(rule_tac x="ca" in exI)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="b" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
      apply(simp)
      apply(rule conjI)
       apply(rule fic.intros)
        apply(simp add: abs_fresh fresh_prod fresh_atm)
        apply(rule psubst_fresh_coname)
          apply(simp)
         apply(simp)
        apply(simp)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
       apply(rule psubst_fresh_coname)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(rule conjI)
       apply(rule BINDING_implies_CAND)
       apply(unfold BINDINGc_def)
       apply(simp)
       apply(rule_tac x="a" in exI)
       apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
       apply(simp)
       apply(rule allI)+
       apply(rule impI)
       apply(simp add: psubst_csubst[symmetric])
       apply(drule_tac x="\<theta>_n" in meta_spec)
       apply(drule_tac x="(a,xa,Pa)#\<theta>_c" in meta_spec)
       apply(drule meta_mp)
        apply(assumption)
       apply(drule meta_mp)
        apply(rule ccloses_extend)
           apply(rule ccloses_subset)
            apply(assumption)
           apply(blast)
          apply(simp)
         apply(simp)
        apply(assumption)
       apply(assumption)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGc_def)
      apply(simp)
      apply(rule_tac x="b" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
      apply(simp)
      apply(rule allI)+
      apply(rule impI)
      apply(simp add: psubst_csubst[symmetric])
      apply(rotate_tac 14)
      apply(drule_tac x="\<theta>_n" in meta_spec)
      apply(drule_tac x="(b,xa,Pa)#\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(assumption)
      apply(drule meta_mp)
       apply(rule ccloses_extend)
          apply(rule ccloses_subset)
           apply(assumption)
          apply(blast)
         apply(simp)
        apply(simp)
       apply(assumption)
      apply(assumption)
     apply(simp)
    apply(blast)
    done
next
  case (TOrL x \<Gamma> N z y M B \<Delta> C \<Gamma>' \<theta>_n \<theta>_c)
  then show ?case 
    apply(simp)
    apply(subgoal_tac "(z,B OR C) \<in> set \<Gamma>'")
     apply(drule ncloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(simp del: NEGc.simps)
     apply(generate_fresh "name")
     apply(fresh_fun_simp)
     apply(rule_tac B="B OR C" in CUT_SNa)
      apply(simp)
     apply(rule NEG_intro)
     apply(simp (no_asm))
     apply(rule disjI2)
     apply(rule disjI2)
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="y" in exI)
     apply(rule_tac x="ca" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule conjI)
      apply(rule fin.intros)
       apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
       apply(rule psubst_fresh_name)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
      apply(rule psubst_fresh_name)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(rule conjI)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGn_def)
      apply(simp del: NEGc.simps)
      apply(rule_tac x="x" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp del: NEGc.simps)
      apply(rule allI)+
      apply(rule impI)
      apply(simp del: NEGc.simps add: psubst_nsubst[symmetric])
      apply(drule_tac x="(x,a,Pa)#\<theta>_n" in meta_spec)
      apply(drule_tac x="\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(rule ncloses_extend)
          apply(rule ncloses_subset)
           apply(assumption)
          apply(blast)
         apply(simp)
        apply(simp)
       apply(assumption)
      apply(drule meta_mp)
       apply(assumption)
      apply(assumption)
     apply(rule BINDING_implies_CAND)
     apply(unfold BINDINGn_def)
     apply(simp del: NEGc.simps)
     apply(rule_tac x="y" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule allI)+
     apply(rule impI)
     apply(simp del: NEGc.simps add: psubst_nsubst[symmetric])
     apply(rotate_tac 14)
     apply(drule_tac x="(y,a,Pa)#\<theta>_n" in meta_spec)
     apply(drule_tac x="\<theta>_c" in meta_spec)
     apply(drule meta_mp)
      apply(rule ncloses_extend)
         apply(rule ncloses_subset)
          apply(assumption)
         apply(blast)
        apply(simp)
       apply(simp)
      apply(assumption)
     apply(drule meta_mp)
      apply(assumption)
     apply(assumption)
    apply(blast)
    done
next
  case (TOrR1 a \<Delta> b \<Gamma> M B1 \<Delta>' B2 \<theta>_n \<theta>_c)
  then show ?case
    apply(simp)
    apply(subgoal_tac "(b,B1 OR B2) \<in> set \<Delta>'")
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+ 
     apply(simp del: NEGc.simps)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(rule_tac B="B1 OR B2" in CUT_SNa)
      apply(simp)
      apply(rule disjI2)
      apply(rule disjI2)
      apply(rule disjI1)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="c" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule conjI)
       apply(rule fic.intros)
       apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
       apply(rule psubst_fresh_coname)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGc_def)
      apply(simp (no_asm))
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp (no_asm))
      apply(rule allI)+
      apply(rule impI)    
      apply(simp del: NEGc.simps add: psubst_csubst[symmetric])
      apply(drule_tac x="\<theta>_n" in meta_spec)
      apply(drule_tac x="(a,xa,Pa)#\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(assumption)
      apply(drule meta_mp)
       apply(rule ccloses_extend)
          apply(rule ccloses_subset)
           apply(assumption)
          apply(blast)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(assumption)
     apply(simp)
    apply(blast)
    done
next
  case (TOrR2 a \<Delta> b \<Gamma> M B2 \<Delta>' B1 \<theta>_n \<theta>_c)
  then show ?case 
    apply(simp)
    apply(subgoal_tac "(b,B1 OR B2) \<in> set \<Delta>'")
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+ 
     apply(simp del: NEGc.simps)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(rule_tac B="B1 OR B2" in CUT_SNa)
      apply(simp)
      apply(rule disjI2)
      apply(rule disjI2)
      apply(rule disjI2)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="c" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule conjI)
       apply(rule fic.intros)
       apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
       apply(rule psubst_fresh_coname)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGc_def)
      apply(simp (no_asm))
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp (no_asm))
      apply(rule allI)+
      apply(rule impI)    
      apply(simp del: NEGc.simps add: psubst_csubst[symmetric])
      apply(drule_tac x="\<theta>_n" in meta_spec)
      apply(drule_tac x="(a,xa,Pa)#\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(assumption)
      apply(drule meta_mp)
       apply(rule ccloses_extend)
          apply(rule ccloses_subset)
           apply(assumption)
          apply(blast)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(assumption)
     apply(simp)
    apply(blast)
    done
next
  case (TImpL a \<Delta> N x \<Gamma> M y B C \<Gamma>' \<theta>_n \<theta>_c)
  then show ?case
    apply(simp)
    apply(subgoal_tac "(y,B IMP C) \<in> set \<Gamma>'")
     apply(drule ncloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(simp del: NEGc.simps)
     apply(generate_fresh "name")
     apply(fresh_fun_simp)
     apply(rule_tac B="B IMP C" in CUT_SNa)
      apply(simp)
     apply(rule NEG_intro)
     apply(simp (no_asm))
     apply(rule disjI2)
     apply(rule disjI2)
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="a" in exI)
     apply(rule_tac x="ca" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule conjI)
      apply(rule fin.intros)
       apply(rule psubst_fresh_name)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
      apply(rule psubst_fresh_name)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(rule conjI)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGc_def)
      apply(simp del: NEGc.simps)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp del: NEGc.simps)
      apply(rule allI)+
      apply(rule impI)
      apply(simp del: NEGc.simps add: psubst_csubst[symmetric])
      apply(drule_tac x="\<theta>_n" in meta_spec)
      apply(drule_tac x="(a,xa,Pa)#\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(rule ncloses_subset)
        apply(assumption)
       apply(blast)
      apply(drule meta_mp)
       apply(rule ccloses_extend)
          apply(assumption)
         apply(simp)
        apply(simp)
       apply(assumption)
      apply(assumption)
     apply(rule BINDING_implies_CAND)
     apply(unfold BINDINGn_def)
     apply(simp del: NEGc.simps)
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule allI)+
     apply(rule impI)
     apply(simp del: NEGc.simps add: psubst_nsubst[symmetric])
     apply(rotate_tac 12)
     apply(drule_tac x="(x,aa,Pa)#\<theta>_n" in meta_spec)
     apply(drule_tac x="\<theta>_c" in meta_spec)
     apply(drule meta_mp)
      apply(rule ncloses_extend)
         apply(rule ncloses_subset)
          apply(assumption)
         apply(blast)
        apply(simp)
       apply(simp)
      apply(assumption)
     apply(drule meta_mp)
      apply(assumption)
     apply(assumption)
    apply(blast)
    done
next
  case (TImpR a \<Delta> b x \<Gamma> B M C \<Delta>' \<theta>_n \<theta>_c)
  then show ?case
    apply(simp)
    apply(subgoal_tac "(b,B IMP C) \<in> set \<Delta>'")
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(simp)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(rule_tac B="B IMP C" in CUT_SNa)
      apply(simp)
      apply(rule disjI2)
      apply(rule disjI2)
      apply(rule_tac x="x" in exI)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="c" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule conjI)
       apply(rule fic.intros)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
       apply(rule psubst_fresh_coname)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(rule conjI)
       apply(rule allI)+
       apply(rule impI)
       apply(simp add: psubst_csubst[symmetric])
       apply(rule BINDING_implies_CAND)
       apply(unfold BINDINGn_def)
       apply(simp)
       apply(rule_tac x="x" in exI)
       apply(rule_tac x="\<theta>_n,((a,z,Pa)#\<theta>_c)<M>" in exI)
       apply(simp)
       apply(rule allI)+
       apply(rule impI)
       apply(rule_tac t="\<theta>_n,((a,z,Pa)#\<theta>_c)<M>{x:=<aa>.Pb}" and 
        s="((x,aa,Pb)#\<theta>_n),((a,z,Pa)#\<theta>_c)<M>" in subst)
        apply(rule psubst_nsubst)
        apply(simp add: fresh_prod fresh_atm fresh_list_cons)
       apply(drule_tac x="(x,aa,Pb)#\<theta>_n" in meta_spec)
       apply(drule_tac x="(a,z,Pa)#\<theta>_c" in meta_spec)
       apply(drule meta_mp)
        apply(rule ncloses_extend)
           apply(assumption)
          apply(simp)
         apply(simp)
        apply(simp)
       apply(drule meta_mp)
        apply(rule ccloses_extend)
           apply(rule ccloses_subset)
            apply(assumption)
           apply(blast)
          apply(auto intro: fresh_subset simp del: NEGc.simps)[1]
         apply(simp)
        apply(simp)
       apply(assumption)
      apply(rule allI)+
      apply(rule impI)
      apply(simp add: psubst_nsubst[symmetric])
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGc_def)
      apply(simp)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="((x,ca,Q)#\<theta>_n),\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule allI)+
      apply(rule impI)
      apply(rule_tac t="((x,ca,Q)#\<theta>_n),\<theta>_c<M>{a:=(xaa).Pa}" and 
        s="((x,ca,Q)#\<theta>_n),((a,xaa,Pa)#\<theta>_c)<M>" in subst)
       apply(rule psubst_csubst)
       apply(simp add: fresh_prod fresh_atm fresh_list_cons)
      apply(drule_tac x="(x,ca,Q)#\<theta>_n" in meta_spec)
      apply(drule_tac x="(a,xaa,Pa)#\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(rule ncloses_extend)
          apply(assumption)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(drule meta_mp)
       apply(rule ccloses_extend)
          apply(rule ccloses_subset)
           apply(assumption)
          apply(blast)
         apply(auto intro: fresh_subset simp del: NEGc.simps)[1]
        apply(simp)
       apply(simp)
      apply(assumption)
     apply(simp)
    apply(blast)
    done
next
  case (TCut a \<Delta> N x \<Gamma> M B \<theta>_n \<theta>_c)
  then show ?case 
    apply -
    apply(case_tac "\<forall>y. M\<noteq>Ax y a")
     apply(case_tac "\<forall>c. N\<noteq>Ax x c")
      apply(simp)
      apply(rule_tac B="B" in CUT_SNa)
       apply(rule BINDING_implies_CAND)
       apply(unfold BINDINGc_def)
       apply(simp)
       apply(rule_tac x="a" in exI)
       apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
       apply(simp)
       apply(rule allI)
       apply(rule allI)
       apply(rule impI)
       apply(simp add: psubst_csubst[symmetric]) (*?*)
       apply(drule_tac x="\<theta>_n" in meta_spec)
       apply(drule_tac x="(a,xa,P)#\<theta>_c" in meta_spec)
       apply(drule meta_mp)
        apply(assumption)
       apply(drule meta_mp)
        apply(rule ccloses_extend) 
           apply(assumption)
          apply(assumption)
         apply(assumption)
        apply(assumption)
       apply(assumption)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGn_def)
      apply(simp)
      apply(rule_tac x="x" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
      apply(simp)
      apply(rule allI)
      apply(rule allI)
      apply(rule impI)
      apply(simp add: psubst_nsubst[symmetric]) (*?*)
      apply(rotate_tac 11)
      apply(drule_tac x="(x,aa,P)#\<theta>_n" in meta_spec)
      apply(drule_tac x="\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(rule ncloses_extend)
          apply(assumption)
         apply(assumption)
        apply(assumption)
       apply(assumption)
      apply(drule_tac meta_mp)
       apply(assumption)
      apply(assumption)
      (* cases at least one axiom *)
     apply(simp (no_asm_use))
     apply(erule exE)
     apply(simp del: psubst.simps)
     apply(drule typing_Ax_elim2)
     apply(auto simp add: trm.inject)[1]
     apply(rule_tac B="B" in CUT_SNa)
      (* left term *)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGc_def)
      apply(simp)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule allI)+
      apply(rule impI)
      apply(drule_tac x="\<theta>_n" in meta_spec)
      apply(drule_tac x="(a,xa,P)#\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(assumption)
      apply(drule meta_mp)
       apply(rule ccloses_extend) 
          apply(assumption)
         apply(assumption)
        apply(assumption)
       apply(assumption)
      apply(simp add: psubst_csubst[symmetric]) (*?*)
      (* right term -axiom *)
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(erule conjE)
     apply(frule_tac y="x" in lookupd_cmaps)
     apply(drule cmaps_fresh)
      apply(assumption)
     apply(simp)
     apply(subgoal_tac "(x):P[xa\<turnstile>n>x] = (xa):P")
      apply(simp)
     apply(simp add: ntrm.inject)
     apply(simp add: alpha fresh_prod fresh_atm)
     apply(rule sym)
     apply(rule nrename_swap)
     apply(simp)
      (* M is axiom *)
    apply(simp)
    apply(auto)[1]
      (* both are axioms *)
     apply(rule_tac B="B" in CUT_SNa)
      apply(drule typing_Ax_elim1)
      apply(drule ncloses_elim)
       apply(assumption)
      apply(erule exE)+
      apply(erule conjE)
      apply(frule_tac a="a" in lookupc_nmaps)
      apply(drule_tac a="a" in nmaps_fresh)
       apply(assumption)
      apply(simp)
      apply(subgoal_tac "<a>:P[c\<turnstile>c>a] = <c>:P")
       apply(simp)
      apply(simp add: ctrm.inject)
      apply(simp add: alpha fresh_prod fresh_atm)
      apply(rule sym)
      apply(rule crename_swap)
      apply(simp)
     apply(drule typing_Ax_elim2)
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(erule conjE)
     apply(frule_tac y="x" in lookupd_cmaps)
     apply(drule cmaps_fresh)
      apply(assumption)
     apply(simp)
     apply(subgoal_tac "(x):P[xa\<turnstile>n>x] = (xa):P")
      apply(simp)
     apply(simp add: ntrm.inject)
     apply(simp add: alpha fresh_prod fresh_atm)
     apply(rule sym)
     apply(rule nrename_swap)
     apply(simp)
      (* N is not axioms *)
    apply(rule_tac B="B" in CUT_SNa)
      (* left term *)
     apply(drule typing_Ax_elim1)
     apply(drule ncloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(erule conjE)
     apply(frule_tac a="a" in lookupc_nmaps)
     apply(drule_tac a="a" in nmaps_fresh)
      apply(assumption)
     apply(simp)
     apply(subgoal_tac "<a>:P[c\<turnstile>c>a] = <c>:P")
      apply(simp)
     apply(simp add: ctrm.inject)
     apply(simp add: alpha fresh_prod fresh_atm)
     apply(rule sym)
     apply(rule crename_swap)
     apply(simp)
    apply(rule BINDING_implies_CAND)
    apply(unfold BINDINGn_def)
    apply(simp)
    apply(rule_tac x="x" in exI)
    apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
    apply(simp)
    apply(rule allI)
    apply(rule allI)
    apply(rule impI)
    apply(simp add: psubst_nsubst[symmetric]) (*?*)
    apply(rotate_tac 10)
    apply(drule_tac x="(x,aa,P)#\<theta>_n" in meta_spec)
    apply(drule_tac x="\<theta>_c" in meta_spec)
    apply(drule meta_mp)
     apply(rule ncloses_extend)
        apply(assumption)
       apply(assumption)
      apply(assumption)
     apply(assumption)
    apply(drule_tac meta_mp)
     apply(assumption)
    apply(assumption)
    done
qed

primrec "idn" :: "(name\<times>ty) list\<Rightarrow>coname\<Rightarrow>(name\<times>coname\<times>trm) list" where
  "idn [] a   = []"
| "idn (p#\<Gamma>) a = ((fst p),a,Ax (fst p) a)#(idn \<Gamma> a)"

primrec "idc" :: "(coname\<times>ty) list\<Rightarrow>name\<Rightarrow>(coname\<times>name\<times>trm) list" where
  "idc [] x    = []"
| "idc (p#\<Delta>) x = ((fst p),x,Ax x (fst p))#(idc \<Delta> x)"

lemma idn_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(idn \<Gamma> a)) = idn (pi1\<bullet>\<Gamma>) (pi1\<bullet>a)"
    and   "(pi2\<bullet>(idn \<Gamma> a)) = idn (pi2\<bullet>\<Gamma>) (pi2\<bullet>a)"
   apply(induct \<Gamma>)
     apply(auto)
  done

lemma idc_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(idc \<Delta> x)) = idc (pi1\<bullet>\<Delta>) (pi1\<bullet>x)"
    and   "(pi2\<bullet>(idc \<Delta> x)) = idc (pi2\<bullet>\<Delta>) (pi2\<bullet>x)"
   apply(induct \<Delta>)
     apply(auto)
  done

lemma ccloses_id:
  shows "(idc \<Delta> x) ccloses \<Delta>"
  apply(induct \<Delta>)
   apply(auto simp add: ccloses_def)
   apply(rule Ax_in_CANDs)
  apply(rule Ax_in_CANDs)
  done

lemma ncloses_id:
  shows "(idn \<Gamma> a) ncloses \<Gamma>"
  apply(induct \<Gamma>)
   apply(auto simp add: ncloses_def)
   apply(rule Ax_in_CANDs)
  apply(rule Ax_in_CANDs)
  done

lemma fresh_idn:
  fixes x::"name"
    and   a::"coname"
  shows "x\<sharp>\<Gamma> \<Longrightarrow> x\<sharp>idn \<Gamma> a"
    and   "a\<sharp>(\<Gamma>,b) \<Longrightarrow> a\<sharp>idn \<Gamma> b"
   apply(induct \<Gamma>)
     apply(auto simp add: fresh_list_cons fresh_list_nil fresh_atm fresh_prod)
  done

lemma fresh_idc:
  fixes x::"name"
    and   a::"coname"
  shows "x\<sharp>(\<Delta>,y) \<Longrightarrow> x\<sharp>idc \<Delta> y"
    and   "a\<sharp>\<Delta>  \<Longrightarrow> a\<sharp>idc \<Delta> y"
   apply(induct \<Delta>)
     apply(auto simp add: fresh_list_cons fresh_list_nil fresh_atm fresh_prod)
  done

lemma idc_cmaps:
  assumes a: "idc \<Delta> y cmaps b to Some (x,M)"
  shows "M=Ax x b"
  using a
  apply(induct \<Delta>)
   apply(auto)
  apply(case_tac "b=a")
   apply(auto)
  done

lemma idn_nmaps:
  assumes a: "idn \<Gamma> a nmaps x to Some (b,M)"
  shows "M=Ax x b"
  using a
  apply(induct \<Gamma>)
   apply(auto)
  apply(case_tac "aa=x")
   apply(auto)
  done

lemma lookup1:
  assumes a: "x\<sharp>(idn \<Gamma> b)"
  shows "lookup x a (idn \<Gamma> b) \<theta>_c = lookupa x a \<theta>_c"
  using a
  apply(induct \<Gamma>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

lemma lookup2:
  assumes a: "\<not>(x\<sharp>(idn \<Gamma> b))"
  shows "lookup x a (idn \<Gamma> b) \<theta>_c = lookupb x a \<theta>_c b (Ax x b)"
  using a
  apply(induct \<Gamma>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm fresh_list_nil)
  done

lemma lookup3:
  assumes a: "a\<sharp>(idc \<Delta> y)"
  shows "lookupa x a (idc \<Delta> y) = Ax x a"
  using a
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

lemma lookup4:
  assumes a: "\<not>(a\<sharp>(idc \<Delta> y))"
  shows "lookupa x a (idc \<Delta> y) = Cut <a>.(Ax x a) (y).Ax y a"
  using a
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm fresh_list_nil)
  done

lemma lookup5:
  assumes a: "a\<sharp>(idc \<Delta> y)"
  shows "lookupb x a (idc \<Delta> y) c P = Cut <c>.P (x).Ax x a"
  using a
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm fresh_list_nil)
  done

lemma lookup6:
  assumes a: "\<not>(a\<sharp>(idc \<Delta> y))"
  shows "lookupb x a (idc \<Delta> y) c P = Cut <c>.P (y).Ax y a"
  using a
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm fresh_list_nil)
  done

lemma lookup7:
  shows "lookupc x a (idn \<Gamma> b) = Ax x a"
  apply(induct \<Gamma>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm fresh_list_nil)
  done

lemma lookup8:
  shows "lookupd x a (idc \<Delta> y) = Ax x a"
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm fresh_list_nil)
  done

lemma id_redu:
  shows "(idn \<Gamma> x),(idc \<Delta> a)<M> \<longrightarrow>\<^sub>a* M"
  apply(nominal_induct M avoiding: \<Gamma> \<Delta> x a rule: trm.strong_induct)
             apply(auto)
    (* Ax *)
             apply(case_tac "name\<sharp>(idn \<Gamma> x)")
              apply(simp add: lookup1)
              apply(case_tac "coname\<sharp>(idc \<Delta> a)")
               apply(simp add: lookup3)
              apply(simp add: lookup4)
              apply(rule rtranclp_trans)
               apply(rule a_starI)
               apply(rule al_redu)
               apply(rule better_LAxR_intro)
               apply(rule fic.intros)
              apply(simp)
             apply(simp add: lookup2)
             apply(case_tac "coname\<sharp>(idc \<Delta> a)")
              apply(simp add: lookup5)
              apply(rule rtranclp_trans)
               apply(rule a_starI)
               apply(rule al_redu)
               apply(rule better_LAxR_intro)
               apply(rule fic.intros)
              apply(simp)
             apply(simp add: lookup6)
             apply(rule rtranclp_trans)
              apply(rule a_starI)
              apply(rule al_redu)
              apply(rule better_LAxR_intro)
              apply(rule fic.intros)
             apply(simp)
    (* Cut *)
            apply(auto simp add: fresh_idn fresh_idc psubst_fresh_name psubst_fresh_coname fresh_atm fresh_prod )[1]
               apply(simp add: lookup7 lookup8)
              apply(simp add: lookup7 lookup8)
              apply(simp add: a_star_Cut)
             apply(simp add: lookup7 lookup8)
             apply(simp add: a_star_Cut)
            apply(simp add: a_star_Cut)
    (* NotR *)
           apply(simp add: fresh_idn fresh_idc)
           apply(case_tac "findc (idc \<Delta> a) coname")
            apply(simp)
            apply(simp add: a_star_NotR)
           apply(auto)[1]
           apply(generate_fresh "coname")
           apply(fresh_fun_simp)
           apply(drule idc_cmaps)
           apply(simp)
           apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
            apply(rule rtranclp_trans)
             apply(rule a_starI)
             apply(rule al_redu)
             apply(rule better_LAxR_intro)
             apply(rule fic.intros)
             apply(assumption)
            apply(simp add: crename_fresh)
            apply(simp add: a_star_NotR)
           apply(rule psubst_fresh_coname)
             apply(rule fresh_idn)
             apply(simp)
            apply(rule fresh_idc)
            apply(simp)
           apply(simp)
    (* NotL *)
          apply(simp add: fresh_idn fresh_idc)
          apply(case_tac "findn (idn \<Gamma> x) name")
           apply(simp)
           apply(simp add: a_star_NotL)
          apply(auto)[1]
          apply(generate_fresh "name")
          apply(fresh_fun_simp)
          apply(drule idn_nmaps)
          apply(simp)
          apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
           apply(rule rtranclp_trans)
            apply(rule a_starI)
            apply(rule al_redu)
            apply(rule better_LAxL_intro)
            apply(rule fin.intros)
            apply(assumption)
           apply(simp add: nrename_fresh)
           apply(simp add: a_star_NotL)
          apply(rule psubst_fresh_name)
            apply(rule fresh_idn)
            apply(simp)
           apply(rule fresh_idc)
           apply(simp)
          apply(simp)
    (* AndR *)
         apply(simp add: fresh_idn fresh_idc)
         apply(case_tac "findc (idc \<Delta> a) coname3")
          apply(simp)
          apply(simp add: a_star_AndR)
         apply(auto)[1]
         apply(generate_fresh "coname")
         apply(fresh_fun_simp)
         apply(drule idc_cmaps)
         apply(simp)
         apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm1>")
          apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm2>")
           apply(rule rtranclp_trans)
            apply(rule a_starI)
            apply(rule al_redu)
            apply(rule better_LAxR_intro)
            apply(rule fic.intros)
             apply(simp add: abs_fresh)
            apply(simp add: abs_fresh)
           apply(auto simp add: fresh_idn fresh_idc psubst_fresh_name crename_fresh fresh_atm fresh_prod )[1]
           apply(rule aux3)
            apply(rule crename.simps)
              apply(auto simp add: fresh_prod fresh_atm)[1]
              apply(rule psubst_fresh_coname)
                apply(rule fresh_idn)
                apply(simp add: fresh_prod fresh_atm)
               apply(rule fresh_idc)
               apply(simp)
              apply(simp)
             apply(auto simp add: fresh_prod fresh_atm)[1]
             apply(rule psubst_fresh_coname)
               apply(rule fresh_idn)
               apply(simp add: fresh_prod fresh_atm)
              apply(rule fresh_idc)
              apply(simp)
             apply(simp)
            apply(simp)
           apply(simp)
           apply(simp add: crename_fresh)
           apply(simp add: a_star_AndR)
          apply(rule psubst_fresh_coname)
            apply(rule fresh_idn)
            apply(simp)
           apply(rule fresh_idc)
           apply(simp)
          apply(simp)
         apply(rule psubst_fresh_coname)
           apply(rule fresh_idn)
           apply(simp)
          apply(rule fresh_idc)
          apply(simp)
         apply(simp)
    (* AndL1 *)
        apply(simp add: fresh_idn fresh_idc)
        apply(case_tac "findn (idn \<Gamma> x) name2")
         apply(simp)
         apply(simp add: a_star_AndL1)
        apply(auto)[1]
        apply(generate_fresh "name")
        apply(fresh_fun_simp)
        apply(drule idn_nmaps)
        apply(simp)
        apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
         apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(rule fin.intros)
          apply(simp add: abs_fresh)
         apply(rule aux3)
          apply(rule nrename.simps)
          apply(auto simp add: fresh_prod fresh_atm)[1]
         apply(simp)
         apply(simp add: nrename_fresh)
         apply(simp add: a_star_AndL1)
        apply(rule psubst_fresh_name)
          apply(rule fresh_idn)
          apply(simp)
         apply(rule fresh_idc)
         apply(simp)
        apply(simp)
    (* AndL2 *)
       apply(simp add: fresh_idn fresh_idc)
       apply(case_tac "findn (idn \<Gamma> x) name2")
        apply(simp)
        apply(simp add: a_star_AndL2)
       apply(auto)[1]
       apply(generate_fresh "name")
       apply(fresh_fun_simp)
       apply(drule idn_nmaps)
       apply(simp)
       apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
        apply(rule rtranclp_trans)
         apply(rule a_starI)
         apply(rule al_redu)
         apply(rule better_LAxL_intro)
         apply(rule fin.intros)
         apply(simp add: abs_fresh)
        apply(rule aux3)
         apply(rule nrename.simps)
         apply(auto simp add: fresh_prod fresh_atm)[1]
        apply(simp)
        apply(simp add: nrename_fresh)
        apply(simp add: a_star_AndL2)
       apply(rule psubst_fresh_name)
         apply(rule fresh_idn)
         apply(simp)
        apply(rule fresh_idc)
        apply(simp)
       apply(simp)
    (* OrR1 *)
      apply(simp add: fresh_idn fresh_idc)
      apply(case_tac "findc (idc \<Delta> a) coname2")
       apply(simp)
       apply(simp add: a_star_OrR1)
      apply(auto)[1]
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(drule idc_cmaps)
      apply(simp)
      apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
       apply(rule rtranclp_trans)
        apply(rule a_starI)
        apply(rule al_redu)
        apply(rule better_LAxR_intro)
        apply(rule fic.intros)
        apply(simp add: abs_fresh)
       apply(rule aux3)
        apply(rule crename.simps)
        apply(auto simp add: fresh_prod fresh_atm)[1]
       apply(simp)
       apply(simp add: crename_fresh)
       apply(simp add: a_star_OrR1)
      apply(rule psubst_fresh_coname)
        apply(rule fresh_idn)
        apply(simp)
       apply(rule fresh_idc)
       apply(simp)
      apply(simp)
    (* OrR2 *)
     apply(simp add: fresh_idn fresh_idc)
     apply(case_tac "findc (idc \<Delta> a) coname2")
      apply(simp)
      apply(simp add: a_star_OrR2)
     apply(auto)[1]
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(drule idc_cmaps)
     apply(simp)
     apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
      apply(rule rtranclp_trans)
       apply(rule a_starI)
       apply(rule al_redu)
       apply(rule better_LAxR_intro)
       apply(rule fic.intros)
       apply(simp add: abs_fresh)
      apply(rule aux3)
       apply(rule crename.simps)
       apply(auto simp add: fresh_prod fresh_atm)[1]
      apply(simp)
      apply(simp add: crename_fresh)
      apply(simp add: a_star_OrR2)
     apply(rule psubst_fresh_coname)
       apply(rule fresh_idn)
       apply(simp)
      apply(rule fresh_idc)
      apply(simp)
     apply(simp)
    (* OrL *)
    apply(simp add: fresh_idn fresh_idc)
    apply(case_tac "findn (idn \<Gamma> x) name3")
     apply(simp)
     apply(simp add: a_star_OrL)
    apply(auto)[1]
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(drule idn_nmaps)
    apply(simp)
    apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm1>")
     apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm2>")
      apply(rule rtranclp_trans)
       apply(rule a_starI)
       apply(rule al_redu)
       apply(rule better_LAxL_intro)
       apply(rule fin.intros)
        apply(simp add: abs_fresh)
       apply(simp add: abs_fresh)
      apply(rule aux3)
       apply(rule nrename.simps)
         apply(auto simp add: fresh_prod fresh_atm)[1]
         apply(rule psubst_fresh_name)
           apply(rule fresh_idn)
           apply(simp)
          apply(rule fresh_idc)
          apply(simp add: fresh_prod fresh_atm)
         apply(simp)
        apply(auto simp add: fresh_prod fresh_atm)[1]
        apply(rule psubst_fresh_name)
          apply(rule fresh_idn)
          apply(simp)
         apply(rule fresh_idc)
         apply(simp add: fresh_prod fresh_atm)
        apply(simp)
       apply(simp)
      apply(simp)
      apply(simp add: nrename_fresh)
      apply(simp add: a_star_OrL)
     apply(rule psubst_fresh_name)
       apply(rule fresh_idn)
       apply(simp)
      apply(rule fresh_idc)
      apply(simp)
     apply(simp)
    apply(rule psubst_fresh_name)
      apply(rule fresh_idn)
      apply(simp)
     apply(rule fresh_idc)
     apply(simp)
    apply(simp)
    (* ImpR *)
   apply(simp add: fresh_idn fresh_idc)
   apply(case_tac "findc (idc \<Delta> a) coname2")
    apply(simp)
    apply(simp add: a_star_ImpR)
   apply(auto)[1]
   apply(generate_fresh "coname")
   apply(fresh_fun_simp)
   apply(drule idc_cmaps)
   apply(simp)
   apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
    apply(rule rtranclp_trans)
     apply(rule a_starI)
     apply(rule al_redu)
     apply(rule better_LAxR_intro)
     apply(rule fic.intros)
     apply(simp add: abs_fresh)
    apply(rule aux3)
     apply(rule crename.simps)
     apply(auto simp add: fresh_prod fresh_atm)[1]
    apply(simp)
    apply(simp add: crename_fresh)
    apply(simp add: a_star_ImpR)
   apply(rule psubst_fresh_coname)
     apply(rule fresh_idn)
     apply(simp)
    apply(rule fresh_idc)
    apply(simp)
   apply(simp)
    (* ImpL *)
  apply(simp add: fresh_idn fresh_idc)
  apply(case_tac "findn (idn \<Gamma> x) name2")
   apply(simp)
   apply(simp add: a_star_ImpL)
  apply(auto)[1]
  apply(generate_fresh "name")
  apply(fresh_fun_simp)
  apply(drule idn_nmaps)
  apply(simp)
  apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm1>")
   apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm2>")
    apply(rule rtranclp_trans)
     apply(rule a_starI)
     apply(rule al_redu)
     apply(rule better_LAxL_intro)
     apply(rule fin.intros)
      apply(simp add: abs_fresh)
     apply(simp add: abs_fresh)
    apply(rule aux3)
     apply(rule nrename.simps)
      apply(auto simp add: fresh_prod fresh_atm)[1]
      apply(rule psubst_fresh_coname)
        apply(rule fresh_idn)
        apply(simp add: fresh_atm)
       apply(rule fresh_idc)
       apply(simp add: fresh_prod fresh_atm)
      apply(simp)
     apply(auto simp add: fresh_prod fresh_atm)[1]
     apply(rule psubst_fresh_name)
       apply(rule fresh_idn)
       apply(simp)
      apply(rule fresh_idc)
      apply(simp add: fresh_prod fresh_atm)
     apply(simp)
    apply(simp)
    apply(simp add: nrename_fresh)
    apply(simp add: a_star_ImpL)
   apply(rule psubst_fresh_name)
     apply(rule fresh_idn)
     apply(simp)
    apply(rule fresh_idc)
    apply(simp)
   apply(simp)
  apply(rule psubst_fresh_name)
    apply(rule fresh_idn)
    apply(simp)
   apply(rule fresh_idc)
   apply(simp)
  apply(simp)
  done

theorem ALL_SNa:
  assumes a: "\<Gamma> \<turnstile> M \<turnstile> \<Delta>"
  shows "SNa M"
proof -
  fix x have "(idc \<Delta> x) ccloses \<Delta>" by (simp add: ccloses_id)
  moreover
  fix a have "(idn \<Gamma> a) ncloses \<Gamma>" by (simp add: ncloses_id)
  ultimately have "SNa ((idn \<Gamma> a),(idc \<Delta> x)<M>)" using a by (simp add: all_CAND)
  moreover
  have "((idn \<Gamma> a),(idc \<Delta> x)<M>) \<longrightarrow>\<^sub>a* M" by (simp add: id_redu)
  ultimately show "SNa M" by (simp add: a_star_preserves_SNa)
qed

end
