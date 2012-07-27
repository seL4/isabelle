theory Class1
imports "../Nominal" 
begin

section {* Term-Calculus from Urban's PhD *}

atom_decl name coname

text {* types *}

nominal_datatype ty =
    PR "string"
  | NOT  "ty"
  | AND  "ty" "ty"   ("_ AND _" [100,100] 100)
  | OR   "ty" "ty"   ("_ OR _" [100,100] 100)
  | IMP  "ty" "ty"   ("_ IMP _" [100,100] 100)

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
   (auto simp add: fresh_string)

text {* terms *}

nominal_datatype trm = 
    Ax   "name" "coname"
  | Cut  "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm"            ("Cut <_>._ (_)._" [100,100,100,100] 100)
  | NotR "\<guillemotleft>name\<guillemotright>trm" "coname"                 ("NotR (_)._ _" [100,100,100] 100)
  | NotL "\<guillemotleft>coname\<guillemotright>trm" "name"                 ("NotL <_>._ _" [100,100,100] 100)
  | AndR "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>coname\<guillemotright>trm" "coname" ("AndR <_>._ <_>._ _" [100,100,100,100,100] 100)
  | AndL1 "\<guillemotleft>name\<guillemotright>trm" "name"                  ("AndL1 (_)._ _" [100,100,100] 100)
  | AndL2 "\<guillemotleft>name\<guillemotright>trm" "name"                  ("AndL2 (_)._ _" [100,100,100] 100)
  | OrR1 "\<guillemotleft>coname\<guillemotright>trm" "coname"               ("OrR1 <_>._ _" [100,100,100] 100)
  | OrR2 "\<guillemotleft>coname\<guillemotright>trm" "coname"               ("OrR2 <_>._ _" [100,100,100] 100)
  | OrL "\<guillemotleft>name\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"        ("OrL (_)._ (_)._ _" [100,100,100,100,100] 100)
  | ImpR "\<guillemotleft>name\<guillemotright>(\<guillemotleft>coname\<guillemotright>trm)" "coname"       ("ImpR (_).<_>._ _" [100,100,100,100] 100)
  | ImpL "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"     ("ImpL <_>._ (_)._ _" [100,100,100,100,100] 100)

text {* named terms *}

nominal_datatype ntrm = Na "\<guillemotleft>name\<guillemotright>trm" ("((_):_)" [100,100] 100)

text {* conamed terms *}

nominal_datatype ctrm = Co "\<guillemotleft>coname\<guillemotright>trm" ("(<_>:_)" [100,100] 100)

text {* renaming functions *}

nominal_primrec (freshness_context: "(d::coname,e::coname)") 
  crename :: "trm \<Rightarrow> coname \<Rightarrow> coname \<Rightarrow> trm"  ("_[_\<turnstile>c>_]" [100,100,100] 100) 
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
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh abs_supp fin_supp)+
apply(fresh_guess)+
done

nominal_primrec (freshness_context: "(u::name,v::name)") 
  nrename :: "trm \<Rightarrow> name \<Rightarrow> name \<Rightarrow> trm"      ("_[_\<turnstile>n>_]" [100,100,100] 100) 
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
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh abs_supp fs_name1 fs_coname1)+
apply(fresh_guess)+
done

lemmas eq_bij = pt_bij[OF pt_name_inst, OF at_name_inst] pt_bij[OF pt_coname_inst, OF at_coname_inst]

lemma crename_name_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(M[d\<turnstile>c>e]) = (pi\<bullet>M)[(pi\<bullet>d)\<turnstile>c>(pi\<bullet>e)]"
apply(nominal_induct M avoiding: d e rule: trm.strong_induct)
apply(auto simp add: fresh_bij eq_bij)
done

lemma crename_coname_eqvt[eqvt]:
  fixes pi::"coname prm"
  shows "pi\<bullet>(M[d\<turnstile>c>e]) = (pi\<bullet>M)[(pi\<bullet>d)\<turnstile>c>(pi\<bullet>e)]"
apply(nominal_induct M avoiding: d e rule: trm.strong_induct)
apply(auto simp add: fresh_bij eq_bij)
done

lemma nrename_name_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(M[x\<turnstile>n>y]) = (pi\<bullet>M)[(pi\<bullet>x)\<turnstile>n>(pi\<bullet>y)]"
apply(nominal_induct M avoiding: x y rule: trm.strong_induct)
apply(auto simp add: fresh_bij eq_bij)
done

lemma nrename_coname_eqvt[eqvt]:
  fixes pi::"coname prm"
  shows "pi\<bullet>(M[x\<turnstile>n>y]) = (pi\<bullet>M)[(pi\<bullet>x)\<turnstile>n>(pi\<bullet>y)]"
apply(nominal_induct M avoiding: x y rule: trm.strong_induct)
apply(auto simp add: fresh_bij eq_bij)
done

lemmas rename_eqvts = crename_name_eqvt crename_coname_eqvt
                      nrename_name_eqvt nrename_coname_eqvt
lemma nrename_fresh:
  assumes a: "x\<sharp>M"
  shows "M[x\<turnstile>n>y] = M"
using a
by (nominal_induct M avoiding: x y rule: trm.strong_induct)
   (auto simp add: trm.inject fresh_atm abs_fresh fin_supp abs_supp)

lemma crename_fresh:
  assumes a: "a\<sharp>M"
  shows "M[a\<turnstile>c>b] = M"
using a
by (nominal_induct M avoiding: a b rule: trm.strong_induct)
   (auto simp add: trm.inject fresh_atm abs_fresh)

lemma nrename_nfresh:
  fixes x::"name"
  shows "x\<sharp>y\<Longrightarrow>x\<sharp>M[x\<turnstile>n>y]"
by (nominal_induct M avoiding: x y rule: trm.strong_induct)
   (auto simp add: fresh_atm abs_fresh abs_supp fin_supp)

 lemma crename_nfresh:
  fixes x::"name"
  shows "x\<sharp>M\<Longrightarrow>x\<sharp>M[a\<turnstile>c>b]"
by (nominal_induct M avoiding: a b rule: trm.strong_induct)
   (auto simp add: fresh_atm abs_fresh abs_supp fin_supp)

lemma crename_cfresh:
  fixes a::"coname"
  shows "a\<sharp>b\<Longrightarrow>a\<sharp>M[a\<turnstile>c>b]"
by (nominal_induct M avoiding: a b rule: trm.strong_induct)
   (auto simp add: fresh_atm abs_fresh abs_supp fin_supp)

lemma nrename_cfresh:
  fixes c::"coname"
  shows "c\<sharp>M\<Longrightarrow>c\<sharp>M[x\<turnstile>n>y]"
by (nominal_induct M avoiding: x y rule: trm.strong_induct)
   (auto simp add: fresh_atm abs_fresh abs_supp fin_supp)

lemma nrename_nfresh':
  fixes x::"name"
  shows "x\<sharp>(M,z,y)\<Longrightarrow>x\<sharp>M[z\<turnstile>n>y]"
by (nominal_induct M avoiding: x z y rule: trm.strong_induct)
   (auto simp add: fresh_prod fresh_atm abs_fresh abs_supp fin_supp)

lemma crename_cfresh':
  fixes a::"coname"
  shows "a\<sharp>(M,b,c)\<Longrightarrow>a\<sharp>M[b\<turnstile>c>c]"
by (nominal_induct M avoiding: a b c rule: trm.strong_induct)
   (auto simp add: fresh_prod fresh_atm abs_fresh abs_supp fin_supp)

lemma nrename_rename:
  assumes a: "x'\<sharp>M"
  shows "([(x',x)]\<bullet>M)[x'\<turnstile>n>y]= M[x\<turnstile>n>y]"
using a
apply(nominal_induct M avoiding: x x' y rule: trm.strong_induct)
apply(auto simp add: abs_fresh fresh_bij fresh_atm fresh_prod fresh_right calc_atm abs_supp fin_supp)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)
done

lemma crename_rename:
  assumes a: "a'\<sharp>M"
  shows "([(a',a)]\<bullet>M)[a'\<turnstile>c>b]= M[a\<turnstile>c>b]"
using a
apply(nominal_induct M avoiding: a a' b rule: trm.strong_induct)
apply(auto simp add: abs_fresh fresh_bij fresh_atm fresh_prod fresh_right calc_atm abs_supp fin_supp)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)
done

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
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  have "(Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N))[u\<turnstile>n>v] = 
                        Cut <a'>.(([(a',a)]\<bullet>M)[u\<turnstile>n>v]) (x').(([(x',x)]\<bullet>N)[u\<turnstile>n>v])"
    using fs1 fs2
    apply -
    apply(rule nrename.simps)
    apply(simp add: fresh_left calc_atm)
    apply(simp add: fresh_left calc_atm)
    done
  also have "\<dots> = Cut <a>.(M[u\<turnstile>n>v]) (x).(N[u\<turnstile>n>v])" using fs1 fs2 a
    apply -
    apply(simp add: trm.inject alpha fresh_atm fresh_prod rename_eqvts)
    apply(simp add: calc_atm)
    apply(simp add: rename_fresh fresh_atm)
    done
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
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  have "(Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N))[b\<turnstile>c>c] = 
                        Cut <a'>.(([(a',a)]\<bullet>M)[b\<turnstile>c>c]) (x').(([(x',x)]\<bullet>N)[b\<turnstile>c>c])"
    using fs1 fs2
    apply -
    apply(rule crename.simps)
    apply(simp add: fresh_left calc_atm)
    apply(simp add: fresh_left calc_atm)
    done
  also have "\<dots> = Cut <a>.(M[b\<turnstile>c>c]) (x).(N[b\<turnstile>c>c])" using fs1 fs2 a
    apply -
    apply(simp add: trm.inject alpha fresh_atm fresh_prod rename_eqvts)
    apply(simp add: calc_atm)
    apply(simp add: rename_fresh fresh_atm)
    done
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
   (simp_all add: calc_atm fresh_atm trm.inject alpha abs_fresh abs_supp fin_supp)

lemma crename_swap:
  shows "a\<sharp>M \<Longrightarrow> [(a,b)]\<bullet>M = M[b\<turnstile>c>a]"
by (nominal_induct M avoiding: a b rule: trm.strong_induct) 
   (simp_all add: calc_atm fresh_atm trm.inject alpha abs_fresh abs_supp fin_supp)

lemma crename_ax:
  assumes a: "M[a\<turnstile>c>b] = Ax x c" "c\<noteq>a" "c\<noteq>b"
  shows "M = Ax x c"
using a
apply(nominal_induct M avoiding: a b x c rule: trm.strong_induct)
apply(simp_all add: trm.inject split: if_splits)
done

lemma nrename_ax:
  assumes a: "M[x\<turnstile>n>y] = Ax z a" "z\<noteq>x" "z\<noteq>y"
  shows "M = Ax z a"
using a
apply(nominal_induct M avoiding: x y z a rule: trm.strong_induct)
apply(simp_all add: trm.inject split: if_splits)
done

text {* substitution functions *}

lemma fresh_perm_coname:
  fixes c::"coname"
  and   pi::"coname prm"
  and   M::"trm"
  assumes a: "c\<sharp>pi" "c\<sharp>M"
  shows "c\<sharp>(pi\<bullet>M)"
using a
apply -
apply(simp add: fresh_left)
apply(simp add: at_prm_fresh[OF at_coname_inst] fresh_list_rev)
done

lemma fresh_perm_name:
  fixes x::"name"
  and   pi::"name prm"
  and   M::"trm"
  assumes a: "x\<sharp>pi" "x\<sharp>M"
  shows "x\<sharp>(pi\<bullet>M)"
using a
apply -
apply(simp add: fresh_left)
apply(simp add: at_prm_fresh[OF at_name_inst] fresh_list_rev)
done

lemma fresh_fun_simp_NotL:
  assumes a: "x'\<sharp>P" "x'\<sharp>M"
  shows "fresh_fun (\<lambda>x'. Cut <c>.P (x').NotL <a>.M x') = Cut <c>.P (x').NotL <a>.M x'"
using a
apply -
apply(rule fresh_fun_app)
apply(rule pt_name_inst)
apply(rule at_name_inst)
apply(finite_guess)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(c,P,a,M)")
apply(erule exE)
apply(rule_tac x="n" in exI)
apply(simp add: fresh_prod abs_fresh)
apply(fresh_guess)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(fresh_guess)
done

lemma fresh_fun_NotL[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>x'. Cut <c>.P (x').NotL <a>.M x')=
             fresh_fun (pi1\<bullet>(\<lambda>x'. Cut <c>.P (x').NotL <a>.M x'))"
  and   "pi2\<bullet>fresh_fun (\<lambda>x'. Cut <c>.P (x').NotL <a>.M x')=
             fresh_fun (pi2\<bullet>(\<lambda>x'. Cut <c>.P (x').NotL <a>.M x'))"
apply -
apply(perm_simp)
apply(generate_fresh "name")
apply(auto simp add: fresh_prod)
apply(simp add: fresh_fun_simp_NotL)
apply(rule sym)
apply(rule trans)
apply(rule fresh_fun_simp_NotL)
apply(rule fresh_perm_name)
apply(assumption)
apply(assumption)
apply(rule fresh_perm_name)
apply(assumption)
apply(assumption)
apply(simp add: at_prm_fresh[OF at_name_inst] swap_simps)
apply(perm_simp)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,pi2\<bullet>P,pi2\<bullet>M,pi2)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_NotL calc_atm)
apply(rule exists_fresh')
apply(simp add: fin_supp)
done

lemma fresh_fun_simp_AndL1:
  assumes a: "z'\<sharp>P" "z'\<sharp>M" "z'\<sharp>x"
  shows "fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL1 (x).M z') = Cut <c>.P (z').AndL1 (x).M z'"
using a
apply -
apply(rule fresh_fun_app)
apply(rule pt_name_inst)
apply(rule at_name_inst)
apply(finite_guess)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(c,P,x,M)")
apply(erule exE)
apply(rule_tac x="n" in exI)
apply(simp add: fresh_prod abs_fresh)
apply(fresh_guess)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(fresh_guess)
done

lemma fresh_fun_AndL1[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL1 (x).M z')=
             fresh_fun (pi1\<bullet>(\<lambda>z'. Cut <c>.P (z').AndL1 (x).M z'))"
  and   "pi2\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL1 (x).M z')=
             fresh_fun (pi2\<bullet>(\<lambda>z'. Cut <c>.P (z').AndL1 (x).M z'))"
apply -
apply(perm_simp)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,x,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>x,pi1)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_AndL1 at_prm_fresh[OF at_name_inst] swap_simps)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(perm_simp)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,x,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>x,pi2)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_AndL1 calc_atm)
apply(rule exists_fresh')
apply(simp add: fin_supp)
done

lemma fresh_fun_simp_AndL2:
  assumes a: "z'\<sharp>P" "z'\<sharp>M" "z'\<sharp>x"
  shows "fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL2 (x).M z') = Cut <c>.P (z').AndL2 (x).M z'"
using a
apply -
apply(rule fresh_fun_app)
apply(rule pt_name_inst)
apply(rule at_name_inst)
apply(finite_guess)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(c,P,x,M)")
apply(erule exE)
apply(rule_tac x="n" in exI)
apply(simp add: fresh_prod abs_fresh)
apply(fresh_guess)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(fresh_guess)
done

lemma fresh_fun_AndL2[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL2 (x).M z')=
             fresh_fun (pi1\<bullet>(\<lambda>z'. Cut <c>.P (z').AndL2 (x).M z'))"
  and   "pi2\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL2 (x).M z')=
             fresh_fun (pi2\<bullet>(\<lambda>z'. Cut <c>.P (z').AndL2 (x).M z'))"
apply -
apply(perm_simp)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,x,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>x,pi1)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_AndL2 at_prm_fresh[OF at_name_inst] swap_simps)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(perm_simp)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,x,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>x,pi2)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_AndL2 calc_atm)
apply(rule exists_fresh')
apply(simp add: fin_supp)
done

lemma fresh_fun_simp_OrL:
  assumes a: "z'\<sharp>P" "z'\<sharp>M" "z'\<sharp>N" "z'\<sharp>u" "z'\<sharp>x"
  shows "fresh_fun (\<lambda>z'. Cut <c>.P (z').OrL (x).M (u).N z') = Cut <c>.P (z').OrL (x).M (u).N z'"
using a
apply -
apply(rule fresh_fun_app)
apply(rule pt_name_inst)
apply(rule at_name_inst)
apply(finite_guess)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(c,P,x,M,u,N)")
apply(erule exE)
apply(rule_tac x="n" in exI)
apply(simp add: fresh_prod abs_fresh)
apply(fresh_guess)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(fresh_guess)
done

lemma fresh_fun_OrL[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').OrL (x).M (u).N z')=
             fresh_fun (pi1\<bullet>(\<lambda>z'. Cut <c>.P (z').OrL (x).M (u).N z'))"
  and   "pi2\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').OrL (x).M (u).N z')=
             fresh_fun (pi2\<bullet>(\<lambda>z'. Cut <c>.P (z').OrL (x).M (u).N z'))"
apply -
apply(perm_simp)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,N,x,u,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>N,pi1\<bullet>x,pi1\<bullet>u,pi1)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_OrL at_prm_fresh[OF at_name_inst] swap_simps)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(perm_simp)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,N,x,u,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>N,pi2\<bullet>x,pi2\<bullet>u,pi2)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_OrL calc_atm)
apply(rule exists_fresh')
apply(simp add: fin_supp)
done

lemma fresh_fun_simp_ImpL:
  assumes a: "z'\<sharp>P" "z'\<sharp>M" "z'\<sharp>N" "z'\<sharp>x"
  shows "fresh_fun (\<lambda>z'. Cut <c>.P (z').ImpL <a>.M (x).N z') = Cut <c>.P (z').ImpL <a>.M (x).N z'"
using a
apply -
apply(rule fresh_fun_app)
apply(rule pt_name_inst)
apply(rule at_name_inst)
apply(finite_guess)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(c,P,x,M,N)")
apply(erule exE)
apply(rule_tac x="n" in exI)
apply(simp add: fresh_prod abs_fresh)
apply(fresh_guess)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(fresh_guess)
done

lemma fresh_fun_ImpL[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').ImpL <a>.M (x).N z')=
             fresh_fun (pi1\<bullet>(\<lambda>z'. Cut <c>.P (z').ImpL <a>.M (x).N z'))"
  and   "pi2\<bullet>fresh_fun (\<lambda>z'. Cut <c>.P (z').ImpL <a>.M (x).N z')=
             fresh_fun (pi2\<bullet>(\<lambda>z'. Cut <c>.P (z').ImpL <a>.M (x).N z'))"
apply -
apply(perm_simp)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,N,x,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>N,pi1\<bullet>x,pi1)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_ImpL at_prm_fresh[OF at_name_inst] swap_simps)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(perm_simp)
apply(subgoal_tac "\<exists>n::name. n\<sharp>(P,M,N,x,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>N,pi2\<bullet>x,pi2)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_ImpL calc_atm)
apply(rule exists_fresh')
apply(simp add: fin_supp)
done

lemma fresh_fun_simp_NotR:
  assumes a: "a'\<sharp>P" "a'\<sharp>M"
  shows "fresh_fun (\<lambda>a'. Cut <a'>.(NotR (y).M a') (x).P) = Cut <a'>.(NotR (y).M a') (x).P"
using a
apply -
apply(rule fresh_fun_app)
apply(rule pt_coname_inst)
apply(rule at_coname_inst)
apply(finite_guess)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(x,P,y,M)")
apply(erule exE)
apply(rule_tac x="n" in exI)
apply(simp add: fresh_prod abs_fresh)
apply(fresh_guess)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(fresh_guess)
done

lemma fresh_fun_NotR[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(NotR (y).M a') (x).P)=
             fresh_fun (pi1\<bullet>(\<lambda>a'. Cut <a'>.(NotR (y).M a') (x).P))"
  and   "pi2\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(NotR (y).M a') (x).P)=
             fresh_fun (pi2\<bullet>(\<lambda>a'. Cut <a'>.(NotR (y).M a') (x).P))"
apply -
apply(perm_simp)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,pi1\<bullet>P,pi1\<bullet>M,pi1)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_NotR calc_atm)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(perm_simp)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,pi2\<bullet>P,pi2\<bullet>M,pi2)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_NotR at_prm_fresh[OF at_coname_inst] swap_simps)
apply(rule exists_fresh')
apply(simp add: fin_supp)
done

lemma fresh_fun_simp_AndR:
  assumes a: "a'\<sharp>P" "a'\<sharp>M" "a'\<sharp>N" "a'\<sharp>b" "a'\<sharp>c"
  shows "fresh_fun (\<lambda>a'. Cut <a'>.(AndR <b>.M <c>.N a') (x).P) = Cut <a'>.(AndR <b>.M <c>.N a') (x).P"
using a
apply -
apply(rule fresh_fun_app)
apply(rule pt_coname_inst)
apply(rule at_coname_inst)
apply(finite_guess)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(x,P,b,M,c,N)")
apply(erule exE)
apply(rule_tac x="n" in exI)
apply(simp add: fresh_prod abs_fresh)
apply(fresh_guess)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(fresh_guess)
done

lemma fresh_fun_AndR[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(AndR <b>.M <c>.N a') (x).P)=
             fresh_fun (pi1\<bullet>(\<lambda>a'. Cut <a'>.(AndR <b>.M <c>.N a') (x).P))"
  and   "pi2\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(AndR <b>.M <c>.N a') (x).P)=
             fresh_fun (pi2\<bullet>(\<lambda>a'. Cut <a'>.(AndR <b>.M <c>.N a') (x).P))"
apply -
apply(perm_simp)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,N,b,c,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>N,pi1\<bullet>b,pi1\<bullet>c,pi1)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_AndR calc_atm)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(perm_simp)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,N,b,c,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>N,pi2\<bullet>b,pi2\<bullet>c,pi2)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_AndR at_prm_fresh[OF at_coname_inst] swap_simps)
apply(rule exists_fresh')
apply(simp add: fin_supp)
done

lemma fresh_fun_simp_OrR1:
  assumes a: "a'\<sharp>P" "a'\<sharp>M" "a'\<sharp>b" 
  shows "fresh_fun (\<lambda>a'. Cut <a'>.(OrR1 <b>.M a') (x).P) = Cut <a'>.(OrR1 <b>.M a') (x).P"
using a
apply -
apply(rule fresh_fun_app)
apply(rule pt_coname_inst)
apply(rule at_coname_inst)
apply(finite_guess)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(x,P,b,M)")
apply(erule exE)
apply(rule_tac x="n" in exI)
apply(simp add: fresh_prod abs_fresh)
apply(fresh_guess)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(fresh_guess)
done

lemma fresh_fun_OrR1[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(OrR1 <b>.M a') (x).P)=
             fresh_fun (pi1\<bullet>(\<lambda>a'. Cut <a'>.(OrR1 <b>.M  a') (x).P))"
  and   "pi2\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(OrR1 <b>.M a') (x).P)=
             fresh_fun (pi2\<bullet>(\<lambda>a'. Cut <a'>.(OrR1 <b>.M a') (x).P))"
apply -
apply(perm_simp)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,b,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>b,pi1)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_OrR1 calc_atm)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(perm_simp)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,b,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>b,pi2)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_OrR1 at_prm_fresh[OF at_coname_inst] swap_simps)
apply(rule exists_fresh')
apply(simp add: fin_supp)
done

lemma fresh_fun_simp_OrR2:
  assumes a: "a'\<sharp>P" "a'\<sharp>M" "a'\<sharp>b" 
  shows "fresh_fun (\<lambda>a'. Cut <a'>.(OrR2 <b>.M a') (x).P) = Cut <a'>.(OrR2 <b>.M a') (x).P"
using a
apply -
apply(rule fresh_fun_app)
apply(rule pt_coname_inst)
apply(rule at_coname_inst)
apply(finite_guess)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(x,P,b,M)")
apply(erule exE)
apply(rule_tac x="n" in exI)
apply(simp add: fresh_prod abs_fresh)
apply(fresh_guess)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(fresh_guess)
done

lemma fresh_fun_OrR2[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(OrR2 <b>.M a') (x).P)=
             fresh_fun (pi1\<bullet>(\<lambda>a'. Cut <a'>.(OrR2 <b>.M  a') (x).P))"
  and   "pi2\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(OrR2 <b>.M a') (x).P)=
             fresh_fun (pi2\<bullet>(\<lambda>a'. Cut <a'>.(OrR2 <b>.M a') (x).P))"
apply -
apply(perm_simp)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,b,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>b,pi1)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_OrR2 calc_atm)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(perm_simp)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,b,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>b,pi2)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_OrR2 at_prm_fresh[OF at_coname_inst] swap_simps)
apply(rule exists_fresh')
apply(simp add: fin_supp)
done

lemma fresh_fun_simp_ImpR:
  assumes a: "a'\<sharp>P" "a'\<sharp>M" "a'\<sharp>b" 
  shows "fresh_fun (\<lambda>a'. Cut <a'>.(ImpR (y).<b>.M a') (x).P) = Cut <a'>.(ImpR (y).<b>.M a') (x).P"
using a
apply -
apply(rule fresh_fun_app)
apply(rule pt_coname_inst)
apply(rule at_coname_inst)
apply(finite_guess)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(x,P,y,b,M)")
apply(erule exE)
apply(rule_tac x="n" in exI)
apply(simp add: fresh_prod abs_fresh)
apply(fresh_guess)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(fresh_guess)
done

lemma fresh_fun_ImpR[eqvt_force]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(ImpR (y).<b>.M a') (x).P)=
             fresh_fun (pi1\<bullet>(\<lambda>a'. Cut <a'>.(ImpR (y).<b>.M  a') (x).P))"
  and   "pi2\<bullet>fresh_fun (\<lambda>a'. Cut <a'>.(ImpR (y).<b>.M a') (x).P)=
             fresh_fun (pi2\<bullet>(\<lambda>a'. Cut <a'>.(ImpR (y).<b>.M a') (x).P))"
apply -
apply(perm_simp)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,b,pi1\<bullet>P,pi1\<bullet>M,pi1\<bullet>b,pi1)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_ImpR calc_atm)
apply(rule exists_fresh')
apply(simp add: fin_supp)
apply(perm_simp)
apply(subgoal_tac "\<exists>n::coname. n\<sharp>(P,M,b,pi2\<bullet>P,pi2\<bullet>M,pi2\<bullet>b,pi2)")
apply(simp add: fresh_prod)
apply(auto)
apply(simp add: fresh_fun_simp_ImpR at_prm_fresh[OF at_coname_inst] swap_simps)
apply(rule exists_fresh')
apply(simp add: fin_supp)
done

nominal_primrec (freshness_context: "(y::name,c::coname,P::trm)")
  substn :: "trm \<Rightarrow> name   \<Rightarrow> coname \<Rightarrow> trm \<Rightarrow> trm" ("_{_:=<_>._}" [100,100,100,100] 100) 
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
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x1,P,y1)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x1,P,y1)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1 abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x1,P,y1)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2 abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x1,P,y1,x3,y2)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x1,P,y1,x3,y2)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x3,P,y1,y2)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::name. x\<sharp>(x3,P,y1,y2)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(fresh_guess)+
done

nominal_primrec (freshness_context: "(d::name,z::coname,P::trm)")
  substc :: "trm \<Rightarrow> coname \<Rightarrow> name   \<Rightarrow> trm \<Rightarrow> trm" ("_{_:=(_)._}" [100,100,100,100] 100)
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
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh abs_supp fs_name1 fs_coname1)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,y1)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,y1,x3,y2)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,y1,x3,y2)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,y1)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1 abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,y1)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2 abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,x2,y1)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR abs_fresh fresh_atm abs_supp)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(rule impI)
apply(subgoal_tac "\<exists>x::coname. x\<sharp>(x1,P,x2,y1)", erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR abs_fresh fresh_atm)
apply(rule exists_fresh', simp add: fin_supp)
apply(simp add: abs_fresh abs_supp)+
apply(fresh_guess add: abs_fresh fresh_prod)+
done

lemma csubst_eqvt[eqvt]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>(M{c:=(x).N}) = (pi1\<bullet>M){(pi1\<bullet>c):=(pi1\<bullet>x).(pi1\<bullet>N)}"
  and   "pi2\<bullet>(M{c:=(x).N}) = (pi2\<bullet>M){(pi2\<bullet>c):=(pi2\<bullet>x).(pi2\<bullet>N)}"
apply(nominal_induct M avoiding: c x N rule: trm.strong_induct)
apply(auto simp add: eq_bij fresh_bij eqvts)
apply(perm_simp)+
done

lemma nsubst_eqvt[eqvt]:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "pi1\<bullet>(M{x:=<c>.N}) = (pi1\<bullet>M){(pi1\<bullet>x):=<(pi1\<bullet>c)>.(pi1\<bullet>N)}"
  and   "pi2\<bullet>(M{x:=<c>.N}) = (pi2\<bullet>M){(pi2\<bullet>x):=<(pi2\<bullet>c)>.(pi2\<bullet>N)}"
apply(nominal_induct M avoiding: c x N rule: trm.strong_induct)
apply(auto simp add: eq_bij fresh_bij eqvts)
apply(perm_simp)+
done

lemma supp_subst1:
  shows "supp (M{y:=<c>.P}) \<subseteq> ((supp M) - {y}) \<union> (supp P)"
apply(nominal_induct M avoiding: y P c rule: trm.strong_induct)
apply(auto)
apply(auto simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)+
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(blast)+
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(blast)+
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(blast)+
done

lemma supp_subst2:
  shows "supp (M{y:=<c>.P}) \<subseteq> supp (M) \<union> ((supp P) - {c})"
apply(nominal_induct M avoiding: y P c rule: trm.strong_induct)
apply(auto)
apply(auto simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)+
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(blast)+
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(blast)+
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(blast)+
done

lemma supp_subst3:
  shows "supp (M{c:=(x).P}) \<subseteq> ((supp M) - {c}) \<union> (supp P)"
apply(nominal_induct M avoiding: x P c rule: trm.strong_induct)
apply(auto)
apply(auto simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)+
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname:=(x).P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname:=(x).P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(blast)+
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(blast)+
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR abs_fresh abs_supp fin_supp fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR abs_fresh abs_supp fin_supp fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR abs_fresh abs_supp fin_supp fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(blast)+
done

lemma supp_subst4:
  shows "supp (M{c:=(x).P}) \<subseteq> (supp M) \<union> ((supp P) - {x})"
apply(nominal_induct M avoiding: x P c rule: trm.strong_induct)
apply(auto)
apply(auto simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)+
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname:=(x).P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname:=(x).P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname:=(x).P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(blast)+
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(blast)+
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR abs_fresh abs_supp fin_supp fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR abs_fresh abs_supp fin_supp fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR abs_fresh abs_supp fin_supp fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(blast)+
done

lemma supp_subst5:
  shows "(supp M - {y}) \<subseteq> supp (M{y:=<c>.P})"
apply(nominal_induct M avoiding: y P c rule: trm.strong_induct)
apply(auto)
apply(auto simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)+
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(blast)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(blast)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(blast)
done

lemma supp_subst6:
  shows "(supp M) \<subseteq> ((supp (M{y:=<c>.P}))::coname set)"
apply(nominal_induct M avoiding: y P c rule: trm.strong_induct)
apply(auto)
apply(auto simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)+
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(blast)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{y:=<c>.P},P,name1,trm2{y:=<c>.P},name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(blast)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm)
apply(blast)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(blast)
done

lemma supp_subst7:
  shows "(supp M - {c}) \<subseteq>  supp (M{c:=(x).P})"
apply(nominal_induct M avoiding: x P c rule: trm.strong_induct)
apply(auto)
apply(auto simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)+
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname:=(x).P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(blast)+
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(blast)+
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR abs_fresh abs_supp fin_supp fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(blast)
done

lemma supp_subst8:
  shows "(supp M) \<subseteq> ((supp (M{c:=(x).P}))::name set)"
apply(nominal_induct M avoiding: x P c rule: trm.strong_induct)
apply(auto)
apply(auto simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)+
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname:=(x).P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(blast)+
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2 abs_fresh fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(blast)
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR abs_fresh abs_supp fin_supp fresh_atm)
apply(simp add: fresh_def abs_supp trm.supp supp_atm fin_supp)
apply(blast)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(blast)+
done

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
apply -
apply(insert subst_supp)
apply(simp_all add: fresh_def supp_prod)
apply(blast)+ 
done

lemma forget:
  shows "x\<sharp>M \<Longrightarrow> M{x:=<c>.P} = M"
  and   "c\<sharp>M \<Longrightarrow> M{c:=(x).P} = M"
apply(nominal_induct M avoiding: x c P rule: trm.strong_induct)
apply(auto simp add: fresh_atm abs_fresh abs_supp fin_supp)
done

lemma substc_rename1:
  assumes a: "c\<sharp>(M,a)"
  shows "M{a:=(x).N} = ([(c,a)]\<bullet>M){c:=(x).N}"
using a
proof(nominal_induct M avoiding: c a x N rule: trm.strong_induct)
  case (Ax z d)
  then show ?case by (auto simp add: fresh_prod fresh_atm calc_atm trm.inject alpha)
next
  case NotL
  then show ?case by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod)
next
  case (NotR y M d)
  then show ?case 
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(N,M{d:=(x).N},([(c,d)]\<bullet>M){c:=(x).N})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_NotR)
    apply(simp add: trm.inject alpha)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (AndR c1 M c2 M' c3)
  then show ?case
    apply(simp)
    apply(auto)
    apply(simp add: fresh_prod calc_atm fresh_atm abs_fresh)
    apply(simp add: fresh_prod calc_atm fresh_atm abs_fresh fresh_left)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(N,M{c3:=(x).N},
                  M'{c3:=(x).N},c1,c2,c3,([(c,c3)]\<bullet>M){c:=(x).N},([(c,c3)]\<bullet>M'){c:=(x).N})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndR)
    apply (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh subst_fresh)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    apply(simp add: fresh_prod calc_atm fresh_atm abs_fresh fresh_left)
    apply(simp add: fresh_prod calc_atm fresh_atm abs_fresh fresh_left)
    apply(auto simp add: trm.inject alpha)
    done
next
  case AndL1
  then show ?case by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod)
next
  case AndL2
  then show ?case by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod)
next
  case (OrR1 d M e)
  then show ?case 
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(N,M{e:=(x).N},([(c,e)]\<bullet>M){c:=(x).N},d,e)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrR1)
    apply(simp add: trm.inject alpha)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (OrR2 d M e)
  then show ?case 
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(N,M{e:=(x).N},([(c,e)]\<bullet>M){c:=(x).N},d,e)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrR2)
    apply(simp add: trm.inject alpha)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (OrL x1 M x2 M' x3)
  then show ?case
    by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
next 
  case ImpL
  then show ?case
    by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
next
  case (ImpR y d M e)
  then show ?case
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(N,M{e:=(x).N},([(c,e)]\<bullet>M){c:=(x).N},d,e)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_ImpR)
    apply(simp add: trm.inject alpha)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (Cut d M y M')
  then show ?case
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
    apply(simp add: calc_atm)
    done
qed

lemma substc_rename2:
  assumes a: "y\<sharp>(N,x)"
  shows "M{a:=(x).N} = M{a:=(y).([(y,x)]\<bullet>N)}"
using a
proof(nominal_induct M avoiding: a x y N rule: trm.strong_induct)
  case (Ax z d)
  then show ?case 
    by (auto simp add: fresh_prod fresh_atm calc_atm trm.inject alpha perm_swap fresh_left)
next
  case NotL
  then show ?case 
    by (auto simp add: fresh_prod fresh_atm calc_atm trm.inject alpha perm_swap fresh_left)
next
  case (NotR y M d)
  then show ?case
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(N,M{d:=(y).([(y,x)]\<bullet>N)},[(y,x)]\<bullet>N)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_NotR)
    apply(simp add: trm.inject alpha perm_swap fresh_left calc_atm)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (AndR c1 M c2 M' c3)
  then show ?case
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac 
       "\<exists>a'::coname. a'\<sharp>(N,M{c3:=(y).([(y,x)]\<bullet>N)},M'{c3:=(y).([(y,x)]\<bullet>N)},[(y,x)]\<bullet>N,c1,c2,c3)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndR)
    apply (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh subst_fresh perm_swap fresh_left)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case AndL1
  then show ?case by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
next
  case AndL2
  then show ?case by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
next
  case (OrR1 d M e)
  then show ?case 
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(N,M{e:=(y).([(y,x)]\<bullet>N)},[(y,x)]\<bullet>N,d,e)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrR1)
    apply(simp add: trm.inject alpha perm_swap fresh_left calc_atm)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (OrR2 d M e)
  then show ?case
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(N,M{e:=(y).([(y,x)]\<bullet>N)},[(y,x)]\<bullet>N,d,e)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrR2)
    apply(simp add: trm.inject alpha perm_swap fresh_left calc_atm)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (OrL x1 M x2 M' x3)
  then show ?case
    by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
next 
  case ImpL
  then show ?case
    by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
next
  case (ImpR y d M e)
  then show ?case
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(N,M{e:=(y).([(y,x)]\<bullet>N)},[(y,x)]\<bullet>N,d,e)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_ImpR)
    apply(simp add: trm.inject alpha perm_swap fresh_left calc_atm)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (Cut d M y M')
  then show ?case
    by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left perm_swap)
qed

lemma substn_rename3:
  assumes a: "y\<sharp>(M,x)"
  shows "M{x:=<a>.N} = ([(y,x)]\<bullet>M){y:=<a>.N}"
using a
proof(nominal_induct M avoiding: a x y N rule: trm.strong_induct)
  case (Ax z d)
  then show ?case by (auto simp add: fresh_prod fresh_atm calc_atm trm.inject alpha)
next
  case NotR
  then show ?case by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod)
next
  case (NotL d M z)
  then show ?case 
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod)
    apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(N,M{x:=<a>.N},([(y,x)]\<bullet>M){y:=<a>.N})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_NotL)
    apply(simp add: trm.inject alpha)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (AndR c1 M c2 M' c3)
  then show ?case
    by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
next
  case OrR1
  then show ?case by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod)
next
  case OrR2
  then show ?case by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod)
next
  case (AndL1 u M v)
  then show ?case 
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod)
    apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(N,M{x:=<a>.N},([(y,x)]\<bullet>M){y:=<a>.N},u,v)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL1)
    apply(simp add: trm.inject alpha)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (AndL2 u M v)
  then show ?case 
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod)
    apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(N,M{x:=<a>.N},([(y,x)]\<bullet>M){y:=<a>.N},u,v)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL2)
    apply(simp add: trm.inject alpha)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (OrL x1 M x2 M' x3)
  then show ?case
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac 
    "\<exists>a'::name. a'\<sharp>(N,M{x:=<a>.N},M'{x:=<a>.N},([(y,x)]\<bullet>M){y:=<a>.N},([(y,x)]\<bullet>M'){y:=<a>.N},x1,x2)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrL)
    apply(simp add: trm.inject alpha)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next 
  case ImpR
  then show ?case
  by(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_left abs_supp fin_supp fresh_prod)
next
  case (ImpL d M v M' u)
  then show ?case
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac 
    "\<exists>a'::name. a'\<sharp>(N,M{u:=<a>.N},M'{u:=<a>.N},([(y,u)]\<bullet>M){y:=<a>.N},([(y,u)]\<bullet>M'){y:=<a>.N},d,v)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_ImpL)
    apply(simp add: trm.inject alpha)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (Cut d M y M')
  then show ?case
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
    apply(simp add: calc_atm)
    done
qed

lemma substn_rename4:
  assumes a: "c\<sharp>(N,a)"
  shows "M{x:=<a>.N} = M{x:=<c>.([(c,a)]\<bullet>N)}"
using a
proof(nominal_induct M avoiding: x c a N rule: trm.strong_induct)
  case (Ax z d)
  then show ?case 
    by (auto simp add: fresh_prod fresh_atm calc_atm trm.inject alpha perm_swap fresh_left)
next
  case NotR
  then show ?case 
    by (auto simp add: fresh_prod fresh_atm calc_atm trm.inject alpha perm_swap fresh_left)
next
  case (NotL d M y)
  then show ?case
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(N,M{x:=<c>.([(c,a)]\<bullet>N)},[(c,a)]\<bullet>N)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_NotL)
    apply(simp add: trm.inject alpha perm_swap fresh_left calc_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (OrL x1 M x2 M' x3)
  then show ?case
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac 
       "\<exists>a'::name. a'\<sharp>(N,M{x:=<c>.([(c,a)]\<bullet>N)},M'{x:=<c>.([(c,a)]\<bullet>N)},[(c,a)]\<bullet>N,x1,x2,x3)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrL)
    apply (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh subst_fresh perm_swap fresh_left)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case OrR1
  then show ?case by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
next
  case OrR2
  then show ?case by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
next
  case (AndL1 u M v)
  then show ?case 
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(N,M{x:=<c>.([(c,a)]\<bullet>N)},[(c,a)]\<bullet>N,u,v)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL1)
    apply(simp add: trm.inject alpha perm_swap fresh_left calc_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (AndL2 u M v)
  then show ?case 
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(N,M{x:=<c>.([(c,a)]\<bullet>N)},[(c,a)]\<bullet>N,u,v)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL2)
    apply(simp add: trm.inject alpha perm_swap fresh_left calc_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (AndR c1 M c2 M' c3)
  then show ?case
    by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
next 
  case ImpR
  then show ?case
    by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
next
  case (ImpL d M y M' u)
  then show ?case
    apply(auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left)
    apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(N,M{u:=<c>.([(c,a)]\<bullet>N)},M'{u:=<c>.([(c,a)]\<bullet>N)},[(c,a)]\<bullet>N,y,u)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_ImpL)
    apply(simp add: trm.inject alpha perm_swap fresh_left calc_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (Cut d M y M')
  then show ?case
    by (auto simp add: calc_atm trm.inject alpha fresh_atm abs_fresh fresh_prod fresh_left perm_swap)
qed

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
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  have eq2: "(M=Ax y a) = (([(a',a)]\<bullet>M)=Ax y a')"
    apply(auto simp add: calc_atm)
    apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
    apply(simp add: calc_atm)
    done
  have "(Cut <a>.M (x).N){y:=<c>.P} = (Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N)){y:=<c>.P}" 
    using eq1 by simp
  also have "\<dots> = (if ([(a',a)]\<bullet>M)=Ax y a' then Cut <c>.P (x').(([(x',x)]\<bullet>N){y:=<c>.P}) 
                              else Cut <a'>.(([(a',a)]\<bullet>M){y:=<c>.P}) (x').(([(x',x)]\<bullet>N){y:=<c>.P}))" 
    using fs1 fs2 by (auto simp add: fresh_prod fresh_left calc_atm fresh_atm)
  also have "\<dots> =(if M=Ax y a then Cut <c>.P (x).(N{y:=<c>.P}) else Cut <a>.(M{y:=<c>.P}) (x).(N{y:=<c>.P}))"
    using fs1 fs2 a
    apply -
    apply(simp only: eq2[symmetric])
    apply(auto simp add: trm.inject)
    apply(simp_all add: alpha fresh_atm fresh_prod subst_fresh)
    apply(simp_all add: eqvts perm_fresh_fresh calc_atm)
    apply(auto)
    apply(rule subst_rename)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: abs_fresh)
    apply(simp add: perm_fresh_fresh)
    done
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
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  have eq2: "(N=Ax x c) = (([(x',x)]\<bullet>N)=Ax x' c)"
    apply(auto simp add: calc_atm)
    apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
    apply(simp add: calc_atm)
    done
  have "(Cut <a>.M (x).N){c:=(y).P} = (Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N)){c:=(y).P}" 
    using eq1 by simp
  also have "\<dots> = (if ([(x',x)]\<bullet>N)=Ax x' c then  Cut <a'>.(([(a',a)]\<bullet>M){c:=(y).P}) (y).P
                              else Cut <a'>.(([(a',a)]\<bullet>M){c:=(y).P}) (x').(([(x',x)]\<bullet>N){c:=(y).P}))" 
    using fs1 fs2  by (simp add: fresh_prod fresh_left calc_atm fresh_atm trm.inject)
  also have "\<dots> =(if N=Ax x c then Cut <a>.(M{c:=(y).P}) (y).P else Cut <a>.(M{c:=(y).P}) (x).(N{c:=(y).P}))"
    using fs1 fs2 a
    apply -
    apply(simp only: eq2[symmetric])
    apply(auto simp add: trm.inject)
    apply(simp_all add: alpha fresh_atm fresh_prod subst_fresh)
    apply(simp_all add: eqvts perm_fresh_fresh calc_atm)
    apply(auto)
    apply(rule subst_rename)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: abs_fresh)
    apply(simp add: perm_fresh_fresh)
    done
  finally show ?thesis by simp
qed

lemma better_Cut_substn':
  assumes a: "a\<sharp>[c].P" "y\<sharp>(N,x)" "M\<noteq>Ax y a"
  shows "(Cut <a>.M (x).N){y:=<c>.P} = Cut <a>.(M{y:=<c>.P}) (x).N"
using a
apply -
apply(generate_fresh "name")
apply(subgoal_tac "Cut <a>.M (x).N = Cut <a>.M (ca).([(ca,x)]\<bullet>N)")
apply(simp)
apply(subgoal_tac"y\<sharp>([(ca,x)]\<bullet>N)")
apply(simp add: forget)
apply(simp add: trm.inject)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(simp add: trm.inject)
apply(rule sym)
apply(simp add: alpha fresh_prod fresh_atm)
done

lemma better_NotR_substc:
  assumes a: "d\<sharp>M"
  shows "(NotR (x).M d){d:=(z).P} = fresh_fun (\<lambda>a'. Cut <a'>.NotR (x).M a' (z).P)"
using a
apply -
apply(generate_fresh "name")
apply(subgoal_tac "NotR (x).M d = NotR (c).([(c,x)]\<bullet>M) d")
apply(auto simp add: fresh_left calc_atm forget)
apply(generate_fresh "coname")
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm)
apply(perm_simp add: trm.inject alpha fresh_prod fresh_atm fresh_left, auto)
done

lemma better_NotL_substn:
  assumes a: "y\<sharp>M"
  shows "(NotL <a>.M y){y:=<c>.P} = fresh_fun (\<lambda>x'. Cut <c>.P (x').NotL <a>.M x')"
using a
apply -
apply(generate_fresh "coname")
apply(subgoal_tac "NotL <a>.M y = NotL <ca>.([(ca,a)]\<bullet>M) y")
apply(auto simp add: fresh_left calc_atm forget)
apply(generate_fresh "name")
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm)
apply(perm_simp add: trm.inject alpha fresh_prod fresh_atm fresh_left, auto)
done

lemma better_AndL1_substn:
  assumes a: "y\<sharp>[x].M"
  shows "(AndL1 (x).M y){y:=<c>.P} = fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL1 (x).M z')"
using a
apply -
apply(generate_fresh "name")
apply(subgoal_tac "AndL1 (x).M y = AndL1 (ca).([(ca,x)]\<bullet>M) y")
apply(auto simp add: fresh_left calc_atm forget abs_fresh)[1]
apply(generate_fresh "name")
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm)
apply(rule forget)
apply(simp add: fresh_left calc_atm)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm)
apply(rule forget)
apply(simp add: fresh_left calc_atm)
apply(perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)
done

lemma better_AndL2_substn:
  assumes a: "y\<sharp>[x].M"
  shows "(AndL2 (x).M y){y:=<c>.P} = fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL2 (x).M z')"
using a
apply -
apply(generate_fresh "name")
apply(subgoal_tac "AndL2 (x).M y = AndL2 (ca).([(ca,x)]\<bullet>M) y")
apply(auto simp add: fresh_left calc_atm forget abs_fresh)[1]
apply(generate_fresh "name")
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm)
apply(rule forget)
apply(simp add: fresh_left calc_atm)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm)
apply(rule forget)
apply(simp add: fresh_left calc_atm)
apply(perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)
done

lemma better_AndR_substc:
  assumes a: "c\<sharp>([a].M,[b].N)"
  shows "(AndR <a>.M <b>.N c){c:=(z).P} = fresh_fun (\<lambda>a'. Cut <a'>.(AndR <a>.M <b>.N a') (z).P)"
using a
apply -
apply(generate_fresh "coname")
apply(generate_fresh "coname")
apply(subgoal_tac "AndR <a>.M <b>.N c = AndR <ca>.([(ca,a)]\<bullet>M) <caa>.([(caa,b)]\<bullet>N) c")
apply(auto simp add: fresh_left calc_atm forget abs_fresh)[1]
apply(rule trans)
apply(rule substc.simps)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(auto simp add: fresh_prod fresh_atm)[1]
apply(simp)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm)
apply(rule conjI)
apply(rule forget)
apply(auto simp add: fresh_left calc_atm abs_fresh)[1]
apply(rule forget)
apply(auto simp add: fresh_left calc_atm abs_fresh)[1]
apply(perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)
done

lemma better_OrL_substn:
  assumes a: "x\<sharp>([y].M,[z].N)"
  shows "(OrL (y).M (z).N x){x:=<c>.P} = fresh_fun (\<lambda>z'. Cut <c>.P (z').OrL (y).M (z).N z')"
using a
apply -
apply(generate_fresh "name")
apply(generate_fresh "name")
apply(subgoal_tac "OrL (y).M (z).N x = OrL (ca).([(ca,y)]\<bullet>M) (caa).([(caa,z)]\<bullet>N) x")
apply(auto simp add: fresh_left calc_atm forget abs_fresh)[1]
apply(rule trans)
apply(rule substn.simps)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(auto simp add: fresh_prod fresh_atm)[1]
apply(simp)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm)
apply(rule conjI)
apply(rule forget)
apply(auto simp add: fresh_left calc_atm abs_fresh)[1]
apply(rule forget)
apply(auto simp add: fresh_left calc_atm abs_fresh)[1]
apply(perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)
done

lemma better_OrR1_substc:
  assumes a: "d\<sharp>[a].M"
  shows "(OrR1 <a>.M d){d:=(z).P} = fresh_fun (\<lambda>a'. Cut <a'>.OrR1 <a>.M a' (z).P)"
using a
apply -
apply(generate_fresh "coname")
apply(subgoal_tac "OrR1 <a>.M d = OrR1 <c>.([(c,a)]\<bullet>M) d")
apply(auto simp add: fresh_left calc_atm forget abs_fresh)[1]
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm)
apply(rule forget)
apply(simp add: fresh_left calc_atm)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm)
apply(rule forget)
apply(simp add: fresh_left calc_atm)
apply(perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)
done

lemma better_OrR2_substc:
  assumes a: "d\<sharp>[a].M"
  shows "(OrR2 <a>.M d){d:=(z).P} = fresh_fun (\<lambda>a'. Cut <a'>.OrR2 <a>.M a' (z).P)"
using a
apply -
apply(generate_fresh "coname")
apply(subgoal_tac "OrR2 <a>.M d = OrR2 <c>.([(c,a)]\<bullet>M) d")
apply(auto simp add: fresh_left calc_atm forget abs_fresh)[1]
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm)
apply(rule forget)
apply(simp add: fresh_left calc_atm)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm)
apply(rule forget)
apply(simp add: fresh_left calc_atm)
apply(perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)
done

lemma better_ImpR_substc:
  assumes a: "d\<sharp>[a].M"
  shows "(ImpR (x).<a>.M d){d:=(z).P} = fresh_fun (\<lambda>a'. Cut <a'>.ImpR (x).<a>.M a' (z).P)"
using a
apply -
apply(generate_fresh "coname")
apply(generate_fresh "name")
apply(subgoal_tac "ImpR (x).<a>.M d = ImpR (ca).<c>.([(c,a)]\<bullet>[(ca,x)]\<bullet>M) d")
apply(auto simp add: fresh_left calc_atm forget abs_fresh)[1]
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm abs_perm abs_fresh fresh_left calc_atm)
apply(rule forget)
apply(simp add: fresh_left calc_atm)
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm abs_perm fresh_left calc_atm abs_fresh)
apply(rule forget)
apply(simp add: fresh_left calc_atm)
apply(rule sym)
apply(perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm abs_fresh abs_perm)
done

lemma better_ImpL_substn:
  assumes a: "y\<sharp>(M,[x].N)"
  shows "(ImpL <a>.M (x).N y){y:=<c>.P} = fresh_fun (\<lambda>z'. Cut <c>.P (z').ImpL <a>.M (x).N z')"
using a
apply -
apply(generate_fresh "coname")
apply(generate_fresh "name")
apply(subgoal_tac "ImpL <a>.M (x).N y = ImpL <ca>.([(ca,a)]\<bullet>M) (caa).([(caa,x)]\<bullet>N) y")
apply(auto simp add: fresh_left calc_atm forget abs_fresh)[1]
apply(rule_tac f="fresh_fun" in arg_cong)
apply(simp add:  fun_eq_iff)
apply(rule allI)
apply(simp add: trm.inject alpha fresh_prod fresh_atm abs_perm abs_fresh fresh_left calc_atm)
apply(rule forget)
apply(simp add: fresh_left calc_atm)
apply(auto)[1]
apply(rule sym)
apply(perm_simp add: trm.inject alpha fresh_left calc_atm fresh_prod fresh_atm abs_fresh abs_perm)
done

lemma freshn_after_substc:
  fixes x::"name"
  assumes a: "x\<sharp>M{c:=(y).P}"
  shows "x\<sharp>M"
using a supp_subst8
apply(simp add: fresh_def)
apply(blast)
done

lemma freshn_after_substn:
  fixes x::"name"
  assumes a: "x\<sharp>M{y:=<c>.P}" "x\<noteq>y"
  shows "x\<sharp>M"
using a
using a supp_subst5
apply(simp add: fresh_def)
apply(blast)
done

lemma freshc_after_substc:
  fixes a::"coname"
  assumes a: "a\<sharp>M{c:=(y).P}" "a\<noteq>c"
  shows "a\<sharp>M"
using a supp_subst7
apply(simp add: fresh_def)
apply(blast)
done

lemma freshc_after_substn:
  fixes a::"coname"
  assumes a: "a\<sharp>M{y:=<c>.P}" 
  shows "a\<sharp>M"
using a supp_subst6
apply(simp add: fresh_def)
apply(blast)
done

lemma substn_crename_comm:
  assumes a: "c\<noteq>a" "c\<noteq>b"
  shows "M{x:=<c>.P}[a\<turnstile>c>b] = M[a\<turnstile>c>b]{x:=<c>.(P[a\<turnstile>c>b])}"
using a
apply(nominal_induct M avoiding: x c P a b rule: trm.strong_induct)
apply(auto simp add: subst_fresh rename_fresh trm.inject)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,x,c)")
apply(erule exE)
apply(subgoal_tac "Cut <c>.P (x).Ax x a = Cut <c>.P (x').Ax x' a")
apply(simp)
apply(rule trans)
apply(rule crename.simps)
apply(simp add: fresh_prod fresh_atm)
apply(simp)
apply(simp add: trm.inject)
apply(simp add: alpha trm.inject calc_atm fresh_atm)
apply(simp add: trm.inject)
apply(simp add: alpha trm.inject calc_atm fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm)
apply(simp)
apply(simp add: crename_id)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(auto simp add: fresh_atm)[1]
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm)
apply(auto simp add: fresh_atm)[1]
apply(drule crename_ax)
apply(simp add: fresh_atm)
apply(simp add: fresh_atm)
apply(simp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<c>.P},P,P[a\<turnstile>c>b],x,trm[a\<turnstile>c>b]{x:=<c>.P[a\<turnstile>c>b]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<c>.P},P,P[a\<turnstile>c>b],name1,trm[a\<turnstile>c>b]{x:=<c>.P[a\<turnstile>c>b]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<c>.P},P,P[a\<turnstile>c>b],name1,trm[a\<turnstile>c>b]{x:=<c>.P[a\<turnstile>c>b]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{x:=<c>.P},trm2{x:=<c>.P},P,P[a\<turnstile>c>b],name1,name2,
                                  trm1[a\<turnstile>c>b]{x:=<c>.P[a\<turnstile>c>b]},trm2[a\<turnstile>c>b]{x:=<c>.P[a\<turnstile>c>b]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh subst_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},trm2{name2:=<c>.P},P,P[a\<turnstile>c>b],name1,
                                  trm1[a\<turnstile>c>b]{name2:=<c>.P[a\<turnstile>c>b]},trm2[a\<turnstile>c>b]{name2:=<c>.P[a\<turnstile>c>b]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh subst_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
done

lemma substc_crename_comm:
  assumes a: "c\<noteq>a" "c\<noteq>b"
  shows "M{c:=(x).P}[a\<turnstile>c>b] = M[a\<turnstile>c>b]{c:=(x).(P[a\<turnstile>c>b])}"
using a
apply(nominal_induct M avoiding: x c P a b rule: trm.strong_induct)
apply(auto simp add: subst_fresh rename_fresh trm.inject)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(drule crename_ax)
apply(simp add: fresh_atm)
apply(simp add: fresh_atm)
apply(simp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(a,b,trm{coname:=(x).P},P,P[a\<turnstile>c>b],x,trm[a\<turnstile>c>b]{coname:=(x).P[a\<turnstile>c>b]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(coname1,coname2,a,b,trm1{coname3:=(x).P},trm2{coname3:=(x).P},
                   P,P[a\<turnstile>c>b],x,trm1[a\<turnstile>c>b]{coname3:=(x).P[a\<turnstile>c>b]},trm2[a\<turnstile>c>b]{coname3:=(x).P[a\<turnstile>c>b]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh subst_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(coname1,trm{coname2:=(x).P},P,P[a\<turnstile>c>b],a,b,
                         trm[a\<turnstile>c>b]{coname2:=(x).P[a\<turnstile>c>b]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(coname1,trm{coname2:=(x).P},P,P[a\<turnstile>c>b],a,b,
                         trm[a\<turnstile>c>b]{coname2:=(x).P[a\<turnstile>c>b]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(coname1,trm{coname2:=(x).P},P,P[a\<turnstile>c>b],a,b,
                         trm[a\<turnstile>c>b]{coname2:=(x).P[a\<turnstile>c>b]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR)
apply(rule trans)
apply(rule better_crename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
done

lemma substn_nrename_comm:
  assumes a: "x\<noteq>y" "x\<noteq>z"
  shows "M{x:=<c>.P}[y\<turnstile>n>z] = M[y\<turnstile>n>z]{x:=<c>.(P[y\<turnstile>n>z])}"
using a
apply(nominal_induct M avoiding: x c P y z rule: trm.strong_induct)
apply(auto simp add: subst_fresh rename_fresh trm.inject)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_prod fresh_atm)
apply(simp add: trm.inject)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm)
apply(simp)
apply(drule nrename_ax)
apply(simp add: fresh_atm)
apply(simp add: fresh_atm)
apply(simp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(y,z,trm{x:=<c>.P},P,P[y\<turnstile>n>z],x,trm[y\<turnstile>n>z]{x:=<c>.P[y\<turnstile>n>z]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<c>.P},P,P[y\<turnstile>n>z],name1,trm[y\<turnstile>n>z]{x:=<c>.P[y\<turnstile>n>z]},y,z)")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(y,z,trm{x:=<c>.P},P,P[y\<turnstile>n>z],name1,trm[y\<turnstile>n>z]{x:=<c>.P[y\<turnstile>n>z]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{x:=<c>.P},trm2{x:=<c>.P},P,P[y\<turnstile>n>z],name1,name2,y,z,
                                  trm1[y\<turnstile>n>z]{x:=<c>.P[y\<turnstile>n>z]},trm2[y\<turnstile>n>z]{x:=<c>.P[y\<turnstile>n>z]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh subst_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},trm2{name2:=<c>.P},P,P[y\<turnstile>n>z],y,z,name1,
                                  trm1[y\<turnstile>n>z]{name2:=<c>.P[y\<turnstile>n>z]},trm2[y\<turnstile>n>z]{name2:=<c>.P[y\<turnstile>n>z]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh subst_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
done

lemma substc_nrename_comm:
  assumes a: "x\<noteq>y" "x\<noteq>z"
  shows "M{c:=(x).P}[y\<turnstile>n>z] = M[y\<turnstile>n>z]{c:=(x).(P[y\<turnstile>n>z])}"
using a
apply(nominal_induct M avoiding: x c P y z rule: trm.strong_induct)
apply(auto simp add: subst_fresh rename_fresh trm.inject)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(drule nrename_ax)
apply(simp add: fresh_atm)
apply(simp add: fresh_atm)
apply(simp)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(drule nrename_ax)
apply(simp add: fresh_atm)
apply(simp add: fresh_atm)
apply(simp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(y,z,trm{coname:=(x).P},P,P[y\<turnstile>n>z],x,trm[y\<turnstile>n>z]{coname:=(x).P[y\<turnstile>n>z]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(coname1,coname2,y,z,trm1{coname3:=(x).P},trm2{coname3:=(x).P},
                   P,P[y\<turnstile>n>z],x,trm1[y\<turnstile>n>z]{coname3:=(x).P[y\<turnstile>n>z]},trm2[y\<turnstile>n>z]{coname3:=(x).P[y\<turnstile>n>z]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh subst_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(coname1,trm{coname2:=(x).P},P,P[y\<turnstile>n>z],y,z,
                         trm[y\<turnstile>n>z]{coname2:=(x).P[y\<turnstile>n>z]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(coname1,trm{coname2:=(x).P},P,P[y\<turnstile>n>z],y,z,
                         trm[y\<turnstile>n>z]{coname2:=(x).P[y\<turnstile>n>z]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(coname1,trm{coname2:=(x).P},P,P[y\<turnstile>n>z],y,z,
                         trm[y\<turnstile>n>z]{coname2:=(x).P[y\<turnstile>n>z]})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR)
apply(rule trans)
apply(rule better_nrename_Cut)
apply(simp add: fresh_atm fresh_prod)
apply(simp add: rename_fresh fresh_atm)
apply(rule exists_fresh')
apply(rule fin_supp)
done

lemma substn_crename_comm':
  assumes a: "a\<noteq>c" "a\<sharp>P"
  shows "M{x:=<c>.P}[a\<turnstile>c>b] = M[a\<turnstile>c>b]{x:=<c>.P}"
using a
proof -
  assume a1: "a\<noteq>c"
  assume a2: "a\<sharp>P"
  obtain c'::"coname" where fs2: "c'\<sharp>(c,P,a,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  have eq: "M{x:=<c>.P} = M{x:=<c'>.([(c',c)]\<bullet>P)}"
    using fs2
    apply -
    apply(rule subst_rename)
    apply(simp)
    done
   have eq': "M[a\<turnstile>c>b]{x:=<c>.P} = M[a\<turnstile>c>b]{x:=<c'>.([(c',c)]\<bullet>P)}"
    using fs2
    apply -
    apply(rule subst_rename)
    apply(simp)
    done
  have eq2: "([(c',c)]\<bullet>P)[a\<turnstile>c>b] = ([(c',c)]\<bullet>P)" using fs2 a2 a1
    apply -
    apply(rule rename_fresh)
    apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
    done
  have "M{x:=<c>.P}[a\<turnstile>c>b] = M{x:=<c'>.([(c',c)]\<bullet>P)}[a\<turnstile>c>b]" using eq by simp
  also have "\<dots> = M[a\<turnstile>c>b]{x:=<c'>.(([(c',c)]\<bullet>P)[a\<turnstile>c>b])}"
    using fs2
    apply -
    apply(rule substn_crename_comm)
    apply(simp_all add: fresh_prod fresh_atm)
    done
  also have "\<dots> = M[a\<turnstile>c>b]{x:=<c'>.(([(c',c)]\<bullet>P))}" using eq2 by simp
  also have "\<dots> = M[a\<turnstile>c>b]{x:=<c>.P}" using eq' by simp 
  finally show ?thesis by simp
qed

lemma substc_crename_comm':
  assumes a: "c\<noteq>a" "c\<noteq>b" "a\<sharp>P"
  shows "M{c:=(x).P}[a\<turnstile>c>b] = M[a\<turnstile>c>b]{c:=(x).P}"
using a
proof -
  assume a1: "c\<noteq>a"
  assume a1': "c\<noteq>b"
  assume a2: "a\<sharp>P"
  obtain c'::"coname" where fs2: "c'\<sharp>(c,M,a,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  have eq: "M{c:=(x).P} = ([(c',c)]\<bullet>M){c':=(x).P}"
    using fs2
    apply -
    apply(rule subst_rename)
    apply(simp)
    done
   have eq': "([(c',c)]\<bullet>(M[a\<turnstile>c>b])){c':=(x).P} = M[a\<turnstile>c>b]{c:=(x).P}"
    using fs2
    apply -
    apply(rule subst_rename[symmetric])
    apply(simp add: rename_fresh)
    done
  have eq2: "([(c',c)]\<bullet>M)[a\<turnstile>c>b] = ([(c',c)]\<bullet>(M[a\<turnstile>c>b]))" using fs2 a2 a1 a1'
    apply -
    apply(simp add: rename_eqvts)
    apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
    done
  have "M{c:=(x).P}[a\<turnstile>c>b] = ([(c',c)]\<bullet>M){c':=(x).P}[a\<turnstile>c>b]" using eq by simp
  also have "\<dots> = ([(c',c)]\<bullet>M)[a\<turnstile>c>b]{c':=(x).P[a\<turnstile>c>b]}"
    using fs2
    apply -
    apply(rule substc_crename_comm)
    apply(simp_all add: fresh_prod fresh_atm)
    done
  also have "\<dots> = ([(c',c)]\<bullet>(M[a\<turnstile>c>b])){c':=(x).P[a\<turnstile>c>b]}" using eq2 by simp
  also have "\<dots> = ([(c',c)]\<bullet>(M[a\<turnstile>c>b])){c':=(x).P}" using a2 by (simp add: rename_fresh)
  also have "\<dots> = M[a\<turnstile>c>b]{c:=(x).P}" using eq' by simp
  finally show ?thesis by simp
qed

lemma substn_nrename_comm':
  assumes a: "x\<noteq>y" "x\<noteq>z" "y\<sharp>P"
  shows "M{x:=<c>.P}[y\<turnstile>n>z] = M[y\<turnstile>n>z]{x:=<c>.P}"
using a
proof -
  assume a1: "x\<noteq>y"
  assume a1': "x\<noteq>z"
  assume a2: "y\<sharp>P"
  obtain x'::"name" where fs2: "x'\<sharp>(x,M,y,z)" by (rule exists_fresh(1), rule fin_supp, blast)
  have eq: "M{x:=<c>.P} = ([(x',x)]\<bullet>M){x':=<c>.P}"
    using fs2
    apply -
    apply(rule subst_rename)
    apply(simp)
    done
   have eq': "([(x',x)]\<bullet>(M[y\<turnstile>n>z])){x':=<c>.P} = M[y\<turnstile>n>z]{x:=<c>.P}"
    using fs2
    apply -
    apply(rule subst_rename[symmetric])
    apply(simp add: rename_fresh)
    done
  have eq2: "([(x',x)]\<bullet>M)[y\<turnstile>n>z] = ([(x',x)]\<bullet>(M[y\<turnstile>n>z]))" using fs2 a2 a1 a1'
    apply -
    apply(simp add: rename_eqvts)
    apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
    done
  have "M{x:=<c>.P}[y\<turnstile>n>z] = ([(x',x)]\<bullet>M){x':=<c>.P}[y\<turnstile>n>z]" using eq by simp
  also have "\<dots> = ([(x',x)]\<bullet>M)[y\<turnstile>n>z]{x':=<c>.P[y\<turnstile>n>z]}"
    using fs2
    apply -
    apply(rule substn_nrename_comm)
    apply(simp_all add: fresh_prod fresh_atm)
    done
  also have "\<dots> = ([(x',x)]\<bullet>(M[y\<turnstile>n>z])){x':=<c>.P[y\<turnstile>n>z]}" using eq2 by simp
  also have "\<dots> = ([(x',x)]\<bullet>(M[y\<turnstile>n>z])){x':=<c>.P}" using a2 by (simp add: rename_fresh)
  also have "\<dots> = M[y\<turnstile>n>z]{x:=<c>.P}" using eq' by simp
  finally show ?thesis by simp
qed

lemma substc_nrename_comm':
  assumes a: "x\<noteq>y" "y\<sharp>P"
  shows "M{c:=(x).P}[y\<turnstile>n>z] = M[y\<turnstile>n>z]{c:=(x).P}"
using a
proof -
  assume a1: "x\<noteq>y"
  assume a2: "y\<sharp>P"
  obtain x'::"name" where fs2: "x'\<sharp>(x,P,y,z)" by (rule exists_fresh(1), rule fin_supp, blast)
  have eq: "M{c:=(x).P} = M{c:=(x').([(x',x)]\<bullet>P)}"
    using fs2
    apply -
    apply(rule subst_rename)
    apply(simp)
    done
   have eq': "M[y\<turnstile>n>z]{c:=(x).P} = M[y\<turnstile>n>z]{c:=(x').([(x',x)]\<bullet>P)}"
    using fs2
    apply -
    apply(rule subst_rename)
    apply(simp)
    done
  have eq2: "([(x',x)]\<bullet>P)[y\<turnstile>n>z] = ([(x',x)]\<bullet>P)" using fs2 a2 a1
    apply -
    apply(rule rename_fresh)
    apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
    done
  have "M{c:=(x).P}[y\<turnstile>n>z] = M{c:=(x').([(x',x)]\<bullet>P)}[y\<turnstile>n>z]" using eq by simp
  also have "\<dots> = M[y\<turnstile>n>z]{c:=(x').(([(x',x)]\<bullet>P)[y\<turnstile>n>z])}"
    using fs2
    apply -
    apply(rule substc_nrename_comm)
    apply(simp_all add: fresh_prod fresh_atm)
    done
  also have "\<dots> = M[y\<turnstile>n>z]{c:=(x').(([(x',x)]\<bullet>P))}" using eq2 by simp
  also have "\<dots> = M[y\<turnstile>n>z]{c:=(x).P}" using eq' by simp 
  finally show ?thesis by simp
qed

lemmas subst_comm = substn_crename_comm substc_crename_comm
                    substn_nrename_comm substc_nrename_comm
lemmas subst_comm' = substn_crename_comm' substc_crename_comm'
                     substn_nrename_comm' substc_nrename_comm'

text {* typing contexts *}

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
  show "a\<sharp>\<Gamma>" by (induct \<Gamma>) (auto simp add: fresh_list_nil fresh_list_cons fresh_prod fresh_atm fresh_ty)
next
  show "x\<sharp>\<Delta>" by (induct \<Delta>) (auto simp add: fresh_list_nil fresh_list_cons fresh_prod fresh_atm fresh_ty)
qed

text {* cut-reductions *}

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
  assumes a: "fin (Ax x a) y"
  shows "x=y"
using a
apply(erule_tac fin.cases)
apply(auto simp add: trm.inject)
done

lemma fin_NotL_elim:
  assumes a: "fin (NotL <a>.M x) y"
  shows "x=y \<and> x\<sharp>M"
using a
apply(erule_tac fin.cases)
apply(auto simp add: trm.inject)
apply(subgoal_tac "y\<sharp>[aa].Ma")
apply(drule sym)
apply(simp_all add: abs_fresh)
done

lemma fin_AndL1_elim:
  assumes a: "fin (AndL1 (x).M y) z"
  shows "z=y \<and> z\<sharp>[x].M"
using a
apply(erule_tac fin.cases)
apply(auto simp add: trm.inject)
done

lemma fin_AndL2_elim:
  assumes a: "fin (AndL2 (x).M y) z"
  shows "z=y \<and> z\<sharp>[x].M"
using a
apply(erule_tac fin.cases)
apply(auto simp add: trm.inject)
done

lemma fin_OrL_elim:
  assumes a: "fin (OrL (x).M (y).N u) z"
  shows "z=u \<and> z\<sharp>[x].M \<and> z\<sharp>[y].N"
using a
apply(erule_tac fin.cases)
apply(auto simp add: trm.inject)
done

lemma fin_ImpL_elim:
  assumes a: "fin (ImpL <a>.M (x).N z) y"
  shows "z=y \<and> z\<sharp>M \<and> z\<sharp>[x].N"
using a
apply(erule_tac fin.cases)
apply(auto simp add: trm.inject)
apply(subgoal_tac "y\<sharp>[aa].Ma")
apply(drule sym)
apply(simp_all add: abs_fresh)
done

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
   (auto simp add: calc_atm simp add: fresh_left abs_fresh)

lemma not_fin_subst1:
  assumes a: "\<not>(fin M x)" 
  shows "\<not>(fin (M{c:=(y).P}) x)"
using a
apply(nominal_induct M avoiding: x c y P rule: trm.strong_induct)
apply(auto)
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(trm{coname:=(y).P},P,x)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(drule fin_elims, simp)
apply(drule fin_elims)
apply(auto)[1]
apply(drule freshn_after_substc)
apply(simp add: fin.intros)
apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(trm1{coname3:=(y).P},trm2{coname3:=(y).P},P,coname1,coname2,coname3,x)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR)
apply(erule fin.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(trm1{coname3:=(y).P},trm2{coname3:=(y).P},P,coname1,coname2,coname3,x)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(erule fin.cases, simp_all add: trm.inject)
apply(drule fin_AndL1_elim)
apply(auto simp add: abs_fresh)[1]
apply(drule freshn_after_substc)
apply(subgoal_tac "name2\<sharp>[name1]. trm")
apply(simp add: fin.intros)
apply(simp add: abs_fresh)
apply(drule fin_AndL2_elim)
apply(auto simp add: abs_fresh)[1]
apply(drule freshn_after_substc)
apply(subgoal_tac "name2\<sharp>[name1].trm")
apply(simp add: fin.intros)
apply(simp add: abs_fresh)
apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(trm{coname2:=(y).P},coname1,P,x)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(erule fin.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(trm{coname2:=(y).P},coname1,P,x)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(erule fin.cases, simp_all add: trm.inject)
apply(drule fin_OrL_elim)
apply(auto simp add: abs_fresh)[1]
apply(drule freshn_after_substc)+
apply(subgoal_tac "name3\<sharp>[name1].trm1 \<and> name3\<sharp>[name2].trm2")
apply(simp add: fin.intros)
apply(simp add: abs_fresh)
apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(trm{coname2:=(y).P},coname1,P,x)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(erule fin.cases, simp_all add: trm.inject)
apply(drule fin_ImpL_elim)
apply(auto simp add: abs_fresh)[1]
apply(drule freshn_after_substc)+
apply(subgoal_tac "x\<sharp>[name1].trm2")
apply(simp add: fin.intros)
apply(simp add: abs_fresh)
done

lemma not_fin_subst2:
  assumes a: "\<not>(fin M x)" 
  shows "\<not>(fin (M{y:=<c>.P}) x)"
using a
apply(nominal_induct M avoiding: x c y P rule: trm.strong_induct)
apply(auto)
apply(erule fin.cases, simp_all add: trm.inject)
apply(erule fin.cases, simp_all add: trm.inject)
apply(erule fin.cases, simp_all add: trm.inject)
apply(erule fin.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(trm{y:=<c>.P},P,x)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fin_NotL_elim)
apply(auto)[1]
apply(drule freshn_after_substn)
apply(simp)
apply(simp add: fin.intros)
apply(erule fin.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(trm{y:=<c>.P},P,name1,x)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fin_AndL1_elim)
apply(auto simp add: abs_fresh)[1]
apply(drule freshn_after_substn)
apply(simp)
apply(subgoal_tac "name2\<sharp>[name1]. trm")
apply(simp add: fin.intros)
apply(simp add: abs_fresh)
apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(trm{y:=<c>.P},P,name1,x)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fin_AndL2_elim)
apply(auto simp add: abs_fresh)[1]
apply(drule freshn_after_substn)
apply(simp)
apply(subgoal_tac "name2\<sharp>[name1].trm")
apply(simp add: fin.intros)
apply(simp add: abs_fresh)
apply(erule fin.cases, simp_all add: trm.inject)
apply(erule fin.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(trm1{y:=<c>.P},trm2{y:=<c>.P},name1,name2,P,x)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fin_OrL_elim)
apply(auto simp add: abs_fresh)[1]
apply(drule freshn_after_substn)
apply(simp)
apply(drule freshn_after_substn)
apply(simp)
apply(subgoal_tac "name3\<sharp>[name1].trm1 \<and> name3\<sharp>[name2].trm2")
apply(simp add: fin.intros)
apply(simp add: abs_fresh)
apply(erule fin.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(trm1{name2:=<c>.P},trm2{name2:=<c>.P},name1,P,x)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fin_ImpL_elim)
apply(auto simp add: abs_fresh)[1]
apply(drule freshn_after_substn)
apply(simp)
apply(drule freshn_after_substn)
apply(simp)
apply(subgoal_tac "x\<sharp>[name1].trm2")
apply(simp add: fin.intros)
apply(simp add: abs_fresh)
done

lemma fin_subst1:
  assumes a: "fin M x" "x\<noteq>y" "x\<sharp>P"
  shows "fin (M{y:=<c>.P}) x"
using a
apply(nominal_induct M avoiding: x y c P rule: trm.strong_induct)
apply(auto dest!: fin_elims simp add: subst_fresh abs_fresh)
apply(rule fin.intros, simp add: subst_fresh abs_fresh)
apply(rule fin.intros, simp add: subst_fresh abs_fresh)
apply(rule fin.intros, simp add: subst_fresh abs_fresh)
apply(rule fin.intros, simp add: subst_fresh abs_fresh)
apply(rule fin.intros, simp add: subst_fresh abs_fresh, simp add: subst_fresh abs_fresh)
apply(rule fin.intros, simp add: subst_fresh abs_fresh, simp add: subst_fresh abs_fresh)
apply(rule fin.intros, simp add: subst_fresh abs_fresh, simp add: subst_fresh abs_fresh)
apply(rule fin.intros, simp add: subst_fresh abs_fresh, simp add: subst_fresh abs_fresh)
apply(rule fin.intros, simp add: subst_fresh abs_fresh, simp add: subst_fresh abs_fresh)
done

lemma fin_subst2:
  assumes a: "fin M y" "x\<noteq>y" "y\<sharp>P" "M\<noteq>Ax y c" 
  shows "fin (M{c:=(x).P}) y"
using a
apply(nominal_induct M avoiding: x y c P rule: trm.strong_induct)
apply(drule fin_elims)
apply(simp add: trm.inject)
apply(rule fin.intros)
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(rule fin.intros)
apply(auto)[1]
apply(rule subst_fresh)
apply(simp)
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(rule fin.intros)
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(drule fin_elims, simp)
apply(rule fin.intros)
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(rule fin.intros)
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(rule fin.intros)
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
done

lemma fin_substn_nrename:
  assumes a: "fin M x" "x\<noteq>y" "x\<sharp>P"
  shows "M[x\<turnstile>n>y]{y:=<c>.P} = Cut <c>.P (x).(M{y:=<c>.P})"
using a
apply(nominal_induct M avoiding: x y c P rule: trm.strong_induct)
apply(drule fin_Ax_elim)
apply(simp)
apply(simp add: trm.inject)
apply(simp add: alpha calc_atm fresh_atm)
apply(simp)
apply(drule fin_rest_elims)
apply(simp)
apply(drule fin_rest_elims)
apply(simp)
apply(drule fin_NotL_elim)
apply(simp)
apply(subgoal_tac "\<exists>z::name. z\<sharp>(trm,y,x,P,trm[x\<turnstile>n>y]{y:=<c>.P})")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL)
apply(simp add: trm.inject alpha fresh_atm calc_atm abs_fresh)
apply(rule conjI)
apply(simp add: nsubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: nrename_fresh)
apply(rule subst_fresh)
apply(simp)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(drule fin_rest_elims)
apply(simp)
apply(drule fin_AndL1_elim)
apply(simp)
apply(subgoal_tac "\<exists>z::name. z\<sharp>(name2,name1,P,trm[name2\<turnstile>n>y]{y:=<c>.P},y,P,trm)")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1)
apply(simp add: trm.inject alpha fresh_atm calc_atm abs_fresh)
apply(rule conjI)
apply(simp add: nsubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: nrename_fresh)
apply(rule subst_fresh)
apply(simp)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(drule fin_AndL2_elim)
apply(simp)
apply(subgoal_tac "\<exists>z::name. z\<sharp>(name2,name1,P,trm[name2\<turnstile>n>y]{y:=<c>.P},y,P,trm)")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2)
apply(simp add: trm.inject alpha fresh_atm calc_atm abs_fresh)
apply(rule conjI)
apply(simp add: nsubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: nrename_fresh)
apply(rule subst_fresh)
apply(simp)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(drule fin_rest_elims)
apply(simp)
apply(drule fin_rest_elims)
apply(simp)
apply(drule fin_OrL_elim)
apply(simp add: abs_fresh)
apply(simp add: subst_fresh rename_fresh)
apply(subgoal_tac "\<exists>z::name. z\<sharp>(name3,name2,name1,P,trm1[name3\<turnstile>n>y]{y:=<c>.P},trm2[name3\<turnstile>n>y]{y:=<c>.P},y,P,trm1,trm2)")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL)
apply(simp add: trm.inject alpha fresh_atm calc_atm abs_fresh)
apply(rule conjI)
apply(simp add: nsubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: nrename_fresh)
apply(simp add: nsubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: nrename_fresh)
apply(rule exists_fresh')
apply(rule fin_supp)
apply(drule fin_rest_elims)
apply(simp)
apply(drule fin_ImpL_elim)
apply(simp add: abs_fresh)
apply(simp add: subst_fresh rename_fresh)
apply(subgoal_tac "\<exists>z::name. z\<sharp>(name1,x,P,trm1[x\<turnstile>n>y]{y:=<c>.P},trm2[x\<turnstile>n>y]{y:=<c>.P},y,P,trm1,trm2)")
apply(erule exE, simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL)
apply(simp add: trm.inject alpha fresh_atm calc_atm abs_fresh)
apply(rule conjI)
apply(simp add: nsubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: nrename_fresh)
apply(simp add: nsubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: nrename_fresh)
apply(rule exists_fresh')
apply(rule fin_supp)
done

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
  assumes a: "fic (Ax x a) b"
  shows "a=b"
using a
apply(erule_tac fic.cases)
apply(auto simp add: trm.inject)
done

lemma fic_NotR_elim:
  assumes a: "fic (NotR (x).M a) b"
  shows "a=b \<and> b\<sharp>M"
using a
apply(erule_tac fic.cases)
apply(auto simp add: trm.inject)
apply(subgoal_tac "b\<sharp>[xa].Ma")
apply(drule sym)
apply(simp_all add: abs_fresh)
done

lemma fic_OrR1_elim:
  assumes a: "fic (OrR1 <a>.M b) c"
  shows "b=c \<and> c\<sharp>[a].M"
using a
apply(erule_tac fic.cases)
apply(auto simp add: trm.inject)
done

lemma fic_OrR2_elim:
  assumes a: "fic (OrR2 <a>.M b) c"
  shows "b=c \<and> c\<sharp>[a].M"
using a
apply(erule_tac fic.cases)
apply(auto simp add: trm.inject)
done

lemma fic_AndR_elim:
  assumes a: "fic (AndR <a>.M <b>.N c) d"
  shows "c=d \<and> d\<sharp>[a].M \<and> d\<sharp>[b].N"
using a
apply(erule_tac fic.cases)
apply(auto simp add: trm.inject)
done

lemma fic_ImpR_elim:
  assumes a: "fic (ImpR (x).<a>.M b) c"
  shows "b=c \<and> b\<sharp>[a].M"
using a
apply(erule_tac fic.cases)
apply(auto simp add: trm.inject)
apply(subgoal_tac "c\<sharp>[xa].[aa].Ma")
apply(drule sym)
apply(simp_all add: abs_fresh)
done

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
   (auto simp add: calc_atm simp add: fresh_left abs_fresh)

lemma not_fic_subst1:
  assumes a: "\<not>(fic M a)" 
  shows "\<not>(fic (M{y:=<c>.P}) a)"
using a
apply(nominal_induct M avoiding: a c y P rule: trm.strong_induct)
apply(auto)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(drule fic_elims)
apply(auto)[1]
apply(drule freshc_after_substn)
apply(simp add: fic.intros)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,a)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fic_elims, simp)
apply(drule fic_elims)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshc_after_substn)
apply(drule freshc_after_substn)
apply(simp add: fic.intros abs_fresh)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1,a)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fic_elims, simp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{y:=<c>.P},P,name1,a)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fic_elims, simp)
apply(drule fic_elims)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshc_after_substn)
apply(simp add: fic.intros abs_fresh)
apply(drule fic_elims)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshc_after_substn)
apply(simp add: fic.intros abs_fresh)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{y:=<c>.P},trm2{y:=<c>.P},P,name1,name2,a)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshc_after_substn)
apply(simp add: fic.intros abs_fresh)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},trm2{name2:=<c>.P},P,name1,name2,a)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fic_elims, simp)
done

lemma not_fic_subst2:
  assumes a: "\<not>(fic M a)" 
  shows "\<not>(fic (M{c:=(y).P}) a)"
using a
apply(nominal_induct M avoiding: a c y P rule: trm.strong_induct)
apply(auto)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(trm{coname:=(y).P},P,a)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(drule fic_elims, simp)
apply(erule conjE)+
apply(drule freshc_after_substc)
apply(simp)
apply(simp add: fic.intros abs_fresh)
apply(drule fic_elims, simp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(trm1{coname3:=(y).P},trm2{coname3:=(y).P},P,coname1,coname2,a)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(drule fic_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshc_after_substc)
apply(simp)
apply(drule freshc_after_substc)
apply(simp)
apply(simp add: fic.intros abs_fresh)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(trm{coname2:=(y).P},P,coname1,a)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(drule fic_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshc_after_substc)
apply(simp)
apply(simp add: fic.intros abs_fresh)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(trm{coname2:=(y).P},P,coname1,a)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(drule fic_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshc_after_substc)
apply(simp)
apply(simp add: fic.intros abs_fresh)
apply(drule fic_elims, simp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(trm{coname2:=(y).P},P,coname1,a)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(drule fic_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshc_after_substc)
apply(simp)
apply(simp add: fic.intros abs_fresh)
apply(drule fic_elims, simp)
done

lemma fic_subst1:
  assumes a: "fic M a" "a\<noteq>b" "a\<sharp>P"
  shows "fic (M{b:=(x).P}) a"
using a
apply(nominal_induct M avoiding: x b a P rule: trm.strong_induct)
apply(drule fic_elims)
apply(simp add: fic.intros)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(rule fic.intros)
apply(auto)[1]
apply(rule subst_fresh)
apply(simp)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(rule fic.intros)
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(rule fic.intros)
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(drule fic_elims, simp)
apply(rule fic.intros)
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(rule fic.intros)
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(drule fic_elims, simp)
done

lemma fic_subst2:
  assumes a: "fic M a" "c\<noteq>a" "a\<sharp>P" "M\<noteq>Ax x a" 
  shows "fic (M{x:=<c>.P}) a"
using a
apply(nominal_induct M avoiding: x a c P rule: trm.strong_induct)
apply(drule fic_elims)
apply(simp add: trm.inject)
apply(rule fic.intros)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(rule fic.intros)
apply(auto)[1]
apply(rule subst_fresh)
apply(simp)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(rule fic.intros)
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(rule fic.intros)
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(drule fic_elims, simp)
apply(rule fic.intros)
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(rule fic.intros)
apply(simp add: abs_fresh fresh_atm)
apply(rule subst_fresh)
apply(auto)[1]
apply(drule fic_elims, simp)
done

lemma fic_substc_crename:
  assumes a: "fic M a" "a\<noteq>b" "a\<sharp>P"
  shows "M[a\<turnstile>c>b]{b:=(y).P} = Cut <a>.(M{b:=(y).P}) (y).P"
using a
apply(nominal_induct M avoiding: a b  y P rule: trm.strong_induct)
apply(drule fic_Ax_elim)
apply(simp)
apply(simp add: trm.inject)
apply(simp add: alpha calc_atm fresh_atm trm.inject)
apply(simp)
apply(drule fic_rest_elims)
apply(simp)
apply(drule fic_NotR_elim)
apply(simp)
apply(generate_fresh "coname")
apply(fresh_fun_simp)
apply(simp add: trm.inject alpha fresh_atm fresh_prod fresh_atm calc_atm abs_fresh)
apply(rule conjI)
apply(simp add: csubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: crename_fresh)
apply(rule subst_fresh)
apply(simp)
apply(drule fic_rest_elims)
apply(simp)
apply(drule fic_AndR_elim)
apply(simp add: abs_fresh fresh_atm subst_fresh rename_fresh)
apply(generate_fresh "coname")
apply(fresh_fun_simp)
apply(simp add: trm.inject alpha fresh_atm calc_atm abs_fresh fresh_prod)
apply(rule conjI)
apply(simp add: csubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: csubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: subst_fresh)
apply(drule fic_rest_elims)
apply(simp)
apply(drule fic_rest_elims)
apply(simp)
apply(drule fic_OrR1_elim)
apply(simp)
apply(generate_fresh "coname")
apply(fresh_fun_simp)
apply(simp add: trm.inject alpha fresh_atm calc_atm abs_fresh fresh_prod)
apply(simp add: csubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: subst_fresh rename_fresh)
apply(drule fic_OrR2_elim)
apply(simp add: abs_fresh fresh_atm)
apply(generate_fresh "coname")
apply(fresh_fun_simp)
apply(simp add: trm.inject alpha fresh_atm calc_atm abs_fresh fresh_prod)
apply(simp add: csubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: subst_fresh rename_fresh)
apply(drule fic_rest_elims)
apply(simp)
apply(drule fic_ImpR_elim)
apply(simp add: abs_fresh fresh_atm)
apply(auto)[1]
apply(generate_fresh "coname")
apply(fresh_fun_simp)
apply(simp add: trm.inject alpha fresh_atm calc_atm abs_fresh fresh_prod)
apply(simp add: csubst_eqvt calc_atm)
apply(simp add: perm_fresh_fresh)
apply(simp add: subst_fresh rename_fresh)
apply(drule fic_rest_elims)
apply(simp)
done

inductive
  l_redu :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<longrightarrow>\<^isub>l _" [100,100] 100)
where
  LAxR:  "\<lbrakk>x\<sharp>M; a\<sharp>b; fic M a\<rbrakk> \<Longrightarrow> Cut <a>.M (x).(Ax x b) \<longrightarrow>\<^isub>l M[a\<turnstile>c>b]"
| LAxL:  "\<lbrakk>a\<sharp>M; x\<sharp>y; fin M x\<rbrakk> \<Longrightarrow> Cut <a>.(Ax y a) (x).M \<longrightarrow>\<^isub>l M[x\<turnstile>n>y]"
| LNot:  "\<lbrakk>y\<sharp>(M,N); x\<sharp>(N,y); a\<sharp>(M,N,b); b\<sharp>M; y\<noteq>x; b\<noteq>a\<rbrakk> \<Longrightarrow>
          Cut <a>.(NotR (x).M a) (y).(NotL <b>.N y) \<longrightarrow>\<^isub>l Cut <b>.N (x).M" 
| LAnd1: "\<lbrakk>b\<sharp>([a1].M1,[a2].M2,N,a1,a2); y\<sharp>([x].N,M1,M2,x); x\<sharp>(M1,M2); a1\<sharp>(M2,N); a2\<sharp>(M1,N); a1\<noteq>a2\<rbrakk> \<Longrightarrow>
          Cut <b>.(AndR <a1>.M1 <a2>.M2 b) (y).(AndL1 (x).N y) \<longrightarrow>\<^isub>l Cut <a1>.M1 (x).N"
| LAnd2: "\<lbrakk>b\<sharp>([a1].M1,[a2].M2,N,a1,a2); y\<sharp>([x].N,M1,M2,x); x\<sharp>(M1,M2); a1\<sharp>(M2,N); a2\<sharp>(M1,N); a1\<noteq>a2\<rbrakk> \<Longrightarrow>
          Cut <b>.(AndR <a1>.M1 <a2>.M2 b) (y).(AndL2 (x).N y) \<longrightarrow>\<^isub>l Cut <a2>.M2 (x).N"
| LOr1:  "\<lbrakk>b\<sharp>([a].M,N1,N2,a); y\<sharp>([x1].N1,[x2].N2,M,x1,x2); x1\<sharp>(M,N2); x2\<sharp>(M,N1); a\<sharp>(N1,N2); x1\<noteq>x2\<rbrakk> \<Longrightarrow>
          Cut <b>.(OrR1 <a>.M b) (y).(OrL (x1).N1 (x2).N2 y) \<longrightarrow>\<^isub>l Cut <a>.M (x1).N1"
| LOr2:  "\<lbrakk>b\<sharp>([a].M,N1,N2,a); y\<sharp>([x1].N1,[x2].N2,M,x1,x2); x1\<sharp>(M,N2); x2\<sharp>(M,N1); a\<sharp>(N1,N2); x1\<noteq>x2\<rbrakk> \<Longrightarrow>
          Cut <b>.(OrR2 <a>.M b) (y).(OrL (x1).N1 (x2).N2 y) \<longrightarrow>\<^isub>l Cut <a>.M (x2).N2"
| LImp:  "\<lbrakk>z\<sharp>(N,[y].P,[x].M,y,x); b\<sharp>([a].M,[c].N,P,c,a); x\<sharp>(N,[y].P,y); 
          c\<sharp>(P,[a].M,b,a); a\<sharp>([c].N,P); y\<sharp>(N,[x].M)\<rbrakk> \<Longrightarrow>
          Cut <b>.(ImpR (x).<a>.M b) (z).(ImpL <c>.N (y).P z) \<longrightarrow>\<^isub>l Cut <a>.(Cut <c>.N (x).M) (y).P"

equivariance l_redu

lemma l_redu_eqvt':
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "(pi1\<bullet>M) \<longrightarrow>\<^isub>l (pi1\<bullet>M') \<Longrightarrow> M \<longrightarrow>\<^isub>l M'"
  and   "(pi2\<bullet>M) \<longrightarrow>\<^isub>l (pi2\<bullet>M') \<Longrightarrow> M \<longrightarrow>\<^isub>l M'"
apply -
apply(drule_tac pi="rev pi1" in l_redu.eqvt(1))
apply(perm_simp)
apply(drule_tac pi="rev pi2" in l_redu.eqvt(2))
apply(perm_simp)
done

nominal_inductive l_redu
  apply(simp_all add: abs_fresh fresh_atm rename_fresh fresh_prod abs_supp fin_supp)
  apply(force)+
  done

lemma fresh_l_redu:
  fixes x::"name"
  and   a::"coname"
  shows "M \<longrightarrow>\<^isub>l M' \<Longrightarrow> x\<sharp>M \<Longrightarrow> x\<sharp>M'"
  and   "M \<longrightarrow>\<^isub>l M' \<Longrightarrow> a\<sharp>M \<Longrightarrow> a\<sharp>M'"
apply -
apply(induct rule: l_redu.induct)
apply(auto simp add: abs_fresh rename_fresh)
apply(case_tac "xa=x")
apply(simp add: rename_fresh)
apply(simp add: rename_fresh fresh_atm)
apply(simp add: fresh_prod abs_fresh abs_supp fin_supp)+
apply(induct rule: l_redu.induct)
apply(auto simp add: abs_fresh rename_fresh)
apply(case_tac "aa=a")
apply(simp add: rename_fresh)
apply(simp add: rename_fresh fresh_atm)
apply(simp add: fresh_prod abs_fresh abs_supp fin_supp)+
done

lemma better_LAxR_intro[intro]:
  shows "fic M a \<Longrightarrow> Cut <a>.M (x).(Ax x b) \<longrightarrow>\<^isub>l M[a\<turnstile>c>b]"
proof -
  assume fin: "fic M a"
  obtain x'::"name" where fs1: "x'\<sharp>(M,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(a,M,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.M (x).(Ax x b) =  Cut <a'>.([(a',a)]\<bullet>M) (x').(Ax x' b)"
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>l ([(a',a)]\<bullet>M)[a'\<turnstile>c>b]" using fs1 fs2 fin
    by (auto intro: l_redu.intros simp add: fresh_left calc_atm fic_rename)
  also have "\<dots> = M[a\<turnstile>c>b]" using fs1 fs2 by (simp add: crename_rename)
  finally show ?thesis by simp
qed
    
lemma better_LAxL_intro[intro]:
  shows "fin M x \<Longrightarrow> Cut <a>.(Ax y a) (x).M \<longrightarrow>\<^isub>l M[x\<turnstile>n>y]"
proof -
  assume fin: "fin M x"
  obtain x'::"name" where fs1: "x'\<sharp>(y,M,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(a,M)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.(Ax y a) (x).M = Cut <a'>.(Ax y a') (x').([(x',x)]\<bullet>M)"
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>l ([(x',x)]\<bullet>M)[x'\<turnstile>n>y]" using fs1 fs2 fin
    by (auto intro: l_redu.intros simp add: fresh_left calc_atm fin_rename)
  also have "\<dots> = M[x\<turnstile>n>y]" using fs1 fs2 by (simp add: nrename_rename)
  finally show ?thesis by simp
qed

lemma better_LNot_intro[intro]:
  shows "\<lbrakk>y\<sharp>N; a\<sharp>M\<rbrakk> \<Longrightarrow> Cut <a>.(NotR (x).M a) (y).(NotL <b>.N y) \<longrightarrow>\<^isub>l Cut <b>.N (x).M"
proof -
  assume fs: "y\<sharp>N" "a\<sharp>M"
  obtain x'::"name" where f1: "x'\<sharp>(y,N,M,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain y'::"name" where f2: "y'\<sharp>(y,N,M,x,x')" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where f3: "a'\<sharp>(a,M,N,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain b'::"coname" where f4: "b'\<sharp>(a,M,N,b,a')" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.(NotR (x).M a) (y).(NotL <b>.N y) 
                      = Cut <a'>.(NotR (x).([(a',a)]\<bullet>M) a') (y').(NotL <b>.([(y',y)]\<bullet>N) y')"
    using f1 f2 f3 f4 
    by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm abs_fresh)
  also have "\<dots> = Cut <a'>.(NotR (x).M a') (y').(NotL <b>.N y')"
    using f1 f2 f3 f4 fs by (perm_simp)
  also have "\<dots> = Cut <a'>.(NotR (x').([(x',x)]\<bullet>M) a') (y').(NotL <b'>.([(b',b)]\<bullet>N) y')"
    using f1 f2 f3 f4 
    by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>l Cut <b'>.([(b',b)]\<bullet>N) (x').([(x',x)]\<bullet>M)"
    using f1 f2 f3 f4 fs
    by (auto intro:  l_redu.intros simp add: fresh_prod fresh_left calc_atm fresh_atm)
  also have "\<dots> = Cut <b>.N (x).M"
    using f1 f2 f3 f4 by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  finally show ?thesis by simp
qed 

lemma better_LAnd1_intro[intro]:
  shows "\<lbrakk>a\<sharp>([b1].M1,[b2].M2); y\<sharp>[x].N\<rbrakk> 
         \<Longrightarrow> Cut <a>.(AndR <b1>.M1 <b2>.M2 a) (y).(AndL1 (x).N y) \<longrightarrow>\<^isub>l Cut <b1>.M1 (x).N"
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
    apply(auto simp add: perm_fresh_fresh)
    done
  also have "\<dots> = Cut <a'>.(AndR <b1'>.([(b1',b1)]\<bullet>M1) <b2'>.([(b2',b2)]\<bullet>M2) a') 
                                                               (y').(AndL1 (x').([(x',x)]\<bullet>N) y')"
    using f1 f2 f3 f4 f5 fs 
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    done
  also have "\<dots> \<longrightarrow>\<^isub>l Cut <b1'>.([(b1',b1)]\<bullet>M1) (x').([(x',x)]\<bullet>N)"
    using f1 f2 f3 f4 f5 fs
    apply -
    apply(rule l_redu.intros)
    apply(auto simp add: abs_fresh fresh_prod fresh_left calc_atm fresh_atm)
    done
  also have "\<dots> = Cut <b1>.M1 (x).N"
    using f1 f2 f3 f4 f5 fs by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  finally show ?thesis by simp
qed 

lemma better_LAnd2_intro[intro]:
  shows "\<lbrakk>a\<sharp>([b1].M1,[b2].M2); y\<sharp>[x].N\<rbrakk> 
         \<Longrightarrow> Cut <a>.(AndR <b1>.M1 <b2>.M2 a) (y).(AndL2 (x).N y) \<longrightarrow>\<^isub>l Cut <b2>.M2 (x).N"
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
    apply(auto simp add: perm_fresh_fresh)
    done
  also have "\<dots> = Cut <a'>.(AndR <b1'>.([(b1',b1)]\<bullet>M1) <b2'>.([(b2',b2)]\<bullet>M2) a') 
                                                               (y').(AndL2 (x').([(x',x)]\<bullet>N) y')"
    using f1 f2 f3 f4 f5 fs 
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    done
  also have "\<dots> \<longrightarrow>\<^isub>l Cut <b2'>.([(b2',b2)]\<bullet>M2) (x').([(x',x)]\<bullet>N)"
    using f1 f2 f3 f4 f5 fs
    apply -
    apply(rule l_redu.intros)
    apply(auto simp add: abs_fresh fresh_prod fresh_left calc_atm fresh_atm)
    done
  also have "\<dots> = Cut <b2>.M2 (x).N"
    using f1 f2 f3 f4 f5 fs by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  finally show ?thesis by simp
qed

lemma better_LOr1_intro[intro]:
  shows "\<lbrakk>y\<sharp>([x1].N1,[x2].N2); b\<sharp>[a].M\<rbrakk> 
         \<Longrightarrow> Cut <b>.(OrR1 <a>.M b) (y).(OrL (x1).N1 (x2).N2 y) \<longrightarrow>\<^isub>l Cut <a>.M (x1).N1"
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
    apply(auto simp add: perm_fresh_fresh)
    done
  also have "\<dots> = Cut <b'>.(OrR1 <a'>.([(a',a)]\<bullet>M) b') 
              (y').(OrL (x1').([(x1',x1)]\<bullet>N1) (x2').([(x2',x2)]\<bullet>N2) y')"   
    using f1 f2 f3 f4 f5 fs 
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    done
  also have "\<dots> \<longrightarrow>\<^isub>l Cut <a'>.([(a',a)]\<bullet>M) (x1').([(x1',x1)]\<bullet>N1)"
    using f1 f2 f3 f4 f5 fs
    apply -
    apply(rule l_redu.intros)
    apply(auto simp add: abs_fresh fresh_prod fresh_left calc_atm fresh_atm)
    done
  also have "\<dots> = Cut <a>.M (x1).N1"
    using f1 f2 f3 f4 f5 fs by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  finally show ?thesis by simp
qed

lemma better_LOr2_intro[intro]:
  shows "\<lbrakk>y\<sharp>([x1].N1,[x2].N2); b\<sharp>[a].M\<rbrakk> 
         \<Longrightarrow> Cut <b>.(OrR2 <a>.M b) (y).(OrL (x1).N1 (x2).N2 y) \<longrightarrow>\<^isub>l Cut <a>.M (x2).N2"
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
    apply(auto simp add: perm_fresh_fresh)
    done
  also have "\<dots> = Cut <b'>.(OrR2 <a'>.([(a',a)]\<bullet>M) b') 
              (y').(OrL (x1').([(x1',x1)]\<bullet>N1) (x2').([(x2',x2)]\<bullet>N2) y')"   
    using f1 f2 f3 f4 f5 fs 
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    done
  also have "\<dots> \<longrightarrow>\<^isub>l Cut <a'>.([(a',a)]\<bullet>M) (x2').([(x2',x2)]\<bullet>N2)"
    using f1 f2 f3 f4 f5 fs
    apply -
    apply(rule l_redu.intros)
    apply(auto simp add: abs_fresh fresh_prod fresh_left calc_atm fresh_atm)
    done
  also have "\<dots> = Cut <a>.M (x2).N2"
    using f1 f2 f3 f4 f5 fs by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  finally show ?thesis by simp
qed 

lemma better_LImp_intro[intro]:
  shows "\<lbrakk>z\<sharp>(N,[y].P); b\<sharp>[a].M; a\<sharp>N\<rbrakk> 
         \<Longrightarrow> Cut <b>.(ImpR (x).<a>.M b) (z).(ImpL <c>.N (y).P z) \<longrightarrow>\<^isub>l Cut <a>.(Cut <c>.N (x).M) (y).P"
proof -
  assume fs: "z\<sharp>(N,[y].P)" "b\<sharp>[a].M" "a\<sharp>N"
  obtain y'::"name" where f1: "y'\<sharp>(y,M,N,P,z,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain x'::"name" where f2: "x'\<sharp>(y,M,N,P,z,x,y')" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain z'::"name" where f3: "z'\<sharp>(y,M,N,P,z,x,y',x')" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where f4: "a'\<sharp>(a,N,P,M,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain b'::"coname" where f5: "b'\<sharp>(a,N,P,M,b,c,a')" by (rule exists_fresh(2),rule fin_supp, blast)
  obtain c'::"coname" where f6: "c'\<sharp>(a,N,P,M,b,c,a',b')" by (rule exists_fresh(2),rule fin_supp, blast)
  have " Cut <b>.(ImpR (x).<a>.M b) (z).(ImpL <c>.N (y).P z)
                      =  Cut <b'>.(ImpR (x).<a>.M b') (z').(ImpL <c>.N (y).P z')"
    using f1 f2 f3 f4 f5 fs
    apply(rule_tac sym)
    apply(perm_simp add: trm.inject alpha calc_atm fresh_prod fresh_left fresh_atm abs_fresh)
    apply(auto simp add: perm_fresh_fresh)
    done
  also have "\<dots> = Cut <b'>.(ImpR (x').<a'>.([(a',a)]\<bullet>([(x',x)]\<bullet>M)) b') 
                           (z').(ImpL <c'>.([(c',c)]\<bullet>N) (y').([(y',y)]\<bullet>P) z')"
    using f1 f2 f3 f4 f5 f6 fs 
    apply(rule_tac sym)
    apply(simp add: trm.inject)
    apply(simp add: alpha)
    apply(rule conjI)
    apply(simp add: trm.inject)
    apply(simp add: alpha fresh_prod fresh_atm abs_perm calc_atm fresh_left abs_fresh)
    apply(simp add: trm.inject)
    apply(simp add: alpha)
    apply(rule conjI)
    apply(simp add: alpha fresh_prod fresh_atm abs_perm calc_atm fresh_left abs_fresh)
    apply(simp add: alpha fresh_prod fresh_atm abs_perm calc_atm fresh_left abs_fresh)
    done
  also have "\<dots> \<longrightarrow>\<^isub>l Cut <a'>.(Cut <c'>.([(c',c)]\<bullet>N) (x').([(a',a)]\<bullet>[(x',x)]\<bullet>M)) (y').([(y',y)]\<bullet>P)"
    using f1 f2 f3 f4 f5 f6 fs
    apply -
    apply(rule l_redu.intros)
    apply(auto simp add: abs_fresh fresh_prod fresh_left calc_atm fresh_atm)
    done
  also have "\<dots> = Cut <a>.(Cut <c>.N (x).M) (y).P"
    using f1 f2 f3 f4 f5 f6 fs 
    apply(simp add: trm.inject)
    apply(rule conjI)
    apply(simp add: alpha)
    apply(rule disjI2)
    apply(simp add: trm.inject)
    apply(rule conjI)
    apply(simp add: fresh_prod fresh_atm)
    apply(rule conjI)
    apply(perm_simp add: calc_atm)
    apply(auto simp add: fresh_prod fresh_atm)[1]
    apply(perm_simp add: alpha)
    apply(perm_simp add: alpha)
    apply(perm_simp add: alpha)
    apply(rule conjI)
    apply(perm_simp add: calc_atm)
    apply(rule_tac pi="[(a',a)]" in pt_bij4[OF pt_coname_inst, OF at_coname_inst])
    apply(perm_simp add: abs_perm calc_atm)
    apply(perm_simp add: alpha fresh_prod fresh_atm)
    apply(simp add: abs_fresh)
    apply(perm_simp add: alpha fresh_prod fresh_atm)
    done
  finally show ?thesis by simp
qed 

lemma alpha_coname:
  fixes M::"trm"
  and   a::"coname"
  assumes a: "[a].M = [b].N" "c\<sharp>(a,b,M,N)"
  shows "M = [(a,c)]\<bullet>[(b,c)]\<bullet>N"
using a
apply(auto simp add: alpha_fresh fresh_prod fresh_atm)
apply(drule sym)
apply(perm_simp)
done 

lemma alpha_name:
  fixes M::"trm"
  and   x::"name"
  assumes a: "[x].M = [y].N" "z\<sharp>(x,y,M,N)"
  shows "M = [(x,z)]\<bullet>[(y,z)]\<bullet>N"
using a
apply(auto simp add: alpha_fresh fresh_prod fresh_atm)
apply(drule sym)
apply(perm_simp)
done 

lemma alpha_name_coname:
  fixes M::"trm"
  and   x::"name"
  and   a::"coname"
  assumes a: "[x].[b].M = [y].[c].N" "z\<sharp>(x,y,M,N)" "a\<sharp>(b,c,M,N)"
  shows "M = [(x,z)]\<bullet>[(b,a)]\<bullet>[(c,a)]\<bullet>[(y,z)]\<bullet>N"
using a
apply(auto simp add: alpha_fresh fresh_prod fresh_atm 
                     abs_supp fin_supp abs_fresh abs_perm fresh_left calc_atm)
apply(drule sym)
apply(simp)
apply(perm_simp)
done 

lemma Cut_l_redu_elim:
  assumes a: "Cut <a>.M (x).N \<longrightarrow>\<^isub>l R"
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
using a
apply(erule_tac l_redu.cases)
apply(rule disjI1)
(* ax case *)
apply(simp add: trm.inject)
apply(rule_tac x="b" in exI)
apply(erule conjE)
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(simp)
apply(simp add: rename_fresh)
apply(rule disjI2)
apply(rule disjI1)
(* ax case *)
apply(simp add: trm.inject)
apply(rule_tac x="y" in exI)
apply(erule conjE)
apply(thin_tac "[a].M = [aa].Ax y aa")
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(simp)
apply(simp add: rename_fresh)
apply(rule disjI2)
apply(rule disjI2)
apply(rule disjI1)
(* not case *)
apply(simp add: trm.inject)
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
apply(auto simp add: calc_atm abs_fresh fresh_left)[1]
apply(case_tac "y=x")
apply(perm_simp)
apply(perm_simp)
apply(case_tac "aa=a")
apply(perm_simp)
apply(perm_simp)
(* and1 case *)
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
apply(rule exI)+
apply(rule conjI)
apply(rule_tac s="x" and t="[(x,ca)]\<bullet>[(y,ca)]\<bullet>y" in subst)
apply(simp add: calc_atm)
apply(rule refl)
apply(auto simp add: fresh_left calc_atm abs_fresh split: if_splits)[1]
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
apply(auto simp add: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
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
apply(auto simp add: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
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
apply(auto simp add: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
apply(perm_simp)+
(* and2 case *)
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
apply(auto simp add: fresh_left calc_atm abs_fresh split: if_splits)[1]
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
apply(auto simp add: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
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
apply(auto simp add: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
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
apply(auto simp add: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
apply(perm_simp)+
(* or1 case *)
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
apply(auto simp add: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
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
apply(auto simp add: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
apply(perm_simp)+
(* or2 case *)
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
apply(auto simp add: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
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
apply(auto simp add: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
apply(perm_simp)+
(* imp-case *)
apply(rule disjI2)
apply(rule disjI2)
apply(rule disjI2)
apply(rule disjI2)
apply(rule disjI2)
apply(rule disjI2)
apply(rule disjI2)
apply(simp add: trm.inject)
apply(erule conjE)+
apply(generate_fresh "coname")
apply(simp add: abs_fresh fresh_prod fresh_atm)
apply(auto)[1]
apply(drule_tac c="ca" in  alpha_coname)
apply(simp add: fresh_prod fresh_atm abs_fresh)
apply(simp)
apply(rule exI)+
apply(rule conjI)
apply(rule_tac s="a" and t="[(a,ca)]\<bullet>[(b,ca)]\<bullet>b" in subst)
apply(simp add: calc_atm)
apply(rule refl)
apply(generate_fresh "name")
apply(simp add: abs_fresh fresh_prod fresh_atm)
apply(auto)[1]
apply(drule_tac z="cb" in  alpha_name)
apply(simp add: fresh_prod fresh_atm abs_fresh)
apply(simp)
apply(rule exI)+
apply(rule conjI)
apply(rule_tac s="x" and t="[(x,cb)]\<bullet>[(z,cb)]\<bullet>z" in subst)
apply(simp add: calc_atm)
apply(rule refl)
apply(auto simp add: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
apply(perm_simp)+
apply(generate_fresh "name")
apply(simp add: abs_fresh fresh_prod fresh_atm)
apply(auto)[1]
apply(drule_tac z="cc" in  alpha_name)
apply(simp add: fresh_prod fresh_atm abs_fresh)
apply(simp)
apply(rule exI)+
apply(rule conjI)
apply(rule_tac s="x" and t="[(x,cc)]\<bullet>[(z,cc)]\<bullet>z" in subst)
apply(simp add: calc_atm)
apply(rule refl)
apply(auto simp add: fresh_left calc_atm abs_fresh alpha perm_fresh_fresh split: if_splits)[1]
apply(perm_simp)+
done

inductive
  c_redu :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<longrightarrow>\<^isub>c _" [100,100] 100)
where
  left[intro]:  "\<lbrakk>\<not>fic M a; a\<sharp>N; x\<sharp>M\<rbrakk> \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>c M{a:=(x).N}"
| right[intro]: "\<lbrakk>\<not>fin N x; a\<sharp>N; x\<sharp>M\<rbrakk> \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>c N{x:=<a>.M}"

equivariance c_redu

nominal_inductive c_redu
 by (simp_all add: abs_fresh subst_fresh)

lemma better_left[intro]:
  shows "\<not>fic M a \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>c M{a:=(x).N}"
proof -
  assume not_fic: "\<not>fic M a"
  obtain x'::"name" where fs1: "x'\<sharp>(N,M,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(a,M,N)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.M (x).N =  Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N)"
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>c ([(a',a)]\<bullet>M){a':=(x').([(x',x)]\<bullet>N)}" using fs1 fs2 not_fic
    apply -
    apply(rule left)
    apply(clarify)
    apply(drule_tac a'="a" in fic_rename)
    apply(simp add: perm_swap)
    apply(simp add: fresh_left calc_atm)+
    done
  also have "\<dots> = M{a:=(x).N}" using fs1 fs2
    by (simp add: subst_rename[symmetric] fresh_atm fresh_prod fresh_left calc_atm)
  finally show ?thesis by simp
qed

lemma better_right[intro]:
  shows "\<not>fin N x \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>c N{x:=<a>.M}"
proof -
  assume not_fin: "\<not>fin N x"
  obtain x'::"name" where fs1: "x'\<sharp>(N,M,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(a,M,N)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.M (x).N =  Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N)"
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>c ([(x',x)]\<bullet>N){x':=<a'>.([(a',a)]\<bullet>M)}" using fs1 fs2 not_fin
    apply -
    apply(rule right)
    apply(clarify)
    apply(drule_tac x'="x" in fin_rename)
    apply(simp add: perm_swap)
    apply(simp add: fresh_left calc_atm)+
    done
  also have "\<dots> = N{x:=<a>.M}" using fs1 fs2
    by (simp add: subst_rename[symmetric] fresh_atm fresh_prod fresh_left calc_atm)
  finally show ?thesis by simp
qed

lemma fresh_c_redu:
  fixes x::"name"
  and   c::"coname"
  shows "M \<longrightarrow>\<^isub>c M' \<Longrightarrow> x\<sharp>M \<Longrightarrow> x\<sharp>M'"
  and   "M \<longrightarrow>\<^isub>c M' \<Longrightarrow> c\<sharp>M \<Longrightarrow> c\<sharp>M'"
apply -
apply(induct rule: c_redu.induct)
apply(auto simp add: abs_fresh rename_fresh subst_fresh)
apply(induct rule: c_redu.induct)
apply(auto simp add: abs_fresh rename_fresh subst_fresh)
done

inductive
  a_redu :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<longrightarrow>\<^isub>a _" [100,100] 100)
where
  al_redu[intro]: "M\<longrightarrow>\<^isub>l M' \<Longrightarrow> M \<longrightarrow>\<^isub>a M'"
| ac_redu[intro]: "M\<longrightarrow>\<^isub>c M' \<Longrightarrow> M \<longrightarrow>\<^isub>a M'"
| a_Cut_l: "\<lbrakk>a\<sharp>N; x\<sharp>M; M\<longrightarrow>\<^isub>a M'\<rbrakk> \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>a Cut <a>.M' (x).N"
| a_Cut_r: "\<lbrakk>a\<sharp>N; x\<sharp>M; N\<longrightarrow>\<^isub>a N'\<rbrakk> \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>a Cut <a>.M (x).N'"
| a_NotL[intro]: "M\<longrightarrow>\<^isub>a M' \<Longrightarrow> NotL <a>.M x \<longrightarrow>\<^isub>a NotL <a>.M' x"
| a_NotR[intro]: "M\<longrightarrow>\<^isub>a M' \<Longrightarrow> NotR (x).M a \<longrightarrow>\<^isub>a NotR (x).M' a"
| a_AndR_l: "\<lbrakk>a\<sharp>(N,c); b\<sharp>(M,c); b\<noteq>a; M\<longrightarrow>\<^isub>a M'\<rbrakk> \<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^isub>a AndR <a>.M' <b>.N c"
| a_AndR_r: "\<lbrakk>a\<sharp>(N,c); b\<sharp>(M,c); b\<noteq>a; N\<longrightarrow>\<^isub>a N'\<rbrakk> \<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^isub>a AndR <a>.M <b>.N' c"
| a_AndL1: "\<lbrakk>x\<sharp>y; M\<longrightarrow>\<^isub>a M'\<rbrakk> \<Longrightarrow> AndL1 (x).M y \<longrightarrow>\<^isub>a AndL1 (x).M' y"
| a_AndL2: "\<lbrakk>x\<sharp>y; M\<longrightarrow>\<^isub>a M'\<rbrakk> \<Longrightarrow> AndL2 (x).M y \<longrightarrow>\<^isub>a AndL2 (x).M' y"
| a_OrL_l: "\<lbrakk>x\<sharp>(N,z); y\<sharp>(M,z); y\<noteq>x; M\<longrightarrow>\<^isub>a M'\<rbrakk> \<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^isub>a OrL (x).M' (y).N z"
| a_OrL_r: "\<lbrakk>x\<sharp>(N,z); y\<sharp>(M,z); y\<noteq>x; N\<longrightarrow>\<^isub>a N'\<rbrakk> \<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^isub>a OrL (x).M (y).N' z"
| a_OrR1: "\<lbrakk>a\<sharp>b; M\<longrightarrow>\<^isub>a M'\<rbrakk> \<Longrightarrow> OrR1 <a>.M b \<longrightarrow>\<^isub>a OrR1 <a>.M' b"
| a_OrR2: "\<lbrakk>a\<sharp>b; M\<longrightarrow>\<^isub>a M'\<rbrakk> \<Longrightarrow> OrR2 <a>.M b \<longrightarrow>\<^isub>a OrR2 <a>.M' b"
| a_ImpL_l: "\<lbrakk>a\<sharp>N; x\<sharp>(M,y); M\<longrightarrow>\<^isub>a M'\<rbrakk> \<Longrightarrow> ImpL <a>.M (x).N y \<longrightarrow>\<^isub>a ImpL <a>.M' (x).N y"
| a_ImpL_r: "\<lbrakk>a\<sharp>N; x\<sharp>(M,y); N\<longrightarrow>\<^isub>a N'\<rbrakk> \<Longrightarrow> ImpL <a>.M (x).N y \<longrightarrow>\<^isub>a ImpL <a>.M (x).N' y"
| a_ImpR: "\<lbrakk>a\<sharp>b; M\<longrightarrow>\<^isub>a M'\<rbrakk> \<Longrightarrow> ImpR (x).<a>.M b \<longrightarrow>\<^isub>a ImpR (x).<a>.M' b"

lemma fresh_a_redu:
  fixes x::"name"
  and   c::"coname"
  shows "M \<longrightarrow>\<^isub>a M' \<Longrightarrow> x\<sharp>M \<Longrightarrow> x\<sharp>M'"
  and   "M \<longrightarrow>\<^isub>a M' \<Longrightarrow> c\<sharp>M \<Longrightarrow> c\<sharp>M'"
apply -
apply(induct rule: a_redu.induct)
apply(simp add: fresh_l_redu)
apply(simp add: fresh_c_redu)
apply(auto simp add: abs_fresh abs_supp fin_supp)
apply(induct rule: a_redu.induct)
apply(simp add: fresh_l_redu)
apply(simp add: fresh_c_redu)
apply(auto simp add: abs_fresh abs_supp fin_supp)
done

equivariance a_redu

nominal_inductive a_redu
  by (simp_all add: abs_fresh fresh_atm fresh_prod abs_supp fin_supp fresh_a_redu)

lemma better_CutL_intro[intro]:
  shows "M\<longrightarrow>\<^isub>a M' \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>a Cut <a>.M' (x).N"
proof -
  assume red: "M\<longrightarrow>\<^isub>a M'"
  obtain x'::"name"   where fs1: "x'\<sharp>(M,N,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.M (x).N =  Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N)"
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a  Cut <a'>.([(a',a)]\<bullet>M') (x').([(x',x)]\<bullet>N)" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt)
  also have "\<dots> = Cut <a>.M' (x).N" 
    using fs1 fs2 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_CutR_intro[intro]:
  shows "N\<longrightarrow>\<^isub>a N' \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>a Cut <a>.M (x).N'"
proof -
  assume red: "N\<longrightarrow>\<^isub>a N'"
  obtain x'::"name"   where fs1: "x'\<sharp>(M,N,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "Cut <a>.M (x).N =  Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N)"
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a  Cut <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N')" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt)
  also have "\<dots> = Cut <a>.M (x).N'" 
    using fs1 fs2 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed
    
lemma better_AndRL_intro[intro]:
  shows "M\<longrightarrow>\<^isub>a M' \<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^isub>a AndR <a>.M' <b>.N c"
proof -
  assume red: "M\<longrightarrow>\<^isub>a M'"
  obtain b'::"coname" where fs1: "b'\<sharp>(M,N,a,b,c)" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a,b,c,b')" by (rule exists_fresh(2), rule fin_supp, blast)
  have "AndR <a>.M <b>.N c =  AndR <a'>.([(a',a)]\<bullet>M) <b'>.([(b',b)]\<bullet>N) c"
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a  AndR <a'>.([(a',a)]\<bullet>M') <b'>.([(b',b)]\<bullet>N) c" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = AndR <a>.M' <b>.N c" 
    using fs1 fs2 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_AndRR_intro[intro]:
  shows "N\<longrightarrow>\<^isub>a N' \<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^isub>a AndR <a>.M <b>.N' c"
proof -
  assume red: "N\<longrightarrow>\<^isub>a N'"
  obtain b'::"coname" where fs1: "b'\<sharp>(M,N,a,b,c)" by (rule exists_fresh(2), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a,b,c,b')" by (rule exists_fresh(2), rule fin_supp, blast)
  have "AndR <a>.M <b>.N c =  AndR <a'>.([(a',a)]\<bullet>M) <b'>.([(b',b)]\<bullet>N) c"
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a  AndR <a'>.([(a',a)]\<bullet>M) <b'>.([(b',b)]\<bullet>N') c" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = AndR <a>.M <b>.N' c" 
    using fs1 fs2 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_AndL1_intro[intro]:
  shows "M\<longrightarrow>\<^isub>a M' \<Longrightarrow> AndL1 (x).M y \<longrightarrow>\<^isub>a AndL1 (x).M' y"
proof -
  assume red: "M\<longrightarrow>\<^isub>a M'"
  obtain x'::"name" where fs1: "x'\<sharp>(M,y,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  have "AndL1 (x).M y = AndL1 (x').([(x',x)]\<bullet>M) y"
    using fs1 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a AndL1 (x').([(x',x)]\<bullet>M') y" using fs1 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = AndL1 (x).M' y" 
    using fs1 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_AndL2_intro[intro]:
  shows "M\<longrightarrow>\<^isub>a M' \<Longrightarrow> AndL2 (x).M y \<longrightarrow>\<^isub>a AndL2 (x).M' y"
proof -
  assume red: "M\<longrightarrow>\<^isub>a M'"
  obtain x'::"name" where fs1: "x'\<sharp>(M,y,x)" by (rule exists_fresh(1), rule fin_supp, blast)
  have "AndL2 (x).M y = AndL2 (x').([(x',x)]\<bullet>M) y"
    using fs1 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a AndL2 (x').([(x',x)]\<bullet>M') y" using fs1 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = AndL2 (x).M' y" 
    using fs1 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_OrLL_intro[intro]:
  shows "M\<longrightarrow>\<^isub>a M' \<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^isub>a OrL (x).M' (y).N z"
proof -
  assume red: "M\<longrightarrow>\<^isub>a M'"
  obtain x'::"name" where fs1: "x'\<sharp>(M,N,x,y,z)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain y'::"name" where fs2: "y'\<sharp>(M,N,x,y,z,x')" by (rule exists_fresh(1), rule fin_supp, blast)
  have "OrL (x).M (y).N z =  OrL (x').([(x',x)]\<bullet>M) (y').([(y',y)]\<bullet>N) z"
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a OrL (x').([(x',x)]\<bullet>M') (y').([(y',y)]\<bullet>N) z" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = OrL (x).M' (y).N z" 
    using fs1 fs2 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_OrLR_intro[intro]:
  shows "N\<longrightarrow>\<^isub>a N' \<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^isub>a OrL (x).M (y).N' z"
proof -
  assume red: "N\<longrightarrow>\<^isub>a N'"
  obtain x'::"name" where fs1: "x'\<sharp>(M,N,x,y,z)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain y'::"name" where fs2: "y'\<sharp>(M,N,x,y,z,x')" by (rule exists_fresh(1), rule fin_supp, blast)
  have "OrL (x).M (y).N z =  OrL (x').([(x',x)]\<bullet>M) (y').([(y',y)]\<bullet>N) z"
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a OrL (x').([(x',x)]\<bullet>M) (y').([(y',y)]\<bullet>N') z" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = OrL (x).M (y).N' z" 
    using fs1 fs2 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_OrR1_intro[intro]:
  shows "M\<longrightarrow>\<^isub>a M' \<Longrightarrow> OrR1 <a>.M b \<longrightarrow>\<^isub>a OrR1 <a>.M' b"
proof -
  assume red: "M\<longrightarrow>\<^isub>a M'"
  obtain a'::"coname" where fs1: "a'\<sharp>(M,b,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "OrR1 <a>.M b = OrR1 <a'>.([(a',a)]\<bullet>M) b"
    using fs1 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a OrR1 <a'>.([(a',a)]\<bullet>M') b" using fs1 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = OrR1 <a>.M' b" 
    using fs1 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_OrR2_intro[intro]:
  shows "M\<longrightarrow>\<^isub>a M' \<Longrightarrow> OrR2 <a>.M b \<longrightarrow>\<^isub>a OrR2 <a>.M' b"
proof -
  assume red: "M\<longrightarrow>\<^isub>a M'"
  obtain a'::"coname" where fs1: "a'\<sharp>(M,b,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "OrR2 <a>.M b = OrR2 <a'>.([(a',a)]\<bullet>M) b"
    using fs1 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a OrR2 <a'>.([(a',a)]\<bullet>M') b" using fs1 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = OrR2 <a>.M' b" 
    using fs1 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_ImpLL_intro[intro]:
  shows "M\<longrightarrow>\<^isub>a M' \<Longrightarrow> ImpL <a>.M (x).N y \<longrightarrow>\<^isub>a ImpL <a>.M' (x).N y"
proof -
  assume red: "M\<longrightarrow>\<^isub>a M'"
  obtain x'::"name"   where fs1: "x'\<sharp>(M,N,x,y)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "ImpL <a>.M (x).N y =  ImpL <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N) y"
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a  ImpL <a'>.([(a',a)]\<bullet>M') (x').([(x',x)]\<bullet>N) y" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = ImpL <a>.M' (x).N y" 
    using fs1 fs2 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_ImpLR_intro[intro]:
  shows "N\<longrightarrow>\<^isub>a N' \<Longrightarrow> ImpL <a>.M (x).N y \<longrightarrow>\<^isub>a ImpL <a>.M (x).N' y"
proof -
  assume red: "N\<longrightarrow>\<^isub>a N'"
  obtain x'::"name"   where fs1: "x'\<sharp>(M,N,x,y)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain a'::"coname" where fs2: "a'\<sharp>(M,N,a)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "ImpL <a>.M (x).N y =  ImpL <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N) y"
    using fs1 fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a  ImpL <a'>.([(a',a)]\<bullet>M) (x').([(x',x)]\<bullet>N') y" using fs1 fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = ImpL <a>.M (x).N' y" 
    using fs1 fs2 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

lemma better_ImpR_intro[intro]:
  shows "M\<longrightarrow>\<^isub>a M' \<Longrightarrow> ImpR (x).<a>.M b \<longrightarrow>\<^isub>a ImpR (x).<a>.M' b"
proof -
  assume red: "M\<longrightarrow>\<^isub>a M'"
  obtain a'::"coname" where fs2: "a'\<sharp>(M,a,b)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "ImpR (x).<a>.M b = ImpR (x).<a'>.([(a',a)]\<bullet>M) b"
    using fs2 by (rule_tac sym, auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a ImpR (x).<a'>.([(a',a)]\<bullet>M') b" using fs2 red
    by (auto intro: a_redu.intros simp add: fresh_left calc_atm a_redu.eqvt fresh_atm fresh_prod)
  also have "\<dots> = ImpR (x).<a>.M' b" 
    using fs2 red by (auto simp add: trm.inject alpha fresh_atm fresh_prod calc_atm fresh_a_redu)
  finally show ?thesis by simp
qed

text {* axioms do not reduce *}

lemma ax_do_not_l_reduce:
  shows "Ax x a \<longrightarrow>\<^isub>l M \<Longrightarrow> False"
by (erule_tac l_redu.cases) (simp_all add: trm.inject)
 
lemma ax_do_not_c_reduce:
  shows "Ax x a \<longrightarrow>\<^isub>c M \<Longrightarrow> False"
by (erule_tac c_redu.cases) (simp_all add: trm.inject)

lemma ax_do_not_a_reduce:
  shows "Ax x a \<longrightarrow>\<^isub>a M \<Longrightarrow> False"
apply(erule_tac a_redu.cases) 
apply(auto simp add: trm.inject)
apply(drule ax_do_not_l_reduce)
apply(simp)
apply(drule ax_do_not_c_reduce)
apply(simp)
done

lemma a_redu_NotL_elim:
  assumes a: "NotL <a>.M x \<longrightarrow>\<^isub>a R"
  shows "\<exists>M'. R = NotL <a>.M' x \<and> M\<longrightarrow>\<^isub>aM'"
using a
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto)
apply(rotate_tac 1)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto simp add: alpha a_redu.eqvt)
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)
apply(simp add: perm_swap)
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)
apply(simp add: perm_swap)
done

lemma a_redu_NotR_elim:
  assumes a: "NotR (x).M a \<longrightarrow>\<^isub>a R"
  shows "\<exists>M'. R = NotR (x).M' a \<and> M\<longrightarrow>\<^isub>aM'"
using a
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto)
apply(rotate_tac 1)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto simp add: alpha a_redu.eqvt)
apply(rule_tac x="([(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)
apply(simp add: perm_swap)
apply(rule_tac x="([(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)
apply(simp add: perm_swap)
done

lemma a_redu_AndR_elim:
  assumes a: "AndR <a>.M <b>.N c\<longrightarrow>\<^isub>a R"
  shows "(\<exists>M'. R = AndR <a>.M' <b>.N c \<and> M\<longrightarrow>\<^isub>aM') \<or> (\<exists>N'. R = AndR <a>.M <b>.N' c \<and> N\<longrightarrow>\<^isub>aN')"
using a
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(rotate_tac 6)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(rule disjI1)
apply(auto simp add: alpha a_redu.eqvt)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI) 
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule disjI2)
apply(auto simp add: alpha a_redu.eqvt)[1]
apply(rule_tac x="([(b,ba)]\<bullet>N')" in exI) 
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,baa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,ba)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,baa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,ba)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,baa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,ba)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,baa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rotate_tac 6)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(rule disjI1)
apply(auto simp add: alpha a_redu.eqvt)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M')" in exI) 
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule disjI2)
apply(auto simp add: alpha a_redu.eqvt)[1]
apply(rule_tac x="([(b,ba)]\<bullet>N'a)" in exI) 
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,ba)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,ba)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,ba)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,baa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,baa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,baa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(b,baa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
done

lemma a_redu_AndL1_elim:
  assumes a: "AndL1 (x).M y \<longrightarrow>\<^isub>a R"
  shows "\<exists>M'. R = AndL1 (x).M' y \<and> M\<longrightarrow>\<^isub>aM'"
using a
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto)
apply(rotate_tac 2)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto simp add: alpha a_redu.eqvt)
apply(rule_tac x="([(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)
apply(simp add: perm_swap)
apply(rule_tac x="([(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)
apply(simp add: perm_swap)
done

lemma a_redu_AndL2_elim:
  assumes a: "AndL2 (x).M y \<longrightarrow>\<^isub>a R"
  shows "\<exists>M'. R = AndL2 (x).M' y \<and> M\<longrightarrow>\<^isub>aM'"
using a
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto)
apply(rotate_tac 2)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto simp add: alpha a_redu.eqvt)
apply(rule_tac x="([(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)
apply(simp add: perm_swap)
apply(rule_tac x="([(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)
apply(simp add: perm_swap)
done

lemma a_redu_OrL_elim:
  assumes a: "OrL (x).M (y).N z\<longrightarrow>\<^isub>a R"
  shows "(\<exists>M'. R = OrL (x).M' (y).N z \<and> M\<longrightarrow>\<^isub>aM') \<or> (\<exists>N'. R = OrL (x).M (y).N' z \<and> N\<longrightarrow>\<^isub>aN')"
using a
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(rotate_tac 6)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(rule disjI1)
apply(auto simp add: alpha a_redu.eqvt)[1]
apply(rule_tac x="([(x,xa)]\<bullet>M'a)" in exI) 
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule disjI2)
apply(auto simp add: alpha a_redu.eqvt)[1]
apply(rule_tac x="([(y,ya)]\<bullet>N')" in exI) 
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,yaa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,ya)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,yaa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,ya)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,yaa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,ya)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,yaa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rotate_tac 6)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(rule disjI1)
apply(auto simp add: alpha a_redu.eqvt)[1]
apply(rule_tac x="([(x,xa)]\<bullet>M')" in exI) 
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xaa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xaa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xaa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(x,xaa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule disjI2)
apply(auto simp add: alpha a_redu.eqvt)[1]
apply(rule_tac x="([(y,ya)]\<bullet>N'a)" in exI) 
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,ya)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,ya)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,ya)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,yaa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,yaa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,yaa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,yaa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
done

lemma a_redu_OrR1_elim:
  assumes a: "OrR1 <a>.M b \<longrightarrow>\<^isub>a R"
  shows "\<exists>M'. R = OrR1 <a>.M' b \<and> M\<longrightarrow>\<^isub>aM'"
using a
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto)
apply(rotate_tac 2)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto simp add: alpha a_redu.eqvt)
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)
apply(simp add: perm_swap)
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)
apply(simp add: perm_swap)
done

lemma a_redu_OrR2_elim:
  assumes a: "OrR2 <a>.M b \<longrightarrow>\<^isub>a R"
  shows "\<exists>M'. R = OrR2 <a>.M' b \<and> M\<longrightarrow>\<^isub>aM'"
using a
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto)
apply(rotate_tac 2)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto simp add: alpha a_redu.eqvt)
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)
apply(simp add: perm_swap)
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)
apply(simp add: perm_swap)
done

lemma a_redu_ImpL_elim:
  assumes a: "ImpL <a>.M (y).N z\<longrightarrow>\<^isub>a R"
  shows "(\<exists>M'. R = ImpL <a>.M' (y).N z \<and> M\<longrightarrow>\<^isub>aM') \<or> (\<exists>N'. R = ImpL <a>.M (y).N' z \<and> N\<longrightarrow>\<^isub>aN')"
using a
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(rotate_tac 5)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(rule disjI1)
apply(auto simp add: alpha a_redu.eqvt)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI) 
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule disjI2)
apply(auto simp add: alpha a_redu.eqvt)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N')" in exI) 
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rotate_tac 5)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(rule disjI1)
apply(auto simp add: alpha a_redu.eqvt)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M')" in exI) 
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(a,aaa)]\<bullet>M')" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule disjI2)
apply(auto simp add: alpha a_redu.eqvt)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N'a)" in exI) 
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
apply(rule_tac x="([(y,xa)]\<bullet>N'a)" in exI)
apply(auto simp add: perm_swap fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu)[1]
done

lemma a_redu_ImpR_elim:
  assumes a: "ImpR (x).<a>.M b \<longrightarrow>\<^isub>a R"
  shows "\<exists>M'. R = ImpR (x).<a>.M' b \<and> M\<longrightarrow>\<^isub>aM'"
using a
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto)
apply(rotate_tac 2)
apply(erule_tac a_redu.cases, simp_all add: trm.inject)
apply(erule_tac l_redu.cases, simp_all add: trm.inject)
apply(erule_tac c_redu.cases, simp_all add: trm.inject)
apply(auto simp add: alpha a_redu.eqvt abs_perm abs_fresh)
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(a,aa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(a,aaa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(a,aa)]\<bullet>[(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule sym)
apply(rule trans)
apply(rule perm_compose)
apply(simp add: calc_atm perm_swap)
apply(rule_tac x="([(a,aaa)]\<bullet>[(x,xa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule sym)
apply(rule trans)
apply(rule perm_compose)
apply(simp add: calc_atm perm_swap)
apply(rule_tac x="([(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule_tac x="([(a,aa)]\<bullet>[(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule sym)
apply(rule trans)
apply(rule perm_compose)
apply(simp add: calc_atm perm_swap)
apply(rule_tac x="([(a,aaa)]\<bullet>[(x,xaa)]\<bullet>M'a)" in exI)
apply(auto simp add: fresh_left alpha a_redu.eqvt calc_atm fresh_a_redu perm_swap)
apply(rule sym)
apply(rule trans)
apply(rule perm_compose)
apply(simp add: calc_atm perm_swap)
done

text {* Transitive Closure*}

abbreviation
 a_star_redu :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<longrightarrow>\<^isub>a* _" [100,100] 100)
where
  "M \<longrightarrow>\<^isub>a* M' \<equiv> (a_redu)^** M M'"

lemma a_starI:
  assumes a: "M \<longrightarrow>\<^isub>a M'"
  shows "M \<longrightarrow>\<^isub>a* M'"
using a by blast

lemma a_starE:
  assumes a: "M \<longrightarrow>\<^isub>a* M'"
  shows "M = M' \<or> (\<exists>N. M \<longrightarrow>\<^isub>a N \<and> N \<longrightarrow>\<^isub>a* M')"
using a 
by (induct) (auto)

lemma a_star_refl:
  shows "M \<longrightarrow>\<^isub>a* M"
  by blast

lemma a_star_trans[trans]:
  assumes a1: "M1\<longrightarrow>\<^isub>a* M2"
  and     a2: "M2\<longrightarrow>\<^isub>a* M3"
  shows "M1 \<longrightarrow>\<^isub>a* M3"
using a2 a1
by (induct) (auto)

text {* congruence rules for \<longrightarrow>\<^isub>a* *}

lemma ax_do_not_a_star_reduce:
  shows "Ax x a \<longrightarrow>\<^isub>a* M \<Longrightarrow> M = Ax x a"
apply(induct set: rtranclp)
apply(auto)
apply(drule  ax_do_not_a_reduce)
apply(simp)
done


lemma a_star_CutL:
    "M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>a* Cut <a>.M' (x).N"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_CutR:
    "N \<longrightarrow>\<^isub>a* N'\<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>a* Cut <a>.M (x).N'"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_Cut:
    "\<lbrakk>M \<longrightarrow>\<^isub>a* M'; N \<longrightarrow>\<^isub>a* N'\<rbrakk> \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>a* Cut <a>.M' (x).N'"
by (blast intro!: a_star_CutL a_star_CutR intro: rtranclp_trans)

lemma a_star_NotR:
    "M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> NotR (x).M a \<longrightarrow>\<^isub>a* NotR (x).M' a"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_NotL:
    "M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> NotL <a>.M x \<longrightarrow>\<^isub>a* NotL <a>.M' x"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_AndRL:
    "M \<longrightarrow>\<^isub>a* M'\<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^isub>a* AndR <a>.M' <b>.N c"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_AndRR:
    "N \<longrightarrow>\<^isub>a* N'\<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^isub>a* AndR <a>.M <b>.N' c"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_AndR:
    "\<lbrakk>M \<longrightarrow>\<^isub>a* M'; N \<longrightarrow>\<^isub>a* N'\<rbrakk> \<Longrightarrow> AndR <a>.M <b>.N c \<longrightarrow>\<^isub>a* AndR <a>.M' <b>.N' c"
by (blast intro!: a_star_AndRL a_star_AndRR intro: rtranclp_trans)

lemma a_star_AndL1:
    "M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> AndL1 (x).M y \<longrightarrow>\<^isub>a* AndL1 (x).M' y"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_AndL2:
    "M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> AndL2 (x).M y \<longrightarrow>\<^isub>a* AndL2 (x).M' y"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_OrLL:
    "M \<longrightarrow>\<^isub>a* M'\<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^isub>a* OrL (x).M' (y).N z"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_OrLR:
    "N \<longrightarrow>\<^isub>a* N'\<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^isub>a* OrL (x).M (y).N' z"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_OrL:
    "\<lbrakk>M \<longrightarrow>\<^isub>a* M'; N \<longrightarrow>\<^isub>a* N'\<rbrakk> \<Longrightarrow> OrL (x).M (y).N z \<longrightarrow>\<^isub>a* OrL (x).M' (y).N' z"
by (blast intro!: a_star_OrLL a_star_OrLR intro: rtranclp_trans)

lemma a_star_OrR1:
    "M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> OrR1 <a>.M b \<longrightarrow>\<^isub>a* OrR1 <a>.M' b"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_OrR2:
    "M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> OrR2 <a>.M b \<longrightarrow>\<^isub>a* OrR2 <a>.M' b"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_ImpLL:
    "M \<longrightarrow>\<^isub>a* M'\<Longrightarrow> ImpL <a>.M (y).N z \<longrightarrow>\<^isub>a* ImpL <a>.M' (y).N z"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_ImpLR:
    "N \<longrightarrow>\<^isub>a* N'\<Longrightarrow> ImpL <a>.M (y).N z \<longrightarrow>\<^isub>a* ImpL <a>.M (y).N' z"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma a_star_ImpL:
    "\<lbrakk>M \<longrightarrow>\<^isub>a* M'; N \<longrightarrow>\<^isub>a* N'\<rbrakk> \<Longrightarrow> ImpL <a>.M (y).N z \<longrightarrow>\<^isub>a* ImpL <a>.M' (y).N' z"
by (blast intro!: a_star_ImpLL a_star_ImpLR intro: rtranclp_trans)

lemma a_star_ImpR:
    "M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> ImpR (x).<a>.M b \<longrightarrow>\<^isub>a* ImpR (x).<a>.M' b"
by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemmas a_star_congs = a_star_Cut a_star_NotR a_star_NotL a_star_AndR a_star_AndL1 a_star_AndL2
                      a_star_OrL a_star_OrR1 a_star_OrR2 a_star_ImpL a_star_ImpR

lemma a_star_redu_NotL_elim:
  assumes a: "NotL <a>.M x \<longrightarrow>\<^isub>a* R"
  shows "\<exists>M'. R = NotL <a>.M' x \<and> M \<longrightarrow>\<^isub>a* M'"
using a
apply(induct set: rtranclp)
apply(auto)
apply(drule a_redu_NotL_elim)
apply(auto)
done

lemma a_star_redu_NotR_elim:
  assumes a: "NotR (x).M a \<longrightarrow>\<^isub>a* R"
  shows "\<exists>M'. R = NotR (x).M' a \<and> M \<longrightarrow>\<^isub>a* M'"
using a
apply(induct set: rtranclp)
apply(auto)
apply(drule a_redu_NotR_elim)
apply(auto)
done

lemma a_star_redu_AndR_elim:
  assumes a: "AndR <a>.M <b>.N c\<longrightarrow>\<^isub>a* R"
  shows "(\<exists>M' N'. R = AndR <a>.M' <b>.N' c \<and> M \<longrightarrow>\<^isub>a* M' \<and> N \<longrightarrow>\<^isub>a* N')"
using a
apply(induct set: rtranclp)
apply(auto)
apply(drule a_redu_AndR_elim)
apply(auto simp add: alpha trm.inject)
done

lemma a_star_redu_AndL1_elim:
  assumes a: "AndL1 (x).M y \<longrightarrow>\<^isub>a* R"
  shows "\<exists>M'. R = AndL1 (x).M' y \<and> M \<longrightarrow>\<^isub>a* M'"
using a
apply(induct set: rtranclp)
apply(auto)
apply(drule a_redu_AndL1_elim)
apply(auto simp add: alpha trm.inject)
done

lemma a_star_redu_AndL2_elim:
  assumes a: "AndL2 (x).M y \<longrightarrow>\<^isub>a* R"
  shows "\<exists>M'. R = AndL2 (x).M' y \<and> M \<longrightarrow>\<^isub>a* M'"
using a
apply(induct set: rtranclp)
apply(auto)
apply(drule a_redu_AndL2_elim)
apply(auto simp add: alpha trm.inject)
done

lemma a_star_redu_OrL_elim:
  assumes a: "OrL (x).M (y).N z \<longrightarrow>\<^isub>a* R"
  shows "(\<exists>M' N'. R = OrL (x).M' (y).N' z \<and> M \<longrightarrow>\<^isub>a* M' \<and> N \<longrightarrow>\<^isub>a* N')"
using a
apply(induct set: rtranclp)
apply(auto)
apply(drule a_redu_OrL_elim)
apply(auto simp add: alpha trm.inject)
done

lemma a_star_redu_OrR1_elim:
  assumes a: "OrR1 <a>.M y \<longrightarrow>\<^isub>a* R"
  shows "\<exists>M'. R = OrR1 <a>.M' y \<and> M \<longrightarrow>\<^isub>a* M'"
using a
apply(induct set: rtranclp)
apply(auto)
apply(drule a_redu_OrR1_elim)
apply(auto simp add: alpha trm.inject)
done

lemma a_star_redu_OrR2_elim:
  assumes a: "OrR2 <a>.M y \<longrightarrow>\<^isub>a* R"
  shows "\<exists>M'. R = OrR2 <a>.M' y \<and> M \<longrightarrow>\<^isub>a* M'"
using a
apply(induct set: rtranclp)
apply(auto)
apply(drule a_redu_OrR2_elim)
apply(auto simp add: alpha trm.inject)
done

lemma a_star_redu_ImpR_elim:
  assumes a: "ImpR (x).<a>.M y \<longrightarrow>\<^isub>a* R"
  shows "\<exists>M'. R = ImpR (x).<a>.M' y \<and> M \<longrightarrow>\<^isub>a* M'"
using a
apply(induct set: rtranclp)
apply(auto)
apply(drule a_redu_ImpR_elim)
apply(auto simp add: alpha trm.inject)
done

lemma a_star_redu_ImpL_elim:
  assumes a: "ImpL <a>.M (y).N z \<longrightarrow>\<^isub>a* R"
  shows "(\<exists>M' N'. R = ImpL <a>.M' (y).N' z \<and> M \<longrightarrow>\<^isub>a* M' \<and> N \<longrightarrow>\<^isub>a* N')"
using a
apply(induct set: rtranclp)
apply(auto)
apply(drule a_redu_ImpL_elim)
apply(auto simp add: alpha trm.inject)
done

text {* Substitution *}

lemma subst_not_fin1:
  shows "\<not>fin(M{x:=<c>.P}) x"
apply(nominal_induct M avoiding: x c P rule: trm.strong_induct)
apply(auto)
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(erule fin.cases, simp_all add: trm.inject)
apply(erule fin.cases, simp_all add: trm.inject)
apply(erule fin.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<c>.P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(erule fin.cases, simp_all add: trm.inject)
apply(erule fin.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(erule fin.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<c>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(erule fin.cases, simp_all add: trm.inject)
apply(erule fin.cases, simp_all add: trm.inject)
apply(erule fin.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{x:=<c>.P},P,name1,trm2{x:=<c>.P},name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(erule fin.cases, simp_all add: trm.inject)
apply(erule fin.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<c>.P},P,name1,trm2{name2:=<c>.P})")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL)
apply(erule fin.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(erule fin.cases, simp_all add: trm.inject)
done

lemma subst_not_fin2:
  assumes a: "\<not>fin M y"
  shows "\<not>fin(M{c:=(x).P}) y" 
using a
apply(nominal_induct M avoiding: x c P y rule: trm.strong_induct)
apply(auto)
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(trm{coname:=(x).P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR)
apply(drule fin_elims, simp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(auto)[1]
apply(drule freshn_after_substc)
apply(simp add: fin.intros)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(trm1{coname3:=(x).P},P,coname1,trm2{coname3:=(x).P},coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR)
apply(drule fin_elims, simp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshn_after_substc)
apply(simp add: fin.intros abs_fresh)
apply(drule fin_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshn_after_substc)
apply(simp add: fin.intros abs_fresh)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1)
apply(drule fin_elims, simp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(drule fin_elims, simp)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2)
apply(drule fin_elims, simp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshn_after_substc)
apply(drule freshn_after_substc)
apply(simp add: fin.intros abs_fresh)
apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(trm{coname2:=(x).P},P,coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR)
apply(drule fin_elims, simp)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(drule fin_elims, simp)
apply(drule fin_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshn_after_substc)
apply(drule freshn_after_substc)
apply(simp add: fin.intros abs_fresh)
done

lemma subst_not_fic1:
  shows "\<not>fic (M{a:=(x).P}) a"
apply(nominal_induct M avoiding: a x P rule: trm.strong_induct)
apply(auto)
apply(erule fic.cases, simp_all add: trm.inject)
apply(erule fic.cases, simp_all add: trm.inject)
apply(erule fic.cases, simp_all add: trm.inject)
apply(erule fic.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(trm{coname:=(x).P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR)
apply(erule fic.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(erule fic.cases, simp_all add: trm.inject)
apply(erule fic.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(trm1{coname3:=(x).P},P,trm2{coname3:=(x).P},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR)
apply(erule fic.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(erule fic.cases, simp_all add: trm.inject)
apply(erule fic.cases, simp_all add: trm.inject)
apply(erule fic.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1)
apply(erule fic.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(erule fic.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2)
apply(erule fic.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(erule fic.cases, simp_all add: trm.inject)
apply(erule fic.cases, simp_all add: trm.inject)
apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(trm{coname2:=(x).P},P,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR)
apply(erule fic.cases, simp_all add: trm.inject)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(erule fic.cases, simp_all add: trm.inject)
apply(erule fic.cases, simp_all add: trm.inject)
done

lemma subst_not_fic2:
  assumes a: "\<not>fic M a"
  shows "\<not>fic(M{x:=<b>.P}) a" 
using a
apply(nominal_induct M avoiding: x a P b rule: trm.strong_induct)
apply(auto)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(auto)[1]
apply(drule freshc_after_substn)
apply(simp add: fic.intros)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<b>.P},P)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshc_after_substn)
apply(drule freshc_after_substn)
apply(simp add: fic.intros abs_fresh)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<b>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fic_elims, simp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<b>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshc_after_substn)
apply(simp add: fic.intros abs_fresh)
apply(drule fic_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshc_after_substn)
apply(simp add: fic.intros abs_fresh)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{x:=<b>.P},P,name1,trm2{x:=<b>.P},name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fic_elims, simp)
apply(drule fic_elims, simp)
apply(auto)[1]
apply(simp add: abs_fresh fresh_atm)
apply(drule freshc_after_substn)
apply(simp add: fic.intros abs_fresh)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<b>.P},trm2{name2:=<b>.P},P,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL)
apply(drule fic_elims, simp)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(drule fic_elims, simp)
done

text {* Reductions *}

lemma fin_l_reduce:
  assumes  a: "fin M x"
  and      b: "M \<longrightarrow>\<^isub>l M'"
  shows "fin M' x"
using b a
apply(induct)
apply(erule fin.cases)
apply(simp_all add: trm.inject)
apply(rotate_tac 3)
apply(erule fin.cases)
apply(simp_all add: trm.inject)
apply(erule fin.cases, simp_all add: trm.inject)+
done

lemma fin_c_reduce:
  assumes  a: "fin M x"
  and      b: "M \<longrightarrow>\<^isub>c M'"
  shows "fin M' x"
using b a
apply(induct)
apply(erule fin.cases, simp_all add: trm.inject)+
done

lemma fin_a_reduce:
  assumes  a: "fin M x"
  and      b: "M \<longrightarrow>\<^isub>a M'"
  shows "fin M' x"
using a b
apply(induct)
apply(drule ax_do_not_a_reduce)
apply(simp)
apply(drule a_redu_NotL_elim)
apply(auto)
apply(rule fin.intros)
apply(simp add: fresh_a_redu)
apply(drule a_redu_AndL1_elim)
apply(auto)
apply(rule fin.intros)
apply(force simp add: abs_fresh fresh_a_redu)
apply(drule a_redu_AndL2_elim)
apply(auto)
apply(rule fin.intros)
apply(force simp add: abs_fresh fresh_a_redu)
apply(drule a_redu_OrL_elim)
apply(auto)
apply(rule fin.intros)
apply(force simp add: abs_fresh fresh_a_redu)
apply(force simp add: abs_fresh fresh_a_redu)
apply(rule fin.intros)
apply(force simp add: abs_fresh fresh_a_redu)
apply(force simp add: abs_fresh fresh_a_redu)
apply(drule a_redu_ImpL_elim)
apply(auto)
apply(rule fin.intros)
apply(force simp add: abs_fresh fresh_a_redu)
apply(force simp add: abs_fresh fresh_a_redu)
apply(rule fin.intros)
apply(force simp add: abs_fresh fresh_a_redu)
apply(force simp add: abs_fresh fresh_a_redu)
done

lemma fin_a_star_reduce:
  assumes  a: "fin M x"
  and      b: "M \<longrightarrow>\<^isub>a* M'"
  shows "fin M' x"
using b a
apply(induct set: rtranclp)
apply(auto simp add: fin_a_reduce)
done

lemma fic_l_reduce:
  assumes  a: "fic M x"
  and      b: "M \<longrightarrow>\<^isub>l M'"
  shows "fic M' x"
using b a
apply(induct)
apply(erule fic.cases)
apply(simp_all add: trm.inject)
apply(rotate_tac 3)
apply(erule fic.cases)
apply(simp_all add: trm.inject)
apply(erule fic.cases, simp_all add: trm.inject)+
done

lemma fic_c_reduce:
  assumes a: "fic M x"
  and     b: "M \<longrightarrow>\<^isub>c M'"
  shows "fic M' x"
using b a
apply(induct)
apply(erule fic.cases, simp_all add: trm.inject)+
done

lemma fic_a_reduce:
  assumes a: "fic M x"
  and     b: "M \<longrightarrow>\<^isub>a M'"
  shows "fic M' x"
using a b
apply(induct)
apply(drule ax_do_not_a_reduce)
apply(simp)
apply(drule a_redu_NotR_elim)
apply(auto)
apply(rule fic.intros)
apply(simp add: fresh_a_redu)
apply(drule a_redu_AndR_elim)
apply(auto)
apply(rule fic.intros)
apply(force simp add: abs_fresh fresh_a_redu)
apply(force simp add: abs_fresh fresh_a_redu)
apply(rule fic.intros)
apply(force simp add: abs_fresh fresh_a_redu)
apply(force simp add: abs_fresh fresh_a_redu)
apply(drule a_redu_OrR1_elim)
apply(auto)
apply(rule fic.intros)
apply(force simp add: abs_fresh fresh_a_redu)
apply(drule a_redu_OrR2_elim)
apply(auto)
apply(rule fic.intros)
apply(force simp add: abs_fresh fresh_a_redu)
apply(drule a_redu_ImpR_elim)
apply(auto)
apply(rule fic.intros)
apply(force simp add: abs_fresh fresh_a_redu)
done

lemma fic_a_star_reduce:
  assumes  a: "fic M x"
  and      b: "M \<longrightarrow>\<^isub>a* M'"
  shows "fic M' x"
using b a
apply(induct set: rtranclp)
apply(auto simp add: fic_a_reduce)
done

text {* substitution properties *}

lemma subst_with_ax1:
  shows "M{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* M[x\<turnstile>n>y]"
proof(nominal_induct M avoiding: x a y rule: trm.strong_induct)
  case (Ax z b x a y)
  show "(Ax z b){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (Ax z b)[x\<turnstile>n>y]"
  proof (cases "z=x")
    case True
    assume eq: "z=x"
    have "(Ax z b){x:=<a>.Ax y a} = Cut <a>.Ax y a (x).Ax x b" using eq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* (Ax x b)[x\<turnstile>n>y]" by blast
    finally show "Ax z b{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (Ax z b)[x\<turnstile>n>y]" using eq by simp
  next
    case False
    assume neq: "z\<noteq>x"
    then show "(Ax z b){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (Ax z b)[x\<turnstile>n>y]" using neq by simp
  qed
next
  case (Cut b M z N x a y)
  have fs: "b\<sharp>x" "b\<sharp>a" "b\<sharp>y" "b\<sharp>N" "z\<sharp>x" "z\<sharp>a" "z\<sharp>y" "z\<sharp>M" by fact+
  have ih1: "M{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* M[x\<turnstile>n>y]" by fact
  have ih2: "N{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* N[x\<turnstile>n>y]" by fact
  show "(Cut <b>.M (z).N){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (Cut <b>.M (z).N)[x\<turnstile>n>y]"
  proof (cases "M = Ax x b")
    case True
    assume eq: "M = Ax x b"
    have "(Cut <b>.M (z).N){x:=<a>.Ax y a} = Cut <a>.Ax y a (z).(N{x:=<a>.Ax y a})" using fs eq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.Ax y a (z).(N[x\<turnstile>n>y])" using ih2 a_star_congs by blast
    also have "\<dots> = Cut <b>.(M[x\<turnstile>n>y]) (z).(N[x\<turnstile>n>y])" using eq
      by (simp add: trm.inject alpha calc_atm fresh_atm)
    finally show "(Cut <b>.M (z).N){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (Cut <b>.M (z).N)[x\<turnstile>n>y]" using fs by simp
  next
    case False
    assume neq: "M \<noteq> Ax x b"
    have "(Cut <b>.M (z).N){x:=<a>.Ax y a} = Cut <b>.(M{x:=<a>.Ax y a}) (z).(N{x:=<a>.Ax y a})" 
      using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* Cut <b>.(M[x\<turnstile>n>y]) (z).(N[x\<turnstile>n>y])" using ih1 ih2 a_star_congs by blast
    finally show "(Cut <b>.M (z).N){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (Cut <b>.M (z).N)[x\<turnstile>n>y]" using fs by simp
  qed
next
  case (NotR z M b x a y)
  have fs: "z\<sharp>x" "z\<sharp>a" "z\<sharp>y" "z\<sharp>b" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* M[x\<turnstile>n>y]" by fact
  have "(NotR (z).M b){x:=<a>.Ax y a} = NotR (z).(M{x:=<a>.Ax y a}) b" using fs by simp
  also have "\<dots> \<longrightarrow>\<^isub>a* NotR (z).(M[x\<turnstile>n>y]) b" using ih by (auto intro: a_star_congs)
  finally show "(NotR (z).M b){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (NotR (z).M b)[x\<turnstile>n>y]" using fs by simp
next
  case (NotL b M z x a y)  
  have fs: "b\<sharp>x" "b\<sharp>a" "b\<sharp>y" "b\<sharp>z" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* M[x\<turnstile>n>y]" by fact
  show "(NotL <b>.M z){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (NotL <b>.M z)[x\<turnstile>n>y]"
  proof(cases "z=x")
    case True
    assume eq: "z=x"
    obtain x'::"name" where new: "x'\<sharp>(Ax y a,M{x:=<a>.Ax y a})" by (rule exists_fresh(1)[OF fs_name1])
    have "(NotL <b>.M z){x:=<a>.Ax y a} = 
                        fresh_fun (\<lambda>x'. Cut <a>.Ax y a (x').NotL <b>.(M{x:=<a>.Ax y a}) x')"
      using eq fs by simp
    also have "\<dots> = Cut <a>.Ax y a (x').NotL <b>.(M{x:=<a>.Ax y a}) x'" 
      using new by (simp add: fresh_fun_simp_NotL fresh_prod)
    also have "\<dots> \<longrightarrow>\<^isub>a* (NotL <b>.(M{x:=<a>.Ax y a}) x')[x'\<turnstile>n>y]"
      using new 
      apply(rule_tac a_starI)
      apply(rule al_redu)
      apply(rule better_LAxL_intro)
      apply(auto)
      done
    also have "\<dots> = NotL <b>.(M{x:=<a>.Ax y a}) y" using new by (simp add: nrename_fresh)
    also have "\<dots> \<longrightarrow>\<^isub>a* NotL <b>.(M[x\<turnstile>n>y]) y" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (NotL <b>.M z)[x\<turnstile>n>y]" using eq by simp
    finally show "(NotL <b>.M z){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (NotL <b>.M z)[x\<turnstile>n>y]" by simp
  next
    case False
    assume neq: "z\<noteq>x"
    have "(NotL <b>.M z){x:=<a>.Ax y a} = NotL <b>.(M{x:=<a>.Ax y a}) z" using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* NotL <b>.(M[x\<turnstile>n>y]) z" using ih by (auto intro: a_star_congs)
    finally show "(NotL <b>.M z){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (NotL <b>.M z)[x\<turnstile>n>y]" using neq by simp
  qed
next
  case (AndR c M d N e x a y)
  have fs: "c\<sharp>x" "c\<sharp>a" "c\<sharp>y" "d\<sharp>x" "d\<sharp>a" "d\<sharp>y" "d\<noteq>c" "c\<sharp>N" "c\<sharp>e" "d\<sharp>M" "d\<sharp>e" by fact+
  have ih1: "M{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* M[x\<turnstile>n>y]" by fact
  have ih2: "N{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* N[x\<turnstile>n>y]" by fact
  have "(AndR <c>.M <d>.N e){x:=<a>.Ax y a} = AndR <c>.(M{x:=<a>.Ax y a}) <d>.(N{x:=<a>.Ax y a}) e"
    using fs by simp
  also have "\<dots> \<longrightarrow>\<^isub>a* AndR <c>.(M[x\<turnstile>n>y]) <d>.(N[x\<turnstile>n>y]) e" using ih1 ih2 by (auto intro: a_star_congs)
  finally show "(AndR <c>.M <d>.N e){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (AndR <c>.M <d>.N e)[x\<turnstile>n>y]"
    using fs by simp
next
  case (AndL1 u M v x a y)
  have fs: "u\<sharp>x" "u\<sharp>a" "u\<sharp>y" "u\<sharp>v" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* M[x\<turnstile>n>y]" by fact
  show "(AndL1 (u).M v){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (AndL1 (u).M v)[x\<turnstile>n>y]"
  proof(cases "v=x")
    case True
    assume eq: "v=x"
    obtain v'::"name" where new: "v'\<sharp>(Ax y a,M{x:=<a>.Ax y a},u)" by (rule exists_fresh(1)[OF fs_name1])
    have "(AndL1 (u).M v){x:=<a>.Ax y a} = 
                        fresh_fun (\<lambda>v'. Cut <a>.Ax y a (v').AndL1 (u).(M{x:=<a>.Ax y a}) v')"
      using eq fs by simp
    also have "\<dots> = Cut <a>.Ax y a (v').AndL1 (u).(M{x:=<a>.Ax y a}) v'" 
      using new by (simp add: fresh_fun_simp_AndL1 fresh_prod)
    also have "\<dots> \<longrightarrow>\<^isub>a* (AndL1 (u).(M{x:=<a>.Ax y a}) v')[v'\<turnstile>n>y]"
      using new 
      apply(rule_tac a_starI)
      apply(rule a_redu.intros)
      apply(rule better_LAxL_intro)
      apply(rule fin.intros)
      apply(simp add: abs_fresh)
      done
    also have "\<dots> = AndL1 (u).(M{x:=<a>.Ax y a}) y" using fs new
      by (auto simp add: fresh_prod fresh_atm nrename_fresh)
    also have "\<dots> \<longrightarrow>\<^isub>a* AndL1 (u).(M[x\<turnstile>n>y]) y" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (AndL1 (u).M v)[x\<turnstile>n>y]" using eq fs by simp
    finally show "(AndL1 (u).M v){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (AndL1 (u).M v)[x\<turnstile>n>y]" by simp
  next
    case False
    assume neq: "v\<noteq>x"
    have "(AndL1 (u).M v){x:=<a>.Ax y a} = AndL1 (u).(M{x:=<a>.Ax y a}) v" using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* AndL1 (u).(M[x\<turnstile>n>y]) v" using ih by (auto intro: a_star_congs)
    finally show "(AndL1 (u).M v){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (AndL1 (u).M v)[x\<turnstile>n>y]" using fs neq by simp
  qed
next
  case (AndL2 u M v x a y)
  have fs: "u\<sharp>x" "u\<sharp>a" "u\<sharp>y" "u\<sharp>v" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* M[x\<turnstile>n>y]" by fact
  show "(AndL2 (u).M v){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (AndL2 (u).M v)[x\<turnstile>n>y]"
  proof(cases "v=x")
    case True
    assume eq: "v=x"
    obtain v'::"name" where new: "v'\<sharp>(Ax y a,M{x:=<a>.Ax y a},u)" by (rule exists_fresh(1)[OF fs_name1])
    have "(AndL2 (u).M v){x:=<a>.Ax y a} = 
                        fresh_fun (\<lambda>v'. Cut <a>.Ax y a (v').AndL2 (u).(M{x:=<a>.Ax y a}) v')"
      using eq fs by simp
    also have "\<dots> = Cut <a>.Ax y a (v').AndL2 (u).(M{x:=<a>.Ax y a}) v'" 
      using new by (simp add: fresh_fun_simp_AndL2 fresh_prod)
    also have "\<dots> \<longrightarrow>\<^isub>a* (AndL2 (u).(M{x:=<a>.Ax y a}) v')[v'\<turnstile>n>y]"
      using new 
      apply(rule_tac a_starI)
      apply(rule a_redu.intros)
      apply(rule better_LAxL_intro)
      apply(rule fin.intros)
      apply(simp add: abs_fresh)
      done
    also have "\<dots> = AndL2 (u).(M{x:=<a>.Ax y a}) y" using fs new
      by (auto simp add: fresh_prod fresh_atm nrename_fresh)
    also have "\<dots> \<longrightarrow>\<^isub>a* AndL2 (u).(M[x\<turnstile>n>y]) y" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (AndL2 (u).M v)[x\<turnstile>n>y]" using eq fs by simp
    finally show "(AndL2 (u).M v){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (AndL2 (u).M v)[x\<turnstile>n>y]" by simp
  next
    case False
    assume neq: "v\<noteq>x"
    have "(AndL2 (u).M v){x:=<a>.Ax y a} = AndL2 (u).(M{x:=<a>.Ax y a}) v" using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* AndL2 (u).(M[x\<turnstile>n>y]) v" using ih by (auto intro: a_star_congs)
    finally show "(AndL2 (u).M v){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (AndL2 (u).M v)[x\<turnstile>n>y]" using fs neq by simp
  qed
next
  case (OrR1 c M d  x a y)
  have fs: "c\<sharp>x" "c\<sharp>a" "c\<sharp>y" "c\<sharp>d" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* M[x\<turnstile>n>y]" by fact
  have "(OrR1 <c>.M d){x:=<a>.Ax y a} = OrR1 <c>.(M{x:=<a>.Ax y a}) d" using fs by (simp add: fresh_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a* OrR1 <c>.(M[x\<turnstile>n>y]) d" using ih by (auto intro: a_star_congs)
  finally show "(OrR1 <c>.M d){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (OrR1 <c>.M d)[x\<turnstile>n>y]" using fs by simp
next
  case (OrR2 c M d  x a y)
  have fs: "c\<sharp>x" "c\<sharp>a" "c\<sharp>y" "c\<sharp>d" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* M[x\<turnstile>n>y]" by fact
  have "(OrR2 <c>.M d){x:=<a>.Ax y a} = OrR2 <c>.(M{x:=<a>.Ax y a}) d" using fs by (simp add: fresh_atm)
  also have "\<dots> \<longrightarrow>\<^isub>a* OrR2 <c>.(M[x\<turnstile>n>y]) d" using ih by (auto intro: a_star_congs)
  finally show "(OrR2 <c>.M d){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (OrR2 <c>.M d)[x\<turnstile>n>y]" using fs by simp
next
  case (OrL u M v N z x a y)
  have fs: "u\<sharp>x" "u\<sharp>a" "u\<sharp>y" "v\<sharp>x" "v\<sharp>a" "v\<sharp>y" "v\<noteq>u" "u\<sharp>N" "u\<sharp>z" "v\<sharp>M" "v\<sharp>z" by fact+
  have ih1: "M{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* M[x\<turnstile>n>y]" by fact
  have ih2: "N{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* N[x\<turnstile>n>y]" by fact
  show "(OrL (u).M (v).N z){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (OrL (u).M (v).N z)[x\<turnstile>n>y]"
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
    also have "\<dots> \<longrightarrow>\<^isub>a* (OrL (u).(M{x:=<a>.Ax y a}) (v).(N{x:=<a>.Ax y a}) z')[z'\<turnstile>n>y]"
      using new 
      apply(rule_tac a_starI)
      apply(rule a_redu.intros)
      apply(rule better_LAxL_intro)
      apply(rule fin.intros)
      apply(simp_all add: abs_fresh)
      done
    also have "\<dots> = OrL (u).(M{x:=<a>.Ax y a}) (v).(N{x:=<a>.Ax y a}) y" using fs new
      by (auto simp add: fresh_prod fresh_atm nrename_fresh subst_fresh)
    also have "\<dots> \<longrightarrow>\<^isub>a* OrL (u).(M[x\<turnstile>n>y]) (v).(N[x\<turnstile>n>y]) y" 
      using ih1 ih2 by (auto intro: a_star_congs)
    also have "\<dots> = (OrL (u).M (v).N z)[x\<turnstile>n>y]" using eq fs by simp
    finally show "(OrL (u).M (v).N z){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (OrL (u).M (v).N z)[x\<turnstile>n>y]" by simp
  next
    case False
    assume neq: "z\<noteq>x"
    have "(OrL (u).M (v).N z){x:=<a>.Ax y a} = OrL (u).(M{x:=<a>.Ax y a}) (v).(N{x:=<a>.Ax y a}) z" 
      using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* OrL (u).(M[x\<turnstile>n>y]) (v).(N[x\<turnstile>n>y]) z" 
      using ih1 ih2 by (auto intro: a_star_congs)
    finally show "(OrL (u).M (v).N z){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (OrL (u).M (v).N z)[x\<turnstile>n>y]" using fs neq by simp
  qed
next
  case (ImpR z c M d x a y)
  have fs: "z\<sharp>x" "z\<sharp>a" "z\<sharp>y" "c\<sharp>x" "c\<sharp>a" "c\<sharp>y" "z\<sharp>d" "c\<sharp>d" by fact+
  have ih: "M{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* M[x\<turnstile>n>y]" by fact
  have "(ImpR (z).<c>.M d){x:=<a>.Ax y a} = ImpR (z).<c>.(M{x:=<a>.Ax y a}) d" using fs by simp
  also have "\<dots> \<longrightarrow>\<^isub>a* ImpR (z).<c>.(M[x\<turnstile>n>y]) d" using ih by (auto intro: a_star_congs)
  finally show "(ImpR (z).<c>.M d){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (ImpR (z).<c>.M d)[x\<turnstile>n>y]" using fs by simp
next
  case (ImpL c M u N v x a y)
  have fs: "c\<sharp>x" "c\<sharp>a" "c\<sharp>y" "u\<sharp>x" "u\<sharp>a" "u\<sharp>y" "c\<sharp>N" "c\<sharp>v" "u\<sharp>M" "u\<sharp>v" by fact+
  have ih1: "M{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* M[x\<turnstile>n>y]" by fact
  have ih2: "N{x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* N[x\<turnstile>n>y]" by fact
  show "(ImpL <c>.M (u).N v){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (ImpL <c>.M (u).N v)[x\<turnstile>n>y]"
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
    also have "\<dots> \<longrightarrow>\<^isub>a* (ImpL <c>.(M{x:=<a>.Ax y a}) (u).(N{x:=<a>.Ax y a}) v')[v'\<turnstile>n>y]"
      using new 
      apply(rule_tac a_starI)
      apply(rule a_redu.intros)
      apply(rule better_LAxL_intro)
      apply(rule fin.intros)
      apply(simp_all add: abs_fresh)
      done
    also have "\<dots> = ImpL <c>.(M{x:=<a>.Ax y a}) (u).(N{x:=<a>.Ax y a}) y" using fs new
      by (auto simp add: fresh_prod subst_fresh fresh_atm trm.inject alpha rename_fresh)
    also have "\<dots> \<longrightarrow>\<^isub>a* ImpL <c>.(M[x\<turnstile>n>y]) (u).(N[x\<turnstile>n>y]) y" 
      using ih1 ih2 by (auto intro: a_star_congs)
    also have "\<dots> = (ImpL <c>.M (u).N v)[x\<turnstile>n>y]" using eq fs by simp
    finally show "(ImpL <c>.M (u).N v){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (ImpL <c>.M (u).N v)[x\<turnstile>n>y]" using fs by simp
  next
    case False
    assume neq: "v\<noteq>x"
    have "(ImpL <c>.M (u).N v){x:=<a>.Ax y a} = ImpL <c>.(M{x:=<a>.Ax y a}) (u).(N{x:=<a>.Ax y a}) v" 
      using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* ImpL <c>.(M[x\<turnstile>n>y]) (u).(N[x\<turnstile>n>y]) v" 
      using ih1 ih2 by (auto intro: a_star_congs)
    finally show "(ImpL <c>.M (u).N v){x:=<a>.Ax y a} \<longrightarrow>\<^isub>a* (ImpL <c>.M (u).N v)[x\<turnstile>n>y]" 
      using fs neq by simp
  qed
qed

lemma subst_with_ax2:
  shows "M{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* M[b\<turnstile>c>a]"
proof(nominal_induct M avoiding: b a x rule: trm.strong_induct)
  case (Ax z c b a x)
  show "(Ax z c){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (Ax z c)[b\<turnstile>c>a]"
  proof (cases "c=b")
    case True
    assume eq: "c=b"
    have "(Ax z c){b:=(x).Ax x a} = Cut <b>.Ax z c (x).Ax x a" using eq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* (Ax z c)[b\<turnstile>c>a]" using eq by blast
    finally show "(Ax z c){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (Ax z c)[b\<turnstile>c>a]" by simp
  next
    case False
    assume neq: "c\<noteq>b"
    then show "(Ax z c){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (Ax z c)[b\<turnstile>c>a]" by simp
  qed
next
  case (Cut c M z N b a x)
  have fs: "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "c\<sharp>N" "z\<sharp>b" "z\<sharp>a" "z\<sharp>x" "z\<sharp>M" by fact+
  have ih1: "M{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* M[b\<turnstile>c>a]" by fact
  have ih2: "N{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* N[b\<turnstile>c>a]" by fact
  show "(Cut <c>.M (z).N){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (Cut <c>.M (z).N)[b\<turnstile>c>a]"
  proof (cases "N = Ax z b")
    case True
    assume eq: "N = Ax z b"
    have "(Cut <c>.M (z).N){b:=(x).Ax x a} = Cut <c>.(M{b:=(x).Ax x a}) (x).Ax x a" using eq fs by simp 
    also have "\<dots> \<longrightarrow>\<^isub>a* Cut <c>.(M[b\<turnstile>c>a]) (x).Ax x a" using ih1 a_star_congs by blast
    also have "\<dots> = Cut <c>.(M[b\<turnstile>c>a]) (z).(N[b\<turnstile>c>a])" using eq fs
      by (simp add: trm.inject alpha calc_atm fresh_atm)
    finally show "(Cut <c>.M (z).N){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (Cut <c>.M (z).N)[b\<turnstile>c>a]" using fs by simp
  next
    case False
    assume neq: "N \<noteq> Ax z b"
    have "(Cut <c>.M (z).N){b:=(x).Ax x a} = Cut <c>.(M{b:=(x).Ax x a}) (z).(N{b:=(x).Ax x a})" 
      using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* Cut <c>.(M[b\<turnstile>c>a]) (z).(N[b\<turnstile>c>a])" using ih1 ih2 a_star_congs by blast
    finally show "(Cut <c>.M (z).N){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (Cut <c>.M (z).N)[b\<turnstile>c>a]" using fs by simp
  qed
next
  case (NotR z M c b a x)
  have fs: "z\<sharp>b" "z\<sharp>a" "z\<sharp>x" "z\<sharp>c" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* M[b\<turnstile>c>a]" by fact
  show "(NotR (z).M c){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (NotR (z).M c)[b\<turnstile>c>a]"
  proof (cases "c=b")
    case True
    assume eq: "c=b"
    obtain a'::"coname" where new: "a'\<sharp>(Ax x a,M{b:=(x).Ax x a})" by (rule exists_fresh(2)[OF fs_coname1])
    have "(NotR (z).M c){b:=(x).Ax x a} = 
                        fresh_fun (\<lambda>a'. Cut <a'>.NotR (z).M{b:=(x).Ax x a} a' (x).Ax x a)" 
      using eq fs by simp
    also have "\<dots> = Cut <a'>.NotR (z).M{b:=(x).Ax x a} a' (x).Ax x a"
      using new by (simp add: fresh_fun_simp_NotR fresh_prod)
    also have "\<dots> \<longrightarrow>\<^isub>a* (NotR (z).(M{b:=(x).Ax x a}) a')[a'\<turnstile>c>a]"
      using new 
      apply(rule_tac a_starI)
      apply(rule a_redu.intros)
      apply(rule better_LAxR_intro)
      apply(rule fic.intros)
      apply(simp)
      done
    also have "\<dots> = NotR (z).(M{b:=(x).Ax x a}) a" using new by (simp add: crename_fresh)
    also have "\<dots> \<longrightarrow>\<^isub>a* NotR (z).(M[b\<turnstile>c>a]) a" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (NotR (z).M c)[b\<turnstile>c>a]" using eq by simp
    finally show "(NotR (z).M c){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (NotR (z).M c)[b\<turnstile>c>a]" by simp
  next
    case False
    assume neq: "c\<noteq>b"
    have "(NotR (z).M c){b:=(x).Ax x a} = NotR (z).(M{b:=(x).Ax x a}) c" using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* NotR (z).(M[b\<turnstile>c>a]) c" using ih by (auto intro: a_star_congs)
    finally show "(NotR (z).M c){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (NotR (z).M c)[b\<turnstile>c>a]" using neq by simp
  qed
next
  case (NotL c M z b a x)  
  have fs: "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "c\<sharp>z" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* M[b\<turnstile>c>a]" by fact
  have "(NotL <c>.M z){b:=(x).Ax x a} = NotL <c>.(M{b:=(x).Ax x a}) z" using fs by simp
  also have "\<dots> \<longrightarrow>\<^isub>a* NotL <c>.(M[b\<turnstile>c>a]) z" using ih by (auto intro: a_star_congs)
  finally show "(NotL <c>.M z){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (NotL <c>.M z)[b\<turnstile>c>a]" using fs by simp
next
  case (AndR c M d N e b a x)
  have fs: "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "d\<sharp>b" "d\<sharp>a" "d\<sharp>x" "d\<noteq>c" "c\<sharp>N" "c\<sharp>e" "d\<sharp>M" "d\<sharp>e" by fact+
  have ih1: "M{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* M[b\<turnstile>c>a]" by fact
  have ih2: "N{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* N[b\<turnstile>c>a]" by fact
  show "(AndR <c>.M <d>.N e){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (AndR <c>.M <d>.N e)[b\<turnstile>c>a]"
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
    also have "\<dots> \<longrightarrow>\<^isub>a* (AndR <c>.(M{b:=(x).Ax x a}) <d>.(N{b:=(x).Ax x a}) e')[e'\<turnstile>c>a]"
      using new 
      apply(rule_tac a_starI)
      apply(rule a_redu.intros)
      apply(rule better_LAxR_intro)
      apply(rule fic.intros)
      apply(simp_all add: abs_fresh)
      done
    also have "\<dots> = AndR <c>.(M{b:=(x).Ax x a}) <d>.(N{b:=(x).Ax x a}) a" using fs new
      by (auto simp add: fresh_prod fresh_atm subst_fresh crename_fresh)
    also have "\<dots> \<longrightarrow>\<^isub>a* AndR <c>.(M[b\<turnstile>c>a]) <d>.(N[b\<turnstile>c>a]) a" using ih1 ih2 by (auto intro: a_star_congs)
    also have "\<dots> = (AndR <c>.M <d>.N e)[b\<turnstile>c>a]" using eq fs by simp
    finally show "(AndR <c>.M <d>.N e){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (AndR <c>.M <d>.N e)[b\<turnstile>c>a]" by simp
  next
    case False
    assume neq: "e\<noteq>b"
    have "(AndR <c>.M <d>.N e){b:=(x).Ax x a} = AndR <c>.(M{b:=(x).Ax x a}) <d>.(N{b:=(x).Ax x a}) e"
      using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* AndR <c>.(M[b\<turnstile>c>a]) <d>.(N[b\<turnstile>c>a]) e" using ih1 ih2 by (auto intro: a_star_congs)
    finally show "(AndR <c>.M <d>.N e){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (AndR <c>.M <d>.N e)[b\<turnstile>c>a]"
      using fs neq by simp
  qed
next
  case (AndL1 u M v b a x)
  have fs: "u\<sharp>b" "u\<sharp>a" "u\<sharp>x" "u\<sharp>v" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* M[b\<turnstile>c>a]" by fact
  have "(AndL1 (u).M v){b:=(x).Ax x a} = AndL1 (u).(M{b:=(x).Ax x a}) v" using fs by simp
  also have "\<dots> \<longrightarrow>\<^isub>a* AndL1 (u).(M[b\<turnstile>c>a]) v" using ih by (auto intro: a_star_congs)
  finally show "(AndL1 (u).M v){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (AndL1 (u).M v)[b\<turnstile>c>a]" using fs by simp
next
  case (AndL2 u M v b a x)
  have fs: "u\<sharp>b" "u\<sharp>a" "u\<sharp>x" "u\<sharp>v" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* M[b\<turnstile>c>a]" by fact
  have "(AndL2 (u).M v){b:=(x).Ax x a} = AndL2 (u).(M{b:=(x).Ax x a}) v" using fs by simp
  also have "\<dots> \<longrightarrow>\<^isub>a* AndL2 (u).(M[b\<turnstile>c>a]) v" using ih by (auto intro: a_star_congs)
  finally show "(AndL2 (u).M v){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (AndL2 (u).M v)[b\<turnstile>c>a]" using fs by simp
next
  case (OrR1 c M d  b a x)
  have fs: "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "c\<sharp>d" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* M[b\<turnstile>c>a]" by fact
  show "(OrR1 <c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (OrR1 <c>.M d)[b\<turnstile>c>a]"
  proof(cases "d=b")
    case True
    assume eq: "d=b"
    obtain a'::"coname" where new: "a'\<sharp>(Ax x a,M{b:=(x).Ax x a},c,x,a)" 
      by (rule exists_fresh(2)[OF fs_coname1])
    have "(OrR1 <c>.M d){b:=(x).Ax x a} = 
             fresh_fun (\<lambda>a'. Cut <a'>.OrR1 <c>.M{b:=(x).Ax x a} a' (x).Ax x a)" using fs eq by (simp)
    also have "\<dots> = Cut <a'>.OrR1 <c>.M{b:=(x).Ax x a} a' (x).Ax x a"
      using new by (simp add: fresh_fun_simp_OrR1)
    also have "\<dots> \<longrightarrow>\<^isub>a* (OrR1 <c>.M{b:=(x).Ax x a} a')[a'\<turnstile>c>a]"
      using new 
      apply(rule_tac a_starI)
      apply(rule a_redu.intros)
      apply(rule better_LAxR_intro)
      apply(rule fic.intros)
      apply(simp_all add: abs_fresh)
      done
    also have "\<dots> = OrR1 <c>.M{b:=(x).Ax x a} a" using fs new
      by (auto simp add: fresh_prod fresh_atm crename_fresh subst_fresh)
    also have "\<dots> \<longrightarrow>\<^isub>a* OrR1 <c>.(M[b\<turnstile>c>a]) a" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (OrR1 <c>.M d)[b\<turnstile>c>a]" using eq fs by simp
    finally show "(OrR1 <c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (OrR1 <c>.M d)[b\<turnstile>c>a]" by simp
  next
    case False
    assume neq: "d\<noteq>b"
    have "(OrR1 <c>.M d){b:=(x).Ax x a} = OrR1 <c>.(M{b:=(x).Ax x a}) d" using fs neq by (simp)
    also have "\<dots> \<longrightarrow>\<^isub>a* OrR1 <c>.(M[b\<turnstile>c>a]) d" using ih by (auto intro: a_star_congs)
    finally show "(OrR1 <c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (OrR1 <c>.M d)[b\<turnstile>c>a]" using fs neq by simp
  qed
next
  case (OrR2 c M d  b a x)
  have fs: "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "c\<sharp>d" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* M[b\<turnstile>c>a]" by fact
  show "(OrR2 <c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (OrR2 <c>.M d)[b\<turnstile>c>a]"
  proof(cases "d=b")
    case True
    assume eq: "d=b"
    obtain a'::"coname" where new: "a'\<sharp>(Ax x a,M{b:=(x).Ax x a},c,x,a)" 
      by (rule exists_fresh(2)[OF fs_coname1])
    have "(OrR2 <c>.M d){b:=(x).Ax x a} = 
             fresh_fun (\<lambda>a'. Cut <a'>.OrR2 <c>.M{b:=(x).Ax x a} a' (x).Ax x a)" using fs eq by (simp)
    also have "\<dots> = Cut <a'>.OrR2 <c>.M{b:=(x).Ax x a} a' (x).Ax x a"
      using new by (simp add: fresh_fun_simp_OrR2)
    also have "\<dots> \<longrightarrow>\<^isub>a* (OrR2 <c>.M{b:=(x).Ax x a} a')[a'\<turnstile>c>a]"
      using new 
      apply(rule_tac a_starI)
      apply(rule a_redu.intros)
      apply(rule better_LAxR_intro)
      apply(rule fic.intros)
      apply(simp_all add: abs_fresh)
      done
    also have "\<dots> = OrR2 <c>.M{b:=(x).Ax x a} a" using fs new
      by (auto simp add: fresh_prod fresh_atm crename_fresh subst_fresh)
    also have "\<dots> \<longrightarrow>\<^isub>a* OrR2 <c>.(M[b\<turnstile>c>a]) a" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (OrR2 <c>.M d)[b\<turnstile>c>a]" using eq fs by simp
    finally show "(OrR2 <c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (OrR2 <c>.M d)[b\<turnstile>c>a]" by simp
  next
    case False
    assume neq: "d\<noteq>b"
    have "(OrR2 <c>.M d){b:=(x).Ax x a} = OrR2 <c>.(M{b:=(x).Ax x a}) d" using fs neq by (simp)
    also have "\<dots> \<longrightarrow>\<^isub>a* OrR2 <c>.(M[b\<turnstile>c>a]) d" using ih by (auto intro: a_star_congs)
    finally show "(OrR2 <c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (OrR2 <c>.M d)[b\<turnstile>c>a]" using fs neq by simp
  qed
next
  case (OrL u M v N z b a x)
  have fs: "u\<sharp>b" "u\<sharp>a" "u\<sharp>x" "v\<sharp>b" "v\<sharp>a" "v\<sharp>x" "v\<noteq>u" "u\<sharp>N" "u\<sharp>z" "v\<sharp>M" "v\<sharp>z" by fact+
  have ih1: "M{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* M[b\<turnstile>c>a]" by fact
  have ih2: "N{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* N[b\<turnstile>c>a]" by fact
  have "(OrL (u).M (v).N z){b:=(x).Ax x a} = OrL (u).(M{b:=(x).Ax x a}) (v).(N{b:=(x).Ax x a}) z" 
    using fs by simp
  also have "\<dots> \<longrightarrow>\<^isub>a* OrL (u).(M[b\<turnstile>c>a]) (v).(N[b\<turnstile>c>a]) z" using ih1 ih2 by (auto intro: a_star_congs)
  finally show "(OrL (u).M (v).N z){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (OrL (u).M (v).N z)[b\<turnstile>c>a]" using fs by simp
next
  case (ImpR z c M d b a x)
  have fs: "z\<sharp>b" "z\<sharp>a" "z\<sharp>x" "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "z\<sharp>d" "c\<sharp>d" by fact+
  have ih: "M{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* M[b\<turnstile>c>a]" by fact
  show "(ImpR (z).<c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (ImpR (z).<c>.M d)[b\<turnstile>c>a]"
  proof(cases "b=d")
    case True
    assume eq: "b=d"
    obtain a'::"coname" where new: "a'\<sharp>(Ax x a,M{b:=(x).Ax x a},x,a,c)" 
      by (rule exists_fresh(2)[OF fs_coname1])
    have "(ImpR (z).<c>.M d){b:=(x).Ax x a} =
                fresh_fun (\<lambda>a'. Cut <a'>.ImpR z.<c>.M{b:=(x).Ax x a} a' (x).Ax x a)" using fs eq by simp
    also have "\<dots> = Cut <a'>.ImpR z.<c>.M{b:=(x).Ax x a} a' (x).Ax x a" 
      using new by (simp add: fresh_fun_simp_ImpR)
    also have "\<dots> \<longrightarrow>\<^isub>a* (ImpR z.<c>.M{b:=(x).Ax x a} a')[a'\<turnstile>c>a]"
      using new 
      apply(rule_tac a_starI)
      apply(rule a_redu.intros)
      apply(rule better_LAxR_intro)
      apply(rule fic.intros)
      apply(simp_all add: abs_fresh)
      done
    also have "\<dots> = ImpR z.<c>.M{b:=(x).Ax x a} a" using fs new
      by (auto simp add: fresh_prod crename_fresh subst_fresh fresh_atm)
    also have "\<dots> \<longrightarrow>\<^isub>a* ImpR z.<c>.(M[b\<turnstile>c>a]) a" using ih by (auto intro: a_star_congs)
    also have "\<dots> = (ImpR z.<c>.M b)[b\<turnstile>c>a]" using eq fs by simp
    finally show "(ImpR (z).<c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (ImpR (z).<c>.M d)[b\<turnstile>c>a]" using eq by simp
  next
    case False
    assume neq: "b\<noteq>d"
    have "(ImpR (z).<c>.M d){b:=(x).Ax x a} = ImpR (z).<c>.(M{b:=(x).Ax x a}) d" using fs neq by simp
    also have "\<dots> \<longrightarrow>\<^isub>a* ImpR (z).<c>.(M[b\<turnstile>c>a]) d" using ih by (auto intro: a_star_congs)
    finally show "(ImpR (z).<c>.M d){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (ImpR (z).<c>.M d)[b\<turnstile>c>a]" using neq fs by simp
  qed
next
  case (ImpL c M u N v b a x)
  have fs: "c\<sharp>b" "c\<sharp>a" "c\<sharp>x" "u\<sharp>b" "u\<sharp>a" "u\<sharp>x" "c\<sharp>N" "c\<sharp>v" "u\<sharp>M" "u\<sharp>v" by fact+
  have ih1: "M{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* M[b\<turnstile>c>a]" by fact
  have ih2: "N{b:=(x).Ax x a} \<longrightarrow>\<^isub>a* N[b\<turnstile>c>a]" by fact
  have "(ImpL <c>.M (u).N v){b:=(x).Ax x a} = ImpL <c>.(M{b:=(x).Ax x a}) (u).(N{b:=(x).Ax x a}) v" 
    using fs by simp
  also have "\<dots> \<longrightarrow>\<^isub>a* ImpL <c>.(M[b\<turnstile>c>a]) (u).(N[b\<turnstile>c>a]) v" 
    using ih1 ih2 by (auto intro: a_star_congs)
  finally show "(ImpL <c>.M (u).N v){b:=(x).Ax x a} \<longrightarrow>\<^isub>a* (ImpL <c>.M (u).N v)[b\<turnstile>c>a]" 
    using fs by simp
qed

text {* substitution lemmas *}

lemma not_Ax1:
  shows "\<not>(b\<sharp>M) \<Longrightarrow> M{b:=(y).Q} \<noteq> Ax x a"
apply(nominal_induct M avoiding: b y Q x a rule: trm.strong_induct)
apply(auto simp add: fresh_atm abs_fresh abs_supp fin_supp)
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname:=(y).Q},Q)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR abs_fresh fresh_atm)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname:=(y).Q},Q)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotR abs_fresh fresh_atm)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(y).Q},Q,trm2{coname3:=(y).Q},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(y).Q},Q,trm2{coname3:=(y).Q},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm1{coname3:=(y).Q},Q,trm2{coname3:=(y).Q},coname1,coname2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(y).Q},Q,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1 abs_fresh fresh_atm)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(y).Q},Q,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR1 abs_fresh fresh_atm)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(y).Q},Q,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2 abs_fresh fresh_atm)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(y).Q},Q,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrR2 abs_fresh fresh_atm)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(y).Q},Q,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR abs_fresh abs_supp fin_supp fresh_atm)
apply(rule exists_fresh'(2)[OF fs_coname1])
apply(subgoal_tac "\<exists>x'::coname. x'\<sharp>(trm{coname2:=(y).Q},Q,coname1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpR abs_fresh abs_supp fin_supp fresh_atm)
apply(rule exists_fresh'(2)[OF fs_coname1])
done

lemma not_Ax2:
  shows "\<not>(x\<sharp>M) \<Longrightarrow> M{x:=<b>.Q} \<noteq> Ax y a"
apply(nominal_induct M avoiding: b y Q x a rule: trm.strong_induct)
apply(auto simp add: fresh_atm abs_fresh abs_supp fin_supp)
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<b>.Q},Q)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL abs_fresh fresh_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<b>.Q},Q)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_NotL abs_fresh fresh_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<b>.Q},Q,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1 abs_fresh fresh_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<b>.Q},Q,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL1 abs_fresh fresh_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<b>.Q},Q,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2 abs_fresh fresh_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm{x:=<b>.Q},Q,name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_AndL2 abs_fresh fresh_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{x:=<b>.Q},Q,trm2{x:=<b>.Q},name1,name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{x:=<b>.Q},Q,trm2{x:=<b>.Q},name1,name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{x:=<b>.Q},Q,trm2{x:=<b>.Q},name1,name2)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<b>.Q},Q,trm2{name2:=<b>.Q},name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<b>.Q},Q,trm2{name2:=<b>.Q},name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(trm1{name2:=<b>.Q},Q,trm2{name2:=<b>.Q},name1)")
apply(erule exE)
apply(simp add: fresh_prod)
apply(erule conjE)+
apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
apply(rule exists_fresh'(1)[OF fs_name1])
done

lemma interesting_subst1:
  assumes a: "x\<noteq>y" "x\<sharp>P" "y\<sharp>P" 
  shows "N{y:=<c>.P}{x:=<c>.P} = N{x:=<c>.Ax y c}{y:=<c>.P}"
using a
proof(nominal_induct N avoiding: x y c P rule: trm.strong_induct)
  case Ax
  then show ?case
    by (auto simp add: abs_fresh fresh_atm forget trm.inject)
next 
  case (Cut d M u M' x' y' c P)
  with assms show ?case
    apply(simp)
    apply(auto)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(auto)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(auto)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(rule impI)
    apply(simp add: trm.inject alpha forget)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(auto)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(auto)
    apply(case_tac "y'\<sharp>M")
    apply(simp add: forget)
    apply(simp add: not_Ax2)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(auto)
    apply(case_tac "x'\<sharp>M")
    apply(simp add: forget)
    apply(simp add: not_Ax2)
    done
next
  case NotR
  then show ?case
    by (auto simp add: abs_fresh fresh_atm forget)
next
  case (NotL d M u)
  then show ?case
    apply (auto simp add: abs_fresh fresh_atm forget)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,M{y:=<c>.P},M{x:=<c>.Ax y c}{y:=<c>.P},y,x)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_NotL)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(simp add: trm.inject alpha forget)
    apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,M{x:=<c>.Ax y c},M{x:=<c>.Ax y c}{y:=<c>.P},Ax y c,y,x)")
    apply(erule exE, simp only: fresh_prod)
    apply(erule conjE)+
    apply(simp only: fresh_fun_simp_NotL)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(simp add: trm.inject alpha forget subst_fresh)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (AndR d1 M d2 M' d3)
  then show ?case
    by (auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
next
  case (AndL1 u M d)
  then show ?case
    apply(auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,M{y:=<c>.P},M{x:=<c>.Ax y c}{y:=<c>.P},u,y,x)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL1)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(simp add: trm.inject alpha forget)
    apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,Ax y c,M{x:=<c>.Ax y c},M{x:=<c>.Ax y c}{y:=<c>.P},u,y,x)")
    apply(erule exE, simp only: fresh_prod)
    apply(erule conjE)+
    apply(simp only: fresh_fun_simp_AndL1)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (AndL2 u M d)
  then show ?case
    apply(auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,M{y:=<c>.P},M{x:=<c>.Ax y c}{y:=<c>.P},u,y,x)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL2)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(simp add: trm.inject alpha forget)
    apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,Ax y c,M{x:=<c>.Ax y c},M{x:=<c>.Ax y c}{y:=<c>.P},u,y,x)")
    apply(erule exE, simp only: fresh_prod)
    apply(erule conjE)+
    apply(simp only: fresh_fun_simp_AndL2)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case OrR1
  then show ?case
    by (auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
next
  case OrR2
  then show ?case
    by (auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
next
  case (OrL x1 M x2 M' x3)
  then show ?case
    apply(auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,M{y:=<c>.P},M{x:=<c>.Ax y c}{y:=<c>.P},
                                        M'{y:=<c>.P},M'{x:=<c>.Ax y c}{y:=<c>.P},x1,x2,x3,y,x)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrL)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(force)
    apply(simp)
    apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,Ax y c,M{x:=<c>.Ax y c},M{x:=<c>.Ax y c}{y:=<c>.P},
                                        M'{x:=<c>.Ax y c},M'{x:=<c>.Ax y c}{y:=<c>.P},x1,x2,x3,y,x)")
    apply(erule exE, simp only: fresh_prod)
    apply(erule conjE)+
    apply(simp only: fresh_fun_simp_OrL)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(force)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case ImpR
  then show ?case
    by (auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
next
  case (ImpL a M x1 M' x2)
  then show ?case
    apply(auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,M{x2:=<c>.P},M{x:=<c>.Ax x2 c}{x2:=<c>.P},
                                        M'{x2:=<c>.P},M'{x:=<c>.Ax x2 c}{x2:=<c>.P},x1,y,x)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_ImpL)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(force)
    apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,Ax y c,M{x2:=<c>.Ax y c},M{x2:=<c>.Ax y c}{y:=<c>.P},
                                        M'{x2:=<c>.Ax y c},M'{x2:=<c>.Ax y c}{y:=<c>.P},x1,x2,y,x)")
    apply(erule exE, simp only: fresh_prod)
    apply(erule conjE)+
    apply(simp only: fresh_fun_simp_ImpL)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
qed 

lemma interesting_subst1':
  assumes a: "x\<noteq>y" "x\<sharp>P" "y\<sharp>P" 
  shows "N{y:=<c>.P}{x:=<c>.P} = N{x:=<a>.Ax y a}{y:=<c>.P}"
proof -
  show ?thesis
  proof (cases "c=a")
    case True then show ?thesis using a by (simp add: interesting_subst1)
  next
    case False then show ?thesis using a
      apply - 
      apply(subgoal_tac "N{x:=<a>.Ax y a} = N{x:=<c>.([(c,a)]\<bullet>Ax y a)}") 
      apply(simp add: interesting_subst1 calc_atm)
      apply(rule subst_rename)
      apply(simp add: fresh_prod fresh_atm)
      done
  qed
qed

lemma interesting_subst2:
  assumes a: "a\<noteq>b" "a\<sharp>P" "b\<sharp>P" 
  shows "N{a:=(y).P}{b:=(y).P} = N{b:=(y).Ax y a}{a:=(y).P}"
using a
proof(nominal_induct N avoiding: a b y P rule: trm.strong_induct)
  case Ax
  then show ?case
    by (auto simp add: abs_fresh fresh_atm forget trm.inject)
next 
  case (Cut d M u M' x' y' c P)
  with assms show ?case
    apply(simp)
    apply(auto simp add: trm.inject)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp)
    apply(simp add: abs_fresh)
    apply(simp add: forget)
    apply(auto)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh) 
    apply(simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(auto)[1]
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(rule impI)
    apply(simp add: fresh_atm trm.inject alpha forget)
    apply(case_tac "x'\<sharp>M'")
    apply(simp add: forget)
    apply(simp add: not_Ax1)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(auto)
    apply(case_tac "y'\<sharp>M'")
    apply(simp add: forget)
    apply(simp add: not_Ax1)
    done
next
  case NotL
  then show ?case
    by (auto simp add: abs_fresh fresh_atm forget)
next
  case (NotR u M d)
  then show ?case
    apply (auto simp add: abs_fresh fresh_atm forget)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(b,P,M{d:=(y).P},M{b:=(y).Ax y d}{d:=(y).P},u,y)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_NotR)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(simp add: trm.inject alpha forget)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(P,M{d:=(y).Ax y a},M{d:=(y).Ax y a}{a:=(y).P},Ax y a,y,d)")
    apply(erule exE, simp only: fresh_prod)
    apply(erule conjE)+
    apply(simp only: fresh_fun_simp_NotR)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha forget subst_fresh)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (AndR d1 M d2 M' d3)
  then show ?case
    apply(auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(P,M{d3:=(y).P},M{b:=(y).Ax y d3}{d3:=(y).P},
                                        M'{d3:=(y).P},M'{b:=(y).Ax y d3}{d3:=(y).P},d1,d2,d3,b,y)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndR)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh fresh_atm)
    apply(simp add: abs_fresh fresh_atm)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(force)
    apply(simp)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(P,Ax y a,M{d3:=(y).Ax y a},M{d3:=(y).Ax y a}{a:=(y).P},
                                        M'{d3:=(y).Ax y a},M'{d3:=(y).Ax y a}{a:=(y).P},d1,d2,d3,y,b)")
    apply(erule exE, simp only: fresh_prod)
    apply(erule conjE)+
    apply(simp only: fresh_fun_simp_AndR)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(force)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (AndL1 u M d)
  then show ?case
    by (auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
next
  case (AndL2 u M d)
  then show ?case
    by (auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
next
  case (OrR1 d M e)
  then show ?case
    apply (auto simp add: abs_fresh fresh_atm forget)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(b,P,M{e:=(y).P},M{b:=(y).Ax y e}{e:=(y).P},d,e)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrR1)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(simp add: trm.inject alpha forget)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(b,P,Ax y a,M{e:=(y).Ax y a},M{e:=(y).Ax y a}{a:=(y).P},d,e)")
    apply(erule exE, simp only: fresh_prod)
    apply(erule conjE)+
    apply(simp only: fresh_fun_simp_OrR1)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha forget subst_fresh)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (OrR2 d M e)
  then show ?case
    apply (auto simp add: abs_fresh fresh_atm forget)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(b,P,M{e:=(y).P},M{b:=(y).Ax y e}{e:=(y).P},d,e)")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrR2)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(simp add: trm.inject alpha forget)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(b,P,Ax y a,M{e:=(y).Ax y a},M{e:=(y).Ax y a}{a:=(y).P},d,e)")
    apply(erule exE, simp only: fresh_prod)
    apply(erule conjE)+
    apply(simp only: fresh_fun_simp_OrR2)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha forget subst_fresh)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (OrL x1 M x2 M' x3)
  then show ?case
    by(auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
next
  case ImpL
  then show ?case
    by (auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
next
  case (ImpR u e M d)
  then show ?case
    apply(auto simp add: abs_fresh fresh_atm forget trm.inject subst_fresh)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(b,e,d,P,M{d:=(y).P},M{b:=(y).Ax y d}{d:=(y).P})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_ImpR)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(simp add: trm.inject alpha forget)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(e,d,P,Ax y a,M{d:=(y).Ax y a},M{d:=(y).Ax y a}{a:=(y).P})")
    apply(erule exE, simp only: fresh_prod)
    apply(erule conjE)+
    apply(simp only: fresh_fun_simp_ImpR)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp)
    apply(auto simp add: fresh_atm)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
qed 

lemma interesting_subst2':
  assumes a: "a\<noteq>b" "a\<sharp>P" "b\<sharp>P" 
  shows "N{a:=(y).P}{b:=(y).P} = N{b:=(z).Ax z a}{a:=(y).P}"
proof -
  show ?thesis
  proof (cases "z=y")
    case True then show ?thesis using a by (simp add: interesting_subst2)
  next
    case False then show ?thesis using a
      apply - 
      apply(subgoal_tac "N{b:=(z).Ax z a} = N{b:=(y).([(y,z)]\<bullet>Ax z a)}") 
      apply(simp add: interesting_subst2 calc_atm)
      apply(rule subst_rename)
      apply(simp add: fresh_prod fresh_atm)
      done
  qed
qed

lemma subst_subst1:
  assumes a: "a\<sharp>(Q,b)" "x\<sharp>(y,P,Q)" "b\<sharp>Q" "y\<sharp>P" 
  shows "M{x:=<a>.P}{b:=(y).Q} = M{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}"
using a
proof(nominal_induct M avoiding: x a P b y Q rule: trm.strong_induct)
  case (Ax z c)
  have fs: "a\<sharp>(Q,b)" "x\<sharp>(y,P,Q)" "b\<sharp>Q" "y\<sharp>P" by fact+
  { assume asm: "z=x \<and> c=b"
    have "(Ax x b){x:=<a>.P}{b:=(y).Q} = (Cut <a>.P (x).Ax x b){b:=(y).Q}" using fs by simp
    also have "\<dots> = Cut <a>.(P{b:=(y).Q}) (y).Q"
      using fs by (simp_all add: fresh_prod fresh_atm)
    also have "\<dots> = Cut <a>.(P{b:=(y).Q}) (y).(Q{x:=<a>.(P{b:=(y).Q})})" using fs by (simp add: forget)
    also have "\<dots> = (Cut <b>.Ax x b (y).Q){x:=<a>.(P{b:=(y).Q})}"
      using fs asm by (auto simp add: fresh_prod fresh_atm subst_fresh)
    also have "\<dots> = (Ax x b){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}" using fs by simp
    finally have "(Ax z c){x:=<a>.P}{b:=(y).Q} = (Ax z c){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}" 
      using asm by simp
  }
  moreover
  { assume asm: "z\<noteq>x \<and> c=b"
    have "(Ax z c){x:=<a>.P}{b:=(y).Q} = (Ax z c){b:=(y).Q}" using asm by simp
    also have "\<dots> = Cut <b>.Ax z c (y).Q" using fs asm by simp
    also have "\<dots> = Cut <b>.(Ax z c{x:=<a>.(P{b:=(y).Q})}) (y).(Q{x:=<a>.(P{b:=(y).Q})})" 
      using fs asm by (simp add: forget)
    also have "\<dots> = (Cut <b>.Ax z c (y).Q){x:=<a>.(P{b:=(y).Q})}" using asm fs
      by (auto simp add: trm.inject subst_fresh fresh_prod fresh_atm abs_fresh)
    also have "\<dots> = (Ax z c){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}" using asm fs by simp
    finally have "(Ax z c){x:=<a>.P}{b:=(y).Q} = (Ax z c){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}" by simp
  }
  moreover
  { assume asm: "z=x \<and> c\<noteq>b"
    have "(Ax z c){x:=<a>.P}{b:=(y).Q} = (Cut <a>.P (x).Ax z c){b:=(y).Q}" using fs asm by simp
    also have "\<dots> = Cut <a>.(P{b:=(y).Q}) (x).Ax z c" using fs asm by (auto simp add: trm.inject abs_fresh)
    also have "\<dots> = (Ax z c){x:=<a>.(P{b:=(y).Q})}" using fs asm by simp
    also have "\<dots> = (Ax z c){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}" using asm by auto
    finally have "(Ax z c){x:=<a>.P}{b:=(y).Q} = (Ax z c){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}" by simp
  }
  moreover
  { assume asm: "z\<noteq>x \<and> c\<noteq>b"
    have "(Ax z c){x:=<a>.P}{b:=(y).Q} = (Ax z c){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}" using asm by auto
  }
  ultimately show ?case by blast
next
  case (Cut c M z N)
  { assume asm: "M = Ax x c \<and> N = Ax z b"
    have "(Cut <c>.M (z).N){x:=<a>.P}{b:=(y).Q} = (Cut <a>.P (z).(N{x:=<a>.P})){b:=(y).Q}" 
      using Cut asm by simp
    also have "\<dots> = (Cut <a>.P (z).N){b:=(y).Q}" using Cut asm by (simp add: fresh_atm)
    also have "\<dots> = (Cut <a>.(P{b:=(y).Q}) (y).Q)" using Cut asm by (auto simp add: fresh_prod fresh_atm)
    finally have eq1: "(Cut <c>.M (z).N){x:=<a>.P}{b:=(y).Q} = (Cut <a>.(P{b:=(y).Q}) (y).Q)" by simp
    have "(Cut <c>.M (z).N){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})} = (Cut <c>.M (y).Q){x:=<a>.(P{b:=(y).Q})}"
      using Cut asm by (simp add: fresh_atm)
    also have "\<dots> = Cut <a>.(P{b:=(y).Q}) (y).(Q{x:=<a>.(P{b:=(y).Q})})" using Cut asm
      by (auto simp add: fresh_prod fresh_atm subst_fresh)
    also have "\<dots> = Cut <a>.(P{b:=(y).Q}) (y).Q" using Cut asm by (simp add: forget)
    finally have eq2: "(Cut <c>.M (z).N){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})} = Cut <a>.(P{b:=(y).Q}) (y).Q"
      by simp
    have "(Cut <c>.M (z).N){x:=<a>.P}{b:=(y).Q} = (Cut <c>.M (z).N){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}" 
      using eq1 eq2 by simp
  }
  moreover
  { assume asm: "M \<noteq> Ax x c \<and> N = Ax z b"
    have neq: "M{b:=(y).Q} \<noteq> Ax x c"
    proof (cases "b\<sharp>M")
      case True then show ?thesis using asm by (simp add: forget)
    next
      case False then show ?thesis by (simp add: not_Ax1)
    qed
    have "(Cut <c>.M (z).N){x:=<a>.P}{b:=(y).Q} = (Cut <c>.(M{x:=<a>.P}) (z).(N{x:=<a>.P})){b:=(y).Q}"
      using Cut asm by simp
    also have "\<dots> = (Cut <c>.(M{x:=<a>.P}) (z).N){b:=(y).Q}" using Cut asm by (simp add: fresh_atm)
    also have "\<dots> = Cut <c>.(M{x:=<a>.P}{b:=(y).Q}) (y).Q" using Cut asm by (simp add: abs_fresh)
    also have "\<dots> = Cut <c>.(M{b:=(y).Q}{x:=<a>.P{b:=(y).Q}}) (y).Q" using Cut asm by simp
    finally 
    have eq1: "(Cut <c>.M (z).N){x:=<a>.P}{b:=(y).Q} = Cut <c>.(M{b:=(y).Q}{x:=<a>.P{b:=(y).Q}}) (y).Q" 
      by simp
    have "(Cut <c>.M (z).N){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})} = 
               (Cut <c>.(M{b:=(y).Q}) (y).Q){x:=<a>.(P{b:=(y).Q})}" using Cut asm by simp
    also have "\<dots> = Cut <c>.(M{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}) (y).(Q{x:=<a>.(P{b:=(y).Q})})"
      using Cut asm neq by (auto simp add: fresh_prod fresh_atm subst_fresh abs_fresh)
    also have "\<dots> = Cut <c>.(M{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}) (y).Q" using Cut asm by (simp add: forget)
    finally have eq2: "(Cut <c>.M (z).N){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})} 
                                       = Cut <c>.(M{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}) (y).Q" by simp
    have "(Cut <c>.M (z).N){x:=<a>.P}{b:=(y).Q} = (Cut <c>.M (z).N){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}" 
      using eq1 eq2 by simp
  }
  moreover 
  { assume asm: "M = Ax x c \<and> N \<noteq> Ax z b"
    have neq: "N{x:=<a>.P} \<noteq> Ax z b"
    proof (cases "x\<sharp>N")
      case True then show ?thesis using asm by (simp add: forget)
    next
      case False then show ?thesis by (simp add: not_Ax2)
    qed
    have "(Cut <c>.M (z).N){x:=<a>.P}{b:=(y).Q} = (Cut <a>.P (z).(N{x:=<a>.P})){b:=(y).Q}"
      using Cut asm by simp
    also have "\<dots> = Cut <a>.(P{b:=(y).Q}) (z).(N{x:=<a>.P}{b:=(y).Q})" using Cut asm neq 
      by (simp add: abs_fresh)
    also have "\<dots> = Cut <a>.(P{b:=(y).Q}) (z).(N{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})})" using Cut asm by simp
    finally have eq1: "(Cut <c>.M (z).N){x:=<a>.P}{b:=(y).Q} 
                    = Cut <a>.(P{b:=(y).Q}) (z).(N{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})})" by simp
    have "(Cut <c>.M (z).N){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})} 
                    = (Cut <c>.(M{b:=(y).Q}) (z).(N{b:=(y).Q})){x:=<a>.(P{b:=(y).Q})}"
      using Cut asm by auto
    also have "\<dots> = (Cut <c>.M (z).(N{b:=(y).Q})){x:=<a>.(P{b:=(y).Q})}"
      using Cut asm by (auto simp add: fresh_atm)
    also have "\<dots> = Cut <a>.(P{b:=(y).Q}) (z).(N{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})})" 
      using Cut asm by (simp add: fresh_prod fresh_atm subst_fresh)
    finally 
    have eq2: "(Cut <c>.M (z).N){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})} 
         = Cut <a>.(P{b:=(y).Q}) (z).(N{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})})" by simp
    have "(Cut <c>.M (z).N){x:=<a>.P}{b:=(y).Q} = (Cut <c>.M (z).N){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}"
      using eq1 eq2 by simp
  }
  moreover
  { assume asm: "M \<noteq> Ax x c \<and> N \<noteq> Ax z b"
    have neq1: "N{x:=<a>.P} \<noteq> Ax z b"
    proof (cases "x\<sharp>N")
      case True then show ?thesis using asm by (simp add: forget)
    next
      case False then show ?thesis by (simp add: not_Ax2)
    qed
    have neq2: "M{b:=(y).Q} \<noteq> Ax x c"
    proof (cases "b\<sharp>M")
      case True then show ?thesis using asm by (simp add: forget)
    next
      case False then show ?thesis by (simp add: not_Ax1)
    qed
    have "(Cut <c>.M (z).N){x:=<a>.P}{b:=(y).Q} = (Cut <c>.(M{x:=<a>.P}) (z).(N{x:=<a>.P})){b:=(y).Q}"
      using Cut asm by simp
    also have "\<dots> = Cut <c>.(M{x:=<a>.P}{b:=(y).Q}) (z).(N{x:=<a>.P}{b:=(y).Q})" using Cut asm neq1
      by (simp add: abs_fresh)
    also have "\<dots> = Cut <c>.(M{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}) (z).(N{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})})"
      using Cut asm by simp
    finally have eq1: "(Cut <c>.M (z).N){x:=<a>.P}{b:=(y).Q}
             = Cut <c>.(M{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}) (z).(N{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})})" by simp
    have "(Cut <c>.M (z).N){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})} = 
                (Cut <c>.(M{b:=(y).Q}) (z).(N{b:=(y).Q})){x:=<a>.(P{b:=(y).Q})}" using Cut asm neq1 by simp
    also have "\<dots> = Cut <c>.(M{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}) (z).(N{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})})"
      using Cut asm neq2 by (simp add: fresh_prod fresh_atm subst_fresh)
    finally have eq2: "(Cut <c>.M (z).N){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})} = 
           Cut <c>.(M{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}) (z).(N{b:=(y).Q}{x:=<a>.(P{b:=(y).Q})})" by simp
    have "(Cut <c>.M (z).N){x:=<a>.P}{b:=(y).Q} = (Cut <c>.M (z).N){b:=(y).Q}{x:=<a>.(P{b:=(y).Q})}"
      using eq1 eq2 by simp
  }
  ultimately show ?case by blast
next
  case (NotR z M c)
  then show ?case
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(M{c:=(y).Q},M{c:=(y).Q}{x:=<a>.P{c:=(y).Q}},Q,a,P,c,y)")
    apply(erule exE)
    apply(simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_NotR abs_fresh fresh_atm)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: fresh_prod fresh_atm subst_fresh abs_fresh)
    apply(simp add: fresh_prod fresh_atm subst_fresh abs_fresh)
    apply(simp add: forget)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (NotL c M z)
  then show ?case  
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,M{x:=<a>.P},P{b:=(y).Q},M{b:=(y).Q}{x:=<a>.P{b:=(y).Q}},y,Q)")
    apply(erule exE)
    apply(simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_NotL abs_fresh fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (AndR c1 M c2 N c3)
  then show ?case  
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(Q,M{c3:=(y).Q},M{c3:=(y).Q}{x:=<a>.P{c3:=(y).Q}},c2,c3,a,
                                     P{c3:=(y).Q},N{c3:=(y).Q},N{c3:=(y).Q}{x:=<a>.P{c3:=(y).Q}},c1)")
    apply(erule exE)
    apply(simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndR abs_fresh fresh_atm)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp_all add: fresh_atm abs_fresh subst_fresh)
    apply(simp add: forget)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (AndL1 z1 M z2)
  then show ?case  
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,M{x:=<a>.P},P{b:=(y).Q},z1,y,Q,M{b:=(y).Q}{x:=<a>.P{b:=(y).Q}})")
    apply(erule exE)
    apply(simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL1 abs_fresh fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (AndL2 z1 M z2)
  then show ?case  
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,M{x:=<a>.P},P{b:=(y).Q},z1,y,Q,M{b:=(y).Q}{x:=<a>.P{b:=(y).Q}})")
    apply(erule exE)
    apply(simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL2 abs_fresh fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (OrL z1 M z2 N z3)
  then show ?case  
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,M{x:=<a>.P},M{b:=(y).Q}{x:=<a>.P{b:=(y).Q}},z2,z3,a,y,Q,
                                     P{b:=(y).Q},N{x:=<a>.P},N{b:=(y).Q}{x:=<a>.P{b:=(y).Q}},z1)")
    apply(erule exE)
    apply(simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrL abs_fresh fresh_atm)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp_all add: fresh_atm subst_fresh)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (OrR1 c1 M c2)
  then show ?case  
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(Q,M{c2:=(y).Q},a,P{c2:=(y).Q},c1,
                                                     M{c2:=(y).Q}{x:=<a>.P{c2:=(y).Q}})")
    apply(erule exE)
    apply(simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrR1 abs_fresh fresh_atm)
    apply(simp_all add: fresh_atm subst_fresh abs_fresh)
    apply(simp add: forget)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (OrR2 c1 M c2)
  then show ?case  
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(Q,M{c2:=(y).Q},a,P{c2:=(y).Q},c1,
                                                     M{c2:=(y).Q}{x:=<a>.P{c2:=(y).Q}})")
    apply(erule exE)
    apply(simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrR2 abs_fresh fresh_atm)
    apply(simp_all add: fresh_atm subst_fresh abs_fresh)
    apply(simp add: forget)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (ImpR z c M d)
  then show ?case  
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(Q,M{d:=(y).Q},a,P{d:=(y).Q},c,
                                                     M{d:=(y).Q}{x:=<a>.P{d:=(y).Q}})")
    apply(erule exE)
    apply(simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_ImpR abs_fresh fresh_atm)
    apply(simp_all add: fresh_atm subst_fresh forget abs_fresh)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (ImpL c M z N u)
  then show ?case  
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)
    apply(subgoal_tac "\<exists>z'::name. z'\<sharp>(P,P{b:=(y).Q},M{u:=<a>.P},N{u:=<a>.P},y,Q,
                        M{b:=(y).Q}{u:=<a>.P{b:=(y).Q}},N{b:=(y).Q}{u:=<a>.P{b:=(y).Q}},z)")
    apply(erule exE)
    apply(simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_ImpL abs_fresh fresh_atm)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp_all add: fresh_atm subst_fresh forget)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
qed

lemma subst_subst2:
  assumes a: "a\<sharp>(b,P,N)" "x\<sharp>(y,P,M)" "b\<sharp>(M,N)" "y\<sharp>P"
  shows "M{a:=(x).N}{y:=<b>.P} = M{y:=<b>.P}{a:=(x).N{y:=<b>.P}}"
using a
proof(nominal_induct M avoiding: a x N y b P rule: trm.strong_induct)
  case (Ax z c)
  then show ?case
    by (auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget trm.inject)
next
  case (Cut d M' u M'')
  then show ?case
    apply(simp add: fresh_atm fresh_prod trm.inject abs_fresh)
    apply(auto)
    apply(simp add: fresh_atm)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh subst_fresh fresh_prod fresh_atm)
    apply(simp add: fresh_prod subst_fresh fresh_atm abs_fresh)
    apply(simp)
    apply(simp add: forget)
    apply(simp add: fresh_atm)
    apply(case_tac "a\<sharp>M'")
    apply(simp add: forget)
    apply(simp add: not_Ax1)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh subst_fresh fresh_prod fresh_atm)
    apply(simp add: fresh_prod subst_fresh fresh_atm abs_fresh)
    apply(auto)[1]
    apply(case_tac "y\<sharp>M''")
    apply(simp add: forget)
    apply(simp add: not_Ax2)
    apply(simp add: forget)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: subst_fresh fresh_atm)
    apply(simp add: abs_fresh subst_fresh)
    apply(auto)[1]
    apply(case_tac "y\<sharp>M''")
    apply(simp add: forget)
    apply(simp add: not_Ax2)
    apply(case_tac "a\<sharp>M'")
    apply(simp add: forget)
    apply(simp add: not_Ax1)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: subst_fresh)
    apply(simp add: subst_fresh abs_fresh)
    apply(simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: subst_fresh fresh_atm)
    apply(simp add: subst_fresh abs_fresh)
    apply(auto)[1]
    apply(case_tac "y\<sharp>M''")
    apply(simp add: forget)
    apply(simp add: not_Ax2)
    done
next
  case (NotR z M' d) 
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(y,P,N,N{y:=<b>.P},M'{d:=(x).N},M'{y:=<b>.P}{d:=(x).N{y:=<b>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_NotR)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_prod subst_fresh fresh_atm)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (NotL d M' z) 
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget trm.inject)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(z,y,P,N,N{y:=<b>.P},M'{y:=<b>.P},M'{y:=<b>.P}{a:=(x).N{y:=<b>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_NotL)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: fresh_prod subst_fresh fresh_atm abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_atm subst_fresh)
    apply(simp)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (AndR d M' e M'' f) 
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget trm.inject)
    apply(subgoal_tac "\<exists>a'::coname. a'\<sharp>(P,b,d,e,N,N{y:=<b>.P},M'{f:=(x).N},M''{f:=(x).N},
                  M'{y:=<b>.P}{f:=(x).N{y:=<b>.P}},M''{y:=<b>.P}{f:=(x).N{y:=<b>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndR)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: fresh_prod subst_fresh fresh_atm abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp add: fresh_atm subst_fresh)
    apply(simp add: fresh_atm)
    apply(simp)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (AndL1 z M' u) 
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget trm.inject)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,b,z,u,x,N,M'{y:=<b>.P},M'{y:=<b>.P}{a:=(x).N{y:=<b>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL1)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: fresh_prod subst_fresh fresh_atm abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (AndL2 z M' u) 
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget trm.inject)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(P,b,z,u,x,N,M'{y:=<b>.P},M'{y:=<b>.P}{a:=(x).N{y:=<b>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL2)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: fresh_prod subst_fresh fresh_atm abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (OrL u M' v M'' w) 
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget trm.inject)
    apply(subgoal_tac "\<exists>z'::name. z'\<sharp>(P,b,u,w,v,N,N{y:=<b>.P},M'{y:=<b>.P},M''{y:=<b>.P},
                  M'{y:=<b>.P}{a:=(x).N{y:=<b>.P}},M''{y:=<b>.P}{a:=(x).N{y:=<b>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrL)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: fresh_prod subst_fresh fresh_atm abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp add: fresh_atm subst_fresh)
    apply(simp add: fresh_atm)
    apply(simp)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (OrR1 e M' f) 
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget trm.inject)
    apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(P,b,e,f,x,N,N{y:=<b>.P},
                                        M'{f:=(x).N},M'{y:=<b>.P}{f:=(x).N{y:=<b>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrR1)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: fresh_prod subst_fresh fresh_atm abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (OrR2 e M' f) 
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget trm.inject)
    apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(P,b,e,f,x,N,N{y:=<b>.P},
                                        M'{f:=(x).N},M'{y:=<b>.P}{f:=(x).N{y:=<b>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrR2)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: fresh_prod subst_fresh fresh_atm abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    done
next
  case (ImpR x e M' f) 
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget trm.inject)
    apply(subgoal_tac "\<exists>c'::coname. c'\<sharp>(P,b,e,f,x,N,N{y:=<b>.P},
                                        M'{f:=(x).N},M'{y:=<b>.P}{f:=(x).N{y:=<b>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_ImpR)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: fresh_prod subst_fresh fresh_atm abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp add: fresh_atm)
    apply(simp add: fresh_atm trm.inject alpha abs_fresh fin_supp abs_supp)
    apply(rule exists_fresh'(2)[OF fs_coname1])
    apply(simp add: fresh_atm trm.inject alpha abs_fresh fin_supp abs_supp)
    done
next
  case (ImpL e M' v M'' w) 
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget trm.inject)
    apply(subgoal_tac "\<exists>z'::name. z'\<sharp>(P,b,e,w,v,N,N{y:=<b>.P},M'{w:=<b>.P},M''{w:=<b>.P},
                  M'{w:=<b>.P}{a:=(x).N{w:=<b>.P}},M''{w:=<b>.P}{a:=(x).N{w:=<b>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_ImpL)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: fresh_prod subst_fresh fresh_atm abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp add: fresh_atm subst_fresh)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
qed

lemma subst_subst3:
  assumes a: "a\<sharp>(P,N,c)" "c\<sharp>(M,N)" "x\<sharp>(y,P,M)" "y\<sharp>(P,x)" "M\<noteq>Ax y a"
  shows "N{x:=<a>.M}{y:=<c>.P} = N{y:=<c>.P}{x:=<a>.(M{y:=<c>.P})}"
using a
proof(nominal_induct N avoiding: x y a c M P rule: trm.strong_induct)
  case (Ax z c)
  then show ?case
    by(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (Cut d M' u M'')
  then show ?case
    apply(simp add: fresh_atm fresh_prod trm.inject abs_fresh)
    apply(auto)
    apply(simp add: fresh_atm)
    apply(simp add: trm.inject)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_prod subst_fresh fresh_atm)
    apply(subgoal_tac "P \<noteq> Ax x c")
    apply(simp)
    apply(simp add: forget)
    apply(clarify)
    apply(simp add: fresh_atm)
    apply(case_tac "x\<sharp>M'")
    apply(simp add: forget)
    apply(simp add: not_Ax2)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_prod subst_fresh fresh_atm)
    apply(simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_prod subst_fresh fresh_atm)
    apply(auto)
    apply(case_tac "y\<sharp>M'")
    apply(simp add: forget)
    apply(simp add: not_Ax2)
    done
next
  case NotR
  then show ?case
    by(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (NotL d M' u)
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(y,P,M,M{y:=<c>.P},M'{x:=<a>.M},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_NotL)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_prod subst_fresh fresh_atm)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(x,y,P,M,M'{y:=<c>.P},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_NotL)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_atm subst_fresh fresh_prod)
    apply(subgoal_tac "P \<noteq> Ax x c")
    apply(simp)
    apply(simp add: forget trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_atm subst_fresh)
    apply(simp add: fresh_atm)
    apply(clarify)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case AndR
  then show ?case
    by(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (AndL1 u M' v)
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(u,y,v,P,M,M{y:=<c>.P},M'{x:=<a>.M},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL1)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_prod subst_fresh fresh_atm)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(x,y,u,v,P,M,M'{y:=<c>.P},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL1)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_atm subst_fresh fresh_prod)
    apply(subgoal_tac "P \<noteq> Ax x c")
    apply(simp)
    apply(simp add: forget trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_atm subst_fresh)
    apply(simp add: fresh_atm)
    apply(clarify)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case (AndL2 u M' v)
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(u,y,v,P,M,M{y:=<c>.P},M'{x:=<a>.M},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL2)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_prod subst_fresh fresh_atm)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(x,y,u,v,P,M,M'{y:=<c>.P},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_AndL2)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_atm subst_fresh fresh_prod)
    apply(subgoal_tac "P \<noteq> Ax x c")
    apply(simp)
    apply(simp add: forget trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_atm subst_fresh)
    apply(simp add: fresh_atm)
    apply(clarify)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case OrR1
  then show ?case
    by(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case OrR2
  then show ?case
    by(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (OrL x1 M' x2 M'' x3)
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(y,P,M,M{y:=<c>.P},M'{x:=<a>.M},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}},
                                      x1,x2,x3,M''{x:=<a>.M},M''{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrL)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_prod subst_fresh fresh_atm)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp add: fresh_atm)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(x,y,P,M,M'{y:=<c>.P},M'{y:=<c>.P}{x:=<a>.M{y:=<c>.P}},
                                      x1,x2,x3,M''{y:=<c>.P},M''{y:=<c>.P}{x:=<a>.M{y:=<c>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_OrL)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_atm subst_fresh fresh_prod)
    apply(simp add: fresh_prod fresh_atm)
    apply(auto)
    apply(simp add: fresh_atm)
    apply(simp add: forget trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_atm subst_fresh)
    apply(simp add: fresh_atm subst_fresh)
    apply(simp add: fresh_atm)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
next
  case ImpR
  then show ?case
    by(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (ImpL d M' x1 M'' x2)
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(y,P,M,M{y:=<c>.P},M'{x2:=<a>.M},M'{y:=<c>.P}{x2:=<a>.M{y:=<c>.P}},
                                      x1,x2,M''{x2:=<a>.M},M''{y:=<c>.P}{x2:=<a>.M{y:=<c>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_ImpL)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_prod subst_fresh fresh_atm)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    apply(subgoal_tac "\<exists>x'::name. x'\<sharp>(x,y,P,M,M'{x2:=<c>.P},M'{x2:=<c>.P}{x:=<a>.M{x2:=<c>.P}},
                                      x1,x2,M''{x2:=<c>.P},M''{x2:=<c>.P}{x:=<a>.M{x2:=<c>.P}})")
    apply(erule exE, simp add: fresh_prod)
    apply(erule conjE)+
    apply(simp add: fresh_fun_simp_ImpL)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp add: fresh_atm subst_fresh fresh_prod)
    apply(simp add: fresh_prod fresh_atm)
    apply(auto)
    apply(simp add: fresh_atm)
    apply(simp add: forget trm.inject alpha)
    apply(rule trans)
    apply(rule substn.simps)
    apply(simp add: fresh_atm subst_fresh)
    apply(simp add: fresh_atm subst_fresh)
    apply(simp add: fresh_atm)
    apply(rule exists_fresh'(1)[OF fs_name1])
    done
qed

lemma subst_subst4:
  assumes a: "x\<sharp>(P,N,y)" "y\<sharp>(M,N)" "a\<sharp>(c,P,M)" "c\<sharp>(P,a)" "M\<noteq>Ax x c"
  shows "N{a:=(x).M}{c:=(y).P} = N{c:=(y).P}{a:=(x).(M{c:=(y).P})}"
using a
proof(nominal_induct N avoiding: x y a c M P rule: trm.strong_induct)
  case (Ax z c)
  then show ?case
    by (auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (Cut d M' u M'')
  then show ?case
    apply(simp add: fresh_atm fresh_prod trm.inject abs_fresh)
    apply(auto)
    apply(simp add: fresh_atm)
    apply(simp add: trm.inject)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh subst_fresh fresh_atm)
    apply(simp add: fresh_prod subst_fresh abs_fresh fresh_atm)
    apply(subgoal_tac "P \<noteq> Ax y a")
    apply(simp)
    apply(simp add: forget)
    apply(clarify)
    apply(simp add: fresh_atm)
    apply(case_tac "a\<sharp>M''")
    apply(simp add: forget)
    apply(simp add: not_Ax1)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: fresh_prod subst_fresh fresh_atm)
    apply(simp add: abs_fresh subst_fresh)
    apply(simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: fresh_prod subst_fresh fresh_atm)
    apply(simp add: abs_fresh subst_fresh)
    apply(auto)
    apply(case_tac "c\<sharp>M''")
    apply(simp add: forget)
    apply(simp add: not_Ax1)
    done
next
  case NotL
  then show ?case
    by(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (NotR u M' d)
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: abs_fresh subst_fresh)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: fresh_prod fresh_atm)
    apply(auto simp add: fresh_atm fresh_prod)[1]
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: fresh_prod fresh_atm subst_fresh)
    apply(simp add: abs_fresh subst_fresh)
    apply(auto simp add: fresh_atm)
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substc.simps)
    apply(simp add: fresh_atm subst_fresh)
    apply(auto simp add: fresh_prod fresh_atm) 
    done
next
  case AndL1
  then show ?case
    by(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case AndL2
  then show ?case
    by(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (AndR d M e M' f)
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: abs_fresh subst_fresh)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substc.simps)
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(simp)
    apply(auto simp add: fresh_atm fresh_prod)[1]
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: subst_fresh fresh_atm fresh_prod)
    apply(simp add: abs_fresh subst_fresh)
    apply(auto simp add: fresh_atm)[1]
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substc.simps)
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(simp)
    apply(auto simp add: fresh_atm fresh_prod)[1]
    done
next
  case OrL
  then show ?case
    by(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (OrR1 d M' e)
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: abs_fresh subst_fresh)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substc.simps)
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: subst_fresh fresh_atm fresh_prod)
    apply(simp add: abs_fresh subst_fresh)
    apply(auto simp add: fresh_atm)[1]
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substc.simps)
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    done
next
  case (OrR2 d M' e)
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: abs_fresh subst_fresh)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substc.simps)
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: subst_fresh fresh_atm fresh_prod)
    apply(simp add: abs_fresh subst_fresh)
    apply(auto simp add: fresh_atm)[1]
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substc.simps)
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    done
next
  case ImpL
  then show ?case
    by(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
next
  case (ImpR u d M' e)
  then show ?case
    apply(auto simp add: subst_fresh abs_fresh fresh_atm fresh_prod forget)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: abs_fresh subst_fresh)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: trm.inject alpha)
    apply(rule trans)
    apply(rule substc.simps)
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(auto simp add: fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)[1]
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(rule sym)
    apply(rule trans)
    apply(rule better_Cut_substc)
    apply(simp add: subst_fresh fresh_atm fresh_prod)
    apply(simp add: abs_fresh subst_fresh)
    apply(auto simp add: fresh_atm)[1]
    apply(simp add: trm.inject alpha forget)
    apply(rule trans)
    apply(rule substc.simps)
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(auto simp add: fresh_prod fresh_atm subst_fresh)[1]
    apply(auto simp add: fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)[1]
    apply(auto simp add: fresh_prod fresh_atm subst_fresh abs_fresh abs_supp fin_supp)[1]
    done
qed

end
