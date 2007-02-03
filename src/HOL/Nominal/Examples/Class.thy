(* $Id$ *)

theory Class 
imports "Nominal" 
begin

section {* Term-Calculus from Urban's PhD *}

atom_decl name coname

nominal_datatype trm = 
    Ax   "name" "coname"
  | Cut  "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm"            ("Cut <_>._ [_]._" [100,100,100,100] 100)
  | NotR "\<guillemotleft>name\<guillemotright>trm" "coname"                 ("NotR [_]._ _" [100,100,100] 100)
  | NotL "\<guillemotleft>coname\<guillemotright>trm" "name"                 ("NotL <_>._ _" [100,100,100] 100)
  | AndR "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>coname\<guillemotright>trm" "coname" ("AndR <_>._ <_>._ _" [100,100,100,100,100] 100)
  | AndL1 "\<guillemotleft>name\<guillemotright>trm" "name"                  ("AndL1 [_]._ _" [100,100,100] 100)
  | AndL2 "\<guillemotleft>name\<guillemotright>trm" "name"                  ("AndL2 [_]._ _" [100,100,100] 100)
  | OrR1 "\<guillemotleft>coname\<guillemotright>trm" "coname"               ("OrR1 <_>._ _" [100,100,100] 100)
  | OrR2 "\<guillemotleft>coname\<guillemotright>trm" "coname"               ("OrR2 <_>._ _" [100,100,100] 100)
  | OrL "\<guillemotleft>name\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"        ("OrL [_]._ [_]._ _" [100,100,100,100,100] 100)
  | ImpR "\<guillemotleft>name\<guillemotright>(\<guillemotleft>coname\<guillemotright>trm)" "coname"       ("ImpR [_].<_>._ _" [100,100,100,100] 100)
  | ImpL "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"     ("ImpL <_>._ [_]._ _" [100,100,100,100,100] 100)

text {* Induction principles *}

thm trm.induct_weak --"weak"
thm trm.induct      --"strong"
thm trm.induct'     --"strong with explicit context (rarely needed)"

text {* named terms *}

nominal_datatype ntrm = Na "\<guillemotleft>name\<guillemotright>trm" ("([_]:_)" [100,100] 100)

text {* conamed terms *}

nominal_datatype ctrm = Co "\<guillemotleft>coname\<guillemotright>trm" ("(<_>:_)" [100,100] 100)

lemma eq_eqvt_name[eqvt]:
  fixes pi::"name prm"
  and   x::"'a::pt_name"
  shows "pi\<bullet>(x=y) = ((pi\<bullet>x)=(pi\<bullet>y))"
  by (simp add: perm_bool perm_bij)

lemma eq_eqvt_coname[eqvt]:
  fixes pi::"coname prm"
  and   x::"'a::pt_coname"
  shows "pi\<bullet>(x=y) = ((pi\<bullet>x)=(pi\<bullet>y))"
  by (simp add: perm_bool perm_bij)

text {* renaming functions *}

consts
  nrename :: "trm \<Rightarrow> name \<Rightarrow> name \<Rightarrow> trm"      ("_[_\<turnstile>n>_]" [100,100,100] 100) 
  crename :: "trm \<Rightarrow> coname \<Rightarrow> coname \<Rightarrow> trm"  ("_[_\<turnstile>c>_]" [100,100,100] 100) 

nominal_primrec (freshness_context: "(d::coname,e::coname)") 
  "(Ax x a)[d\<turnstile>c>e] = (if a=d then Ax x e else Ax x a)" 
  "\<lbrakk>a\<sharp>(d,e,N);x\<sharp>M\<rbrakk> \<Longrightarrow> (Cut <a>.M [x].N)[d\<turnstile>c>e] = Cut <a>.(M[d\<turnstile>c>e]) [x].(N[d\<turnstile>c>e])" 
  "(NotR [x].M a)[d\<turnstile>c>e] = (if a=d then NotR [x].(M[d\<turnstile>c>e]) e else NotR [x].(M[d\<turnstile>c>e]) a)" 
  "a\<sharp>(d,e) \<Longrightarrow> (NotL <a>.M x)[d\<turnstile>c>e] = (NotL <a>.(M[d\<turnstile>c>e]) x)" 
  "\<lbrakk>a\<sharp>(d,e,N,c);b\<sharp>(d,e,M,c);b\<noteq>a\<rbrakk> \<Longrightarrow> (AndR <a>.M <b>.N c)[d\<turnstile>c>e] = 
          (if c=d then AndR <a>.(M[d\<turnstile>c>e]) <b>.(N[d \<turnstile>c>e]) e else AndR <a>.(M[d\<turnstile>c>e]) <b>.(N[d\<turnstile>c>e]) c)" 
  "x\<sharp>y \<Longrightarrow> (AndL1 [x].M y)[d\<turnstile>c>e] = AndL1 [x].(M[d\<turnstile>c>e]) y"
  "x\<sharp>y \<Longrightarrow> (AndL2 [x].M y)[d\<turnstile>c>e] = AndL2 [x].(M[d\<turnstile>c>e]) y"
  "a\<sharp>(d,e,b) \<Longrightarrow> (OrR1 <a>.M b)[d\<turnstile>c>e] = (if b=d then OrR1 <a>.(M[d\<turnstile>c>e]) e else OrR1 <a>.(M[d\<turnstile>c>e]) b)"
  "a\<sharp>(d,e,b) \<Longrightarrow> (OrR2 <a>.M b)[d\<turnstile>c>e] = (if b=d then OrR2 <a>.(M[d\<turnstile>c>e]) e else OrR2 <a>.(M[d\<turnstile>c>e]) b)"
  "\<lbrakk>x\<sharp>(N,z);y\<sharp>(M,z);y\<noteq>x\<rbrakk> \<Longrightarrow> (OrL [x].M [y].N z)[d\<turnstile>c>e] = OrL [x].(M[d\<turnstile>c>e]) [y].(N[d\<turnstile>c>e]) z"
  "a\<sharp>(d,e,b) \<Longrightarrow> (ImpR [x].<a>.M b)[d\<turnstile>c>e] = 
       (if b=d then ImpR [x].<a>.(M[d\<turnstile>c>e]) e else ImpR [x].<a>.(M[d\<turnstile>c>e]) b)"
  "\<lbrakk>a\<sharp>(d,e,N);x\<sharp>(M,y)\<rbrakk> \<Longrightarrow> (ImpL <a>.M [x].N y)[d\<turnstile>c>e] = ImpL <a>.(M[d\<turnstile>c>e]) [x].(N[d\<turnstile>c>e]) y"
apply(finite_guess add: eqvt perm_if fs_coname1 fs_name1 | 
      perm_simp add: abs_fresh abs_supp fs_name1 fs_coname1)+
apply(fresh_guess add: eqvt perm_if fs_coname1 fs_name1 | perm_simp add: fresh_atm)+
done

nominal_primrec (freshness_context: "(u::name,v::name)") 
  "(Ax x a)[u\<turnstile>n>v] = (if x=u then Ax v a else Ax x a)" 
  "\<lbrakk>a\<sharp>N;x\<sharp>(u,v,M)\<rbrakk> \<Longrightarrow> (Cut <a>.M [x].N)[u\<turnstile>n>v] = Cut <a>.(M[u\<turnstile>n>v]) [x].(N[u\<turnstile>n>v])" 
  "x\<sharp>(u,v) \<Longrightarrow> (NotR [x].M a)[u\<turnstile>n>v] = NotR [x].(M[u\<turnstile>n>v]) a" 
  "(NotL <a>.M x)[u\<turnstile>n>v] = (if x=u then NotL <a>.(M[u\<turnstile>n>v]) v else NotL <a>.(M[u\<turnstile>n>v]) x)" 
  "\<lbrakk>a\<sharp>(N,c);b\<sharp>(M,c);b\<noteq>a\<rbrakk> \<Longrightarrow> (AndR <a>.M <b>.N c)[u\<turnstile>n>v] = AndR <a>.(M[u\<turnstile>n>v]) <b>.(N[u\<turnstile>n>v]) c" 
  "x\<sharp>(u,v,y) \<Longrightarrow> (AndL1 [x].M y)[u\<turnstile>n>v] = (if y=u then AndL1 [x].(M[u\<turnstile>n>v]) v else AndL1 [x].(M[u\<turnstile>n>v]) y)"
  "x\<sharp>(u,v,y) \<Longrightarrow> (AndL2 [x].M y)[u\<turnstile>n>v] = (if y=u then AndL2 [x].(M[u\<turnstile>n>v]) v else AndL2 [x].(M[u\<turnstile>n>v]) y)"
  "a\<sharp>b \<Longrightarrow> (OrR1 <a>.M b)[u\<turnstile>n>v] = OrR1 <a>.(M[u\<turnstile>n>v]) b"
  "a\<sharp>b \<Longrightarrow> (OrR2 <a>.M b)[u\<turnstile>n>v] = OrR2 <a>.(M[u\<turnstile>n>v]) b"
  "\<lbrakk>x\<sharp>(u,v,N,z);y\<sharp>(u,v,M,z);y\<noteq>x\<rbrakk> \<Longrightarrow> (OrL [x].M [y].N z)[u\<turnstile>n>v] = 
        (if z=u then OrL [x].(M[u\<turnstile>n>v]) [y].(N[u\<turnstile>n>v]) v else OrL [x].(M[u\<turnstile>n>v]) [y].(N[u\<turnstile>n>v]) z)"
  "\<lbrakk>a\<sharp>b; x\<sharp>(u,v)\<rbrakk> \<Longrightarrow> (ImpR [x].<a>.M b)[u\<turnstile>n>v] = ImpR [x].<a>.(M[u\<turnstile>n>v]) b"
  "\<lbrakk>a\<sharp>N;x\<sharp>(u,v,M,y)\<rbrakk> \<Longrightarrow> (ImpL <a>.M [x].N y)[u\<turnstile>n>v] = 
        (if y=u then ImpL <a>.(M[u\<turnstile>n>v]) [x].(N[u\<turnstile>n>v]) v else ImpL <a>.(M[u\<turnstile>n>v]) [x].(N[u\<turnstile>n>v]) y)"
apply(finite_guess add: eqvt perm_if fs_coname1 fs_name1 | 
      perm_simp add: abs_fresh abs_supp fresh_prod fs_name1 fs_coname1)+
apply(fresh_guess add: eqvt perm_if fs_coname1 fs_name1 | perm_simp add: fresh_atm)+
done

text {* We should now define the two forms of substitition :o( *}

consts
  substn :: "trm \<Rightarrow> name   \<Rightarrow> ctrm \<Rightarrow> trm" ("_[_::n=_]" [100,100,100] 100) 
  substc :: "trm \<Rightarrow> coname \<Rightarrow> ntrm \<Rightarrow> trm" ("_[_::c=_]" [100,100,100] 100)

end

