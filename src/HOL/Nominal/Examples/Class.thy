(* $Id$ *)

theory Class 
imports "../Nominal" 
begin

section {* Term-Calculus from Urban's PhD *}

atom_decl name coname

text {* types *}

nominal_datatype ty =
    PROP "string"
  | NOT  "ty"
  | AND  "ty" "ty"   ("_ AND _" [100,100] 100)
  | OR   "ty" "ty"   ("_ OR _" [100,100] 100)
  | IMP  "ty" "ty"   ("_ IMPL _" [100,100] 100)

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

text {* Induction principles *}

thm trm.induct_weak --"weak"
thm trm.induct      --"strong"
thm trm.induct'     --"strong with explicit context (rarely needed)"

text {* named terms *}

nominal_datatype ntrm = Na "\<guillemotleft>name\<guillemotright>trm" ("((_):_)" [100,100] 100)

text {* conamed terms *}

nominal_datatype ctrm = Co "\<guillemotleft>coname\<guillemotright>trm" ("(<_>:_)" [100,100] 100)

text {* renaming functions *}

consts
  nrename :: "trm \<Rightarrow> name \<Rightarrow> name \<Rightarrow> trm"      ("_[_\<turnstile>n>_]" [100,100,100] 100) 
  crename :: "trm \<Rightarrow> coname \<Rightarrow> coname \<Rightarrow> trm"  ("_[_\<turnstile>c>_]" [100,100,100] 100) 

nominal_primrec (freshness_context: "(d::coname,e::coname)") 
  "(Ax x a)[d\<turnstile>c>e] = (if a=d then Ax x e else Ax x a)" 
  "\<lbrakk>a\<sharp>(d,e,N);x\<sharp>M\<rbrakk> \<Longrightarrow> (Cut <a>.M (x).N)[d\<turnstile>c>e] = Cut <a>.(M[d\<turnstile>c>e]) (x).(N[d\<turnstile>c>e])" 
  "(NotR (x).M a)[d\<turnstile>c>e] = (if a=d then NotR (x).(M[d\<turnstile>c>e]) e else NotR (x).(M[d\<turnstile>c>e]) a)" 
  "a\<sharp>(d,e) \<Longrightarrow> (NotL <a>.M x)[d\<turnstile>c>e] = (NotL <a>.(M[d\<turnstile>c>e]) x)" 
  "\<lbrakk>a\<sharp>(d,e,N,c);b\<sharp>(d,e,M,c);b\<noteq>a\<rbrakk> \<Longrightarrow> (AndR <a>.M <b>.N c)[d\<turnstile>c>e] = 
          (if c=d then AndR <a>.(M[d\<turnstile>c>e]) <b>.(N[d \<turnstile>c>e]) e else AndR <a>.(M[d\<turnstile>c>e]) <b>.(N[d\<turnstile>c>e]) c)" 
  "x\<sharp>y \<Longrightarrow> (AndL1 (x).M y)[d\<turnstile>c>e] = AndL1 (x).(M[d\<turnstile>c>e]) y"
  "x\<sharp>y \<Longrightarrow> (AndL2 (x).M y)[d\<turnstile>c>e] = AndL2 (x).(M[d\<turnstile>c>e]) y"
  "a\<sharp>(d,e,b) \<Longrightarrow> (OrR1 <a>.M b)[d\<turnstile>c>e] = (if b=d then OrR1 <a>.(M[d\<turnstile>c>e]) e else OrR1 <a>.(M[d\<turnstile>c>e]) b)"
  "a\<sharp>(d,e,b) \<Longrightarrow> (OrR2 <a>.M b)[d\<turnstile>c>e] = (if b=d then OrR2 <a>.(M[d\<turnstile>c>e]) e else OrR2 <a>.(M[d\<turnstile>c>e]) b)"
  "\<lbrakk>x\<sharp>(N,z);y\<sharp>(M,z);y\<noteq>x\<rbrakk> \<Longrightarrow> (OrL (x).M (y).N z)[d\<turnstile>c>e] = OrL (x).(M[d\<turnstile>c>e]) (y).(N[d\<turnstile>c>e]) z"
  "a\<sharp>(d,e,b) \<Longrightarrow> (ImpR (x).<a>.M b)[d\<turnstile>c>e] = 
       (if b=d then ImpR (x).<a>.(M[d\<turnstile>c>e]) e else ImpR (x).<a>.(M[d\<turnstile>c>e]) b)"
  "\<lbrakk>a\<sharp>(d,e,N);x\<sharp>(M,y)\<rbrakk> \<Longrightarrow> (ImpL <a>.M (x).N y)[d\<turnstile>c>e] = ImpL <a>.(M[d\<turnstile>c>e]) (x).(N[d\<turnstile>c>e]) y"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh abs_supp fin_supp)+
apply(fresh_guess)+
done

nominal_primrec (freshness_context: "(u::name,v::name)") 
  "(Ax x a)[u\<turnstile>n>v] = (if x=u then Ax v a else Ax x a)" 
  "\<lbrakk>a\<sharp>N;x\<sharp>(u,v,M)\<rbrakk> \<Longrightarrow> (Cut <a>.M (x).N)[u\<turnstile>n>v] = Cut <a>.(M[u\<turnstile>n>v]) (x).(N[u\<turnstile>n>v])" 
  "x\<sharp>(u,v) \<Longrightarrow> (NotR (x).M a)[u\<turnstile>n>v] = NotR (x).(M[u\<turnstile>n>v]) a" 
  "(NotL <a>.M x)[u\<turnstile>n>v] = (if x=u then NotL <a>.(M[u\<turnstile>n>v]) v else NotL <a>.(M[u\<turnstile>n>v]) x)" 
  "\<lbrakk>a\<sharp>(N,c);b\<sharp>(M,c);b\<noteq>a\<rbrakk> \<Longrightarrow> (AndR <a>.M <b>.N c)[u\<turnstile>n>v] = AndR <a>.(M[u\<turnstile>n>v]) <b>.(N[u\<turnstile>n>v]) c" 
  "x\<sharp>(u,v,y) \<Longrightarrow> (AndL1 (x).M y)[u\<turnstile>n>v] = (if y=u then AndL1 (x).(M[u\<turnstile>n>v]) v else AndL1 (x).(M[u\<turnstile>n>v]) y)"
  "x\<sharp>(u,v,y) \<Longrightarrow> (AndL2 (x).M y)[u\<turnstile>n>v] = (if y=u then AndL2 (x).(M[u\<turnstile>n>v]) v else AndL2 (x).(M[u\<turnstile>n>v]) y)"
  "a\<sharp>b \<Longrightarrow> (OrR1 <a>.M b)[u\<turnstile>n>v] = OrR1 <a>.(M[u\<turnstile>n>v]) b"
  "a\<sharp>b \<Longrightarrow> (OrR2 <a>.M b)[u\<turnstile>n>v] = OrR2 <a>.(M[u\<turnstile>n>v]) b"
  "\<lbrakk>x\<sharp>(u,v,N,z);y\<sharp>(u,v,M,z);y\<noteq>x\<rbrakk> \<Longrightarrow> (OrL (x).M (y).N z)[u\<turnstile>n>v] = 
        (if z=u then OrL (x).(M[u\<turnstile>n>v]) (y).(N[u\<turnstile>n>v]) v else OrL (x).(M[u\<turnstile>n>v]) (y).(N[u\<turnstile>n>v]) z)"
  "\<lbrakk>a\<sharp>b; x\<sharp>(u,v)\<rbrakk> \<Longrightarrow> (ImpR (x).<a>.M b)[u\<turnstile>n>v] = ImpR (x).<a>.(M[u\<turnstile>n>v]) b"
  "\<lbrakk>a\<sharp>N;x\<sharp>(u,v,M,y)\<rbrakk> \<Longrightarrow> (ImpL <a>.M (x).N y)[u\<turnstile>n>v] = 
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
apply(nominal_induct M avoiding: d e rule: trm.induct)
apply(auto simp add: fresh_bij eq_bij)
done


lemma crename_coname_eqvt[eqvt]:
  fixes pi::"coname prm"
  shows "pi\<bullet>(M[d\<turnstile>c>e]) = (pi\<bullet>M)[(pi\<bullet>d)\<turnstile>c>(pi\<bullet>e)]"
apply(nominal_induct M avoiding: d e rule: trm.induct)
apply(auto simp add: fresh_bij eq_bij)
done

lemma nrename_name_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(M[x\<turnstile>n>y]) = (pi\<bullet>M)[(pi\<bullet>x)\<turnstile>n>(pi\<bullet>y)]"
apply(nominal_induct M avoiding: x y rule: trm.induct)
apply(auto simp add: fresh_bij eq_bij)
done

lemma nrename_coname_eqvt[eqvt]:
  fixes pi::"coname prm"
  shows "pi\<bullet>(M[x\<turnstile>n>y]) = (pi\<bullet>M)[(pi\<bullet>x)\<turnstile>n>(pi\<bullet>y)]"
apply(nominal_induct M avoiding: x y rule: trm.induct)
apply(auto simp add: fresh_bij eq_bij)
done

text {* substitution functions *}

consts
  substn :: "trm \<Rightarrow> name   \<Rightarrow> coname \<Rightarrow> trm \<Rightarrow> trm" ("_[_:=<_>._]" [100,100,100,100] 100) 
  substc :: "trm \<Rightarrow> coname \<Rightarrow> name   \<Rightarrow> trm \<Rightarrow> trm" ("_[_:=(_)._]" [100,100,100,100] 100)

nominal_primrec (freshness_context: "(y::name,c::coname,P::trm)")
  "(Ax x a)[y:=<c>.P] = (if x=y then P[c\<turnstile>c>a] else Ax x a)" 
  "\<lbrakk>a\<sharp>(c,P,N);x\<sharp>(y,c,P,M)\<rbrakk> \<Longrightarrow> 
   (Cut <a>.M (x).N)[y:=<c>.P] = Cut <a>.(M[y:=<c>.P]) (x).(N[y:=<c>.P])" 
  "x\<sharp>(y,c,P) \<Longrightarrow> 
   (NotR (x).M a)[y:=<c>.P] = NotR (x).(M[y:=<c>.P]) a" 
  "a\<sharp>(c,P)\<Longrightarrow>
   (NotL <a>.M x)[y:=<c>.P] = (if x=y then Cut <c>.P (x).(NotL <a>. (M[y:=<c>.P]) x) 
                                      else NotL <a>. (M[y:=<c>.P]) x)" 
  "\<lbrakk>a\<sharp>(c,P,N,d);b\<sharp>(c,P,M,d);b\<noteq>a\<rbrakk> \<Longrightarrow> 
   (AndR <a>.M <b>.N d)[y:=<c>.P] = AndR <a>.(M[y:=<c>.P]) <b>.(N[y:=<c>.P]) d" 
  "x\<sharp>(y,c,P,z) \<Longrightarrow> 
   (AndL1 (x).M z)[y:=<c>.P] = (if z=y then Cut <c>.P (z).AndL1 (x).(M[y:=<c>.P]) z 
                                       else AndL1 (x).(M[y:=<c>.P]) z)"
  "x\<sharp>(y,c,P,z) \<Longrightarrow> 
   (AndL2 (x).M z)[y:=<c>.P] = (if z=y then Cut <c>.P (z).AndL2 (x).(M[y:=<c>.P]) z 
                                       else AndL2 (x).(M[y:=<c>.P]) z)"
  "a\<sharp>(c,P,b) \<Longrightarrow> 
   (OrR1 <a>.M b)[y:=<c>.P] = OrR1 <a>.(M[y:=<c>.P]) b"
  "a\<sharp>(c,P,b) \<Longrightarrow> 
   (OrR2 <a>.M b)[y:=<c>.P] = OrR2 <a>.(M[y:=<c>.P]) b"
  "\<lbrakk>x\<sharp>(y,N,c,P,z);u\<sharp>(y,M,c,P,z);x\<noteq>u\<rbrakk> \<Longrightarrow> 
   (OrL (x).M (u).N z)[y:=<c>.P] = (if z=y then Cut <c>.P (z).(OrL (x).(M[y:=<c>.P]) (u).(N[y:=<c>.P]) z) 
                                           else OrL (x).(M[y:=<c>.P]) (u).(N[y:=<c>.P]) z)"
  "\<lbrakk>a\<sharp>(b,c,P); x\<sharp>(y,c,P)\<rbrakk> \<Longrightarrow> 
   (ImpR (x).<a>.M b)[y:=<c>.P] = ImpR (x).<a>.(M[y:=<c>.P]) b"
  "\<lbrakk>a\<sharp>(N,c,P);x\<sharp>(y,c,P,M,z)\<rbrakk> \<Longrightarrow> 
   (ImpL <a>.M (x).N z)[y:=<c>.P] = (if y=z then Cut <c>.P (z).(ImpL <a>.(M[y:=<c>.P]) (x).(N[y:=<c>.P]) z) 
                                            else ImpL <a>.(M[y:=<c>.P]) (x).(N[y:=<c>.P]) z)"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh abs_supp fs_name1 fs_coname1)+
apply(fresh_guess)+
done

text {* typing contexts *}

types 
  ctxtn = "(name\<times>ty) list"
  ctxtc = "(coname\<times>ty) list"

inductive2
  validc :: "ctxtc \<Rightarrow> bool"
where
  vc1[intro]: "validc []"
| vc2[intro]: "\<lbrakk>a\<sharp>\<Delta>; validc \<Delta>\<rbrakk> \<Longrightarrow> validc ((a,T)#\<Delta>)"  

inductive2
  validn :: "ctxtn \<Rightarrow> bool"
where
  vn1[intro]: "validn []"
| vn2[intro]: "\<lbrakk>x\<sharp>\<Gamma>; validn \<Gamma>\<rbrakk> \<Longrightarrow> validn ((x,T)#\<Gamma>)"

text {* typing relation *}

inductive2
   typing :: "ctxtn \<Rightarrow> trm \<Rightarrow> ctxtc \<Rightarrow> bool" ("_ \<turnstile> _ \<turnstile> _" [100,100,100] 100)
where
  "\<lbrakk>validn \<Gamma>;validc \<Delta>; (x,B)\<in>set \<Gamma>; (a,B)\<in>set \<Delta>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Ax x a \<turnstile> \<Delta>"
| "\<lbrakk>x\<sharp>\<Gamma>; ((x,B)#\<Gamma>) \<turnstile> M \<turnstile> \<Delta>\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> NotR (x).M a \<turnstile> ((a,NOT B)#\<Delta>)"
| "\<lbrakk>a\<sharp>\<Delta>; \<Gamma> \<turnstile> M \<turnstile> ((a,B)#\<Delta>)\<rbrakk> \<Longrightarrow>  ((x,NOT B)#\<Gamma>) \<turnstile> NotL <a>.M x \<turnstile> \<Delta>"
| "\<lbrakk>x\<sharp>\<Gamma>; ((x,B1)#\<Gamma>) \<turnstile> M \<turnstile> \<Delta>\<rbrakk> \<Longrightarrow>  ((y,B1 AND B2)#\<Gamma>) \<turnstile> AndL1 (x).M y \<turnstile> \<Delta>"
| "\<lbrakk>x\<sharp>\<Gamma>; ((x,B2)#\<Gamma>) \<turnstile> M \<turnstile> \<Delta>\<rbrakk> \<Longrightarrow>  ((y,B1 AND B2)#\<Gamma>) \<turnstile> AndL2 (x).M y \<turnstile> \<Delta>"
| "\<lbrakk>a\<sharp>\<Delta>;b\<sharp>\<Delta>; \<Gamma> \<turnstile> M \<turnstile> ((a,B)#\<Delta>); \<Gamma> \<turnstile> N \<turnstile> ((b,C)#\<Delta>)\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> AndR <a>.M <b>.N c \<turnstile> ((c,B AND C)#\<Delta>)"
| "\<lbrakk>x\<sharp>\<Gamma>;y\<sharp>\<Gamma>; ((x,B)#\<Gamma>) \<turnstile> M \<turnstile> \<Delta>; ((y,C)#\<Gamma>) \<turnstile> N \<turnstile> \<Delta>\<rbrakk> \<Longrightarrow>  ((z,B OR C)#\<Gamma>) \<turnstile> OrL (x).M (y).N z \<turnstile> \<Delta>"
| "\<lbrakk>a\<sharp>\<Delta>; \<Gamma> \<turnstile> M \<turnstile> ((a,B1)#\<Delta>)\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> OrR1 <a>.M b \<turnstile> ((b,B1 OR B2)#\<Delta>)"
| "\<lbrakk>a\<sharp>\<Delta>; \<Gamma> \<turnstile> M \<turnstile> ((a,B2)#\<Delta>)\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> OrR2 <a>.M b \<turnstile> ((b,B1 OR B2)#\<Delta>)"
| "\<lbrakk>a\<sharp>\<Delta>;x\<sharp>\<Gamma>; \<Gamma> \<turnstile> M \<turnstile> ((a,B)#\<Delta>); ((x,C)#\<Gamma>) \<turnstile> N \<turnstile> \<Delta>\<rbrakk> \<Longrightarrow>  ((y,B IMPL C)#\<Gamma>) \<turnstile> ImpL <a>.M (x).N y \<turnstile> \<Delta>"
| "\<lbrakk>a\<sharp>\<Delta>;x\<sharp>\<Gamma>; ((x,B)#\<Gamma>) \<turnstile> M \<turnstile> ((a,C)#\<Delta>)\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> ImpR (x).<a>.M b \<turnstile> ((b,B IMPL C)#\<Delta>)"
| "\<lbrakk>a\<sharp>\<Delta>1;x\<sharp>\<Gamma>2; validn(\<Gamma>1@\<Gamma>2); validc (\<Delta>1@\<Delta>2); \<Gamma>1 \<turnstile> M \<turnstile> ((a,B)#\<Delta>1); ((x,B)#\<Gamma>2) \<turnstile> N \<turnstile> \<Delta>2\<rbrakk> 
   \<Longrightarrow>  (\<Gamma>1@\<Gamma>2) \<turnstile> Cut <a>.M (x).N \<turnstile> (\<Delta>1@\<Delta>2)"

text {* relations about freshly introducing a name or coname *} 

inductive2
  fin :: "trm \<times> name \<Rightarrow> bool"
where
  "fin (Ax x a,x)"
| "x\<sharp>M \<Longrightarrow> fin (NotL <a>.M x,x)"
| "y\<sharp>[x].M \<Longrightarrow> fin (AndL1 (x).M y,y)"
| "y\<sharp>[x].M \<Longrightarrow> fin (AndL2 (x).M y,y)"
| "\<lbrakk>z\<sharp>[x].M;z\<sharp>[y].N\<rbrakk> \<Longrightarrow> fin (OrL (x).M (y).N z,z)"
| "\<lbrakk>y\<sharp>M;y\<sharp>[x].N\<rbrakk> \<Longrightarrow> fin (ImpL <a>.M (x).N y,y)"

inductive2
  fic :: "trm \<times> coname \<Rightarrow> bool"
where
  "fic (Ax x a,a)"
| "a\<sharp>M \<Longrightarrow> fic (NotR (x).M a,a)"
| "\<lbrakk>c\<sharp>[a].M;c\<sharp>[b].N\<rbrakk> \<Longrightarrow> fic (AndR <a>.M <b>.N c,c)"
| "b\<sharp>[a].M \<Longrightarrow> fic (OrR1 <a>.M b,b)"
| "b\<sharp>[a].M \<Longrightarrow> fic (OrR2 <a>.M b,b)"
| "\<lbrakk>b\<sharp>[a].M\<rbrakk> \<Longrightarrow> fic (ImpR (x).<a>.M b,b)"

text {* cut-reductions *}

inductive2
  red :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<longrightarrow>\<^isub>c _" [100,100] 100)
where
  "fic (M,a) \<Longrightarrow> Cut <a>.M (x).(Ax x b) \<longrightarrow>\<^isub>c M[a\<turnstile>c>b]"
| "fin (M,x) \<Longrightarrow> Cut <a>.(Ax y a) (x).M \<longrightarrow>\<^isub>c M[x\<turnstile>n>y]"
| "\<lbrakk>fic (NotR (x).M a,a); fin (NotL <b>.N y,y)\<rbrakk> \<Longrightarrow>
   Cut <a>.(NotR (x).M a) (y).(NotL <b>.N y) \<longrightarrow>\<^isub>c Cut <b>.N (x).M" 
| "\<lbrakk>fic (AndR <a1>.M1 <a2>.M2 b,b); fin (AndL1 (x).N y,y)\<rbrakk> \<Longrightarrow>
   Cut <b>.(AndR <a1>.M1 <a2>.M2 b) (y).(AndL1 (x).N y) \<longrightarrow>\<^isub>c Cut <a1>.M1 (x).N"
| "\<lbrakk>fic (AndR <a1>.M1 <a2>.M2 b,b); fin (AndL2 (x).N y,y)\<rbrakk> \<Longrightarrow>
   Cut <b>.(AndR <a1>.M1 <a2>.M2 b) (y).(AndL2 (x).N y) \<longrightarrow>\<^isub>c Cut <a2>.M2 (x).N"
| "\<lbrakk>fic (AndR <a1>.M1 <a2>.M2 b,b); fin (AndL1 (x).N y,y)\<rbrakk> \<Longrightarrow>
   Cut <b>.(AndR <a1>.M1 <a2>.M2 b) (y).(AndL1 (x).N y) \<longrightarrow>\<^isub>c Cut <a1>.M1 (x).N"
| "\<lbrakk>fic (OrR1 <a>.M b,b); fin (OrL (x1).N1 (x2).N2 y,y)\<rbrakk> \<Longrightarrow>
   Cut <b>.(OrR1 <a>.M b) (y).(OrL (x1).N1 (x2).N2 y) \<longrightarrow>\<^isub>c Cut <a>.M (x1).N1"
| "\<lbrakk>fic (OrR2 <a>.M b,b); fin (OrL (x1).N1 (x2).N2 y,y)\<rbrakk> \<Longrightarrow>
   Cut <b>.(OrR2 <a>.M b) (y).(OrL (x1).N1 (x2).N2 y) \<longrightarrow>\<^isub>c Cut <a>.M (x2).N2"
| "\<lbrakk>fin (ImpL <c>.N (y).P z,z); fic (ImpR (x).<a>.M b,b)\<rbrakk> \<Longrightarrow>
   Cut <b>.(ImpR (x).<a>.M b) (z).(ImpL <c>.N (y).P z) \<longrightarrow>\<^isub>c Cut <a>.(Cut <c>.N (x).M) (y).P"
| "\<lbrakk>fin (ImpL <c>.N (y).P z,z); fic (ImpR (x).<a>.M b,b)\<rbrakk> \<Longrightarrow>
   Cut <b>.(ImpR (x).<a>.M b) (z).(ImpL <c>.N (y).P z) \<longrightarrow>\<^isub>c Cut <a>.N (x).(Cut <a>.M (y).P)"
| "\<not>fic (M,a) \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>c M[a:=(x).N]"
| "\<not>fin (N,x) \<Longrightarrow> Cut <a>.M (x).N \<longrightarrow>\<^isub>c N[x:=<a>.M]"

text {* PROOFS *}

lemma validn_eqvt[eqvt]:
  fixes   pi1:: "name prm"
  and     pi2:: "coname prm"
  assumes a: "validn \<Gamma>"
  shows   "validn (pi1\<bullet>\<Gamma>)" and "validn (pi2\<bullet>\<Gamma>)"
using a by (induct) (auto simp add: fresh_bij)

lemma validc_eqvt[eqvt]:
  fixes   pi1:: "name prm"
  and     pi2:: "coname prm"
  assumes a: "validc \<Delta>"
  shows   "validc (pi1\<bullet>\<Delta>)" and "validc (pi2\<bullet>\<Delta>)"
using a by (induct) (auto simp add: fresh_bij)

text {* Weakening Lemma *}

abbreviation
  "subn" :: "ctxtn \<Rightarrow> ctxtn \<Rightarrow> bool" (" _ \<lless>n _ " [80,80] 80) 
where
  "\<Gamma>1 \<lless>n \<Gamma>2 \<equiv> \<forall>x B. (x,B)\<in>set \<Gamma>1 \<longrightarrow> (x,B)\<in>set \<Gamma>2"

abbreviation
  "subc" :: "ctxtc \<Rightarrow> ctxtc \<Rightarrow> bool" (" _ \<lless>c _ " [80,80] 80) 
where
  "\<Delta>1 \<lless>c \<Delta>2 \<equiv> \<forall>a B. (a,B)\<in>set \<Delta>1 \<longrightarrow> (a,B)\<in>set \<Delta>2"


end

