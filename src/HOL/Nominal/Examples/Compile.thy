(* The definitions for a challenge suggested by Adam Chlipala *)

theory Compile
imports "HOL-Nominal.Nominal"
begin

atom_decl name 

nominal_datatype data = 
    DNat
  | DProd "data" "data"
  | DSum "data" "data"

nominal_datatype ty = 
    Data "data"
  | Arrow "ty" "ty" (\<open>_\<rightarrow>_\<close> [100,100] 100)

nominal_datatype trm = 
  Var "name"
  | Lam "\<guillemotleft>name\<guillemotright>trm" (\<open>Lam [_]._\<close> [100,100] 100)
  | App "trm" "trm"
  | Const "nat"
  | Pr "trm" "trm"
  | Fst "trm"
  | Snd "trm"
  | InL "trm"
  | InR "trm"
  | Case "trm" "\<guillemotleft>name\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" 
          (\<open>Case _ of inl _ \<rightarrow> _ | inr _ \<rightarrow> _\<close> [100,100,100,100,100] 100)

nominal_datatype dataI = OneI | NatI

nominal_datatype tyI = 
    DataI "dataI"
  | ArrowI "tyI" "tyI" (\<open>_\<rightarrow>_\<close> [100,100] 100)

nominal_datatype trmI = 
    IVar "name"
  | ILam "\<guillemotleft>name\<guillemotright>trmI" (\<open>ILam [_]._\<close> [100,100] 100)
  | IApp "trmI" "trmI"
  | IUnit
  | INat "nat"
  | ISucc "trmI"
  | IAss "trmI" "trmI" (\<open>_\<mapsto>_\<close> [100,100] 100)
  | IRef "trmI" 
  | ISeq "trmI" "trmI" (\<open>_;;_\<close> [100,100] 100)
  | Iif "trmI" "trmI" "trmI"

text \<open>valid contexts\<close>

inductive 
  valid :: "(name\<times>'a::pt_name) list \<Rightarrow> bool"
where
  v1[intro]: "valid []"
| v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)" (* maybe dom of \<Gamma> *)

text \<open>typing judgements for trms\<close>

inductive 
  typing :: "(name\<times>ty) list\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" (\<open> _ \<turnstile> _ : _ \<close> [80,80,80] 80)
where
  t0[intro]: "\<lbrakk>valid \<Gamma>; (x,\<tau>)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Var x : \<tau>"
| t1[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : \<tau>1\<rightarrow>\<tau>2; \<Gamma> \<turnstile> e2 : \<tau>1\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : \<tau>2"
| t2[intro]: "\<lbrakk>x\<sharp>\<Gamma>;((x,\<tau>1)#\<Gamma>) \<turnstile> t : \<tau>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].t : \<tau>1\<rightarrow>\<tau>2"
| t3[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Const n : Data(DNat)"
| t4[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : Data(\<sigma>1); \<Gamma> \<turnstile> e2 : Data(\<sigma>2)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Pr e1 e2 : Data (DProd \<sigma>1 \<sigma>2)"
| t5[intro]: "\<lbrakk>\<Gamma> \<turnstile> e : Data(DProd \<sigma>1 \<sigma>2)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Fst e : Data(\<sigma>1)"
| t6[intro]: "\<lbrakk>\<Gamma> \<turnstile> e : Data(DProd \<sigma>1 \<sigma>2)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Snd e : Data(\<sigma>2)"
| t7[intro]: "\<lbrakk>\<Gamma> \<turnstile> e : Data(\<sigma>1)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> InL e : Data(DSum \<sigma>1 \<sigma>2)"
| t8[intro]: "\<lbrakk>\<Gamma> \<turnstile> e : Data(\<sigma>2)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> InR e : Data(DSum \<sigma>1 \<sigma>2)"
| t9[intro]: "\<lbrakk>x1\<sharp>\<Gamma>; x2\<sharp>\<Gamma>; \<Gamma> \<turnstile> e: Data(DSum \<sigma>1 \<sigma>2); 
             ((x1,Data(\<sigma>1))#\<Gamma>) \<turnstile> e1 : \<tau>; ((x2,Data(\<sigma>2))#\<Gamma>) \<turnstile> e2 : \<tau>\<rbrakk> 
             \<Longrightarrow> \<Gamma> \<turnstile> (Case e of inl x1 \<rightarrow> e1 | inr x2 \<rightarrow> e2) : \<tau>"

text \<open>typing judgements for Itrms\<close>

inductive 
  Ityping :: "(name\<times>tyI) list\<Rightarrow>trmI\<Rightarrow>tyI\<Rightarrow>bool" (\<open> _ I\<turnstile> _ : _ \<close> [80,80,80] 80)
where
  t0[intro]: "\<lbrakk>valid \<Gamma>; (x,\<tau>)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> I\<turnstile> IVar x : \<tau>"
| t1[intro]: "\<lbrakk>\<Gamma> I\<turnstile> e1 : \<tau>1\<rightarrow>\<tau>2; \<Gamma> I\<turnstile> e2 : \<tau>1\<rbrakk>\<Longrightarrow> \<Gamma> I\<turnstile> IApp e1 e2 : \<tau>2"
| t2[intro]: "\<lbrakk>x\<sharp>\<Gamma>;((x,\<tau>1)#\<Gamma>) I\<turnstile> t : \<tau>2\<rbrakk> \<Longrightarrow> \<Gamma> I\<turnstile> ILam [x].t : \<tau>1\<rightarrow>\<tau>2"
| t3[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> I\<turnstile> IUnit : DataI(OneI)"
| t4[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> I\<turnstile> INat(n) : DataI(NatI)"
| t5[intro]: "\<Gamma> I\<turnstile> e : DataI(NatI) \<Longrightarrow> \<Gamma> I\<turnstile> ISucc(e) : DataI(NatI)"
| t6[intro]: "\<lbrakk>\<Gamma> I\<turnstile> e : DataI(NatI)\<rbrakk> \<Longrightarrow> \<Gamma> I\<turnstile> IRef e : DataI (NatI)"
| t7[intro]: "\<lbrakk>\<Gamma> I\<turnstile> e1 : DataI(NatI); \<Gamma> I\<turnstile> e2 : DataI(NatI)\<rbrakk> \<Longrightarrow> \<Gamma> I\<turnstile> e1\<mapsto>e2 : DataI(OneI)"
| t8[intro]: "\<lbrakk>\<Gamma> I\<turnstile> e1 : DataI(NatI); \<Gamma> I\<turnstile> e2 : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> I\<turnstile> e1;;e2 : \<tau>"
| t9[intro]: "\<lbrakk>\<Gamma> I\<turnstile> e: DataI(NatI); \<Gamma> I\<turnstile> e1 : \<tau>; \<Gamma> I\<turnstile> e2 : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> I\<turnstile> Iif e e1 e2 : \<tau>"

text \<open>capture-avoiding substitution\<close>

class subst =
  fixes subst :: "'a \<Rightarrow> name \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>_[_::=_]\<close> [100,100,100] 100)

instantiation trm :: subst
begin

nominal_primrec subst_trm
where
  "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
| "(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
| "\<lbrakk>x\<sharp>y; x\<sharp>t'\<rbrakk> \<Longrightarrow> (Lam [x].t)[y::=t'] = Lam [x].(t[y::=t'])"
| "(Const n)[y::=t'] = Const n"
| "(Pr e1 e2)[y::=t'] = Pr (e1[y::=t']) (e2[y::=t'])"
| "(Fst e)[y::=t'] = Fst (e[y::=t'])"
| "(Snd e)[y::=t'] = Snd (e[y::=t'])"
| "(InL e)[y::=t'] = InL (e[y::=t'])"
| "(InR e)[y::=t'] = InR (e[y::=t'])"
| "\<lbrakk>z\<noteq>x; x\<sharp>y; x\<sharp>e; x\<sharp>e2; z\<sharp>y; z\<sharp>e; z\<sharp>e1; x\<sharp>t'; z\<sharp>t'\<rbrakk> \<Longrightarrow>
     (Case e of inl x \<rightarrow> e1 | inr z \<rightarrow> e2)[y::=t'] =
       (Case (e[y::=t']) of inl x \<rightarrow> (e1[y::=t']) | inr z \<rightarrow> (e2[y::=t']))"
  by(finite_guess | simp add: abs_fresh | fresh_guess)+

instance ..

end

instantiation trmI :: subst
begin

nominal_primrec subst_trmI
where
  "(IVar x)[y::=t'] = (if x=y then t' else (IVar x))"
| "(IApp t1 t2)[y::=t'] = IApp (t1[y::=t']) (t2[y::=t'])"
| "\<lbrakk>x\<sharp>y; x\<sharp>t'\<rbrakk> \<Longrightarrow> (ILam [x].t)[y::=t'] = ILam [x].(t[y::=t'])"
| "(INat n)[y::=t'] = INat n"
| "(IUnit)[y::=t'] = IUnit"
| "(ISucc e)[y::=t'] = ISucc (e[y::=t'])"
| "(IAss e1 e2)[y::=t'] = IAss (e1[y::=t']) (e2[y::=t'])"
| "(IRef e)[y::=t'] = IRef (e[y::=t'])"
| "(ISeq e1 e2)[y::=t'] = ISeq (e1[y::=t']) (e2[y::=t'])"
| "(Iif e e1 e2)[y::=t'] = Iif (e[y::=t']) (e1[y::=t']) (e2[y::=t'])"
  by(finite_guess | simp add: abs_fresh | fresh_guess)+

instance ..

end

lemma Isubst_eqvt[eqvt]:
  fixes pi::"name prm"
  and   t1::"trmI"
  and   t2::"trmI"
  and   x::"name"
  shows "pi\<bullet>(t1[x::=t2]) = ((pi\<bullet>t1)[(pi\<bullet>x)::=(pi\<bullet>t2)])"
  by (nominal_induct t1 avoiding: x t2 rule: trmI.strong_induct)
     (simp_all add: subst_trmI.simps eqvts fresh_bij)

lemma Isubst_supp:
  fixes t1::"trmI"
  and   t2::"trmI"
  and   x::"name"
  shows "((supp (t1[x::=t2]))::name set) \<subseteq> (supp t2)\<union>((supp t1)-{x})"
proof (nominal_induct t1 avoiding: x t2 rule: trmI.strong_induct)
  case (IVar name)
  then show ?case
    by (simp add: supp_atm trmI.supp(1))
qed (fastforce simp add: subst_trmI.simps trmI.supp supp_atm abs_supp supp_nat)+

lemma Isubst_fresh:
  fixes x::"name"
  and   y::"name"
  and   t1::"trmI"
  and   t2::"trmI"
  assumes "x\<sharp>[y].t1" "x\<sharp>t2"
  shows "x\<sharp>(t1[y::=t2])"
  using assms Isubst_supp abs_supp(2)  unfolding fresh_def Isubst_supp by fastforce

text \<open>big-step evaluation for trms\<close>

inductive 
  big :: "trm\<Rightarrow>trm\<Rightarrow>bool" (\<open>_ \<Down> _\<close> [80,80] 80)
where
  b0[intro]: "Lam [x].e \<Down> Lam [x].e"
| b1[intro]: "\<lbrakk>e1\<Down>Lam [x].e; e2\<Down>e2'; e[x::=e2']\<Down>e'\<rbrakk> \<Longrightarrow> App e1 e2 \<Down> e'"
| b2[intro]: "Const n \<Down> Const n"
| b3[intro]: "\<lbrakk>e1\<Down>e1'; e2\<Down>e2'\<rbrakk> \<Longrightarrow> Pr e1 e2 \<Down> Pr e1' e2'"
| b4[intro]: "e\<Down>Pr e1 e2 \<Longrightarrow> Fst e\<Down>e1"
| b5[intro]: "e\<Down>Pr e1 e2 \<Longrightarrow> Snd e\<Down>e2"
| b6[intro]: "e\<Down>e' \<Longrightarrow> InL e \<Down> InL e'"
| b7[intro]: "e\<Down>e' \<Longrightarrow> InR e \<Down> InR e'"
| b8[intro]: "\<lbrakk>e\<Down>InL e'; e1[x::=e']\<Down>e''\<rbrakk> \<Longrightarrow> Case e of inl x1 \<rightarrow> e1 | inr x2 \<rightarrow> e2 \<Down> e''"
| b9[intro]: "\<lbrakk>e\<Down>InR e'; e2[x::=e']\<Down>e''\<rbrakk> \<Longrightarrow> Case e of inl x1 \<rightarrow> e1 | inr x2 \<rightarrow> e2 \<Down> e''"

inductive 
  Ibig :: "((nat\<Rightarrow>nat)\<times>trmI)\<Rightarrow>((nat\<Rightarrow>nat)\<times>trmI)\<Rightarrow>bool" (\<open>_ I\<Down> _\<close> [80,80] 80)
where
  m0[intro]: "(m,ILam [x].e) I\<Down> (m,ILam [x].e)"
| m1[intro]: "\<lbrakk>(m,e1)I\<Down>(m',ILam [x].e); (m',e2)I\<Down>(m'',e3); (m'',e[x::=e3])I\<Down>(m''',e4)\<rbrakk> 
            \<Longrightarrow> (m,IApp e1 e2) I\<Down> (m''',e4)"
| m2[intro]: "(m,IUnit) I\<Down> (m,IUnit)"
| m3[intro]: "(m,INat(n))I\<Down>(m,INat(n))"
| m4[intro]: "(m,e)I\<Down>(m',INat(n)) \<Longrightarrow> (m,ISucc(e))I\<Down>(m',INat(n+1))"
| m5[intro]: "(m,e)I\<Down>(m',INat(n)) \<Longrightarrow> (m,IRef(e))I\<Down>(m',INat(m' n))"
| m6[intro]: "\<lbrakk>(m,e1)I\<Down>(m',INat(n1)); (m',e2)I\<Down>(m'',INat(n2))\<rbrakk> \<Longrightarrow> (m,e1\<mapsto>e2)I\<Down>(m''(n1:=n2),IUnit)"
| m7[intro]: "\<lbrakk>(m,e1)I\<Down>(m',IUnit); (m',e2)I\<Down>(m'',e)\<rbrakk> \<Longrightarrow> (m,e1;;e2)I\<Down>(m'',e)"
| m8[intro]: "\<lbrakk>(m,e)I\<Down>(m',INat(n)); n\<noteq>0; (m',e1)I\<Down>(m'',e)\<rbrakk> \<Longrightarrow> (m,Iif e e1 e2)I\<Down>(m'',e)"
| m9[intro]: "\<lbrakk>(m,e)I\<Down>(m',INat(0)); (m',e2)I\<Down>(m'',e)\<rbrakk> \<Longrightarrow> (m,Iif e e1 e2)I\<Down>(m'',e)"

text \<open>Translation functions\<close>

nominal_primrec
  trans :: "trm \<Rightarrow> trmI"
where
  "trans (Var x) = (IVar x)"
| "trans (App e1 e2) = IApp (trans e1) (trans e2)"
| "trans (Lam [x].e) = ILam [x].(trans e)"
| "trans (Const n) = INat n"
| "trans (Pr e1 e2) = 
       (let limit = IRef(INat 0) in 
        let v1 = (trans e1) in 
        let v2 = (trans e2) in 
        (((ISucc limit)\<mapsto>v1);;(ISucc(ISucc limit)\<mapsto>v2));;(INat 0 \<mapsto> ISucc(ISucc(limit))))"
| "trans (Fst e) = IRef (ISucc (trans e))"
| "trans (Snd e) = IRef (ISucc (ISucc (trans e)))"
| "trans (InL e) = 
        (let limit = IRef(INat 0) in 
         let v = (trans e) in 
         (((ISucc limit)\<mapsto>INat(0));;(ISucc(ISucc limit)\<mapsto>v));;(INat 0 \<mapsto> ISucc(ISucc(limit))))"
| "trans (InR e) = 
        (let limit = IRef(INat 0) in 
         let v = (trans e) in 
         (((ISucc limit)\<mapsto>INat(1));;(ISucc(ISucc limit)\<mapsto>v));;(INat 0 \<mapsto> ISucc(ISucc(limit))))"
| "\<lbrakk>x2\<noteq>x1; x1\<sharp>e; x1\<sharp>e2; x2\<sharp>e; x2\<sharp>e1\<rbrakk> \<Longrightarrow> 
   trans (Case e of inl x1 \<rightarrow> e1 | inr x2 \<rightarrow> e2) =
       (let v = (trans e) in
        let v1 = (trans e1) in
        let v2 = (trans e2) in 
        Iif (IRef (ISucc v)) (v2[x2::=IRef (ISucc (ISucc v))]) (v1[x1::=IRef (ISucc (ISucc v))]))"
  unfolding Let_def
  by(finite_guess | simp add: abs_fresh Isubst_fresh | fresh_guess)+

nominal_primrec
  trans_type :: "ty \<Rightarrow> tyI"
where
  "trans_type (Data \<sigma>) = DataI(NatI)"
| "trans_type (\<tau>1\<rightarrow>\<tau>2) = (trans_type \<tau>1)\<rightarrow>(trans_type \<tau>2)"
  by (rule TrueI)+

end
