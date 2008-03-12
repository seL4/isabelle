(* $Id$ *)

theory Height
  imports "../Nominal"
begin

text {*  
  A small problem suggested by D. Wang. It shows how
  the height of a lambda-terms behaves under substitution.
*}

atom_decl name

nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

text {* Definition of the height-function on lambda-terms. *} 
consts 
  height :: "lam \<Rightarrow> int"

nominal_primrec
  "height (Var x) = 1"
  "height (App t1 t2) = (max (height t1) (height t2)) + 1"
  "height (Lam [a].t) = (height t) + 1"
  apply(finite_guess add: perm_int_def)+
  apply(rule TrueI)+
  apply(simp add: fresh_int)
  apply(fresh_guess add: perm_int_def)+
  done

text {* Definition of capture-avoiding substitution. *}

consts
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_[_::=_]" [100,100,100] 100)

nominal_primrec
  "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
  "(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
  "\<lbrakk>x\<sharp>y; x\<sharp>t'\<rbrakk> \<Longrightarrow> (Lam [x].t)[y::=t'] = Lam [x].(t[y::=t'])"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(fresh_guess)+
done

text{* The next lemma is needed in the Var-case of the theorem below. *}

lemma height_ge_one: 
  shows "1 \<le> (height e)"
by (nominal_induct e rule: lam.induct) (simp_all)

text {* 
  Unlike the proplem suggested by Wang, however, the 
  theorem is here formulated entirely by using functions. 
*}

theorem height_subst:
  shows "height (e[x::=e']) \<le> ((height e) - 1) + (height e')"
proof (nominal_induct e avoiding: x e' rule: lam.induct)
  case (Var y)
  have "1 \<le> height e'" by (rule height_ge_one)
  then show "height (Var y[x::=e']) \<le> height (Var y) - 1 + height e'" by simp
next
  case (Lam y e1)
  hence ih: "height (e1[x::=e']) \<le> ((height e1) - 1) + (height e')" by simp
  moreover
  have vc: "y\<sharp>x" "y\<sharp>e'" by fact+ (* usual variable convention *)
  ultimately show "height ((Lam [y].e1)[x::=e']) \<le> height (Lam [y].e1) - 1 + height e'" by simp
next    
  case (App e1 e2)
  hence ih1: "height (e1[x::=e']) \<le> ((height e1) - 1) + (height e')" 
    and ih2: "height (e2[x::=e']) \<le> ((height e2) - 1) + (height e')" by simp_all
  then show "height ((App e1 e2)[x::=e']) \<le> height (App e1 e2) - 1 + height e'"  by simp 
qed

theorem height_subst:
  shows "height (e[x::=e']) \<le> ((height e) - 1) + (height e')"
proof (nominal_induct e avoiding: x e' rule: lam.induct)
  case (Var y)
  have "1 \<le> height e'" by (rule height_ge_one)
  then show "height (Var y[x::=e']) \<le> height (Var y) - 1 + height e'" by simp
next
  case (Lam y e1)
  hence ih: "height (e1[x::=e']) \<le> ((height e1) - 1) + (height e')" by simp
  moreover
  have vc: "y\<sharp>x" "y\<sharp>e'" by fact+ (* usual variable convention *)
  ultimately show "height ((Lam [y].e1)[x::=e']) \<le> height (Lam [y].e1) - 1 + height e'" by simp
next    
  case (App e1 e2)
  hence ih1: "height (e1[x::=e']) \<le> ((height e1) - 1) + (height e')" 
    and ih2: "height (e2[x::=e']) \<le> ((height e2) - 1) + (height e')" by simp_all
  then show "height ((App e1 e2)[x::=e']) \<le> height (App e1 e2) - 1 + height e'"  by simp 
qed


end
