(* $Id$ *)

(*  Simple, but artificial, problem suggested by D. Wang *)

theory Height
imports "Nominal"
begin

atom_decl name

nominal_datatype lam = Var "name"
                     | App "lam" "lam"
                     | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

text {* definition of the height-function by "structural recursion" ;o) *} 

constdefs 
  height_Var :: "name \<Rightarrow> int"
  "height_Var \<equiv> \<lambda>_. 1"
  
  height_App :: "lam\<Rightarrow>lam\<Rightarrow>int\<Rightarrow>int\<Rightarrow>int"
  "height_App \<equiv> \<lambda>_ _ n1 n2. (max n1 n2)+1"

  height_Lam :: "name\<Rightarrow>lam\<Rightarrow>int\<Rightarrow>int"
  "height_Lam \<equiv> \<lambda>_ _ n. n+1"

  height :: "lam \<Rightarrow> int"
  "height \<equiv> lam_rec height_Var height_App height_Lam"

text {* show that height is a function *}
lemma fin_supp_height:
  shows "finite ((supp height_Var)::name set)"
  and   "finite ((supp height_App)::name set)"
  and   "finite ((supp height_Lam)::name set)"
  by (finite_guess add: height_Var_def height_App_def height_Lam_def perm_int_def fs_name1)+

lemma fcb_height_Lam:
  assumes fr: "a\<sharp>height_Lam"
  shows "a\<sharp>height_Lam a t n"
apply(simp add: height_Lam_def perm_int_def fresh_def supp_int)
done

text {* derive the characteristic equations for height from the iteration combinator *}

lemmas lam_recs = lam.recs[where P="\<lambda>_. True" and z="()", simplified]

lemma height[simp]:
  shows "height (Var c) = 1"
  and   "height (App t1 t2) = (max (height t1) (height t2))+1"
  and   "height (Lam [a].t) = (height t)+1"
apply(simp add: height_def)
apply(simp add: lam_recs fin_supp_height fcb_height_Lam supp_unit)
apply(simp add: height_Var_def)
apply(simp add: height_def)
apply(simp add: lam_recs fin_supp_height fcb_height_Lam supp_unit)
apply(simp add: height_App_def)
apply(simp add: height_def)
apply(rule trans)
apply(rule lam_recs)
apply(rule fin_supp_height)+
apply(simp add: supp_unit)
apply(rule fcb_height_Lam)
apply(assumption)
apply(fresh_guess add: height_Var_def perm_int_def)
apply(fresh_guess add: height_App_def perm_int_def)
apply(fresh_guess add: height_Lam_def perm_int_def)
apply(simp add: height_Lam_def)
done

text {* define capture-avoiding substitution *}

constdefs 
  subst_Var :: "name \<Rightarrow> lam \<Rightarrow> name \<Rightarrow> lam"
  "subst_Var x t' \<equiv> \<lambda>y. (if y=x then t' else (Var y))"
  
  subst_App :: "name \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam"
  "subst_App x t' \<equiv> \<lambda>_ _ r1 r2. App r1 r2"

  subst_Lam :: "name \<Rightarrow> lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam"
  "subst_Lam x t' \<equiv> \<lambda>a _ r. Lam [a].r"

  subst_lam :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam" ("_[_::=_]" [100,100,100] 100)
  "t[x::=t'] \<equiv> (lam_rec (subst_Var x t') (subst_App x t') (subst_Lam x t')) t"

lemma supports_subst_Var:
  shows "((supp (x,t))::name set) supports (subst_Var x t)"
apply(supports_simp add: subst_Var_def)
apply(rule impI)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(perm_simp)
done

lemma fin_supp_subst:
  shows "finite ((supp (subst_Var x t))::name set)"
  and   "finite ((supp (subst_App x t))::name set)"
  and   "finite ((supp (subst_Lam x t))::name set)"
proof -
  case goal1
  have f: "finite ((supp (x,t))::name set)" by (simp add: fs_name1)
  then have "supp (subst_Var x t) \<subseteq> ((supp (x,t))::name set)"
    using supp_is_subset[OF supports_subst_Var] by simp
  then show "finite ((supp (subst_Var x t))::name set)" using f by (simp add: finite_subset)
qed (finite_guess add: subst_App_def subst_Lam_def fs_name1)+

lemma fcb_subst_Lam:
  assumes fr: "a\<sharp>(subst_Lam y t')" 
  shows "a\<sharp>(subst_Lam y t') a t r"
  by (simp add: subst_Lam_def abs_fresh)

lemma subst_lam[simp]:
  shows "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
  and   "(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
  and   "\<lbrakk>a\<sharp>y; a\<sharp>t'\<rbrakk> \<Longrightarrow> (Lam [a].t)[y::=t'] = Lam [a].(t[y::=t'])"
apply(unfold subst_lam_def)
apply(simp add: lam_recs fin_supp_subst fcb_subst_Lam supp_unit)
apply(simp add: subst_Var_def)
apply(simp add: lam_recs fin_supp_subst fcb_subst_Lam supp_unit)
apply(simp only: subst_App_def)
apply(rule trans)
apply(rule lam_recs)
apply(rule fin_supp_subst)+
apply(simp add: supp_unit)
apply(rule fcb_subst_Lam)
apply(assumption)
apply(rule supports_fresh, rule supports_subst_Var, simp add: fs_name1, simp add: fresh_def supp_prod)
apply(fresh_guess add: fresh_prod subst_App_def fs_name1)
apply(fresh_guess add: fresh_prod subst_Lam_def fs_name1)
apply(simp add: subst_Lam_def)
done

text{* the next lemma is needed in the Var-case of the theorem *}

lemma height_ge_one: 
  shows "1 \<le> (height e)"
  by (nominal_induct e rule: lam.induct) 
     (simp | arith)+

text {* unlike the proplem suggested by Wang, however, the 
        theorem is formulated here entirely by using functions *}

theorem height_subst:
  shows "height (e[x::=e']) \<le> (((height e) - 1) + (height e'))"
proof (nominal_induct e avoiding: x e' rule: lam.induct)
  case (Var y)
  have "1 \<le> height e'" by (rule height_ge_one)
  then show "height (Var y[x::=e']) \<le> height (Var y) - 1 + height e'" by simp
next
  case (Lam y e1)
  hence ih: "height (e1[x::=e']) \<le> (((height e1) - 1) + (height e'))" by simp
  moreover
  have vc: "y\<sharp>x" "y\<sharp>e'" by fact (* usual variable convention *)
  ultimately show "height ((Lam [y].e1)[x::=e']) \<le> height (Lam [y].e1) - 1 + height e'" by simp 
next    
  case (App e1 e2)
  hence ih1: "height (e1[x::=e']) \<le> (((height e1) - 1) + (height e'))" 
    and ih2: "height (e2[x::=e']) \<le> (((height e2) - 1) + (height e'))" by simp_all
  then show "height ((App e1 e2)[x::=e']) \<le> height (App e1 e2) - 1 + height e'"  by simp 
qed

end

