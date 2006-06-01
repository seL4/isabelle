(* $Id$ *)

(*  Simple, but artificial, problem suggested by D. Wang *)

theory Height
imports Lam_substs
(* 
   - inherit the type of alpha-equated lambda-terms, 
     the iteration combinator for this type and the
     definition of capture-avoiding substitution

     (the iteration combinator is not yet derived 
      automatically in the last stable version of 
      the nominal package) 

   - capture-avoiding substitution is written
     
        t[x::=t']

     and is defined such that

     (Var y)[x::=t'] = (if x=y then t' else Var y)
     (App t1 t2)[x::=t'] = App (t1[x::=t']) (t2[x::=t'])
     y\<sharp>x \<and> y\<sharp>t2 \<Longrightarrow> (Lam [y].t)[x::=t'] = Lam [y].(t[x::=t'])   
*)
begin

text {* definition of the height-function by cases *} 
constdefs 
  height_Var :: "name \<Rightarrow> int"
  "height_Var \<equiv> \<lambda>(a::name). 1"
  
  height_App :: "int \<Rightarrow> int \<Rightarrow> int"
  "height_App \<equiv> \<lambda>n1 n2. (max n1 n2)+1"

  height_Lam :: "name \<Rightarrow> int \<Rightarrow> int"
  "height_Lam \<equiv> \<lambda>(a::name) n. n+1"

  height :: "lam \<Rightarrow> int"
  "height \<equiv> itfun height_Var height_App height_Lam"

text {* show that height is a function *}
lemma supp_height_Lam:
  shows "((supp height_Lam)::name set)={}"
  apply(simp add: height_Lam_def supp_def perm_fun_def perm_int_def)
  done
 
lemma fin_supp_height:
  shows "finite ((supp (height_Var,height_App,height_Lam))::name set)"
  by (finite_guess add: height_Var_def height_App_def height_Lam_def perm_int_def fs_name1)

lemma FCB_height_Lam:
  shows "\<exists>(a::name). a\<sharp>height_Lam \<and> (\<forall>n. a\<sharp>height_Lam a n)"
apply(simp add: height_Lam_def fresh_def supp_def perm_fun_def perm_int_def)
done

text {* derive the characteristic equations for height from the iteration combinator *}
lemma height_Var:
  shows "height (Var c) = 1"
apply(simp add: height_def itfun_Var[OF fin_supp_height, OF FCB_height_Lam])
apply(simp add: height_Var_def)
done

lemma height_App:
  shows "height (App t1 t2) = (max (height t1) (height t2))+1"
apply(simp add: height_def itfun_App[OF fin_supp_height, OF FCB_height_Lam])
apply(simp add: height_App_def)
done

lemma height_Lam:
  shows "height (Lam [a].t) = (height t)+1"
apply(simp add: height_def)
apply(rule trans)
apply(rule itfun_Lam[OF fin_supp_height, OF FCB_height_Lam])
apply(simp add: fresh_def supp_prod supp_height_Lam)
apply(simp add: supp_def height_Var_def height_App_def perm_fun_def perm_int_def) 
apply(simp add: height_Lam_def)
done

text {* add the characteristic equations of height to the simplifier *}
declare height_Var[simp] height_App[simp] height_Lam[simp]


text{* the next lemma is needed in the Var-case of the theorem *}

lemma height_ge_one: 
  shows "1 \<le> (height e)"
  by (nominal_induct e rule: lam.induct) (simp | arith)+


text {* unlike the proplem suggested by Wang, the theorem is formulated 
        here entirely by using functions *}

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
  have fresh: "y\<sharp>x" "y\<sharp>e'" by fact
  ultimately show "height ((Lam [y].e1)[x::=e']) \<le> height (Lam [y].e1) - 1 + height e'" by simp 
next    
  case (App e1 e2)
  hence ih1: "height (e1[x::=e']) \<le> (((height e1) - 1) + (height e'))" 
    and ih2: "height (e2[x::=e']) \<le> (((height e2) - 1) + (height e'))" by simp_all
  then show "height ((App e1 e2)[x::=e']) \<le> height (App e1 e2) - 1 + height e'" by (simp, arith) 
qed

end

