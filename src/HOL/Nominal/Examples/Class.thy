theory class = nominal:

atom_decl name coname

section {* Term-Calculus from my PHD *}

nominal_datatype trm = Ax  "name" "coname"
                     | ImpR "\<guillemotleft>name\<guillemotright>(\<guillemotleft>coname\<guillemotright>trm)" "coname"
                     | ImpL "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"
                     | Cut "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm"

consts
  Ax   :: "name \<Rightarrow> coname \<Rightarrow> trm"
  ImpR :: "name \<Rightarrow> coname \<Rightarrow> trm \<Rightarrow> coname \<Rightarrow> trm"
          ("ImpR [_].[_]._ _" [100,100,100,100] 100)
  ImpL :: "coname \<Rightarrow> trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> name \<Rightarrow> trm"
          ("ImpL [_]._ [_]._ _" [100,100,100,100,100] 100)
  Cut  :: "coname \<Rightarrow> trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm"
          ("Cut [_]._ [_]._" [100,100,100,100] 100)

defs
  Ax_trm_def:   "Ax x a 
                 \<equiv> Abs_trm (trm_Rep.Ax x a)"     
  ImpR_trm_def: "ImpR [x].[a].t b 
                 \<equiv> Abs_trm (trm_Rep.ImpR ([x].([a].(Rep_trm t))) b)"
  ImpL_trm_def: "ImpL [a].t1 [x].t2 y 
                 \<equiv> Abs_trm (trm_Rep.ImpL ([a].(Rep_trm t1)) ([x].(Rep_trm t2)) y)"
  Cut_trm_def:  "Cut [a].t1 [x].t2 
                 \<equiv> Abs_trm (trm_Rep.Cut ([a].(Rep_trm t1)) ([x].(Rep_trm t2)))"

lemma Ax_inject:
  shows "(Ax x a = Ax y b) = (x=y\<and>a=b)"
apply(subgoal_tac "trm_Rep.Ax x a \<in> trm_Rep_set")(*A*)
apply(subgoal_tac "trm_Rep.Ax y b \<in> trm_Rep_set")(*B*)
apply(simp add: Ax_trm_def Abs_trm_inject)
  (*A B*)
apply(rule trm_Rep_set.intros)
apply(rule trm_Rep_set.intros)
done

lemma permF_perm_name:  
  fixes t  :: "trm"
  and   pi :: "name prm" 
  shows "pi\<bullet>(Rep_trm t) = Rep_trm (pi\<bullet>t)"
apply(simp add: prm_trm_def) 
apply(subgoal_tac "pi\<bullet>(Rep_trm t)\<in>trm_Rep_set")(*A*)
apply(simp add: Abs_trm_inverse)
(*A*)
apply(rule perm_closed)
apply(rule Rep_trm)
done

lemma permF_perm_coname:  
  fixes t  :: "trm"
  and   pi :: "coname prm" 
  shows "pi\<bullet>(Rep_trm t) = Rep_trm (pi\<bullet>t)"
apply(simp add: prm_trm_def) 
apply(subgoal_tac "pi\<bullet>(Rep_trm t)\<in>trm_Rep_set")(*A*)
apply(simp add: Abs_trm_inverse)
(*A*)
apply(rule perm_closed)
apply(rule Rep_trm)
done

lemma freshF_fresh_name: 
  fixes t  :: "trm"
  and   b  :: "name"
  shows "b\<sharp>(Rep_trm t) = b\<sharp>t"
apply(simp add: fresh_def supp_def)
apply(simp add: permF_perm_name)
apply(simp add: Rep_trm_inject)
done

lemma freshF_fresh_coname: 
  fixes t  :: "trm"
  and   b  :: "coname"
  shows "b\<sharp>(Rep_trm t) = b\<sharp>t"
apply(simp add: fresh_def supp_def)
apply(simp add: permF_perm_coname)
apply(simp add: Rep_trm_inject)
done

lemma ImpR_inject:
  shows "((ImpR [x].[a].t1 b) = (ImpR [y].[c].t2 d)) = (([x].([a].t1) = [y].([c].t2)) \<and> b=d)"
apply(simp add: ImpR_trm_def)
apply(subgoal_tac "trm_Rep.ImpR ([x].([a].(Rep_trm t1))) b \<in> trm_Rep_set")(*A*)
apply(subgoal_tac "trm_Rep.ImpR ([y].([c].(Rep_trm t2))) d \<in> trm_Rep_set")(*B*)
apply(simp add: Abs_trm_inject)
apply(simp add: alpha abs_perm perm_dj abs_fresh
                permF_perm_name freshF_fresh_name 
                permF_perm_coname freshF_fresh_coname 
                Rep_trm_inject)
(* A B *)
apply(rule trm_Rep_set.intros, rule Rep_trm)
apply(rule trm_Rep_set.intros, rule Rep_trm)
done

lemma ImpL_inject:
  shows "((ImpL [a1].t1 [x1].s1 y1) = (ImpL [a2].t2 [x2].s2 y2)) = 
         ([a1].t1 = [a2].t2 \<and>  [x1].s1 = [x2].s2 \<and> y1=y2)"
apply(simp add: ImpL_trm_def)
apply(subgoal_tac "(trm_Rep.ImpL ([a1].(Rep_trm t1)) ([x1].(Rep_trm s1)) y1) \<in> trm_Rep_set")(*A*)
apply(subgoal_tac "(trm_Rep.ImpL ([a2].(Rep_trm t2)) ([x2].(Rep_trm s2)) y2) \<in> trm_Rep_set")(*B*)
apply(simp add: Abs_trm_inject)
apply(simp add: alpha abs_perm perm_dj abs_fresh
                permF_perm_name freshF_fresh_name 
                permF_perm_coname freshF_fresh_coname 
                Rep_trm_inject)
(* A B *)
apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
done                

lemma Cut_inject:
  shows "((Cut [a1].t1 [x1].s1) = (Cut [a2].t2 [x2].s2)) = ([a1].t1 = [a2].t2 \<and>  [x1].s1 = [x2].s2)"
apply(simp add: Cut_trm_def)
apply(subgoal_tac "trm_Rep.Cut ([a1].(Rep_trm t1)) ([x1].(Rep_trm s1)) \<in> trm_Rep_set")(*A*)
apply(subgoal_tac "trm_Rep.Cut ([a2].(Rep_trm t2)) ([x2].(Rep_trm s2)) \<in> trm_Rep_set")(*B*)
apply(simp add: Abs_trm_inject)
apply(simp add: alpha abs_perm perm_dj abs_fresh
                permF_perm_name freshF_fresh_name 
                permF_perm_coname freshF_fresh_coname 
                Rep_trm_inject)
(* A B *)
apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
done 


lemma Ax_ineqs:
  shows "Ax x a \<noteq> ImpR [y].[b].t1 c"
  and   "Ax x a \<noteq> ImpL [b].t1 [y].t2 z"
  and   "Ax x a \<noteq> Cut [b].t1 [y].t2"
  apply(auto)
(*1*)
  apply(subgoal_tac "trm_Rep.Ax x a\<in>trm_Rep_set")(*A*)
  apply(subgoal_tac "trm_Rep.ImpR ([y].([b].(Rep_trm t1))) c\<in>trm_Rep_set")(*B*)
  apply(simp add: Ax_trm_def ImpR_trm_def Abs_trm_inject)
  (*A B*)
  apply(rule trm_Rep_set.intros, rule Rep_trm)
  apply(rule trm_Rep_set.intros)
(*2*)
  apply(subgoal_tac "trm_Rep.Ax x a\<in>trm_Rep_set")(*C*)
  apply(subgoal_tac "trm_Rep.ImpL ([b].(Rep_trm t1)) ([y].(Rep_trm t2)) z\<in>trm_Rep_set")(*D*)
  apply(simp add: Ax_trm_def ImpL_trm_def Abs_trm_inject)
  (* C D *)
  apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
  apply(rule trm_Rep_set.intros)
(*3*)
  apply(subgoal_tac "trm_Rep.Ax x a\<in>trm_Rep_set")(*E*)
  apply(subgoal_tac "trm_Rep.Cut ([b].(Rep_trm t1)) ([y].(Rep_trm t2))\<in>trm_Rep_set")(*F*)
  apply(simp add: Ax_trm_def Cut_trm_def Abs_trm_inject)
  (* E F *)
  apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
  apply(rule trm_Rep_set.intros)
done

lemma ImpR_ineqs:
  shows "ImpR [y].[b].t c \<noteq> Ax x a"
  and   "ImpR [y].[b].t c \<noteq> ImpL [a].t1 [x].t2 z"
  and   "ImpR [y].[b].t c \<noteq> Cut [a].t1 [x].t2"
  apply(auto)
(*1*)
  apply(subgoal_tac "trm_Rep.ImpR ([y].([b].(Rep_trm t))) c\<in>trm_Rep_set")(*B*)
  apply(subgoal_tac "trm_Rep.Ax x a\<in>trm_Rep_set")(*A*)
  apply(simp add: Ax_trm_def ImpR_trm_def Abs_trm_inject)
  (*A B*)
  apply(rule trm_Rep_set.intros)
  apply(rule trm_Rep_set.intros, rule Rep_trm)
(*2*)
  apply(subgoal_tac "trm_Rep.ImpR ([y].([b].(Rep_trm t))) c\<in>trm_Rep_set")(*C*)
  apply(subgoal_tac "trm_Rep.ImpL ([a].(Rep_trm t1)) ([x].(Rep_trm t2)) z\<in>trm_Rep_set")(*D*)
  apply(simp add: ImpR_trm_def ImpL_trm_def Abs_trm_inject)
  (* C D *)
  apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
  apply(rule trm_Rep_set.intros, rule Rep_trm)
(*3*)
  apply(subgoal_tac "trm_Rep.ImpR ([y].([b].(Rep_trm t))) c\<in>trm_Rep_set")(*E*)
  apply(subgoal_tac "trm_Rep.Cut ([a].(Rep_trm t1)) ([x].(Rep_trm t2))\<in>trm_Rep_set")(*F*)
  apply(simp add: ImpR_trm_def Cut_trm_def Abs_trm_inject)
  (* E F *)
  apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
  apply(rule trm_Rep_set.intros, rule Rep_trm)
done

lemma ImpL_ineqs:
  shows "ImpL [b].t1 [x].t2 y \<noteq> Ax z a"
  and   "ImpL [b].t1 [x].t2 y \<noteq> ImpR [z].[a].s1 c"
  and   "ImpL [b].t1 [x].t2 y \<noteq> Cut [a].s1 [z].s2"
  apply(auto)
(*1*)
  apply(subgoal_tac "trm_Rep.ImpL ([b].(Rep_trm t1)) ([x].(Rep_trm t2)) y\<in>trm_Rep_set")(*B*)
  apply(subgoal_tac "trm_Rep.Ax z a\<in>trm_Rep_set")(*A*)
  apply(simp add: Ax_trm_def ImpL_trm_def Abs_trm_inject)
  (*A B*)
  apply(rule trm_Rep_set.intros)
  apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
(*2*)
  apply(subgoal_tac "trm_Rep.ImpL ([b].(Rep_trm t1)) ([x].(Rep_trm t2)) y\<in>trm_Rep_set")(*D*)
  apply(subgoal_tac "trm_Rep.ImpR ([z].([a].(Rep_trm s1))) c\<in>trm_Rep_set")(*C*)
  apply(simp add: ImpR_trm_def ImpL_trm_def Abs_trm_inject)
  (* C D *)
  apply(rule trm_Rep_set.intros, rule Rep_trm)
  apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
(*3*)
  apply(subgoal_tac "trm_Rep.ImpL ([b].(Rep_trm t1)) ([x].(Rep_trm t2)) y\<in>trm_Rep_set")(*E*)
  apply(subgoal_tac "trm_Rep.Cut ([a].(Rep_trm s1)) ([z].(Rep_trm s2))\<in>trm_Rep_set")(*F*)
  apply(simp add: ImpL_trm_def Cut_trm_def Abs_trm_inject)
  (* E F *)
  apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
  apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
done

lemma Cut_ineqs:
  shows "Cut [b].t1 [x].t2 \<noteq> Ax z a"
  and   "Cut [b].t1 [x].t2 \<noteq> ImpR [z].[a].s1 c"
  and   "Cut [b].t1 [x].t2 \<noteq> ImpL [a].s1 [z].s2 y"
  apply(auto)
(*1*)
  apply(subgoal_tac "trm_Rep.Cut ([b].(Rep_trm t1)) ([x].(Rep_trm t2))\<in>trm_Rep_set")(*B*)
  apply(subgoal_tac "trm_Rep.Ax z a\<in>trm_Rep_set")(*A*)
  apply(simp add: Ax_trm_def Cut_trm_def Abs_trm_inject)
  (*A B*)
  apply(rule trm_Rep_set.intros)
  apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
(*2*)
  apply(subgoal_tac "trm_Rep.Cut ([b].(Rep_trm t1)) ([x].(Rep_trm t2))\<in>trm_Rep_set")(*D*)
  apply(subgoal_tac "trm_Rep.ImpR ([z].([a].(Rep_trm s1))) c\<in>trm_Rep_set")(*C*)
  apply(simp add: ImpR_trm_def Cut_trm_def Abs_trm_inject)
  (* C D *)
  apply(rule trm_Rep_set.intros, rule Rep_trm)
  apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
(*3*)
  apply(subgoal_tac "trm_Rep.Cut ([b].(Rep_trm t1)) ([x].(Rep_trm t2))\<in>trm_Rep_set")(*E*)
  apply(subgoal_tac "trm_Rep.ImpL ([a].(Rep_trm s1)) ([z].(Rep_trm s2)) y\<in>trm_Rep_set")(*F*)
  apply(simp add: ImpL_trm_def Cut_trm_def Abs_trm_inject)
  (* E F *)
  apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
  apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
done

lemma pi_Ax[simp]: 
  fixes pi1 :: "name prm"
  and   pi2 :: "coname prm"
  shows "pi1\<bullet>(Ax x a) = Ax (pi1\<bullet>x) a"
  and   "pi2\<bullet>(Ax x a) = Ax x (pi2\<bullet>a)"
apply(subgoal_tac "trm_Rep.Ax x a\<in>trm_Rep_set")(*A*)
apply(simp add: prm_trm_def Ax_trm_def Abs_trm_inverse perm_dj)
(*A*)
apply(rule trm_Rep_set.intros)
apply(subgoal_tac "trm_Rep.Ax x a\<in>trm_Rep_set")(*B*)
apply(simp add: prm_trm_def Ax_trm_def Abs_trm_inverse perm_dj)
(*B*)
apply(rule trm_Rep_set.intros)
done

lemma pi_ImpR[simp]: 
  fixes pi1 :: "name prm"
  and   pi2 :: "coname prm"
  shows "pi1\<bullet>(ImpR [x].[a].t b) = ImpR [(pi1\<bullet>x)].[a].(pi1\<bullet>t) b"
  and   "pi2\<bullet>(ImpR [x].[a].t b) = ImpR [x].[(pi2\<bullet>a)].(pi2\<bullet>t) (pi2\<bullet>b)"
apply(subgoal_tac "trm_Rep.ImpR ([x].([a].(Rep_trm t))) b\<in>trm_Rep_set")(*A*)
apply(subgoal_tac "pi1\<bullet>(Rep_trm t)\<in>trm_Rep_set")(*B*)
apply(simp add: prm_trm_def ImpR_trm_def Abs_trm_inverse perm_fun_def[symmetric] abs_perm)
apply(simp add: perm_dj)
(* A B *)
apply(rule perm_closed, rule Rep_trm)
apply(rule trm_Rep_set.intros, rule Rep_trm)
apply(subgoal_tac "trm_Rep.ImpR ([x].([a].(Rep_trm t))) b\<in>trm_Rep_set")(*C*)
apply(subgoal_tac "pi2\<bullet>(Rep_trm t)\<in>trm_Rep_set")(*D*)
apply(simp add: prm_trm_def ImpR_trm_def Abs_trm_inverse perm_fun_def[symmetric] abs_perm)
apply(simp add: perm_dj)
(* C D *)
apply(rule perm_closed, rule Rep_trm)
apply(rule trm_Rep_set.intros, rule Rep_trm)
done

lemma pi_ImpL[simp]: 
  fixes pi1 :: "name prm"
  and   pi2 :: "coname prm"
  shows "pi1\<bullet>(ImpL [a].t1 [x].t2 y) = ImpL [a].(pi1\<bullet>t1) [(pi1\<bullet>x)].(pi1\<bullet>t2) (pi1\<bullet>y)"
  and   "pi2\<bullet>(ImpL [a].t1 [x].t2 y) = ImpL [(pi2\<bullet>a)].(pi2\<bullet>t1) [x].(pi2\<bullet>t2) y"
apply(subgoal_tac "trm_Rep.ImpL ([a].(Rep_trm t1)) ([x].(Rep_trm t2)) y\<in>trm_Rep_set")(*A*)
apply(subgoal_tac "pi1\<bullet>(Rep_trm t1)\<in>trm_Rep_set")(*B*)
apply(subgoal_tac "pi1\<bullet>(Rep_trm t2)\<in>trm_Rep_set")(*C*)
apply(simp add: prm_trm_def ImpL_trm_def Abs_trm_inverse perm_fun_def[symmetric] abs_perm)
apply(simp add: perm_dj)
(* A B C *)
apply(rule perm_closed, rule Rep_trm)
apply(rule perm_closed, rule Rep_trm)
apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
apply(subgoal_tac "trm_Rep.ImpL ([a].(Rep_trm t1)) ([x].(Rep_trm t2)) y\<in>trm_Rep_set")(*E*)
apply(subgoal_tac "pi2\<bullet>(Rep_trm t1)\<in>trm_Rep_set")(*D*)
apply(subgoal_tac "pi2\<bullet>(Rep_trm t2)\<in>trm_Rep_set")(*F*)
apply(simp add: prm_trm_def ImpL_trm_def Abs_trm_inverse perm_fun_def[symmetric] abs_perm)
apply(simp add: perm_dj)
(* C D *)
apply(rule perm_closed, rule Rep_trm)
apply(rule perm_closed, rule Rep_trm)
apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
done

lemma pi_Cut[simp]: 
  fixes pi1 :: "name prm"
  and   pi2 :: "coname prm"
  shows "pi1\<bullet>(Cut [a].t1 [x].t2) = Cut [a].(pi1\<bullet>t1) [(pi1\<bullet>x)].(pi1\<bullet>t2)"
  and   "pi2\<bullet>(Cut [a].t1 [x].t2) = Cut [(pi2\<bullet>a)].(pi2\<bullet>t1) [x].(pi2\<bullet>t2)"
apply(subgoal_tac "trm_Rep.Cut ([a].(Rep_trm t1)) ([x].(Rep_trm t2))\<in>trm_Rep_set")(*A*)
apply(subgoal_tac "pi1\<bullet>(Rep_trm t1)\<in>trm_Rep_set")(*B*)
apply(subgoal_tac "pi1\<bullet>(Rep_trm t2)\<in>trm_Rep_set")(*C*)
apply(simp add: prm_trm_def Cut_trm_def Abs_trm_inverse perm_fun_def[symmetric] abs_perm)
apply(simp add: perm_dj)
(* A B C *)
apply(rule perm_closed, rule Rep_trm)
apply(rule perm_closed, rule Rep_trm)
apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
apply(subgoal_tac "trm_Rep.Cut ([a].(Rep_trm t1)) ([x].(Rep_trm t2))\<in>trm_Rep_set")(*E*)
apply(subgoal_tac "pi2\<bullet>(Rep_trm t1)\<in>trm_Rep_set")(*D*)
apply(subgoal_tac "pi2\<bullet>(Rep_trm t2)\<in>trm_Rep_set")(*F*)
apply(simp add: prm_trm_def Cut_trm_def Abs_trm_inverse perm_fun_def[symmetric] abs_perm)
apply(simp add: perm_dj)
(* C D *)
apply(rule perm_closed, rule Rep_trm)
apply(rule perm_closed, rule Rep_trm)
apply(rule trm_Rep_set.intros, rule Rep_trm, rule Rep_trm)
done

lemma supp_Ax:
  shows "((supp (Ax x a))::name set)   = (supp x)"
  and   "((supp (Ax x a))::coname set) = (supp a)"
  apply(simp add: supp_def Ax_inject)+
  done

lemma supp_ImpR:
  shows "((supp (ImpR [x].[a].t b))::name set)   = (supp ([x].t))"
  and   "((supp (ImpR [x].[a].t b))::coname set) = (supp ([a].t,b))"
  apply(simp add: supp_def ImpR_inject)
  apply(simp add: abs_perm alpha perm_dj abs_fresh)
  apply(simp add: supp_def ImpR_inject)
  apply(simp add: abs_perm alpha perm_dj abs_fresh)
  done

lemma supp_ImpL:
  shows "((supp (ImpL [a].t1 [x].t2 y))::name set)   = (supp (t1,[x].t2,y))"
  and   "((supp (ImpL [a].t1 [x].t2 y))::coname set) = (supp ([a].t1,t2))"
  apply(simp add: supp_def ImpL_inject)
  apply(simp add: abs_perm alpha perm_dj abs_fresh)
  apply(simp add: supp_def ImpL_inject)
  apply(simp add: abs_perm alpha perm_dj abs_fresh)
  done

lemma supp_Cut:
  shows "((supp (Cut [a].t1 [x].t2))::name set)   = (supp (t1,[x].t2))"
  and   "((supp (Cut [a].t1 [x].t2))::coname set) = (supp ([a].t1,t2))"
  apply(simp add: supp_def Cut_inject)
  apply(simp add: abs_perm alpha perm_dj abs_fresh)
  apply(simp add: supp_def Cut_inject)
  apply(simp add: abs_perm alpha perm_dj abs_fresh)
  done

lemma fresh_Ax[simp]:
  fixes x :: "name"
  and   a :: "coname"
  shows "x\<sharp>(Ax y b) = x\<sharp>y"
  and   "a\<sharp>(Ax y b) = a\<sharp>b"
  by (simp_all add: fresh_def supp_Ax)

lemma fresh_ImpR[simp]:
  fixes x :: "name"
  and   a :: "coname"
  shows "x\<sharp>(ImpR [y].[b].t c) = x\<sharp>([y].t)"
  and   "a\<sharp>(ImpR [y].[b].t c) = a\<sharp>([b].t,c)"
  by (simp_all add: fresh_def supp_ImpR)

lemma fresh_ImpL[simp]:
  fixes x :: "name"
  and   a :: "coname"
  shows "x\<sharp>(ImpL [b].t1 [y].t2 z) = x\<sharp>(t1,[y].t2,z)"
  and   "a\<sharp>(ImpL [b].t1 [y].t2 z) = a\<sharp>([b].t1,t2)"
  by (simp_all add: fresh_def supp_ImpL)

lemma fresh_Cut[simp]:
  fixes x :: "name"
  and   a :: "coname"
  shows "x\<sharp>(Cut [b].t1 [y].t2) = x\<sharp>(t1,[y].t2)"
  and   "a\<sharp>(Cut [b].t1 [y].t2) = a\<sharp>([b].t1,t2)"
  by (simp_all add: fresh_def supp_Cut)

lemma trm_inverses:
shows "Abs_trm (trm_Rep.Ax x a) = (Ax x a)"
and   "\<lbrakk>t1\<in>trm_Rep_set;t2\<in>trm_Rep_set\<rbrakk>
       \<Longrightarrow> Abs_trm (trm_Rep.ImpL ([a].t1) ([x].t2) y) = ImpL [a].(Abs_trm t1) [x].(Abs_trm t2) y"
and   "\<lbrakk>t1\<in>trm_Rep_set;t2\<in>trm_Rep_set\<rbrakk>
       \<Longrightarrow> Abs_trm (trm_Rep.Cut ([a].t1) ([x].t2)) = Cut [a].(Abs_trm t1) [x].(Abs_trm t2)"
and   "\<lbrakk>t1\<in>trm_Rep_set\<rbrakk>
       \<Longrightarrow> Abs_trm (trm_Rep.ImpR ([y].([a].t1)) b) = (ImpR [y].[a].(Abs_trm t1) b)"
(*1*)
apply(simp add: Ax_trm_def)
(*2*)
apply(simp add: ImpL_trm_def Abs_trm_inverse)
(*3*)
apply(simp add: Cut_trm_def Abs_trm_inverse)
(*4*)
apply(simp add: ImpR_trm_def Abs_trm_inverse)
done

lemma trm_Rep_set_fsupp_name: 
  fixes t :: "trm_Rep" 
  shows "t\<in>trm_Rep_set \<Longrightarrow> finite ((supp (Abs_trm t))::name set)"
apply(erule trm_Rep_set.induct)
(* Ax_Rep *)
apply(simp add: trm_inverses supp_Ax at_supp[OF at_name_inst])
(* ImpR_Rep *)
apply(simp add: trm_inverses supp_ImpR abs_fun_supp[OF pt_name_inst, OF at_name_inst])
(* ImpL_Rep *)
apply(simp add: trm_inverses supp_prod supp_ImpL abs_fun_supp[OF pt_name_inst, OF at_name_inst] 
                at_supp[OF at_name_inst])
(* Cut_Rep *)
apply(simp add: trm_inverses supp_prod supp_Cut abs_fun_supp[OF pt_name_inst, OF at_name_inst])
done

instance trm :: fs_name
apply(intro_classes)
apply(rule Abs_trm_induct)
apply(simp add: trm_Rep_set_fsupp_name)
done

lemma trm_Rep_set_fsupp_coname: 
  fixes t :: "trm_Rep" 
  shows "t\<in>trm_Rep_set \<Longrightarrow> finite ((supp (Abs_trm t))::coname set)"
apply(erule trm_Rep_set.induct)
(* Ax_Rep *)
apply(simp add: trm_inverses supp_Ax at_supp[OF at_coname_inst])
(* ImpR_Rep *)
apply(simp add: trm_inverses supp_prod supp_ImpR abs_fun_supp[OF pt_coname_inst, OF at_coname_inst]
                at_supp[OF at_coname_inst])
(* ImpL_Rep *)
apply(simp add: trm_inverses supp_prod supp_ImpL abs_fun_supp[OF pt_coname_inst, OF at_coname_inst] 
                at_supp[OF at_coname_inst])
(* Cut_Rep *)
apply(simp add: trm_inverses supp_prod supp_Cut abs_fun_supp[OF pt_coname_inst, OF at_coname_inst])
done

instance trm :: fs_coname
apply(intro_classes)
apply(rule Abs_trm_induct)
apply(simp add: trm_Rep_set_fsupp_coname)
done


section {* strong induction principle for lam *}

lemma trm_induct_weak: 
  fixes P :: "trm \<Rightarrow> bool"
  assumes h1: "\<And>x a. P (Ax x a)"  
      and h2: "\<And>x a t b. P t \<Longrightarrow> P (ImpR [x].[a].t b)" 
      and h3: "\<And>a t1 x t2 y. P t1 \<Longrightarrow> P t2 \<Longrightarrow> P (ImpL [a].t1 [x].t2 y)"
      and h4: "\<And>a t1 x t2. P t1 \<Longrightarrow> P t2 \<Longrightarrow> P (Cut [a].t1 [x].t2)"
    shows "P t"
apply(rule Abs_trm_induct) 
apply(erule trm_Rep_set.induct)
apply(fold Ax_trm_def)
apply(rule h1)
apply(drule h2)
apply(unfold ImpR_trm_def)
apply(simp add: Abs_trm_inverse)
apply(drule h3)
apply(simp)
apply(unfold ImpL_trm_def)
apply(simp add: Abs_trm_inverse)
apply(drule h4)
apply(simp)
apply(unfold Cut_trm_def)
apply(simp add: Abs_trm_inverse)
done

lemma trm_induct_aux:
  fixes P :: "trm \<Rightarrow> 'a \<Rightarrow> bool"
  and   f1 :: "'a \<Rightarrow> name set"
  and   f2 :: "'a \<Rightarrow> coname set"
  assumes fs1: "\<And>x. finite (f1 x)"
      and fs2: "\<And>x. finite (f2 x)"
      and h1: "\<And>k x a. P (Ax x a) k"  
      and h2: "\<And>k x a t b. x\<notin>f1 k \<Longrightarrow> a\<notin>f2 k \<Longrightarrow> (\<forall>l. P t l) \<Longrightarrow> P (ImpR [x].[a].t b) k" 
      and h3: "\<And>k a t1 x t2 y. a\<notin>f2 k \<Longrightarrow> x\<notin>f1 k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) 
               \<Longrightarrow> P (ImpL [a].t1 [x].t2 y) k" 
      and h4: "\<And>k a t1 x t2. a\<notin>f2 k \<Longrightarrow> x\<notin>f1 k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) 
               \<Longrightarrow> P (Cut [a].t1 [x].t2) k" 
  shows "\<forall>(pi1::name prm) (pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t)) k"
proof (induct rule: trm_induct_weak)
  case (goal1 a)
  show ?case using h1 by simp
next
  case (goal2 x a t b)
  assume i1: "\<forall>(pi1::name prm)(pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t)) k" 
  show ?case 
  proof (intro strip, simp add: abs_perm perm_dj)
    fix pi1::"name prm" and pi2::"coname prm" and k::"'a"
    have "\<exists>u::name. u\<sharp>(f1 k,pi1\<bullet>x,pi1\<bullet>(pi2\<bullet>t))"
      by (rule at_exists_fresh[OF at_name_inst], simp add: supp_prod fs_name1 
               at_fin_set_supp[OF at_name_inst, OF fs1] fs1)
    then obtain u::"name" 
      where f1: "u\<noteq>(pi1\<bullet>x)" and f2: "u\<sharp>(f1 k)" and f3: "u\<sharp>(pi1\<bullet>(pi2\<bullet>t))" 
      by (auto simp add: fresh_prod at_fresh[OF at_name_inst])
    have "\<exists>c::coname. c\<sharp>(f2 k,pi2\<bullet>a,pi1\<bullet>(pi2\<bullet>t))"
      by (rule at_exists_fresh[OF at_coname_inst], simp add: supp_prod fs_coname1 
               at_fin_set_supp[OF at_coname_inst, OF fs2] fs2)
    then obtain c::"coname" 
      where e1: "c\<noteq>(pi2\<bullet>a)" and e2: "c\<sharp>(f2 k)" and e3: "c\<sharp>(pi1\<bullet>(pi2\<bullet>t))" 
      by (auto simp add: fresh_prod at_fresh[OF at_coname_inst])
    have g: "ImpR [u].[c].([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>([(c,pi2\<bullet>a)]\<bullet>(pi2\<bullet>t)))) (pi2\<bullet>b)
            =ImpR [(pi1\<bullet>x)].[(pi2\<bullet>a)].(pi1\<bullet>(pi2\<bullet>t)) (pi2\<bullet>b)" using f1 f3 e1 e3
      apply (auto simp add: ImpR_inject alpha abs_fresh abs_perm perm_dj,
                  simp add: dj_cp[OF cp_name_coname_inst, OF dj_coname_name])
      apply(simp add:  pt_fresh_left_ineq[OF pt_name_inst, OF pt_name_inst, 
                                          OF at_name_inst, OF cp_name_coname_inst] perm_dj)
      done
    from i1 have "\<forall>k. P (([(u,pi1\<bullet>x)]@pi1)\<bullet>(([(c,pi2\<bullet>a)]@pi2)\<bullet>t)) k" by force
    hence i1b: "\<forall>k. P ([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>([(c,pi2\<bullet>a)]\<bullet>(pi2\<bullet>t)))) k" 
      by (simp add: pt_name2[symmetric] pt_coname2[symmetric])
    with h2 f2 e2 have "P (ImpR [u].[c].([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>([(c,pi2\<bullet>a)]\<bullet>(pi2\<bullet>t)))) (pi2\<bullet>b)) k" 
      by (simp add: fresh_def at_fin_set_supp[OF at_name_inst, OF fs1]
                                   at_fin_set_supp[OF at_coname_inst, OF fs2])
    with g show "P (ImpR [(pi1\<bullet>x)].[(pi2\<bullet>a)].(pi1\<bullet>(pi2\<bullet>t)) (pi2\<bullet>b)) k" by simp 
  qed
next
  case (goal3 a t1 x t2 y)
  assume i1: "\<forall>(pi1::name prm)(pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t1)) k" 
  and    i2: "\<forall>(pi1::name prm)(pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t2)) k"
  show ?case
  proof (intro strip, simp add: abs_perm)
    fix pi1::"name prm" and pi2::"coname prm" and k::"'a"
    have "\<exists>u::name. u\<sharp>(f1 k,pi1\<bullet>x,pi1\<bullet>(pi2\<bullet>t2))"
      by (rule at_exists_fresh[OF at_name_inst], simp add: supp_prod fs_name1 
               at_fin_set_supp[OF at_name_inst, OF fs1] fs1)
    then obtain u::"name" 
      where f1: "u\<noteq>(pi1\<bullet>x)" and f2: "u\<sharp>(f1 k)" and f3: "u\<sharp>(pi1\<bullet>(pi2\<bullet>t2))" 
      by (auto simp add: fresh_prod at_fresh[OF at_name_inst])
    have "\<exists>c::coname. c\<sharp>(f2 k,pi2\<bullet>a,pi1\<bullet>(pi2\<bullet>t1))"
      by (rule at_exists_fresh[OF at_coname_inst], simp add: supp_prod fs_coname1 
               at_fin_set_supp[OF at_coname_inst, OF fs2] fs2)
    then obtain c::"coname" 
      where e1: "c\<noteq>(pi2\<bullet>a)" and e2: "c\<sharp>(f2 k)" and e3: "c\<sharp>(pi1\<bullet>(pi2\<bullet>t1))" 
      by (auto simp add: fresh_prod at_fresh[OF at_coname_inst])
    have g: "ImpL [c].([(c,pi2\<bullet>a)]\<bullet>(pi1\<bullet>(pi2\<bullet>t1))) [u].([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>(pi2\<bullet>t2))) (pi1\<bullet>y)
            =ImpL [(pi2\<bullet>a)].(pi1\<bullet>(pi2\<bullet>t1)) [(pi1\<bullet>x)].(pi1\<bullet>(pi2\<bullet>t2)) (pi1\<bullet>y)" using f1 f3 e1 e3
      by (simp add: ImpL_inject alpha abs_fresh abs_perm perm_dj)
    from i2 have "\<forall>k. P (([(u,pi1\<bullet>x)]@pi1)\<bullet>(pi2\<bullet>t2)) k" by force
    hence i2b: "\<forall>k. P ([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>(pi2\<bullet>t2))) k" 
      by (simp add: pt_name2[symmetric])
    from i1 have "\<forall>k. P (pi1\<bullet>(([(c,pi2\<bullet>a)]@pi2)\<bullet>t1)) k" by force
    hence i1b: "\<forall>k. P ([(c,pi2\<bullet>a)]\<bullet>(pi1\<bullet>(pi2\<bullet>t1))) k" 
      by (simp add: pt_coname2[symmetric] dj_cp[OF cp_name_coname_inst, OF dj_coname_name])
    from h3 f2 e2 i1b i2b 
    have "P (ImpL [c].([(c,pi2\<bullet>a)]\<bullet>(pi1\<bullet>(pi2\<bullet>t1))) [u].([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>(pi2\<bullet>t2))) (pi1\<bullet>y)) k" 
      by (simp add: fresh_def at_fin_set_supp[OF at_name_inst, OF fs1]
                                   at_fin_set_supp[OF at_coname_inst, OF fs2])
    with g show "P (ImpL [(pi2\<bullet>a)].(pi1\<bullet>(pi2\<bullet>t1)) [(pi1\<bullet>x)].(pi1\<bullet>(pi2\<bullet>t2)) (pi1\<bullet>y)) k" by simp 
  qed
next
  case (goal4 a t1 x t2)
  assume i1: "\<forall>(pi1::name prm)(pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t1)) k" 
  and    i2: "\<forall>(pi1::name prm)(pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t2)) k"
  show ?case
  proof (intro strip, simp add: abs_perm)
    fix pi1::"name prm" and pi2::"coname prm" and k::"'a"
    have "\<exists>u::name. u\<sharp>(f1 k,pi1\<bullet>x,pi1\<bullet>(pi2\<bullet>t2))"
      by (rule at_exists_fresh[OF at_name_inst], simp add: supp_prod fs_name1 
               at_fin_set_supp[OF at_name_inst, OF fs1] fs1)
    then obtain u::"name" 
      where f1: "u\<noteq>(pi1\<bullet>x)" and f2: "u\<sharp>(f1 k)" and f3: "u\<sharp>(pi1\<bullet>(pi2\<bullet>t2))" 
      by (auto simp add: fresh_prod at_fresh[OF at_name_inst])
    have "\<exists>c::coname. c\<sharp>(f2 k,pi2\<bullet>a,pi1\<bullet>(pi2\<bullet>t1))"
      by (rule at_exists_fresh[OF at_coname_inst], simp add: supp_prod fs_coname1 
               at_fin_set_supp[OF at_coname_inst, OF fs2] fs2)
    then obtain c::"coname" 
      where e1: "c\<noteq>(pi2\<bullet>a)" and e2: "c\<sharp>(f2 k)" and e3: "c\<sharp>(pi1\<bullet>(pi2\<bullet>t1))" 
      by (auto simp add: fresh_prod at_fresh[OF at_coname_inst])
    have g: "Cut [c].([(c,pi2\<bullet>a)]\<bullet>(pi1\<bullet>(pi2\<bullet>t1))) [u].([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>(pi2\<bullet>t2)))
            =Cut [(pi2\<bullet>a)].(pi1\<bullet>(pi2\<bullet>t1)) [(pi1\<bullet>x)].(pi1\<bullet>(pi2\<bullet>t2))" using f1 f3 e1 e3
      by (simp add: Cut_inject alpha abs_fresh abs_perm perm_dj)
    from i2 have "\<forall>k. P (([(u,pi1\<bullet>x)]@pi1)\<bullet>(pi2\<bullet>t2)) k" by force
    hence i2b: "\<forall>k. P ([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>(pi2\<bullet>t2))) k" 
      by (simp add: pt_name2[symmetric])
    from i1 have "\<forall>k. P (pi1\<bullet>(([(c,pi2\<bullet>a)]@pi2)\<bullet>t1)) k" by force
    hence i1b: "\<forall>k. P ([(c,pi2\<bullet>a)]\<bullet>(pi1\<bullet>(pi2\<bullet>t1))) k" 
      by (simp add: pt_coname2[symmetric] dj_cp[OF cp_name_coname_inst, OF dj_coname_name])
    from h3 f2 e2 i1b i2b 
    have "P (Cut [c].([(c,pi2\<bullet>a)]\<bullet>(pi1\<bullet>(pi2\<bullet>t1))) [u].([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>(pi2\<bullet>t2)))) k" 
      by (simp add: fresh_def at_fin_set_supp[OF at_name_inst, OF fs1]
                                   at_fin_set_supp[OF at_coname_inst, OF fs2])
    with g show "P (Cut [(pi2\<bullet>a)].(pi1\<bullet>(pi2\<bullet>t1)) [(pi1\<bullet>x)].(pi1\<bullet>(pi2\<bullet>t2))) k" by simp 
  qed
qed

lemma trm_induct'[case_names Ax ImpR ImpL Cut]: 
  fixes P :: "trm \<Rightarrow> 'a \<Rightarrow> bool"
  and   f1 :: "'a \<Rightarrow> name set"
  and   f2 :: "'a \<Rightarrow> coname set"
  assumes fs1: "\<And>x. finite (f1 x)"
      and fs2: "\<And>x. finite (f2 x)"
      and h1: "\<And>k x a. P (Ax x a) k"  
      and h2: "\<And>k x a t b. x\<notin>f1 k \<Longrightarrow> a\<notin>f2 k \<Longrightarrow> (\<forall>l. P t l) \<Longrightarrow> P (ImpR [x].[a].t b) k" 
      and h3: "\<And>k a t1 x t2 y. a\<notin>f2 k \<Longrightarrow> x\<notin>f1 k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) 
               \<Longrightarrow> P (ImpL [a].t1 [x].t2 y) k" 
      and h4: "\<And>k a t1 x t2. a\<notin>f2 k \<Longrightarrow> x\<notin>f1 k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) 
               \<Longrightarrow> P (Cut [a].t1 [x].t2) k" 
  shows  "P t k"
proof -
  have "\<forall>(pi1::name prm)(pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t)) k"
  using fs1 fs2 h1 h2 h3 h4 by (rule trm_induct_aux, auto)
  hence "P (([]::name prm)\<bullet>(([]::coname prm)\<bullet>t)) k" by blast
  thus "P t k" by simp
qed

lemma trm_induct[case_names Ax ImpR ImpL Cut]: 
  fixes P :: "trm \<Rightarrow> ('a::{fs_name,fs_coname}) \<Rightarrow> bool"
  assumes h1: "\<And>k x a. P (Ax x a) k"  
      and h2: "\<And>k x a t b. x\<sharp>k \<Longrightarrow> a\<sharp>k \<Longrightarrow> (\<forall>l. P t l) \<Longrightarrow> P (ImpR [x].[a].t b) k" 
      and h3: "\<And>k a t1 x t2 y. a\<sharp>k \<Longrightarrow> x\<sharp>k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) 
               \<Longrightarrow> P (ImpL [a].t1 [x].t2 y) k" 
      and h4: "\<And>k a t1 x t2. a\<sharp>k \<Longrightarrow> x\<sharp>k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) 
               \<Longrightarrow> P (Cut [a].t1 [x].t2) k" 
  shows  "P t k"
by (rule trm_induct'[of "\<lambda>x. ((supp x)::name set)" "\<lambda>x. ((supp x)::coname set)" "P"], 
    simp_all add: fs_name1 fs_coname1 fresh_def[symmetric], auto intro: h1 h2 h3 h4)
