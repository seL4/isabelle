(*  Title:      ZF/Coind/Values.thy
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

theory Values imports Language Map begin

(* Values, values environments and associated operators *)

consts
  Val  :: i
  ValEnv  :: i
  Val_ValEnv  :: i

codatatype
    "Val" = v_const ("c \<in> Const")
          | v_clos ("x \<in> ExVar","e \<in> Exp","ve \<in> ValEnv")
  and
    "ValEnv" = ve_mk ("m \<in> PMap(ExVar,Val)")
  monos       PMap_mono
  type_intros  A_into_univ mapQU

consts
  ve_owr :: "[i,i,i] \<Rightarrow> i"
  ve_dom :: "i\<Rightarrow>i"
  ve_app :: "[i,i] \<Rightarrow> i"


primrec "ve_owr(ve_mk(m), x, v) = ve_mk(map_owr(m,x,v))"

primrec "ve_dom(ve_mk(m)) = domain(m)"

primrec "ve_app(ve_mk(m), a) = map_app(m,a)"

definition
  ve_emp :: i  where
   "ve_emp \<equiv> ve_mk(map_emp)"


(* Elimination rules *)

lemma ValEnvE:
  "\<lbrakk>ve \<in> ValEnv; \<And>m.\<lbrakk>ve=ve_mk(m); m \<in> PMap(ExVar,Val)\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (unfold Part_def Val_def ValEnv_def, clarify) 
apply (erule Val_ValEnv.cases) 
apply (auto simp add: Val_def Part_def Val_ValEnv.con_defs)
done

lemma ValE:
  "\<lbrakk>v \<in> Val;  
      \<And>c. \<lbrakk>v = v_const(c); c \<in> Const\<rbrakk> \<Longrightarrow> Q; 
      \<And>e ve x.  
        \<lbrakk>v = v_clos(x,e,ve); x \<in> ExVar; e \<in> Exp; ve \<in> ValEnv\<rbrakk> \<Longrightarrow> Q  
\<rbrakk> \<Longrightarrow>  
   Q"
apply (unfold Part_def Val_def ValEnv_def, clarify) 
apply (erule Val_ValEnv.cases) 
apply (auto simp add: ValEnv_def Part_def Val_ValEnv.con_defs)
done

(* Nonempty sets *)

lemma v_closNE [simp]: "v_clos(x,e,ve) \<noteq> 0"
by (unfold QPair_def QInl_def QInr_def Val_ValEnv.con_defs, blast)

declare v_closNE [THEN notE, elim!]


lemma v_constNE [simp]: "c \<in> Const \<Longrightarrow> v_const(c) \<noteq> 0"
  unfolding QPair_def QInl_def QInr_def Val_ValEnv.con_defs
apply (drule constNEE, auto)
done


(* Proving that the empty set is not a value *)

lemma ValNEE: "v \<in> Val \<Longrightarrow> v \<noteq> 0"
by (erule ValE, auto)

(* Equalities for value environments *)

lemma ve_dom_owr [simp]:
     "\<lbrakk>ve \<in> ValEnv; v \<noteq>0\<rbrakk> \<Longrightarrow> ve_dom(ve_owr(ve,x,v)) = ve_dom(ve) \<union> {x}"
apply (erule ValEnvE)
apply (auto simp add: map_domain_owr)
done

lemma ve_app_owr [simp]:
     "ve \<in> ValEnv  
      \<Longrightarrow> ve_app(ve_owr(ve,y,v),x) = (if x=y then v else ve_app(ve,x))"
by (erule ValEnvE, simp add: map_app_owr)

(* Introduction rules for operators on value environments *)

lemma ve_appI: "\<lbrakk>ve \<in> ValEnv; x \<in> ve_dom(ve)\<rbrakk> \<Longrightarrow> ve_app(ve,x):Val"
by (erule ValEnvE, simp add: pmap_appI) 

lemma ve_domI: "\<lbrakk>ve \<in> ValEnv; x \<in> ve_dom(ve)\<rbrakk> \<Longrightarrow> x \<in> ExVar"
apply (erule ValEnvE, simp) 
apply (blast dest: pmap_domainD)
done

lemma ve_empI: "ve_emp \<in> ValEnv"
  unfolding ve_emp_def
apply (rule Val_ValEnv.intros)
apply (rule pmap_empI)
done

lemma ve_owrI:
     "\<lbrakk>ve \<in> ValEnv; x \<in> ExVar; v \<in> Val\<rbrakk> \<Longrightarrow> ve_owr(ve,x,v):ValEnv"
apply (erule ValEnvE, simp)
apply (blast intro: pmap_owrI Val_ValEnv.intros)
done

end
