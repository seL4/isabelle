(*  Title:      ZF/Coind/Values.thy
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

theory Values = Language + Map:

(* Values, values environments and associated operators *)

consts
  Val  :: i
  ValEnv  :: i
  Val_ValEnv  :: i;

codatatype
    "Val" = v_const ("c \<in> Const")
          | v_clos ("x \<in> ExVar","e \<in> Exp","ve \<in> ValEnv")
  and
    "ValEnv" = ve_mk ("m \<in> PMap(ExVar,Val)")
  monos       PMap_mono
  type_intros  A_into_univ mapQU

consts
  ve_owr :: "[i,i,i] => i"
  ve_dom :: "i=>i"
  ve_app :: "[i,i] => i"


primrec "ve_owr(ve_mk(m), x, v) = ve_mk(map_owr(m,x,v))"

primrec "ve_dom(ve_mk(m)) = domain(m)"

primrec "ve_app(ve_mk(m), a) = map_app(m,a)"

constdefs
  ve_emp :: i
   "ve_emp == ve_mk(map_emp)"


(* Elimination rules *)

lemma ValEnvE:
  "[| ve \<in> ValEnv; !!m.[| ve=ve_mk(m); m \<in> PMap(ExVar,Val) |] ==> Q |] ==> Q"
apply (unfold Part_def Val_def ValEnv_def)
apply (clarify ); 
apply (erule Val_ValEnv.cases) 
apply (auto simp add: Val_def Part_def Val_ValEnv.con_defs)
done

lemma ValE:
  "[| v \<in> Val;  
      !!c. [| v = v_const(c); c \<in> Const |] ==> Q; 
      !!e ve x.  
        [| v = v_clos(x,e,ve); x \<in> ExVar; e \<in> Exp; ve \<in> ValEnv |] ==> Q  
   |] ==>  
   Q"
apply (unfold Part_def Val_def ValEnv_def)
apply (clarify ); 
apply (erule Val_ValEnv.cases) 
apply (auto simp add: ValEnv_def Part_def Val_ValEnv.con_defs);
done

(* Nonempty sets *)

lemma v_closNE [simp]: "v_clos(x,e,ve) \<noteq> 0"
apply (unfold QPair_def QInl_def QInr_def Val_ValEnv.con_defs)
apply blast
done

declare v_closNE [THEN notE, elim!]


lemma v_constNE [simp]: "c \<in> Const ==> v_const(c) \<noteq> 0"
apply (unfold QPair_def QInl_def QInr_def Val_ValEnv.con_defs)
apply (drule constNEE)
apply auto
done


(* Proving that the empty set is not a value *)

lemma ValNEE: "v \<in> Val ==> v \<noteq> 0"
by (erule ValE, auto)

(* Equalities for value environments *)

lemma ve_dom_owr [simp]:
     "[| ve \<in> ValEnv; v \<noteq>0 |] ==> ve_dom(ve_owr(ve,x,v)) = ve_dom(ve) Un {x}"
apply (erule ValEnvE)
apply (auto simp add: map_domain_owr)
done

lemma ve_app_owr [simp]:
     "ve \<in> ValEnv  
      ==> ve_app(ve_owr(ve,y,v),x) = (if x=y then v else ve_app(ve,x))"
by (erule ValEnvE, simp add: map_app_owr)

(* Introduction rules for operators on value environments *)

lemma ve_appI: "[| ve \<in> ValEnv; x \<in> ve_dom(ve) |] ==> ve_app(ve,x):Val"
by (erule ValEnvE, simp add: pmap_appI) 

lemma ve_domI: "[| ve \<in> ValEnv; x \<in> ve_dom(ve) |] ==> x \<in> ExVar"
apply (erule ValEnvE)
apply (simp ); 
apply (blast dest: pmap_domainD)
done

lemma ve_empI: "ve_emp \<in> ValEnv"
apply (unfold ve_emp_def)
apply (rule Val_ValEnv.intros)
apply (rule pmap_empI)
done

lemma ve_owrI:
     "[|ve \<in> ValEnv; x \<in> ExVar; v \<in> Val |] ==> ve_owr(ve,x,v):ValEnv"
apply (erule ValEnvE)
apply simp
apply (blast intro: pmap_owrI Val_ValEnv.intros)
done

end
