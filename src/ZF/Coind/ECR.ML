(*  Title:      ZF/Coind/ECR.ML
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

(* Specialised co-induction rule *)

Goal "[| x:ExVar; e:Exp; t:Ty; ve:ValEnv; te:TyEnv;  \
\        <te, e_fn(x, e), t>:ElabRel; ve_dom(ve) = te_dom(te); \
\        {<ve_app(ve,y),te_app(te,y)>.y:ve_dom(ve)}: \
\        Pow({<v_clos(x,e,ve),t>} Un HasTyRel) |]    \
\     ==> <v_clos(x, e, ve),t>:HasTyRel";
by (rtac (singletonI RS HasTyRel.coinduct) 1);
by (ALLGOALS Blast_tac);
qed "htr_closCI";

(* Specialised elimination rules *)

val htr_constE = HasTyRel.mk_cases "<v_const(c),t>:HasTyRel";

val htr_closE = HasTyRel.mk_cases "<v_clos(x,e,ve),t>:HasTyRel";

(* Classical reasoning sets *)

fun mk_htr_cs cs =
  let open HasTyRel in 
    ( cs 
      addSIs [htr_constI] 
      addSEs [htr_constE]
      addIs [htr_closI,htr_closCI]
      addEs [htr_closE])
  end;

claset_ref() := mk_htr_cs (claset());

(* Properties of the pointwise extension to environments *)

bind_thm ("HasTyRel_non_zero", 
	  HasTyRel.dom_subset RS subsetD RS SigmaD1 RS ValNEE);

Goalw [hastyenv_def]
  "[| ve:ValEnv; te:TyEnv; hastyenv(ve,te); <v,t>:HasTyRel |] ==> \
\   hastyenv(ve_owr(ve,x,v),te_owr(te,x,t))";
by (asm_full_simp_tac
    (simpset() addsimps [ve_app_owr, HasTyRel_non_zero, ve_dom_owr]) 1);
by Auto_tac;
qed "hastyenv_owr";

Goalw  [isofenv_def,hastyenv_def]
  "[| ve:ValEnv; te:TyEnv; isofenv(ve,te) |] ==> hastyenv(ve,te)";
by Safe_tac;
by (dtac bspec 1);
by (assume_tac 1);
by Safe_tac;
by (dtac HasTyRel.htr_constI 1);
by (assume_tac 2);
by (etac te_appI 1);
by (etac ve_domI 1);
by (ALLGOALS Asm_full_simp_tac);
qed "basic_consistency_lem";



