(*  Title:      CTT/bool
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header {* The two-element type (booleans and conditionals) *}

theory Bool
imports CTT
begin

definition
  Bool :: "t"
  "Bool == T+T"

  true :: "i"
  "true == inl(tt)"

  false :: "i"
  "false == inr(tt)"

  cond :: "[i,i,i]=>i"
  "cond(a,b,c) == when(a, %u. b, %u. c)"

lemmas bool_defs = Bool_def true_def false_def cond_def


subsection {* Derivation of rules for the type Bool *}

(*formation rule*)
lemma boolF: "Bool type"
apply (unfold bool_defs)
apply (tactic "typechk_tac []")
done


(*introduction rules for true, false*)

lemma boolI_true: "true : Bool"
apply (unfold bool_defs)
apply (tactic "typechk_tac []")
done

lemma boolI_false: "false : Bool"
apply (unfold bool_defs)
apply (tactic "typechk_tac []")
done

(*elimination rule: typing of cond*)
lemma boolE: 
    "[| p:Bool;  a : C(true);  b : C(false) |] ==> cond(p,a,b) : C(p)"
apply (unfold bool_defs)
apply (tactic "typechk_tac []")
apply (erule_tac [!] TE)
apply (tactic "typechk_tac []")
done

lemma boolEL: 
    "[| p = q : Bool;  a = c : C(true);  b = d : C(false) |]  
     ==> cond(p,a,b) = cond(q,c,d) : C(p)"
apply (unfold bool_defs)
apply (rule PlusEL)
apply (erule asm_rl refl_elem [THEN TEL])+
done

(*computation rules for true, false*)

lemma boolC_true: 
    "[| a : C(true);  b : C(false) |] ==> cond(true,a,b) = a : C(true)"
apply (unfold bool_defs)
apply (rule comp_rls)
apply (tactic "typechk_tac []")
apply (erule_tac [!] TE)
apply (tactic "typechk_tac []")
done

lemma boolC_false: 
    "[| a : C(true);  b : C(false) |] ==> cond(false,a,b) = b : C(false)"
apply (unfold bool_defs)
apply (rule comp_rls)
apply (tactic "typechk_tac []")
apply (erule_tac [!] TE)
apply (tactic "typechk_tac []")
done

end
