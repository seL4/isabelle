(*  Title:      HOL/MicroJava/BV/Convert.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

The supertype relation lifted to type options, type lists and state types.
*)

Convert = JVMExec + 

types
 locvars_type = ty option list
 opstack_type = ty list
 state_type   = "opstack_type \\<times> locvars_type"

constdefs

 sup_ty_opt :: "['code prog,ty option,ty option] \\<Rightarrow> bool" ("_ \\<turnstile>_ <=o _")
 "G \\<turnstile> a' <=o a \\<equiv>
    case a of
      None \\<Rightarrow> True
    | Some t  \\<Rightarrow>  case a' of 
		     None \\<Rightarrow> False
		   | Some t' \\<Rightarrow> G \\<turnstile> t' \\<preceq> t" 

 sup_loc :: "['code prog,locvars_type,locvars_type] \\<Rightarrow> bool"	  ("_ \\<turnstile> _ <=l _"  [71,71] 70)
 "G \\<turnstile> LT <=l LT' \\<equiv> list_all2 (%t t'. G \\<turnstile> t <=o t') LT LT'"

 sup_state :: "['code prog,state_type,state_type] \\<Rightarrow> bool"	  ("_ \\<turnstile> _ <=s _"  [71,71] 70)
 "G \\<turnstile> s <=s s' \\<equiv> G \\<turnstile> map Some (fst s) <=l map Some (fst s') \\<and> G \\<turnstile> snd s <=l snd s'"

end
