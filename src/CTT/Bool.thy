(*  Title:      CTT/bool
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

The two-element type (booleans and conditionals)
*)

Bool = CTT +

consts Bool             :: "t"
       true,false       :: "i"
       cond             :: "[i,i,i]=>i"
rules
  Bool_def      "Bool == T+T"
  true_def      "true == inl(tt)"
  false_def     "false == inr(tt)"
  cond_def      "cond(a,b,c) == when(a, %u.b, %u.c)"
end
