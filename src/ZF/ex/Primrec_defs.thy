(*  Title:      ZF/ex/Primrec_defs.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Primitive Recursive Functions: preliminary definitions of the constructors

[These must reside in a separate theory in order to be visible in the
 con_defs part of prim_rec's inductive definition.]
*)

Primrec_defs = Main +

consts
    SC      :: i
    CONST   :: i=>i
    PROJ    :: i=>i
    COMP    :: [i,i]=>i
    PREC    :: [i,i]=>i
    ACK     :: i=>i
    ack     :: [i,i]=>i

translations
  "ack(x,y)"  == "ACK(x) ` [y]"

defs

  SC_def    "SC == lam l:list(nat).list_case(0, %x xs. succ(x), l)"

  CONST_def "CONST(k) == lam l:list(nat).k"

  PROJ_def  "PROJ(i) == lam l:list(nat). list_case(0, %x xs. x, drop(i,l))"

  COMP_def  "COMP(g,fs) == lam l:list(nat). g ` List.map(%f. f`l, fs)"

  (*Note that g is applied first to PREC(f,g)`y and then to y!*)
  PREC_def  "PREC(f,g) == 
            lam l:list(nat). list_case(0, 
                      %x xs. rec(x, f`xs, %y r. g ` Cons(r, Cons(y, xs))), l)"
  
  ACK_def   "ACK(i) == rec(i, SC, 
                      %z r. PREC (CONST (r`[1]), COMP(r,[PROJ(0)])))"


end
