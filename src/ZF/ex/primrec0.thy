(*  Title: 	ZF/ex/primrec.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Primitive Recursive Functions

Proof adopted from
Nora Szasz, 
A Machine Checked Proof that Ackermann's Function is not Primitive Recursive,
In: Huet & Plotkin, eds., Logical Environments (CUP, 1993), 317-338.
*)

Primrec0 = ListFn +
consts
    SC      :: "i"
    CONST   :: "i=>i"
    PROJ    :: "i=>i"
    COMP    :: "[i,i]=>i"
    PREC    :: "[i,i]=>i"
    primrec :: "i"
    ACK	    :: "i=>i"
    ack	    :: "[i,i]=>i"

translations
  "ack(x,y)"  == "ACK(x) ` [y]"

rules

  SC_def    "SC == lam l:list(nat).list_case(0, %x xs.succ(x), l)"

  CONST_def "CONST(k) == lam l:list(nat).k"

  PROJ_def  "PROJ(i) == lam l:list(nat). list_case(0, %x xs.x, drop(i,l))"

  COMP_def  "COMP(g,fs) == lam l:list(nat). g ` map(%f. f`l, fs)"

  (*Note that g is applied first to PREC(f,g)`y and then to y!*)
  PREC_def  "PREC(f,g) == \
\            lam l:list(nat). list_case(0, \
\                      %x xs. rec(x, f`xs, %y r. g ` Cons(r, Cons(y, xs))), l)"
  
  ACK_def   "ACK(i) == rec(i, SC, \
\                      %z r. PREC (CONST (r`[1]), COMP(r,[PROJ(0)])))"

end
