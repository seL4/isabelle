(*  Title:      ZF/ex/Primrec.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Primitive Recursive Functions: the inductive definition

Proof adopted from
Nora Szasz, 
A Machine Checked Proof that Ackermann's Function is not Primitive Recursive,
In: Huet & Plotkin, eds., Logical Environments (CUP, 1993), 317-338.

See also E. Mendelson, Introduction to Mathematical Logic.
(Van Nostrand, 1964), page 250, exercise 11.
*)

Primrec = Primrec_defs +
consts
    prim_rec :: i

inductive
  domains "prim_rec" <= "list(nat)->nat"
  intrs
    SC       "SC : prim_rec"
    CONST    "k: nat ==> CONST(k) : prim_rec"
    PROJ     "i: nat ==> PROJ(i) : prim_rec"
    COMP     "[| g: prim_rec; fs: list(prim_rec) |] ==> COMP(g,fs): prim_rec"
    PREC     "[| f: prim_rec; g: prim_rec |] ==> PREC(f,g): prim_rec"
  monos       list_mono
  con_defs    SC_def, CONST_def, PROJ_def, COMP_def, PREC_def
  type_intrs "nat_typechecks @ list.intrs @                     
              [lam_type, list_case_type, drop_type, map_type,   
              apply_type, rec_type]"

end
