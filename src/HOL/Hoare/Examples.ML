(*  Title:      HOL/Hoare/Examples.thy
    ID:         $Id$
    Author:     Norbert Galm & Tobias Nipkow
    Copyright   1998 TUM
*)

(*** ARITHMETIC ***)

(** multiplication by successive addition **)

Goal "|- VARS m s a b. \
\  {a=A & b=B} \
\  m := 0; s := 0; \
\  WHILE m~=a \
\  INV {s=m*b & a=A & b=B} \  
\  DO s := s+b; m := m+1 OD \
\  {s = A*B}"; 
by (hoare_tac (Asm_full_simp_tac) 1);
qed "multiply_by_add";

(** Euclid's algorithm for GCD **)

Goal "|- VARS a b. \
\ {0<A & 0<B} \
\ a := A; b := B; \
\ WHILE  a~=b  \
\ INV {0<a & 0<b & gcd A B = gcd a b} \
\ DO IF a<b THEN b := b-a ELSE a := a-b FI OD \
\ {a = gcd A B}";
by (hoare_tac (K all_tac) 1);
(*Now prove the verification conditions*)
by   Auto_tac;
by    (etac gcd_nnn 4);
by   (asm_full_simp_tac (simpset() addsimps [not_less_iff_le, gcd_diff_l]) 3);
by  (force_tac (claset(),
               simpset() addsimps [not_less_iff_le, le_eq_less_or_eq]) 2);
by (asm_simp_tac (simpset() addsimps [gcd_diff_r,less_imp_le]) 1);
qed "Euclid_GCD";

(** Power by iterated squaring and multiplication **)

Goal "|- VARS a b c. \
\ {a=A & b=B} \
\ c := 1; \
\ WHILE b ~= 0 \
\ INV {A^B = c * a^b} \
\ DO  WHILE b mod #2 = 0 \
\     INV {A^B = c * a^b} \
\     DO  a := a*a; b := b div #2 OD; \
\     c := c*a; b := b-1 \
\ OD \
\ {c = A^B}";
by (hoare_tac (Asm_full_simp_tac) 1);
by (case_tac "b" 1);
by  (asm_full_simp_tac (simpset() addsimps [mod_less]) 1);
by (Asm_simp_tac 1);
qed "power_by_mult";

(** Factorial **)

Goal "|- VARS a b. \
\ {a=A} \
\ b := 1; \
\ WHILE a ~= 0 \
\ INV {fac A = b * fac a} \
\ DO b := b*a; a := a-1 OD \
\ {b = fac A}";
by (hoare_tac Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (case_tac "a" 1);
by  (ALLGOALS (asm_simp_tac
     (simpset() addsimps [add_mult_distrib,add_mult_distrib2,mult_assoc])));
qed "factorial";

(** Square root **)

(* the easy way: *)

Goal "|- VARS r x. \
\ {True} \
\ x := X; r := 0; \
\ WHILE (r+1)*(r+1) <= x \
\ INV {r*r <= x & x=X} \
\ DO r := r+1 OD \
\ {r*r <= X & X < (r+1)*(r+1)}";
by (hoare_tac (SELECT_GOAL Auto_tac) 1);
qed "sqrt";

(* without multiplication *)

Goal "|- VARS u w r x. \
\ {True} \
\ x := X; u := 1; w := 1; r := 0; \
\ WHILE w <= x \
\ INV {u = r+r+1 & w = (r+1)*(r+1) & r*r <= x & x=X} \
\ DO r := r+1; w := w+u+2; u := u+2 OD \
\ {r*r <= X & X < (r+1)*(r+1)}";
by (hoare_tac (SELECT_GOAL Auto_tac) 1);
qed "sqrt_without_multiplication";


(*** LISTS ***)

Goal "|- VARS y x. \
\ {x=X} \
\ y:=[]; \
\ WHILE x ~= [] \
\ INV {rev(x)@y = rev(X)} \
\ DO y := (hd x # y); x := tl x OD \
\ {y=rev(X)}";
by (hoare_tac Asm_full_simp_tac 1);
by  (asm_full_simp_tac (simpset() addsimps [neq_Nil_conv]) 1);
by  Auto_tac;
qed "imperative_reverse";

Goal
"|- VARS x y. \
\ {x=X & y=Y} \
\ x := rev(x); \
\ WHILE x~=[] \
\ INV {rev(x)@y = X@Y} \
\ DO y := (hd x # y); \
\    x := tl x \
\ OD \
\ {y = X@Y}";
by (hoare_tac Asm_full_simp_tac 1);
by  (asm_full_simp_tac (simpset() addsimps [neq_Nil_conv]) 1);
by  Auto_tac;
qed "imperative_append";


(*** ARRAYS ***)

(* Search for 0 *)
Goal
"|- VARS A i. \
\ {True} \
\ i := 0; \
\ WHILE i < length A & A!i ~= 0 \
\ INV {!j. j<i --> A!j ~= 0} \
\ DO i := i+1 OD \
\ {(i < length A --> A!i = 0) & \
\  (i = length A --> (!j. j < length A --> A!j ~= 0))}";
by (hoare_tac Asm_full_simp_tac 1);
by (blast_tac (claset() addSEs [less_SucE]) 1);
qed "zero_search";

(* 
The `partition' procedure for quicksort.
`A' is the array to be sorted (modelled as a list).
Elements of A must be of class order to infer at the end
that the elements between u and l are equal to pivot.

Ambiguity warnings of parser are due to := being used
both for assignment and list update.
*)
Goal
"[| leq == %A i. !k. k<i --> A!k <= pivot; \
\   geq == %A i. !k. i<k & k<length A --> pivot <= A!k |] ==> \
\ |- VARS A u l.\
\ {0 < length(A::('a::order)list)} \
\ l := 0; u := length A - 1; \
\ WHILE l <= u \
\  INV {leq A l & geq A u & u<length A & l<=length A} \
\  DO WHILE l < length A & A!l <= pivot \
\      INV {leq A l & geq A u & u<length A & l<=length A} \
\      DO l := l+1 OD; \
\     WHILE 0 < u & pivot <= A!u \
\      INV {leq A l & geq A u  & u<length A & l<=length A} \
\      DO u := u-1 OD; \
\     IF l <= u THEN A := A[l := A!u, u := A!l] ELSE SKIP FI \
\  OD \
\ {leq A u & (!k. u<k & k<l --> A!k = pivot) & geq A l}";
(* expand and delete abbreviations first *)
by (asm_simp_tac HOL_basic_ss 1);
by (REPEAT (etac thin_rl 1));
by (hoare_tac Asm_full_simp_tac 1);
    by (SELECT_GOAL (auto_tac (claset(), simpset() addsimps [neq_Nil_conv])) 1);
   by (blast_tac (claset() addSEs [less_SucE] addIs [Suc_leI]) 1);
  by (blast_tac (claset() addSEs [less_SucE] addIs [less_imp_diff_less]
                          addDs [pred_less_imp_le RS le_imp_less_Suc] ) 1);
 by (SELECT_GOAL (auto_tac (claset(), simpset() addsimps [nth_list_update])) 1);
by (SELECT_GOAL (auto_tac (claset() addIs [order_antisym], simpset())) 1);
qed "Partition";
