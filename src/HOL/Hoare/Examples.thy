(*  Title:      HOL/Hoare/Examples.thy
    ID:         $Id$
    Author:     Norbert Galm
    Copyright   1998 TUM

Various examples.
*)

theory Examples = Hoare + Arith2:

(*** ARITHMETIC ***)

(** multiplication by successive addition **)

lemma multiply_by_add: "VARS m s a b
  {a=A & b=B}
  m := 0; s := 0;
  WHILE m~=a
  INV {s=m*b & a=A & b=B}
  DO s := s+b; m := m+(1::nat) OD
  {s = A*B}"
by vcg_simp


(** Euclid's algorithm for GCD **)

lemma Euclid_GCD: "VARS a b
 {0<A & 0<B}
 a := A; b := B;
 WHILE  a~=b
 INV {0<a & 0<b & gcd A B = gcd a b}
 DO IF a<b THEN b := b-a ELSE a := a-b FI OD
 {a = gcd A B}"
apply vcg
(*Now prove the verification conditions*)
  apply auto
  apply(simp add: gcd_diff_r less_imp_le)
 apply(simp add: not_less_iff_le gcd_diff_l)
apply(erule gcd_nnn)
done

(** Dijkstra's extension of Euclid's algorithm for simultaneous GCD and SCM **)
(* From E.W. Disjkstra. Selected Writings on Computing, p 98 (EWD474),
   where it is given without the invariant. Instead of defining scm
   explicitly we have used the theorem scm x y = x*y/gcd x y and avoided
   division by mupltiplying with gcd x y.
*)

lemmas distribs =
  diff_mult_distrib diff_mult_distrib2 add_mult_distrib add_mult_distrib2

lemma gcd_scm: "VARS a b x y
 {0<A & 0<B & a=A & b=B & x=B & y=A}
 WHILE  a ~= b
 INV {0<a & 0<b & gcd A B = gcd a b & 2*A*B = a*x + b*y}
 DO IF a<b THEN (b := b-a; x := x+y) ELSE (a := a-b; y := y+x) FI OD
 {a = gcd A B & 2*A*B = a*(x+y)}"
apply vcg
  apply simp
 apply(simp add: distribs gcd_diff_r not_less_iff_le gcd_diff_l)
 apply arith
apply(simp add: distribs gcd_nnn)
done

(** Power by iterated squaring and multiplication **)

lemma power_by_mult: "VARS a b c
 {a=A & b=B}
 c := (1::nat);
 WHILE b ~= 0
 INV {A^B = c * a^b}
 DO  WHILE b mod 2 = 0
     INV {A^B = c * a^b}
     DO  a := a*a; b := b div 2 OD;
     c := c*a; b := b - 1
 OD
 {c = A^B}"
apply vcg_simp
apply(case_tac "b")
 apply(simp add: mod_less)
apply simp
done

(** Factorial **)

lemma factorial: "VARS a b
 {a=A}
 b := 1;
 WHILE a ~= 0
 INV {fac A = b * fac a}
 DO b := b*a; a := a - 1 OD
 {b = fac A}"
apply vcg_simp
apply(clarsimp split: nat_diff_split)
done

lemma [simp]: "1 \<le> i \<Longrightarrow> fac (i - Suc 0) * i = fac i"
by(induct i, simp_all)

lemma "VARS i f
 {True}
 i := (1::nat); f := 1;
 WHILE i <= n INV {f = fac(i - 1) & 1 <= i & i <= n+1}
 DO f := f*i; i := i+1 OD
 {f = fac n}"
apply vcg_simp
apply(subgoal_tac "i = Suc n")
apply simp
apply arith
done

(** Square root **)

(* the easy way: *)

lemma sqrt: "VARS r x
 {True}
 x := X; r := (0::nat);
 WHILE (r+1)*(r+1) <= x
 INV {r*r <= x & x=X}
 DO r := r+1 OD
 {r*r <= X & X < (r+1)*(r+1)}"
apply vcg_simp
apply auto
done

(* without multiplication *)

lemma sqrt_without_multiplication: "VARS u w r x
 {True}
 x := X; u := 1; w := 1; r := (0::nat);
 WHILE w <= x
 INV {u = r+r+1 & w = (r+1)*(r+1) & r*r <= x & x=X}
 DO r := r + 1; w := w + u + 2; u := u + 2 OD
 {r*r <= X & X < (r+1)*(r+1)}"
apply vcg_simp
apply auto
done


(*** LISTS ***)

lemma imperative_reverse: "VARS y x
 {x=X}
 y:=[];
 WHILE x ~= []
 INV {rev(x)@y = rev(X)}
 DO y := (hd x # y); x := tl x OD
 {y=rev(X)}"
apply vcg_simp
 apply(simp add: neq_Nil_conv)
 apply auto
done

lemma imperative_append: "VARS x y
 {x=X & y=Y}
 x := rev(x);
 WHILE x~=[]
 INV {rev(x)@y = X@Y}
 DO y := (hd x # y);
    x := tl x
 OD
 {y = X@Y}"
apply vcg_simp
apply(simp add: neq_Nil_conv)
apply auto
done


(*** ARRAYS ***)

(* Search for a key *)
lemma zero_search: "VARS A i
 {True}
 i := 0;
 WHILE i < length A & A!i ~= key
 INV {!j. j<i --> A!j ~= key}
 DO i := i+1 OD
 {(i < length A --> A!i = key) &
  (i = length A --> (!j. j < length A --> A!j ~= key))}"
apply vcg_simp
apply(blast elim!: less_SucE)
done

(* 
The `partition' procedure for quicksort.
`A' is the array to be sorted (modelled as a list).
Elements of A must be of class order to infer at the end
that the elements between u and l are equal to pivot.

Ambiguity warnings of parser are due to := being used
both for assignment and list update.
*)
lemma lem: "m - Suc 0 < n ==> m < Suc n"
by arith


lemma Partition:
"[| leq == %A i. !k. k<i --> A!k <= pivot;
    geq == %A i. !k. i<k & k<length A --> pivot <= A!k |] ==>
 VARS A u l
 {0 < length(A::('a::order)list)}
 l := 0; u := length A - Suc 0;
 WHILE l <= u
  INV {leq A l & geq A u & u<length A & l<=length A}
  DO WHILE l < length A & A!l <= pivot
     INV {leq A l & geq A u & u<length A & l<=length A}
     DO l := l+1 OD;
     WHILE 0 < u & pivot <= A!u
     INV {leq A l & geq A u  & u<length A & l<=length A}
     DO u := u - 1 OD;
     IF l <= u THEN A := A[l := A!u, u := A!l] ELSE SKIP FI
  OD
 {leq A u & (!k. u<k & k<l --> A!k = pivot) & geq A l}"
(* expand and delete abbreviations first *)
apply (simp);
apply (erule thin_rl)+
apply vcg_simp
    apply (force simp: neq_Nil_conv)
   apply (blast elim!: less_SucE intro: Suc_leI)
  apply (blast elim!: less_SucE intro: less_imp_diff_less dest: lem)
 apply (force simp: nth_list_update)
apply (auto intro: order_antisym)
done

end