(*  Title:      HOL/Hoare/Examples.thy
    Author:     Norbert Galm
    Copyright   1998 TUM
*)

section \<open>Various examples\<close>

theory Examples
  imports Hoare_Logic Arith2
begin

subsection \<open>Arithmetic\<close>

subsubsection \<open>Multiplication by successive addition\<close>

lemma multiply_by_add: "VARS m s a b
  {a=A \<and> b=B}
  m := 0; s := 0;
  WHILE m\<noteq>a
  INV {s=m*b \<and> a=A \<and> b=B}
  DO s := s+b; m := m+(1::nat) OD
  {s = A*B}"
by vcg_simp

lemma multiply_by_add_time: "VARS m s a b t
  {a=A \<and> b=B \<and> t=0}
  m := 0; t := t+1; s := 0; t := t+1;
  WHILE m\<noteq>a
  INV {s=m*b \<and> a=A \<and> b=B \<and> t = 2*m + 2}
  DO s := s+b; t := t+1; m := m+(1::nat); t := t+1 OD
  {s = A*B \<and> t = 2*A + 2}"
by vcg_simp

lemma multiply_by_add2: "VARS M N P :: int
 {m=M \<and> n=N}
 IF M < 0 THEN M := -M; N := -N ELSE SKIP FI;
 P := 0;
 WHILE 0 < M
 INV {0 \<le> M \<and> (\<exists>p. p = (if m<0 then -m else m) & p*N = m*n & P = (p-M)*N)}
 DO P := P+N; M := M - 1 OD
 {P = m*n}"
apply vcg_simp
 apply (auto simp add:int_distrib)
done

lemma multiply_by_add2_time: "VARS M N P t :: int
 {m=M \<and> n=N \<and> t=0}
 IF M < 0 THEN M := -M; t := t+1; N := -N; t := t+1 ELSE SKIP FI;
 P := 0; t := t+1;
 WHILE 0 < M
 INV {0 \<le> M & (\<exists>p. p = (if m<0 then -m else m) & p*N = m*n & P = (p-M)*N & t \<ge> 0 & t \<le> 2*(p-M)+3)}
 DO P := P+N; t := t+1; M := M - 1; t := t+1 OD
 {P = m*n & t \<le> 2*abs m + 3}"
apply vcg_simp
 apply (auto simp add:int_distrib)
done


subsubsection \<open>Euclid's algorithm for GCD\<close>

lemma Euclid_GCD: "VARS a b
 {0<A & 0<B}
 a := A; b := B;
 WHILE  a \<noteq> b
 INV {0<a & 0<b & gcd A B = gcd a b}
 DO IF a<b THEN b := b-a ELSE a := a-b FI OD
 {a = gcd A B}"
apply vcg
  \<comment> \<open>Now prove the verification conditions\<close>
  apply auto
  apply(simp add: gcd_diff_r less_imp_le)
 apply(simp add: linorder_not_less gcd_diff_l)
apply(erule gcd_nnn)
done

lemma Euclid_GCD_time: "VARS a b t
 {0<A & 0<B & t=0}
 a := A; t := t+1; b := B; t := t+1; 
 WHILE  a \<noteq> b
 INV {0<a & 0<b & gcd A B = gcd a b & a\<le>A & b\<le>B & t \<le> max A B - max a b + 2}
 DO IF a<b THEN b := b-a; t := t+1 ELSE a := a-b; t := t+1 FI OD
 {a = gcd A B & t \<le> max A B + 2}"
apply vcg
  \<comment> \<open>Now prove the verification conditions\<close>
  apply auto
  apply(simp add: gcd_diff_r less_imp_le)
 apply(simp add: linorder_not_less gcd_diff_l)
apply(erule gcd_nnn)
done


subsubsection \<open>Dijkstra's extension of Euclid's algorithm for simultaneous GCD and SCM\<close>

text \<open>
  From E.W. Disjkstra. Selected Writings on Computing, p 98 (EWD474),
  where it is given without the invariant. Instead of defining \<open>scm\<close>
  explicitly we have used the theorem \<open>scm x y = x * y / gcd x y\<close> and avoided
  division by mupltiplying with \<open>gcd x y\<close>.
\<close>

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
 apply(simp add: distribs gcd_diff_r linorder_not_less gcd_diff_l)
apply(simp add: distribs gcd_nnn)
done


subsubsection \<open>Power by iterated squaring and multiplication\<close>

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
 apply simp
apply simp
done


subsubsection \<open>Factorial\<close>

lemma factorial: "VARS a b
 {a=A}
 b := 1;
 WHILE a > 0
 INV {fac A = b * fac a}
 DO b := b*a; a := a - 1 OD
 {b = fac A}"
apply vcg_simp
apply(clarsimp split: nat_diff_split)
done

lemma factorial_time: "VARS a b t
 {a=A & t=0}
 b := 1; t := t+1;
 WHILE a > 0
 INV {fac A = b * fac a & a \<le> A & t = 2*(A-a)+1}
 DO b := b*a; t := t+1; a := a - 1; t := t+1 OD
 {b = fac A & t = 2*A + 1}"
apply vcg_simp
apply(clarsimp split: nat_diff_split)
done

lemma [simp]: "1 \<le> i \<Longrightarrow> fac (i - Suc 0) * i = fac i"
by(induct i, simp_all)

lemma factorial2: "VARS i f
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

lemma factorial2_time: "VARS i f t
 {t=0}
 i := (1::nat); t := t+1; f := 1; t := t+1;
 WHILE i \<le> n INV {f = fac(i - 1) & 1 \<le> i & i \<le> n+1 & t = 2*(i-1)+2}
 DO f := f*i; t := t+1; i := i+1; t := t+1 OD
 {f = fac n & t = 2*n+2}"
apply vcg_simp
 apply auto
apply(subgoal_tac "i = Suc n")
 apply simp
apply arith
done


subsubsection \<open>Square root\<close>

\<comment> \<open>the easy way:\<close>

lemma sqrt: "VARS r x
 {True}
 r := (0::nat);
 WHILE (r+1)*(r+1) <= X
 INV {r*r \<le> X}
 DO r := r+1 OD
 {r*r <= X & X < (r+1)*(r+1)}"
apply vcg_simp
done

lemma sqrt_time: "VARS r t
 {t=0}
 r := (0::nat); t := t+1;
 WHILE (r+1)*(r+1) <= X
 INV {r*r \<le> X & t = r+1}
 DO r := r+1; t := t+1 OD
 {r*r <= X & X < (r+1)*(r+1) & (t-1)*(t-1) \<le> X}"
apply vcg_simp
done

\<comment> \<open>without multiplication\<close>
lemma sqrt_without_multiplication: "VARS u w r
 {x=X}
 u := 1; w := 1; r := (0::nat);
 WHILE w <= X
 INV {u = r+r+1 & w = (r+1)*(r+1) & r*r <= X}
 DO r := r + 1; w := w + u + 2; u := u + 2 OD
 {r*r <= X & X < (r+1)*(r+1)}"
apply vcg_simp
done


subsection \<open>Lists\<close>

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

lemma imperative_reverse_time: "VARS y x t
 {x=X & t=0}
 y:=[]; t := t+1;
 WHILE x ~= []
 INV {rev(x)@y = rev(X) & t = 2*(length y) + 1}
 DO y := (hd x # y); t := t+1; x := tl x; t := t+1 OD
 {y=rev(X) & t = 2*length X + 1}"
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

lemma imperative_append_time_no_rev: "VARS x y t
 {x=X & y=Y}
 x := rev(x); t := 0;
 WHILE x~=[]
 INV {rev(x)@y = X@Y & length x \<le> length X & t = 2 * (length X - length x)}
 DO y := (hd x # y); t := t+1;
    x := tl x; t := t+1
 OD
 {y = X@Y & t = 2 * length X}"
apply vcg_simp
apply(simp add: neq_Nil_conv)
apply auto
done


subsection \<open>Arrays\<close>

subsubsection \<open>Search for a key\<close>

lemma zero_search: "VARS A i
 {True}
 i := 0;
 WHILE i < length A & A!i \<noteq> key
 INV {\<forall>j. j<i --> A!j \<noteq> key}
 DO i := i+1 OD
 {(i < length A --> A!i = key) &
  (i = length A --> (\<forall>j. j < length A \<longrightarrow> A!j \<noteq> key))}"
apply vcg_simp
apply(blast elim!: less_SucE)
done

lemma zero_search_time: "VARS A i t
 {t=0}
 i := 0; t := t+1;
 WHILE i < length A \<and> A!i \<noteq> key
 INV {(\<forall>j. j<i \<longrightarrow> A!j \<noteq> key) \<and> i \<le> length A \<and> t = i+1}
 DO i := i+1; t := t+1 OD
 {(i < length A \<longrightarrow> A!i = key) \<and>
  (i = length A \<longrightarrow> (\<forall>j. j < length A --> A!j \<noteq> key)) \<and> t \<le> length A + 1}"
apply vcg_simp
apply(blast elim!: less_SucE)
done

text \<open>
  The \<open>partition\<close> procedure for quicksort.
    \<^item> \<open>A\<close> is the array to be sorted (modelled as a list).
    \<^item> Elements of \<open>A\<close> must be of class order to infer at the end
      that the elements between u and l are equal to pivot.

  Ambiguity warnings of parser are due to \<open>:=\<close> being used
  both for assignment and list update.
\<close>
lemma lem: "m - Suc 0 < n ==> m < Suc n"
by arith


lemma Partition:
"[| leq == \<lambda>A i. \<forall>k. k<i \<longrightarrow> A!k \<le> pivot;
    geq == \<lambda>A i. \<forall>k. i<k \<and> k<length A \<longrightarrow> pivot \<le> A!k |] ==>
 VARS A u l
 {0 < length(A::('a::order)list)}
 l := 0; u := length A - Suc 0;
 WHILE l \<le> u
  INV {leq A l \<and> geq A u \<and> u<length A \<and> l\<le>length A}
  DO WHILE l < length A \<and> A!l \<le> pivot
     INV {leq A l & geq A u \<and> u<length A \<and> l\<le>length A}
     DO l := l+1 OD;
     WHILE 0 < u & pivot \<le> A!u
     INV {leq A l & geq A u  \<and> u<length A \<and> l\<le>length A}
     DO u := u - 1 OD;
     IF l \<le> u THEN A := A[l := A!u, u := A!l] ELSE SKIP FI
  OD
 {leq A u & (\<forall>k. u<k \<and> k<l --> A!k = pivot) \<and> geq A l}"
\<comment> \<open>expand and delete abbreviations first\<close>
apply (simp)
apply (erule thin_rl)+
apply vcg_simp
   apply (force simp: neq_Nil_conv)
  apply (blast elim!: less_SucE intro: Suc_leI)
 apply (blast elim!: less_SucE intro: less_imp_diff_less dest: lem)
apply (force simp: nth_list_update)
done

end
