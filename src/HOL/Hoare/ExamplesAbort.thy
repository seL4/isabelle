(*  Title:      HOL/Hoare/ExamplesAbort.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Some small examples for programs that may abort.
*)

theory ExamplesAbort = HoareAbort:

lemma "VARS x y z::nat
 {y = z & z \<noteq> 0} z \<noteq> 0 \<rightarrow> x := y div z {x = 1}"
by vcg_simp

lemma
 "VARS a i j
 {k <= length a & i < k & j < k} j < length a \<rightarrow> a[i] := a!j {True}"
apply vcg_simp
apply arith
done

lemma "VARS (a::int list) i
 {True}
 i := 0;
 WHILE i < length a
 INV {i <= length a}
 DO a[i] := 7; i := i+1 OD
 {True}"
apply vcg_simp
apply arith
done

end
