(*  ID:         $Id$

Temporary test of nbe module.
*)

theory nbe
imports Main
begin

datatype n = Z | S n
consts
 add :: "n \<Rightarrow> n \<Rightarrow> n"
 mul :: "n \<Rightarrow> n \<Rightarrow> n"
 exp :: "n \<Rightarrow> n \<Rightarrow> n"
primrec
"add Z = id"
"add (S m) = S o add m"
primrec
"mul Z = (%n. Z)"
"mul (S m) = (%n. add (mul m n) n)"
primrec
"exp m Z = S Z"
"exp m (S n) = mul (exp m n) m"

(*ML"set Toplevel.timing"*)
;norm_by_eval "exp (S(S(S(S(S(S(S Z))))))) (S(S(S(S(S Z)))))";
norm_by_eval "0 + (n::nat)";
norm_by_eval "0 + Suc(n)";
norm_by_eval "Suc(n) + Suc m";
norm_by_eval "[] @ xs";
norm_by_eval "(x#xs) @ ys";
norm_by_eval "[x,y,z] @ [a,b,c]";

end
