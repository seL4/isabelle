(*  ID:         $Id$

Temporary test of nbe module.
*)

theory nbe
imports Main
begin

ML "reset quick_and_dirty"

declare disj_assoc[code]

norm_by_eval "(P | Q) | R"

(*lemma[code]: "(P \<longrightarrow> P) = True" by blast
norm_by_eval "P \<longrightarrow> P"
norm_by_eval "True \<longrightarrow> P"*)


datatype n = Z | S n
consts
 add :: "n \<Rightarrow> n \<Rightarrow> n"
 add2 :: "n \<Rightarrow> n \<Rightarrow> n"
 mul :: "n \<Rightarrow> n \<Rightarrow> n"
 mul2 :: "n \<Rightarrow> n \<Rightarrow> n"
 exp :: "n \<Rightarrow> n \<Rightarrow> n"
primrec
"add Z = id"
"add (S m) = S o add m"
primrec
"add2 Z n = n"
"add2 (S m) n = S(add2 m n)"

lemma [code]: "add2 (add2 n m) k = add2 n (add2 m k)"
by(induct n, auto)
lemma [code]: "add2 n (S m) =  S(add2 n m)"
by(induct n, auto)
lemma [code]: "add2 n Z = n"
by(induct n, auto)
 
norm_by_eval "add2 (add2 n m) k"
norm_by_eval "add2 (add2 (S n) (S m)) (S k)"
norm_by_eval "add2 (add2 (S n)(add2 (S m) Z)) (S k)"

primrec
"mul Z = (%n. Z)"
"mul (S m) = (%n. add (mul m n) n)"
primrec
"mul2 Z n = Z"
"mul2 (S m) n = add2 n (mul2 m n)"
primrec
"exp m Z = S Z"
"exp m (S n) = mul (exp m n) m"

norm_by_eval "mul2 (S(S(S(S(S(S(S Z))))))) (S(S(S(S(S Z)))))"
norm_by_eval "mul (S(S(S(S(S(S(S Z))))))) (S(S(S(S(S Z)))))"
norm_by_eval "exp (S(S(S(S(S(S(S Z))))))) (S(S(S(S(S Z)))))"

norm_by_eval "[] @ []"
norm_by_eval "[] @ xs"
norm_by_eval "[a,b,c] @ xs"
norm_by_eval "[%a. a, %b. b, c] @ xs"
norm_by_eval "[%a. a, %b. b, c] @ [u,v]"
norm_by_eval "map f [x,y,z]"
norm_by_eval "map (%f. f True) [id,g,Not]"
norm_by_eval "map (%f. f True) ([id,g,Not] @ fs)"
norm_by_eval "rev[a,b,c]"
norm_by_eval "rev(a#b#cs)"
norm_by_eval "map map [f,g,h]"
norm_by_eval "map (%F. F [a,b,c]) (map map [f,g,h])"
norm_by_eval "map (%F. F ([a,b,c] @ ds)) (map map ([f,g,h]@fs))"
norm_by_eval "map (%F. F [Z,S Z,S(S Z)]) (map map [S,add (S Z),mul (S(S Z)),id])"
norm_by_eval "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) [None, Some ()]"
norm_by_eval "case xs of [] \<Rightarrow> True | x#xs \<Rightarrow> False"
norm_by_eval "case Z of Z \<Rightarrow> True | S x \<Rightarrow> False"
norm_by_eval "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) xs"
norm_by_eval "let x = y in [x,x]"
norm_by_eval "Let y (%x. [x,x])"
norm_by_eval "case n of Z \<Rightarrow> True | S x \<Rightarrow> False"
norm_by_eval "(%(x,y). add x y) (S z,S z)"
norm_by_eval "filter (%x. x) ([True,False,x]@xs)"
norm_by_eval "filter Not ([True,False,x]@xs)"

norm_by_eval "0 + (n::nat)"
norm_by_eval "0 + Suc(n)"
norm_by_eval "Suc(n) + Suc m"
norm_by_eval "[] @ xs"
norm_by_eval "(x#xs) @ ys"
norm_by_eval "[x,y,z] @ [a,b,c]"
norm_by_eval "%(xs, ys). xs @ ys"
norm_by_eval "(%(xs, ys). xs @ ys) ([a, b, c], [d, e, f])"
norm_by_eval "%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True"
norm_by_eval "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) [None, Some ()]"
norm_by_eval "rev [a, b, c]"

norm_by_eval "case n of None \<Rightarrow> True | Some((x,y),(u,v)) \<Rightarrow> False"
norm_by_eval "let ((x,y),(u,v)) = ((Z,Z),(Z,Z)) in add (add x y) (add u v)"
norm_by_eval "(%((x,y),(u,v)). add (add x y) (add u v)) ((Z,Z),(Z,Z))"
norm_by_eval "last[a,b,c]"

(*
  won't work since it relies on 
  polymorphically used ad-hoc overloaded function:
  norm_by_eval "max 0 (0::nat)"
*)

text (*
  Numerals still take their time\<dots>
*)

end
