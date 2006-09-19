(*  ID:         $Id$
    Authors:    Klaus Aehlig, Tobias Nipkow

Test of normalization function
*)

theory NormalForm
imports Main
begin

lemma "p \<longrightarrow> True" by normalization
declare disj_assoc [code func]
lemma "((P | Q) | R) = (P | (Q | R))" by normalization
lemma "0 + (n::nat) = n" by normalization
lemma "0 + Suc n = Suc n" by normalization
lemma "Suc n + Suc m = n + Suc (Suc m)" by normalization
lemma "~((0::nat) < (0::nat))" by normalization


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

lemma "add2 (add2 n m) k = add2 n (add2 m k)" by normalization
lemma "add2 (add2 (S n) (S m)) (S k) = S(S(S(add2 n (add2 m k))))" by normalization
lemma "add2 (add2 (S n) (add2 (S m) Z)) (S k) = S(S(S(add2 n (add2 m k))))" by normalization

primrec
"mul Z = (%n. Z)"
"mul (S m) = (%n. add (mul m n) n)"
primrec
"mul2 Z n = Z"
"mul2 (S m) n = add2 n (mul2 m n)"
primrec
"exp m Z = S Z"
"exp m (S n) = mul (exp m n) m"

lemma "mul2 (S(S(S(S(S Z))))) (S(S(S Z))) = S(S(S(S(S(S(S(S(S(S(S(S(S(S(S Z))))))))))))))" by normalization
lemma "mul (S(S(S(S(S Z))))) (S(S(S Z))) = S(S(S(S(S(S(S(S(S(S(S(S(S(S(S Z))))))))))))))" by normalization
lemma "exp (S(S Z)) (S(S(S(S Z)))) = exp (S(S(S(S Z)))) (S(S Z))" by normalization

lemma "(let ((x,y),(u,v)) = ((Z,Z),(Z,Z)) in add (add x y) (add u v)) = Z" by normalization
lemma "(%((x,y),(u,v)). add (add x y) (add u v)) ((Z,Z),(Z,Z)) = Z" by normalization

lemma "case Z of Z \<Rightarrow> True | S x \<Rightarrow> False" by normalization

normal_form "[] @ []"
normal_form "[] @ xs"
normal_form "[a::'d,b,c] @ xs"
normal_form "[%a::'x. a, %b. b, c] @ xs"
normal_form "[%a::'x. a, %b. b, c] @ [u,v]"
normal_form "map f (xs::'c list)"
normal_form "map f [x,y,z::'x]"
normal_form "map (%f. f True) [id,g,Not]"
normal_form "map (%f. f True) ([id,g,Not] @ fs)"
normal_form "rev[a,b,c]"
normal_form "rev(a#b#cs)"
normal_form "map map [f,g,h]"
normal_form "map (%F. F [a,b,c::'x]) (map map [f,g,h])"
normal_form "map (%F. F ([a,b,c] @ ds)) (map map ([f,g,h]@fs))"
normal_form "map (%F. F [Z,S Z,S(S Z)]) (map map [S,add (S Z),mul (S(S Z)),id])"
normal_form "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) [None, Some ()]"
normal_form "case xs of [] \<Rightarrow> True | x#xs \<Rightarrow> False"
normal_form "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) xs"
normal_form "let x = y::'x in [x,x]"
normal_form "Let y (%x. [x,x])"
normal_form "case n of Z \<Rightarrow> True | S x \<Rightarrow> False"
normal_form "(%(x,y). add x y) (S z,S z)"
normal_form "filter (%x. x) ([True,False,x]@xs)"
normal_form "filter Not ([True,False,x]@xs)"

normal_form "[x,y,z] @ [a,b,c]"
normal_form "%(xs, ys). xs @ ys"
normal_form "(%(xs, ys). xs @ ys) ([a, b, c], [d, e, f])"
normal_form "%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True"
normal_form "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) [None, Some ()]"

normal_form "last [a, b, c]"
normal_form "last ([a, b, c] @ xs)"

normal_form "min 0 x"
normal_form "min 0 (x::nat)"

normal_form "(2::int) + 3 - 1 + (- k) * 2"
normal_form "(4::int) * 2"
normal_form "(-4::int) * 2"
normal_form "abs ((-4::int) + 2 * 1)"
normal_form "(2::int) + 3"
normal_form "(2::int) + 3 * (- 4) * (- 1)"
normal_form "(2::int) + 3 * (- 4) * 1 + 0"
normal_form "(2::int) < 3"
normal_form "(2::int) <= 3"
normal_form "abs ((-4::int) + 2 * 1)"
normal_form "4 - 42 * abs (3 + (-7\<Colon>int))"

end
