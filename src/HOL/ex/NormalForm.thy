(*  ID:         $Id$
    Authors:    Klaus Aehlig, Tobias Nipkow
*)

header {* Test of normalization function *}

theory NormalForm
imports Main "~~/src/HOL/Real/Rational"
begin

lemma "True" by normalization
lemma "p \<longrightarrow> True" by normalization
declare disj_assoc [code func]
lemma "((P | Q) | R) = (P | (Q | R))" by normalization rule
declare disj_assoc [code func del]
lemma "0 + (n::nat) = n" by normalization rule
lemma "0 + Suc n = Suc n" by normalization rule
lemma "Suc n + Suc m = n + Suc (Suc m)" by normalization rule
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

declare add2.simps [code]
lemma [code]: "add2 (add2 n m) k = add2 n (add2 m k)"
  by (induct n) auto
lemma [code]: "add2 n (S m) =  S (add2 n m)"
  by(induct n) auto
lemma [code]: "add2 n Z = n"
  by(induct n) auto

lemma "add2 (add2 n m) k = add2 n (add2 m k)" by normalization rule
lemma "add2 (add2 (S n) (S m)) (S k) = S(S(S(add2 n (add2 m k))))" by normalization rule
lemma "add2 (add2 (S n) (add2 (S m) Z)) (S k) = S(S(S(add2 n (add2 m k))))" by normalization rule

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
lemma "split (%x y. x) (a, b) = a" by normalization rule
lemma "(%((x,y),(u,v)). add (add x y) (add u v)) ((Z,Z),(Z,Z)) = Z" by normalization

lemma "case Z of Z \<Rightarrow> True | S x \<Rightarrow> False" by normalization

lemma "[] @ [] = []" by normalization
lemma "map f [x,y,z::'x] = [f x, f y, f z]" by normalization rule+
lemma "[a, b, c] @ xs = a # b # c # xs" by normalization rule+
lemma "[] @ xs = xs" by normalization rule
lemma "map (%f. f True) [id, g, Not] = [True, g True, False]" by normalization rule+
lemma "map (%f. f True) ([id, g, Not] @ fs) = [True, g True, False] @ map (%f. f True) fs" by normalization rule+
lemma "rev [a, b, c] = [c, b, a]" by normalization rule+
normal_form "rev (a#b#cs) = rev cs @ [b, a]"
normal_form "map (%F. F [a,b,c::'x]) (map map [f,g,h])"
normal_form "map (%F. F ([a,b,c] @ ds)) (map map ([f,g,h]@fs))"
normal_form "map (%F. F [Z,S Z,S(S Z)]) (map map [S,add (S Z),mul (S(S Z)),id])"
lemma "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) [None, Some ()] = [False, True]" 
  by normalization
normal_form "case xs of [] \<Rightarrow> True | x#xs \<Rightarrow> False"
normal_form "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) xs = P"
lemma "let x = y in [x, x] = [y, y]" by normalization rule+
lemma "Let y (%x. [x,x]) = [y, y]" by normalization rule+
normal_form "case n of Z \<Rightarrow> True | S x \<Rightarrow> False"
lemma "(%(x,y). add x y) (S z,S z) = S (add z (S z))" by normalization rule+
normal_form "filter (%x. x) ([True,False,x]@xs)"
normal_form "filter Not ([True,False,x]@xs)"

lemma "[x,y,z] @ [a,b,c] = [x, y, z, a, b, c]" by normalization rule+
lemma "(%(xs, ys). xs @ ys) ([a, b, c], [d, e, f]) = [a, b, c, d, e, f]" by normalization rule+
lemma "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) [None, Some ()] = [False, True]" by normalization

lemma "last [a, b, c] = c" by normalization rule
lemma "last ([a, b, c] @ xs) = (if null xs then c else last xs)"
  by normalization rule

lemma "(2::int) + 3 - 1 + (- k) * 2 = 4 + - k * 2" by normalization rule
lemma "(-4::int) * 2 = -8" by normalization
lemma "abs ((-4::int) + 2 * 1) = 2" by normalization
lemma "(2::int) + 3 = 5" by normalization
lemma "(2::int) + 3 * (- 4) * (- 1) = 14" by normalization
lemma "(2::int) + 3 * (- 4) * 1 + 0 = -10" by normalization
lemma "(2::int) < 3" by normalization
lemma "(2::int) <= 3" by normalization
lemma "abs ((-4::int) + 2 * 1) = 2" by normalization
lemma "4 - 42 * abs (3 + (-7\<Colon>int)) = -164" by normalization
lemma "(if (0\<Colon>nat) \<le> (x\<Colon>nat) then 0\<Colon>nat else x) = 0" by normalization
lemma "4 = Suc (Suc (Suc (Suc 0)))" by normalization
lemma "nat 4 = Suc (Suc (Suc (Suc 0)))" by normalization
lemma "[Suc 0, 0] = [Suc 0, 0]" by normalization
lemma "max (Suc 0) 0 = Suc 0" by normalization
lemma "(42::rat) / 1704 = 1 / 284 + 3 / 142" by normalization
normal_form "Suc 0 \<in> set ms"

lemma "f = f" by normalization rule+
lemma "f x = f x" by normalization rule+
lemma "(f o g) x = f (g x)" by normalization rule+
lemma "(f o id) x = f x" by normalization rule+
normal_form "(\<lambda>x. x)"

(* Church numerals: *)

normal_form "(%m n f x. m f (n f x)) (%f x. f(f(f(x)))) (%f x. f(f(f(x))))"
normal_form "(%m n f x. m (n f) x) (%f x. f(f(f(x)))) (%f x. f(f(f(x))))"
normal_form "(%m n. n m) (%f x. f(f(f(x)))) (%f x. f(f(f(x))))"

end
