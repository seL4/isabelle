(*  Authors:  Klaus Aehlig, Tobias Nipkow *)

section \<open>Testing implementation of normalization by evaluation\<close>

theory Normalization_by_Evaluation
imports Complex_Main "HOL-Library.Word"
begin

lemma "True" by normalization
lemma "p \<longrightarrow> True" by normalization
declare disj_assoc [code nbe]
lemma "((P | Q) | R) = (P | (Q | R))" by normalization
lemma "0 + (n::nat) = n" by normalization
lemma "0 + Suc n = Suc n" by normalization
lemma "Suc n + Suc m = n + Suc (Suc m)" by normalization
lemma "~((0::nat) < (0::nat))" by normalization

datatype n = Z | S n

primrec add :: "n \<Rightarrow> n \<Rightarrow> n" where
   "add Z = id"
 | "add (S m) = S o add m"

primrec add2 :: "n \<Rightarrow> n \<Rightarrow> n" where
   "add2 Z n = n"
 | "add2 (S m) n = S(add2 m n)"

declare add2.simps [code]
lemma [code]: "add2 n Z = n"
  by(induct n) auto
lemma [code]: "add2 n (S m) =  S (add2 n m)"
  by(induct n) auto
lemma [code nbe]: "add2 (add2 n m) k = add2 n (add2 m k)"
  by (induct n) auto


lemma "add2 (add2 n m) k = add2 n (add2 m k)" by normalization
lemma "add2 (add2 (S n) (S m)) (S k) = S(S(S(add2 n (add2 m k))))" by normalization
lemma "add2 (add2 (S n) (add2 (S m) Z)) (S k) = S(S(S(add2 n (add2 m k))))" by normalization

primrec mul :: "n \<Rightarrow> n \<Rightarrow> n" where
   "mul Z = (%n. Z)"
 | "mul (S m) = (%n. add (mul m n) n)"

primrec mul2 :: "n \<Rightarrow> n \<Rightarrow> n" where
   "mul2 Z n = Z"
 | "mul2 (S m) n = add2 n (mul2 m n)"

primrec exp :: "n \<Rightarrow> n \<Rightarrow> n" where
   "exp m Z = S Z"
 | "exp m (S n) = mul (exp m n) m"

lemma "mul2 (S(S(S(S(S Z))))) (S(S(S Z))) = S(S(S(S(S(S(S(S(S(S(S(S(S(S(S Z))))))))))))))" by normalization
lemma "mul (S(S(S(S(S Z))))) (S(S(S Z))) = S(S(S(S(S(S(S(S(S(S(S(S(S(S(S Z))))))))))))))" by normalization
lemma "exp (S(S Z)) (S(S(S(S Z)))) = exp (S(S(S(S Z)))) (S(S Z))" by normalization

lemma "(let ((x,y),(u,v)) = ((Z,Z),(Z,Z)) in add (add x y) (add u v)) = Z" by normalization
lemma "case_prod (%x y. x) (a, b) = a" by normalization
lemma "(%((x,y),(u,v)). add (add x y) (add u v)) ((Z,Z),(Z,Z)) = Z" by normalization

lemma "case Z of Z \<Rightarrow> True | S x \<Rightarrow> False" by normalization

lemma "[] @ [] = []" by normalization
lemma "map f [x,y,z::'x] = [f x, f y, f z]" by normalization
lemma "[a, b, c] @ xs = a # b # c # xs" by normalization
lemma "[] @ xs = xs" by normalization
lemma "map (%f. f True) [id, g, Not] = [True, g True, False]" by normalization

lemma "map (%f. f True) ([id, g, Not] @ fs) = [True, g True, False] @ map (%f. f True) fs"
  by normalization rule
lemma "rev [a, b, c] = [c, b, a]" by normalization
value [nbe] "rev (a#b#cs) = rev cs @ [b, a]"
value [nbe] "map (%F. F [a,b,c::'x]) (map map [f,g,h])"
value [nbe] "map (%F. F ([a,b,c] @ ds)) (map map ([f,g,h]@fs))"
value [nbe] "map (%F. F [Z,S Z,S(S Z)]) (map map [S,add (S Z),mul (S(S Z)),id])"
lemma "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) [None, Some ()] = [False, True]" 
  by normalization
value [nbe] "case xs of [] \<Rightarrow> True | x#xs \<Rightarrow> False"
value [nbe] "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) xs = P"
lemma "let x = y in [x, x] = [y, y]" by normalization
lemma "Let y (%x. [x,x]) = [y, y]" by normalization
value [nbe] "case n of Z \<Rightarrow> True | S x \<Rightarrow> False"
lemma "(%(x,y). add x y) (S z,S z) = S (add z (S z))" by normalization
value [nbe] "filter (%x. x) ([True,False,x]@xs)"
value [nbe] "filter Not ([True,False,x]@xs)"

lemma "[x,y,z] @ [a,b,c] = [x, y, z, a, b, c]" by normalization
lemma "(%(xs, ys). xs @ ys) ([a, b, c], [d, e, f]) = [a, b, c, d, e, f]" by normalization
lemma "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) [None, Some ()] = [False, True]" by normalization

lemma "last [a, b, c] = c" by normalization
lemma "last ([a, b, c] @ xs) = last (c # xs)" by normalization

lemma "(2::int) + 3 - 1 + (- k) * 2 = 4 + - k * 2" by normalization
lemma "(-4::int) * 2 = -8" by normalization
lemma "\<bar>(-4::int) + 2 * 1\<bar> = 2" by normalization
lemma "(2::int) + 3 = 5" by normalization
lemma "(2::int) + 3 * (- 4) * (- 1) = 14" by normalization
lemma "(2::int) + 3 * (- 4) * 1 + 0 = -10" by normalization
lemma "(2::int) < 3" by normalization
lemma "(2::int) <= 3" by normalization
lemma "\<bar>(-4::int) + 2 * 1\<bar> = 2" by normalization
lemma "4 - 42 * \<bar>3 + (-7::int)\<bar> = -164" by normalization
lemma "(if (0::nat) \<le> (x::nat) then 0::nat else x) = 0" by normalization
lemma "4 = Suc (Suc (Suc (Suc 0)))" by normalization
lemma "nat 4 = Suc (Suc (Suc (Suc 0)))" by normalization
lemma "[Suc 0, 0] = [Suc 0, 0]" by normalization
lemma "max (Suc 0) 0 = Suc 0" by normalization
lemma "(42::rat) / 1704 = 1 / 284 + 3 / 142" by normalization
value [nbe] "Suc 0 \<in> set ms"

lemma "4 - 42 * 3 - 7 = (256 + 35) - (164 :: 8 word)"
  by normalization

(* non-left-linear patterns, equality by extensionality *)

lemma "f = f" by normalization
lemma "f x = f x" by normalization
lemma "(f o g) x = f (g x)" by normalization
lemma "(f o id) x = f x" by normalization
lemma "(id :: bool \<Rightarrow> bool) = id" by normalization
value [nbe] "(\<lambda>x. x)"

(* Church numerals: *)

value [nbe] "(%m n f x. m f (n f x)) (%f x. f(f(f(x)))) (%f x. f(f(f(x))))"
value [nbe] "(%m n f x. m (n f) x) (%f x. f(f(f(x)))) (%f x. f(f(f(x))))"
value [nbe] "(%m n. n m) (%f x. f(f(f(x)))) (%f x. f(f(f(x))))"

(* handling of type classes in connection with equality *)

lemma "map f [x, y] = [f x, f y]" by normalization
lemma "(map f [x, y], w) = ([f x, f y], w)" by normalization
lemma "map f [x, y] = [f x :: 'a::semigroup_add, f y]" by normalization
lemma "map f [x :: 'a::semigroup_add, y] = [f x, f y]" by normalization
lemma "(map f [x :: 'a::semigroup_add, y], w :: 'b::finite) = ([f x, f y], w)" by normalization

end
