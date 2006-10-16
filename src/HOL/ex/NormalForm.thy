(*  ID:         $Id$
    Authors:    Klaus Aehlig, Tobias Nipkow
*)

header "Test of normalization function"

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
  by(induct n) auto
lemma [code]: "add2 n (S m) =  S (add2 n m)"
  by(induct n) auto
lemma [code]: "add2 n Z = n"
  by(induct n) auto

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
lemma "split (%x y. x) (a, b) = a" by normalization
lemma "(%((x,y),(u,v)). add (add x y) (add u v)) ((Z,Z),(Z,Z)) = Z" by normalization

lemma "case Z of Z \<Rightarrow> True | S x \<Rightarrow> False" by normalization

lemma "[] @ [] = []" by normalization
lemma "[] @ xs = xs" by normalization
lemma "[a \<Colon> 'd, b, c] @ xs = a # b # c # xs" by normalization
lemma "[%a::'x. a, %b. b, c] @ xs = (%x. x) # (%x. x) # c # xs" by normalization
lemma "[%a::'x. a, %b. b, c] @ [u,v] = [%x. x, %x. x, c, u, v]" by normalization
lemma "map f [x,y,z::'x] = [f x, f y, f z]" by normalization
normal_form "map (%f. f True) [id,g,Not]"
normal_form "map (%f. f True) ([id,g,Not] @ fs)"
lemma "rev[a,b,c] = [c, b, a]" by normalization
normal_form "rev(a#b#cs)"
lemma "map map [f,g,h] = [map f, map g, map h]" by normalization
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

lemma "[x,y,z] @ [a,b,c] = [x, y, z, a, b ,c]" by normalization
normal_form "%(xs, ys). xs @ ys"
normal_form "(%(xs, ys). xs @ ys) ([a, b, c], [d, e, f])"
normal_form "%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True"
normal_form "map (%x. case x of None \<Rightarrow> False | Some y \<Rightarrow> True) [None, Some ()]"

lemma "last [a, b, c] = c"
  by normalization
lemma "last ([a, b, c] @ xs) = (if null xs then c else last xs)"
  by normalization

lemma "(2::int) + 3 - 1 + (- k) * 2 = 4 + - k * 2" by normalization
lemma "(-4::int) * 2 = -8" by normalization
lemma "abs ((-4::int) + 2 * 1) = 2" by normalization
lemma "(2::int) + 3 = 5" by normalization
lemma "(2::int) + 3 * (- 4) * (- 1) = 14" by normalization
lemma "(2::int) + 3 * (- 4) * 1 + 0 = -10" by normalization
lemma "(2::int) < 3" by normalization
lemma "(2::int) <= 3" by normalization
lemma "abs ((-4::int) + 2 * 1) = 2" by normalization
lemma "4 - 42 * abs (3 + (-7\<Colon>int)) = -164" by normalization
normal_form "min 0 x"
normal_form "min 0 (x::nat)"
lemma "(if (0\<Colon>nat) \<le> (x\<Colon>nat) then 0\<Colon>nat else x) = 0" by normalization

(* Delaying if: FIXME move to HOL.thy(?) *)

definition delayed_if :: "bool \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a"
"delayed_if b f g = (if b then f() else g())"

lemma [normal_pre]: "(if b then x else y) == delayed_if b (%u. x) (%u. y)"
unfolding delayed_if_def by simp

lemma [normal_post]: "delayed_if b f g == (if b then f() else g())"
unfolding delayed_if_def by simp

lemma [code func]:
 shows "delayed_if True f g = f()" and "delayed_if False f g = g()"
by (auto simp:delayed_if_def)

hide (open) const delayed_if

normal_form "Code_Generator.eq [2..<4] [2,3]"
(*lemma "Code_Generator.eq [2..<4] [2,3]" by normalization*)

definition
 andalso :: "bool \<Rightarrow> bool \<Rightarrow> bool"
"andalso x y = (if x then y else False)"

lemma "andalso a b = (if a then b else False)" by normalization

end
