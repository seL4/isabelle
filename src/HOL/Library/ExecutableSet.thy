(*  Title:      HOL/Library/ExecutableSet.thy
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Implementation of finite sets by lists *}

theory ExecutableSet
imports Main
begin

lemma [code target: Set]: "(A = B) = (A \<subseteq> B \<and> B \<subseteq> A)"
  by blast

declare bex_triv_one_point1 [symmetric, standard, code]

types_code
  set ("_ list")
attach (term_of) {*
fun term_of_set f T [] = Const ("{}", Type ("set", [T]))
  | term_of_set f T (x :: xs) = Const ("insert",
      T --> Type ("set", [T]) --> Type ("set", [T])) $ f x $ term_of_set f T xs;
*}
attach (test) {*
fun gen_set' aG i j = frequency
  [(i, fn () => aG j :: gen_set' aG (i-1) j), (1, fn () => [])] ()
and gen_set aG i = gen_set' aG i i;
*}

code_syntax_tyco set
  ml ("_ list")
  haskell (target_atom "[_]")

code_syntax_const "{}"
  ml (target_atom "[]")
  haskell (target_atom "[]")

consts_code
  "{}"      ("[]")
  "insert"  ("(_ ins _)")
  "op Un"   ("(_ union _)")
  "op Int"  ("(_ inter _)")
  "op -" :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" ("(_ \\\\ _)")
  "image"   ("\<module>image")
attach {*
fun image f S = distinct (map f S);
*}
  "UNION"   ("\<module>UNION")
attach {*
fun UNION S f = Library.foldr Library.union (map f S, []);
*}
  "INTER"   ("\<module>INTER")
attach {*
fun INTER S f = Library.foldr1 Library.inter (map f S);
*}
  "Bex"     ("\<module>Bex")
attach {*
fun Bex S P = Library.exists P S;
*}
  "Ball"     ("\<module>Ball")
attach {*
fun Ball S P = Library.forall P S;
*}

code_generate ("op mem")

code_primconst "insert"
  depending_on ("List.const.member")
ml {*
fun insert x xs =
  if List.member x xs then xs
  else x::xs;
*}
haskell {*
insert x xs =
  if elem x xs then xs else x:xs
*}

code_primconst "op Un"
  depending_on ("List.const.insert")
ml {*
fun union xs [] = xs
  | union [] ys = ys
  | union (x::xs) ys = union xs (insert x ys);
*}
haskell {*
union xs [] = xs
union [] ys = ys
union (x:xs) ys = union xs (insert x ys)
*}

code_primconst "op Int"
  depending_on ("List.const.member")
ml {*
fun inter [] ys = []
  | inter (x::xs) ys =
      if List.member x ys
      then x :: inter xs ys
      else inter xs ys;
*}
haskell {*
inter [] ys = []
inter (x:xs) ys =
  if elem x ys
  then x : inter xs ys
  else inter xs ys
*}

code_primconst  "op -" :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
ml {*
fun op_minus ys [] = ys
  | op_minus ys (x::xs) =
      let
        fun minus [] x = []
          | minus (y::ys) x = if x = y then ys else y :: minus ys x
      in
        op_minus (minus ys x) xs
      end;
*}
haskell {*
op_minus ys [] = ys
op_minus ys (x:xs) = op_minus (minus ys x) xs where
  minus [] x = []
  minus (y:ys) x = if x = y then ys else y : minus ys x
*}

code_primconst "image"
  depending_on ("List.const.insert")
ml {*
fun image f =
  let
    fun img xs [] = xs
      | img xs (y::ys) = img (insert (f y) xs) ys;
  in img [] end;;
*}
haskell {*
image f = img [] where
  img xs [] = xs
  img xs (y:ys) = img (insert (f y) xs) ys;
*}

code_primconst "UNION"
  depending_on ("List.const.union")
ml {*
fun UNION [] f = []
  | UNION (x::xs) f = union (f x) (UNION xs);
*}
haskell {*
UNION [] f = []
UNION (x:xs) f = union (f x) (UNION xs);
*}

code_primconst "INTER"
  depending_on ("List.const.inter")
ml {*
fun INTER [] f = []
  | INTER (x::xs) f = inter (f x) (INTER xs);
*}
haskell {*
INTER [] f = []
INTER (x:xs) f = inter (f x) (INTER xs);
*}

code_primconst "Ball"
ml {*
fun Ball [] f = true
  | Ball (x::xs) f = f x andalso Ball f xs;
*}
haskell {*
Ball = all . flip
*}

code_primconst "Bex"
ml {*
fun Bex [] f = false
  | Bex (x::xs) f = f x orelse Bex f xs;
*}
haskell {*
Ball = any . flip
*}

end
