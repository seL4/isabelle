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

consts
  flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c"
  member :: "'a list \<Rightarrow> 'a \<Rightarrow> bool"
  insert_ :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  remove :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  inter :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"

defs
  flip_def: "flip f a b == f b a"
  member_def: "member xs x == x mem xs"
  insert_def: "insert_ x xs == if member xs x then xs else x#xs"

primrec
  "remove x [] = []"
  "remove x (y#ys) = (if x = y then ys else y # remove x ys)"

primrec
  "inter [] ys = []"
  "inter (x#xs) ys = (let xs' = inter xs ys in if member ys x then x#xs' else xs')"

code_syntax_const "insert"
  ml ("{*insert_*}")
  haskell ("{*insert_*}")

code_syntax_const "op Un"
  ml ("{*foldr insert_*}")
  haskell ("{*foldr insert_*}")

code_syntax_const "op -" :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  ml ("{*(flip o foldr) remove*}")
  haskell ("{*(flip o foldr) remove*}")

code_syntax_const "op Int"
  ml ("{*inter*}")
  haskell ("{*inter*}")

code_syntax_const "image"
  ml ("{*\<lambda>f. foldr (insert_ o f)*}")
  haskell ("{*\<lambda>f. foldr (insert_ o f)*}")

code_syntax_const "INTER"
  ml ("{*\<lambda>xs f.  foldr (inter o f) xs*}")
  haskell ("{*\<lambda>xs f.  foldr (inter o f) xs*}")

code_syntax_const "UNION"
  ml ("{*\<lambda>xs f.  foldr (foldr insert_ o f) xs*}")
  haskell ("{*\<lambda>xs f.  foldr (foldr insert_ o f) xs*}")

code_primconst "Ball"
ml {*
fun `_` [] f = true
  | `_` (x::xs) f = f x andalso `_` xs f;
*}
haskell {*
`_` = flip all
*}

code_primconst "Bex"
ml {*
fun `_` [] f = false
  | `_` (x::xs) f = f x orelse `_` xs f;
*}
haskell {*
`_` = flip any
*}

end
