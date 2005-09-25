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

end
