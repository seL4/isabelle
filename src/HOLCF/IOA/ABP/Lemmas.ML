(*  Title:      HOLCF/IOA/ABP/Lemmas.ML
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

(* Logic *)

val prems = goal HOL.thy "(P ==> Q-->R) ==> P&Q --> R";
  by (fast_tac (claset() addDs prems) 1);
qed "imp_conj_lemma";

goal HOL.thy "(~(A&B)) = ((~A)&B| ~B)";
by (Fast_tac 1);
val and_de_morgan_and_absorbe = result();

goal HOL.thy "(if C then A else B) --> (A|B)";
by (stac split_if 1);
by (Fast_tac 1);
val bool_if_impl_or = result();

(* Sets *)

val set_lemmas =
   map (fn s => prove_goal Set.thy s (fn _ => [Fast_tac 1]))
        ["f(x) : (UN x. {f(x)})",
         "f x y : (UN x y. {f x y})",
         "!!a. (!x. a ~= f(x)) ==> a ~: (UN x. {f(x)})",
         "!!a. (!x y. a ~= f x y) ==> a ~: (UN x y. {f x y})"];

(* 2 Lemmas to add to set_lemmas ... , used also for action handling, 
   namely for Intersections and the empty list (compatibility of IOA!)  *)
goal Set.thy "(UN b.{x. x=f(b)})= (UN b.{f(b)})"; 
 by (rtac set_ext 1);
 by (Fast_tac 1);
val singleton_set =result();

goal HOL.thy "((A|B)=False) = ((~A)&(~B))";
 by (Fast_tac 1);
val de_morgan = result();

(* Lists *)

val list_ss = simpset_of List.thy;

goal List.thy "hd(l@m) = (if l~=[] then hd(l) else hd(m))";
by (induct_tac "l" 1);
by (simp_tac list_ss 1);
by (simp_tac list_ss 1);
val hd_append =result();

goal List.thy "l ~= [] --> (? x xs. l = (x#xs))";
 by (induct_tac "l" 1);
 by (simp_tac list_ss 1);
 by (Fast_tac 1);
qed"cons_not_nil";
