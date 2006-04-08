(*  Title:      HOLCF/IOA/ABP/Lemmas.ML
    ID:         $Id$
    Author:     Olaf Mueller
*)

(* Logic *)

Goal "(~(A&B)) = ((~A)&B| ~B)";
by (Fast_tac 1);
qed "and_de_morgan_and_absorbe";

Goal "(if C then A else B) --> (A|B)";
by (stac split_if 1);
by (Fast_tac 1);
qed "bool_if_impl_or";

Goal "(? x. x=P & Q(x)) = Q(P)";
by (Fast_tac 1);
qed"exis_elim";


(* Sets *)

val set_lemmas =
   map (fn s => prove_goal Main.thy s (fn _ => [Fast_tac 1]))
        ["f(x) : (UN x. {f(x)})",
         "f x y : (UN x y. {f x y})",
         "!!a. (!x. a ~= f(x)) ==> a ~: (UN x. {f(x)})",
         "!!a. (!x y. a ~= f x y) ==> a ~: (UN x y. {f x y})"];

(* 2 Lemmas to add to set_lemmas ... , used also for action handling, 
   namely for Intersections and the empty list (compatibility of IOA!)  *)
Goal "(UN b.{x. x=f(b)})= (UN b.{f(b)})"; 
 by (rtac set_ext 1);
 by (Fast_tac 1);
qed "singleton_set";

Goal "((A|B)=False) = ((~A)&(~B))";
 by (Fast_tac 1);
qed "de_morgan";

(* Lists *)

Goal "hd(l@m) = (if l~=[] then hd(l) else hd(m))";
by (induct_tac "l" 1);
by (Simp_tac 1);
by (Simp_tac 1);
qed "hd_append";

Goal "l ~= [] --> (? x xs. l = (x#xs))";
 by (induct_tac "l" 1);
 by (Simp_tac 1);
 by (Fast_tac 1);
qed"cons_not_nil";
