(*  Title:      HOL/Isar_examples/KnasterTarski.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Typical textbook proof example.
*)


theory KnasterTarski = Main:;

(*

text {*
 The proof of Knaster-Tarski below closely follows the presentation in
 'Introduction to Lattices and Order' by Davey/Priestley, pages
 93--94.  Only one statement of their narration has not been rephrased
 in formal Isar language elements, but left as a comment.  Also note
 that Davey/Priestley do not point out non-emptyness of the set ??H,
 (which is obvious, but not vacous).
*};
*)

theorems [dest] = monoD;  (* FIXME [dest!!] *)


theorem KnasterTarski: "mono f ==> EX a::'a set. f a = a";
proof;
  let ??H = "{u. f u <= u}";
  let ??a = "Inter ??H";

  assume mono: "mono f";
  show "f ??a = ??a";
  proof same;
    fix x;
    presume mem: "x : ??H";
    hence "??a <= x"; by (rule Inter_lower);
    with mono; have "f ??a <= f x"; ..;
    also; from mem; have "f x <= x"; ..;
    finally; have "f ??a <= x"; .;
    hence ge: "f ??a <= ??a"; by (rule Inter_greatest);
    (* text {* We now use this inequality to prove the reverse one (!)
      and thereby complete the proof that @term{??a} is a fixpoint. *};  *)
    with mono; have "f (f ??a) <= f ??a"; ..;
    hence "f ??a : ??H"; ..;
    hence "??a <= f ??a"; by (rule Inter_lower);
    also (order_antisym); note ge;
    finally; show "f ??a = ??a"; proof same;
  next;
    have "f UNIV <= UNIV"; by (rule subset_UNIV);
    thus "UNIV : ??H"; ..;
  qed;
qed;


end;
