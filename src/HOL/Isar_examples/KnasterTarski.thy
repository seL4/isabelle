(*  Title:      HOL/Isar_examples/KnasterTarski.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Typical textbook proof example.
*)


theory KnasterTarski = Main:;


theorems [dest] = monoD;  (* FIXME [dest!!] *)

(*
 The proof of Knaster-Tarski below closely follows the presentation in
 'Introduction to Lattices' and Order by Davey/Priestley, pages
 93--94.  All of their narration has been rephrased in terms of formal
 Isar language elements, except one stament only that has been left as
 a comment.  Also note that Davey/Priestley do not point out
 non-emptyness of the set @term{??H}, (which is obvious, but not
 vacous).

 Just as many textbook-style proofs, there is a strong bias towards
 forward reasoning, with little hierarchical structure.
*)

theorem KnasterTarski: "mono f ==> EX a::'a set. f a = a";
proof;
  assume mono: "mono f";

  let ??H = "{u. f u <= u}";
  let ??a = "Inter ??H";

  have "f UNIV <= UNIV"; by (rule subset_UNIV);
  hence "UNIV : ??H"; ..;
  thus "f ??a = ??a";
  proof same;
    fix x;
    assume mem: "x : ??H";
    hence "??a <= x"; by (rule Inter_lower);
    with mono; have "f ??a <= f x"; ..;
    also; from mem; have "... <= x"; ..;
    finally (order_trans); have "f ??a <= x"; .;
    hence ge: "f ??a <= ??a"; by (rule Inter_greatest);
    txt {* We now use this inequality to prove the reverse one (!)
      and thereby complete the proof that @term{??a} is a fixpoint. *};
    with mono; have "f (f ??a) <= f ??a"; ..;
    hence "f ??a : ??H"; ..;
    hence "??a <= f ??a"; by (rule Inter_lower);
    also; note ge;
    finally (order_antisym); show "f ??a = ??a"; by (rule sym);
  qed;
qed;


end;
