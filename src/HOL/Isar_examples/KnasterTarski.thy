(*  Title:      HOL/Isar_examples/KnasterTarski.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Typical textbook proof example.
*)


theory KnasterTarski = Main:;


text {*
 The proof of Knaster-Tarski below closely follows the presentation in
 'Introduction to Lattices' and Order by Davey/Priestley, pages
 93--94.  All of their narration has been rephrased in terms of formal
 Isar language elements.  Just as many textbook-style proofs, there is
 a strong bias towards forward reasoning, and little hierarchical
 structure.
*};

theorem KnasterTarski: "mono f ==> EX a::'a set. f a = a";
proof;
  let ??H = "{u. f u <= u}";
  let ??a = "Inter ??H";

  assume mono: "mono f";
  show "f ??a = ??a";
  proof same;
    {{;
      fix x;
      assume mem: "x : ??H";
      hence "??a <= x"; by (rule Inter_lower);
      with mono; have "f ??a <= f x"; ..;
      also; from mem; have "... <= x"; ..;
      finally; have "f ??a <= x"; .;
    }};
    hence ge: "f ??a <= ??a"; by (rule Inter_greatest);
    {{;
      also; presume "... <= f ??a";
      finally (order_antisym); show ??thesis; .;
    }};
    from mono ge; have "f (f ??a) <= f ??a"; ..;
    hence "f ??a : ??H"; ..;
    thus "??a <= f ??a"; by (rule Inter_lower);
  qed;
qed;


end;
