(*  Title:      HOL/Isar_examples/KnasterTarski.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Typical textbook proof example.
*)


theory KnasterTarski = Main:;

text {*
 According to the book ``Introduction to Lattices and Order'' (by
 B. A. Davey and H. A. Priestley, CUP 1990), the Knaster-Tarski
 fixpoint theorem is as follows (pages 93--94).  Note that we have
 dualized their argument, and tuned the notation a little bit.

 \paragraph{The Knaster-Tarski Fixpoint Theorem.}  Let $L$ be a
 complete lattice and $f \colon L \to L$ an order-preserving map.
 Then $\bigwedge \{ x \in L \mid f(x) \le x \}$ is a fixpoint of $f$.

 \textbf{Proof.} Let $H = \{x \in L \mid f(x) \le x\}$ and $a =
 \bigwedge H$.  For all $x \in H$ we have $a \le x$, so $f(a) \le f(x)
 \le x$.  Thus $f(a)$ is a lower bound of $H$, whence $f(a) \le a$.
 We now use this inequality to prove the reverse one (!) and thereby
 complete the proof that $a$ is a fixpoint.  Since $f$ is
 order-preserving, $f(f(a)) \le f(a)$.  This says $f(a) \in H$, so $a
 \le f(a)$.
*};

text {*
 Our proof below closely follows this presentation.  Virtually all of
 the prose narration has been rephrased in terms of formal Isar
 language elements.  Just as many textbook-style proofs, there is a
 strong bias towards forward reasoning, and little hierarchical
 structure.
*};

theorem KnasterTarski: "mono f ==> EX a::'a set. f a = a";
proof;
  let ??H = "{u. f u <= u}";
  let ??a = "Inter ??H";

  assume mono: "mono f";
  show "f ??a = ??a";
  proof -;
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
