(*  Title:      HOL/Isar_examples/MultisetOrder.thy
    ID:         $Id$
    Author:     Markus Wenzel

Wellfoundedness proof for the multiset order.

Original tactic script by Tobias Nipkow (see also
HOL/Induct/Multiset).  Pen-and-paper proof by Wilfried Buchholz.
*)


theory MultisetOrder = Multiset:;


lemma all_accessible: "wf r ==> ALL M. M : acc (mult1 r)";
proof;
  let ??R = "mult1 r";
  let ??W = "acc ??R";


  {{;
    fix M M0 a;
    assume wf_hyp: "ALL b. (b, a) : r --> (ALL M:??W. M + {#b#} : ??W)"
      and M0: "M0 : ??W"
      and acc_hyp: "ALL M. (M, M0) : ??R --> M + {#a#} : ??W";
    have "M0 + {#a#} : ??W";
    proof (rule accI [of "M0 + {#a#}"]);
      fix N; assume "(N, M0 + {#a#}) : ??R";
      hence "((EX M. (M, M0) : ??R & N = M + {#a#}) |
             (EX K. (ALL b. elem K b --> (b, a) : r) & N = M0 + K))";
	by (simp only: less_add_conv);
      thus "N : ??W";
      proof (elim exE disjE conjE);
	fix M; assume "(M, M0) : ??R" and N: "N = M + {#a#}";
	from acc_hyp; have "(M, M0) : ??R --> M + {#a#} : ??W"; ..;
	hence "M + {#a#} : ??W"; ..;
	thus "N : ??W"; by (simp only: N);
      next;
	fix K; assume "ALL b. elem K b --> (b, a) : r" (is "??A a K")
	  and N: "N = M0 + K";

	have "??A a K --> M0 + K : ??W" (is "??P K");
	proof (rule multiset_induct [of _ K]);
	  from M0; have "M0 + {#} : ??W"; by simp;
	  thus "??P {#}"; ..;

	  fix K x; assume hyp: "??P K";
	  show "??P (K + {#x#})";
	  proof;
	    assume a: "??A a (K + {#x#})";
	    hence "(x, a) : r"; by simp;
	    with wf_hyp [RS spec]; have b: "ALL M:??W. M + {#x#} : ??W"; ..;

	    from a hyp; have "M0 + K : ??W"; by simp;
	    with b; have "(M0 + K) + {#x#} : ??W"; ..;
	    thus "M0 + (K + {#x#}) : ??W"; by (simp only: union_assoc);
	  qed;
	qed;
	hence "M0 + K : ??W"; ..;
	thus "N : ??W"; by (simp only: N);
      qed;
    qed;
  }}; note tedious_reasoning = this;


  assume wf: "wf r";
  fix M;
  show "M : ??W";
  proof (rule multiset_induct [of _ M]);
    show "{#} : ??W";
    proof (rule accI);
      fix b; assume "(b, {#}) : ??R";
      with not_less_empty; show "b : ??W"; by contradiction;
    qed;

    fix M a; assume "M : ??W";
    from wf; have "ALL M:??W. M + {#a#} : ??W";
    proof (rule wf_induct [of r]);
      fix a; assume "ALL b. (b, a) : r --> (ALL M:??W. M + {#b#} : ??W)";
      show "ALL M:??W. M + {#a#} : ??W";
      proof;
	fix M; assume "M : ??W";
	thus "M + {#a#} : ??W"; by (rule acc_induct) (rule tedious_reasoning);
      qed;
    qed;
    thus "M + {#a#} : ??W"; ..;
  qed;
qed;


theorem wf_mult1: "wf r ==> wf (mult1 r)";
  by (rule acc_wfI, rule all_accessible);

theorem wf_mult: "wf r ==> wf (mult r)";
  by (unfold mult_def, rule wf_trancl, rule wf_mult1);


end;
