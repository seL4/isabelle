(*  Title:      HOL/Isar_examples/MultisetOrder.thy
    ID:         $Id$
    Author:     Markus Wenzel

Wellfoundedness proof for the multiset order.  Based on
HOL/induct/Multiset by Tobias Nipkow.
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
    proof (rule accI); thm accI; thm accI [where ?a = "M0 + {#a#}" and ?r = "??R"];
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
	fix K; assume K: "ALL b. elem K b --> (b, a) : r" (is ??K) and N: "N = M0 + K";

	have "??K --> M0 + K : ??W" (is "??P K");
	proof (rule multiset_induct [of _ K]); thm multiset_induct [of _ K];
	  show "??P {#}"; by asm_simp;   (* FIXME *)
	  fix K x; assume hyp: "??P K";
	  show "??P (K + {#x#})";
	  proof -;
	    apply (simp_tac add: union_assoc [RS sym]);
	    apply blast;        (* FIXME *)
	  qed;
	qed;
	hence "M0 + K : ??W"; ..;
	thus "N : ??W"; by (simp only: N);
      qed;
    qed;
  }}; note subproof = this;


  assume wf: "wf r";
  fix M;
  show "M : ??W";
  proof (rule multiset_induct [of _ M]); thm multiset_induct [of _ M];
    show "{#} : ??W";
    proof (rule accI);
      fix b; assume "(b, {#}) : ??R";
      with not_less_empty; show "b : ??W"; by contradiction;
    qed;

    fix a;
    from wf; have "ALL M:??W. M + {#a#} : ??W";
    proof (rule wf_induct [of r]);  thm wf_induct [of r];
      fix a; assume wf_hyp: "ALL b. (b, a) : r --> (ALL M:??W. M + {#b#} : ??W)";
      show "ALL M:??W. M + {#a#} : ??W";
      proof;
	fix M; assume "M : ??W";
	thus "M + {#a#} : ??W"; by (rule acc_induct) (rule subproof, finish);   (* FIXME elim finish *)
      qed;
    qed;
    thus "!!M. M:??W ==> M + {#a#} : ??W"; by (rule bspec);    (* FIXME !? *)
  qed;
qed;


theorem wf_mult1: "wf r ==> wf (mult1 r)";
  by (rule acc_wfI, rule all_accessible);

theorem wf_mult: "wf r ==> wf (mult r)";
  by (unfold mult_def, rule wf_trancl, rule wf_mult1);


end;
