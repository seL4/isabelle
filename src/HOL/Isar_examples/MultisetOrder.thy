(*  Title:      HOL/Isar_examples/MultisetOrder.thy
    ID:         $Id$
    Author:     Markus Wenzel

Wellfoundedness proof for the multiset order.

Original tactic script by Tobias Nipkow (see also
HOL/Induct/Multiset).  Pen-and-paper proof by Wilfried Buchholz.
*)


theory MultisetOrder = Multiset:;


lemma less_add: "(N, M0 + {#a#}) : mult1 r ==>
    (EX M. (M, M0) : mult1 r & N = M + {#a#}) |
    (EX K. (ALL b. elem K b --> (b, a) : r) & N = M0 + K)"
  (concl is "?case1 (mult1 r) | ?case2");
proof (unfold mult1_def);
  let ?r = "%K a. ALL b. elem K b --> (b, a) : r";
  let ?R = "%N M. EX a M0 K. M = M0 + {#a#} & N = M0 + K & ?r K a";
  let ?case1 = "?case1 {(N, M). ?R N M}";

  assume "(N, M0 + {#a#}) : {(N, M). ?R N M}";
  hence "EX a' M0' K. M0 + {#a#} = M0' + {#a'#} & N = M0' + K & ?r K a'"; by simp;
  thus "?case1 | ?case2";
  proof (elim exE conjE);
    fix a' M0' K; assume N: "N = M0' + K" and r: "?r K a'";
    assume "M0 + {#a#} = M0' + {#a'#}";
    hence "M0 = M0' & a = a' | (EX K'. M0 = K' + {#a'#} & M0' = K' + {#a#})";
      by (simp only: add_eq_conv_ex);
    thus ?thesis;
    proof (elim disjE conjE exE);
      assume "M0 = M0'" "a = a'";
      with N r; have "?r K a & N = M0 + K"; by simp;
      hence ?case2; ..; thus ?thesis; ..;
    next;
      fix K';
      assume "M0' = K' + {#a#}";
      with N; have n: "N = K' + K + {#a#}"; by (simp add: union_ac);

      assume "M0 = K' + {#a'#}";
      with r; have "?R (K' + K) M0"; by simp blast;
      with n; have ?case1; by simp; thus ?thesis; ..;
    qed;
  qed;
qed;


lemma all_accessible: "wf r ==> ALL M. M : acc (mult1 r)";
proof;
  let ?R = "mult1 r";
  let ?W = "acc ?R";


  {{;
    fix M M0 a;
    assume wf_hyp: "ALL b. (b, a) : r --> (ALL M:?W. M + {#b#} : ?W)"
      and M0: "M0 : ?W"
      and acc_hyp: "ALL M. (M, M0) : ?R --> M + {#a#} : ?W";
    have "M0 + {#a#} : ?W";
    proof (rule accI [of "M0 + {#a#}"]);
      fix N; assume "(N, M0 + {#a#}) : ?R";
      hence "((EX M. (M, M0) : ?R & N = M + {#a#}) |
             (EX K. (ALL b. elem K b --> (b, a) : r) & N = M0 + K))";
	by (rule less_add);
      thus "N : ?W";
      proof (elim exE disjE conjE);
	fix M; assume "(M, M0) : ?R" and N: "N = M + {#a#}";
	from acc_hyp; have "(M, M0) : ?R --> M + {#a#} : ?W"; ..;
	hence "M + {#a#} : ?W"; ..;
	thus "N : ?W"; by (simp only: N);
      next;
	fix K;
	assume N: "N = M0 + K";
	assume "ALL b. elem K b --> (b, a) : r";
	have "?this --> M0 + K : ?W" (is "?P K");
	proof (induct K rule: multiset_induct);
	  from M0; have "M0 + {#} : ?W"; by simp;
	  thus "?P {#}"; ..;

	  fix K x; assume hyp: "?P K";
	  show "?P (K + {#x#})";
	  proof;
	    assume a: "ALL b. elem (K + {#x#}) b --> (b, a) : r";
	    hence "(x, a) : r"; by simp;
	    with wf_hyp [RS spec]; have b: "ALL M:?W. M + {#x#} : ?W"; ..;

	    from a hyp; have "M0 + K : ?W"; by simp;
	    with b; have "(M0 + K) + {#x#} : ?W"; ..;
	    thus "M0 + (K + {#x#}) : ?W"; by (simp only: union_assoc);
	  qed;
	qed;
	hence "M0 + K : ?W"; ..;
	thus "N : ?W"; by (simp only: N);
      qed;
    qed;
  }}; note tedious_reasoning = this;


  assume wf: "wf r";
  fix M;
  show "M : ?W";
  proof (induct M rule: multiset_induct);
    show "{#} : ?W";
    proof (rule accI);
      fix b; assume "(b, {#}) : ?R";
      with not_less_empty; show "b : ?W"; by contradiction;
    qed;

    fix M a; assume "M : ?W";
    from wf; have "ALL M:?W. M + {#a#} : ?W";
    proof (rule wf_induct [of r]);
      fix a; assume "ALL b. (b, a) : r --> (ALL M:?W. M + {#b#} : ?W)";
      show "ALL M:?W. M + {#a#} : ?W";
      proof;
	fix M; assume "M : ?W";
	thus "M + {#a#} : ?W"; by (rule acc_induct) (rule tedious_reasoning);
      qed;
    qed;
    thus "M + {#a#} : ?W"; ..;
  qed;
qed;


theorem wf_mult1: "wf r ==> wf (mult1 r)";
  by (rule acc_wfI, rule all_accessible);

theorem wf_mult: "wf r ==> wf (mult r)";
  by (unfold mult_def, rule wf_trancl, rule wf_mult1);


end;
