(*  Title:      ZF/AC/AC0_AC1.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

AC0 is equivalent to AC1
AC0 comes from Suppes, AC1 from Rubin & Rubin
*)

Goal "0\\<notin>A ==> A \\<subseteq> Pow(Union(A))-{0}";
by (Fast_tac 1);
qed "subset_Pow_Union";

Goal "[| f:(\\<Pi>X \\<in> A. X); D \\<subseteq> A |] ==> \\<exists>g. g:(\\<Pi>X \\<in> D. X)";
by (fast_tac (claset() addSIs [restrict_type, apply_type]) 1);
val lemma1 = result();

Goalw AC_defs "AC0 ==> AC1"; 
by (fast_tac (FOL_cs addSEs [lemma1, subset_Pow_Union]) 1);
qed "AC0_AC1";

Goalw AC_defs "AC1 ==> AC0";
by (Deepen_tac 0 1);
(*Large search space.  Faster proof by
  by (fast_tac (claset() addSIs [notI, singletonI] addSEs [notE, DiffE]) 1);
*)
qed "AC1_AC0";
