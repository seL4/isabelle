(*  Title:      HOL/Real/HahnBanach/Subspace.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

theory Subspace = LinearSpace:;


section {* subspaces *};

constdefs
  is_subspace ::  "['a set, 'a set] => bool"
  "is_subspace U V ==  <0>:U  & U <= V 
     &  (ALL x:U. ALL y:U. ALL a. x [+] y : U                          
                       & a [*] x : U)";                            

lemma subspaceI [intro]: 
  "[| <0>:U; U <= V; ALL x:U. ALL y:U. (x [+] y : U); ALL x:U. ALL a. a [*] x : U |]
  \ ==> is_subspace U V";
  by (unfold is_subspace_def) simp;

lemma "is_subspace U V ==> U ~= {}";
  by (unfold is_subspace_def) force;

lemma zero_in_subspace [intro !!]: "is_subspace U V ==> <0>:U";
  by (unfold is_subspace_def) simp;;

lemma subspace_subset [intro !!]: "is_subspace U V ==> U <= V";
  by (unfold is_subspace_def) simp;

lemma subspace_subsetD [simp, intro!!]: "[| is_subspace U V; x:U |]==> x:V";
  by (unfold is_subspace_def) force;

lemma subspace_add_closed [simp, intro!!]: "[| is_subspace U V; x: U; y: U |] ==> x [+] y: U";
  by (unfold is_subspace_def) simp;

lemma subspace_mult_closed [simp, intro!!]: "[| is_subspace U V; x: U |] ==> a [*] x: U";
  by (unfold is_subspace_def) simp;

lemma subspace_diff_closed [simp, intro!!]: "[| is_subspace U V; x: U; y: U |] ==> x [-] y: U";
  by (unfold diff_def negate_def) simp;

lemma subspace_neg_closed [simp, intro!!]: "[| is_subspace U V; x: U |] ==> [-] x: U";
 by (unfold negate_def) simp;


theorem subspace_vs [intro!!]:
  "[| is_subspace U V; is_vectorspace V |] ==> is_vectorspace U";
proof -;
  assume "is_subspace U V" "is_vectorspace V";
  show ?thesis;
  proof; 
    show "<0>:U"; ..;
    show "ALL x:U. ALL a. a [*] x : U"; by (simp!);
    show "ALL x:U. ALL y:U. x [+] y : U"; by (simp!);
  qed (simp! add: vs_add_mult_distrib1 vs_add_mult_distrib2)+;
qed;

lemma subspace_refl [intro]: "is_vectorspace V ==> is_subspace V V";
proof; 
  assume "is_vectorspace V";
  show "<0> : V"; ..;
  show "V <= V"; ..;
  show "ALL x:V. ALL y:V. x [+] y : V"; by (simp!);
  show "ALL x:V. ALL a. a [*] x : V"; by (simp!);
qed;

lemma subspace_trans: "[| is_subspace U V; is_subspace V W |] ==> is_subspace U W";
proof; 
  assume "is_subspace U V" "is_subspace V W";
  show "<0> : U"; ..;

  have "U <= V"; ..;
  also; have "V <= W"; ..;
  finally; show "U <= W"; .;

  show "ALL x:U. ALL y:U. x [+] y : U"; 
  proof (intro ballI);
    fix x y; assume "x:U" "y:U";
    show "x [+] y : U"; by (simp!);
  qed;

  show "ALL x:U. ALL a. a [*] x : U";
  proof (intro ballI allI);
    fix x a; assume "x:U";
    show "a [*] x : U"; by (simp!);
  qed;
qed;


section {* linear closure *};

constdefs
  lin :: "'a => 'a set"
  "lin x == {y. ? a. y = a [*] x}";

lemma linD: "x : lin v = (? a::real. x = a [*] v)";
  by (unfold lin_def) force;

lemma linI [intro!!]: "a [*] x0 : lin x0";
  by (unfold lin_def) force;

lemma x_lin_x: "[| is_vectorspace V; x:V |] ==> x:lin x";
proof (unfold lin_def, intro CollectI exI);
  assume "is_vectorspace V" "x:V";
  show "x = 1r [*] x"; by (simp!);
qed;

lemma lin_subspace [intro!!]: "[| is_vectorspace V; x:V |] ==> is_subspace (lin x) V";
proof;
  assume "is_vectorspace V" "x:V";
  show "<0> : lin x"; 
  proof (unfold lin_def, intro CollectI exI);
    show "<0> = 0r [*] x"; by (simp!);
  qed;

  show "lin x <= V";
  proof (unfold lin_def, intro subsetI, elim CollectE exE); 
    fix xa a; assume "xa = a [*] x"; 
    show "xa:V"; by (simp!);
  qed;

  show "ALL x1 : lin x. ALL x2 : lin x. x1 [+] x2 : lin x"; 
  proof (intro ballI);
    fix x1 x2; assume "x1 : lin x" "x2 : lin x"; 
    thus "x1 [+] x2 : lin x";
    proof (unfold lin_def, elim CollectE exE, intro CollectI exI);
      fix a1 a2; assume "x1 = a1 [*] x" "x2 = a2 [*] x";
      show "x1 [+] x2 = (a1 + a2) [*] x"; by (simp! add: vs_add_mult_distrib2);
    qed;
  qed;

  show "ALL xa:lin x. ALL a. a [*] xa : lin x"; 
  proof (intro ballI allI);
    fix x1 a; assume "x1 : lin x"; 
    thus "a [*] x1 : lin x";
    proof (unfold lin_def, elim CollectE exE, intro CollectI exI);
      fix a1; assume "x1 = a1 [*] x";
      show "a [*] x1 = (a * a1) [*] x"; by (simp!);
    qed;
  qed; 
qed;


lemma lin_vs [intro!!]: "[| is_vectorspace V; x:V |] ==> is_vectorspace (lin x)";
proof (rule subspace_vs);
  assume "is_vectorspace V" "x:V";
  show "is_subspace (lin x) V"; ..;
qed;

section {* sum of two vectorspaces *};

constdefs 
  vectorspace_sum :: "['a set, 'a set] => 'a set"
  "vectorspace_sum U V == {x. ? u:U. ? v:V. x = u [+] v}";

lemma vs_sumD: "x:vectorspace_sum U V = (? u:U. ? v:V. x = u [+] v)";
  by (unfold vectorspace_sum_def) simp;

lemmas vs_sumE = vs_sumD [RS iffD1, elimify];

lemma vs_sumI [intro!!]: "[| x: U; y:V; (t::'a) = x [+] y |] ==> (t::'a) : vectorspace_sum U V";
  by (unfold vectorspace_sum_def, intro CollectI bexI); 

lemma subspace_vs_sum1 [intro!!]: 
  "[| is_vectorspace U; is_vectorspace V |] ==> is_subspace U (vectorspace_sum U V)";
proof; 
  assume "is_vectorspace U" "is_vectorspace V";
  show "<0> : U"; ..;
  show "U <= vectorspace_sum U V";
  proof (intro subsetI vs_sumI);
  fix x; assume "x:U";
    show "x = x [+] <0>"; by (simp!);
    show "<0> : V"; by (simp!);
  qed;
  show "ALL x:U. ALL y:U. x [+] y : U"; 
  proof (intro ballI);
    fix x y; assume "x:U" "y:U"; show "x [+] y : U"; by (simp!);
  qed;
  show "ALL x:U. ALL a. a [*] x : U"; 
  proof (intro ballI allI);
    fix x a; assume "x:U"; show "a [*] x : U"; by (simp!);
  qed;
qed;

lemma vs_sum_subspace [intro!!]: 
  "[| is_subspace U E; is_subspace V E; is_vectorspace E |] 
  ==> is_subspace (vectorspace_sum U V) E";
proof; 
  assume "is_subspace U E" "is_subspace V E" and e: "is_vectorspace E";

  show "<0> : vectorspace_sum U V";
  proof (intro vs_sumI);
    show "<0> : U"; ..;
    show "<0> : V"; ..;
    show "(<0>::'a) = <0> [+] <0>"; by (simp!);
  qed;
  
  show "vectorspace_sum U V <= E";
  proof (intro subsetI, elim vs_sumE bexE);
    fix x u v; assume "u : U" "v : V" "x = u [+] v";
    show "x:E"; by (simp!);
  qed;
  
  show "ALL x:vectorspace_sum U V. ALL y:vectorspace_sum U V. x [+] y : vectorspace_sum U V";
  proof (intro ballI);
    fix x y; assume "x:vectorspace_sum U V" "y:vectorspace_sum U V";
    thus "x [+] y : vectorspace_sum U V";
    proof (elim vs_sumE bexE, intro vs_sumI);
      fix ux vx uy vy; 
      assume "ux : U" "vx : V" "x = ux [+] vx" "uy : U" "vy : V" "y = uy [+] vy";
      show "x [+] y = (ux [+] uy) [+] (vx [+] vy)"; by (simp!);
    qed (simp!)+;
  qed;

  show "ALL x:vectorspace_sum U V. ALL a. a [*] x : vectorspace_sum U V";
  proof (intro ballI allI);
    fix x a; assume "x:vectorspace_sum U V";
    thus "a [*] x : vectorspace_sum U V";
    proof (elim vs_sumE bexE, intro vs_sumI);
      fix a x u v; assume "u : U" "v : V" "x = u [+] v";
      show "a [*] x = (a [*] u) [+] (a [*] v)"; by (simp! add: vs_add_mult_distrib1);
    qed (simp!)+;
  qed;
qed;

lemma vs_sum_vs [intro!!]: 
  "[| is_subspace U E; is_subspace V E; is_vectorspace E |] 
  ==> is_vectorspace (vectorspace_sum U V)";
proof (rule subspace_vs);
  assume "is_subspace U E" "is_subspace V E" "is_vectorspace E";
  show "is_subspace (vectorspace_sum U V) E"; ..;
qed;


section {* special case: direct sum of a vectorspace and a linear closure of a vector *};

lemma decomp: "[| is_vectorspace E; is_subspace U E; is_subspace V E; U Int V = {<0>}; 
  u1:U; u2:U; v1:V; v2:V; u1 [+] v1 = u2 [+] v2 |] 
  ==> u1 = u2 & v1 = v2"; 
proof; 
  assume "is_vectorspace E" "is_subspace U E" "is_subspace V E"  "U Int V = {<0>}" 
         "u1:U" "u2:U" "v1:V" "v2:V" "u1 [+] v1 = u2 [+] v2"; 
  have eq: "u1 [-] u2 = v2 [-] v1"; by (simp! add: vs_add_diff_swap);
  have u: "u1 [-] u2 : U"; by (simp!); with eq; have v': "v2 [-] v1 : U"; by simp; 
  have v: "v2 [-] v1 : V"; by (simp!); with eq; have u': "u1 [-] u2 : V"; by simp;
  
  show "u1 = u2";
  proof (rule vs_add_minus_eq);
    show "u1 [-] u2 = <0>"; by (rule Int_singletonD [OF _ u u']); 
  qed (rule);

  show "v1 = v2";
  proof (rule vs_add_minus_eq [RS sym]);
    show "v2 [-] v1 = <0>"; by (rule Int_singletonD [OF _ v' v]); 
  qed (rule);
qed;

lemma decomp4: "[| is_vectorspace E; is_subspace H E; y1 : H; y2 : H; x0 ~: H; x0 :E; 
  x0 ~= <0>; y1 [+] a1 [*] x0 = y2 [+] a2 [*] x0 |]
  ==> y1 = y2 & a1 = a2";
proof;
  assume "is_vectorspace E" and h: "is_subspace H E"
     and "y1 : H" "y2 : H" "x0 ~: H" "x0 : E" "x0 ~= <0>" 
         "y1 [+] a1 [*] x0 = y2 [+] a2 [*] x0";

  have c: "y1 = y2 & a1 [*] x0 = a2 [*] x0";
  proof (rule decomp); 
    show "a1 [*] x0 : lin x0"; ..; 
    show "a2 [*] x0 : lin x0"; ..;
    show "H Int (lin x0) = {<0>}"; 
    proof;
      show "H Int lin x0 <= {<0>}"; 
      proof (intro subsetI, elim IntE, rule singleton_iff[RS iffD2]);
        fix x; assume "x:H" "x:lin x0"; 
        thus "x = <0>";
        proof (unfold lin_def, elim CollectE exE);
          fix a; assume "x = a [*] x0";
          show ?thesis;
          proof (rule case_split [of "a = 0r"]);
            assume "a = 0r"; show ?thesis; by (simp!);
          next;
            assume "a ~= 0r"; 
            from h; have "(rinv a) [*] a [*] x0 : H"; by (rule subspace_mult_closed) (simp!);
            also; have "(rinv a) [*] a [*] x0 = x0"; by (simp!);
            finally; have "x0 : H"; .;
            thus ?thesis; by contradiction;
          qed;
       qed;
      qed;
      show "{<0>} <= H Int lin x0";
      proof (intro subsetI, elim singletonE, intro IntI, simp+);
        show "<0> : H"; ..;
        from lin_vs; show "<0> : lin x0"; ..;
      qed;
    qed;
    show "is_subspace (lin x0) E"; ..;
  qed;
  
  from c; show "y1 = y2"; by simp;
  
  show  "a1 = a2"; 
  proof (rule vs_mult_right_cancel [RS iffD1]);
    from c; show "a1 [*] x0 = a2 [*] x0"; by simp; 
  qed;
qed;

lemma decomp1: 
  "[| is_vectorspace E; is_subspace H E; t:H; x0~:H; x0:E; x0 ~= <0> |] 
  ==> (@ (y, a). t = y [+] a [*] x0 & y : H) = (t, 0r)";
proof (rule, unfold split_paired_all);
  assume "is_vectorspace E" "is_subspace H E" "t:H" "x0~:H" "x0:E" "x0 ~= <0>";
  have h: "is_vectorspace H"; ..;
  fix y a; presume t1: "t = y [+] a [*] x0" and "y : H";
  have "y = t & a = 0r"; 
    by (rule decomp4) (assumption | (simp!))+; 
  thus "(y, a) = (t, 0r)"; by (simp!);
qed (simp!)+;

lemma decomp3:
  "[| h0 = (%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H) 
                in (h y) + a * xi);
      x = y [+] a [*] x0; 
      is_vectorspace E; is_subspace H E; y:H; x0 ~: H; x0:E; x0 ~= <0> |]
  ==> h0 x = h y + a * xi";
proof -;  
  assume "h0 = (%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H) 
                    in (h y) + a * xi)"
         "x = y [+] a [*] x0"
         "is_vectorspace E" "is_subspace H E" "y:H" "x0 ~: H" "x0:E" "x0 ~= <0>";

  have "x : vectorspace_sum H (lin x0)"; 
    by (simp! add: vectorspace_sum_def lin_def, intro bexI exI conjI) force+;
  have "EX! xa. ((%(y, a). x = y [+] a [*] x0 & y:H) xa)"; 
  proof%%;
    show "EX xa. ((%(y, a). x = y [+] a [*] x0 & y:H) xa)";
      by (force!);
  next;
    fix xa ya;
    assume "(%(y,a). x = y [+] a [*] x0 & y : H) xa"
           "(%(y,a). x = y [+] a [*] x0 & y : H) ya";
    show "xa = ya"; ;
    proof -;
      show "fst xa = fst ya & snd xa = snd ya ==> xa = ya"; 
        by (rule Pair_fst_snd_eq [RS iffD2]);
      have x: "x = (fst xa) [+] (snd xa) [*] x0 & (fst xa) : H"; by (force!);
      have y: "x = (fst ya) [+] (snd ya) [*] x0 & (fst ya) : H"; by (force!);
      from x y; show "fst xa = fst ya & snd xa = snd ya"; by (elim conjE) (rule decomp4, (simp!)+);
    qed;
  qed;
  hence eq: "(@ (y, a). (x = y [+] a [*] x0 & y:H)) = (y, a)"; by (rule select1_equality) (force!);
  thus "h0 x = h y + a * xi"; by (simp! add: Let_def);
qed;

end;


