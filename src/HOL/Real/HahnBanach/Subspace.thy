
theory Subspace = LinearSpace:;


section {* subspaces *};

constdefs
  is_subspace ::  "['a set, 'a set] => bool"
  "is_subspace U V ==  <0>:U  & U <= V 
     &  (ALL x:U. ALL y:U. ALL a. x [+] y : U                          
                       & a [*] x : U)";                            

lemma subspace_I: 
  "[| <0>:U; U <= V; ALL x:U. ALL y:U. (x [+] y : U); ALL x:U. ALL a. a [*] x : U |]
  \ ==> is_subspace U V";
  by (unfold is_subspace_def) blast;

lemma "is_subspace U V ==> U ~= {}";
  by (unfold is_subspace_def) force;

lemma zero_in_subspace: "is_subspace U V ==> <0>:U";
  by (unfold is_subspace_def) force;

lemma subspace_subset: "is_subspace U V ==> U <= V";
  by (unfold is_subspace_def) fast;

lemma subspace_subset2 [simp]: "[| is_subspace U V; x:U |]==> x:V";
  by (unfold is_subspace_def) fast;

lemma subspace_add_closed [simp]: "[| is_subspace U V; x: U; y: U |] ==> x [+] y: U";
  by (unfold is_subspace_def) asm_simp;

lemma subspace_mult_closed [simp]: "[| is_subspace U V; x: U |] ==> a [*] x: U";
  by (unfold is_subspace_def) asm_simp;

lemma subspace_diff_closed [simp]: "[| is_subspace U V; x: U; y: U |] ==> x [-] y: U";
  by (unfold diff_def negate_def) asm_simp;

lemma subspace_neg_closed [simp]: "[| is_subspace U V; x: U |] ==> [-] x: U";
 by (unfold negate_def) asm_simp;

theorem subspace_vs [intro!!]:
  "[| is_subspace U V; is_vectorspace V |] ==> is_vectorspace U";
proof -;
  presume "U <= V";
  assume "is_vectorspace V";
  assume "is_subspace U V";
  show ?thesis;
  proof (rule vs_I);
    show "<0>:U"; by (rule zero_in_subspace);
    show "ALL x:U. ALL a. a [*] x : U"; by asm_simp;
    show "ALL x:U. ALL y:U. x [+] y : U"; by asm_simp;
  qed (asm_simp add: vs_add_mult_distrib1 vs_add_mult_distrib2)+;
next;
  assume "is_subspace U V";
  show "U <= V"; by (rule subspace_subset);
qed;

lemma subspace_refl: "is_vectorspace V ==> is_subspace V V";
proof (unfold is_subspace_def, intro conjI); 
  assume "is_vectorspace V";
  show "<0> : V"; by (rule zero_in_vs [of V], assumption);
  show "V <= V"; by (simp);
  show "ALL x::'a:V. ALL y::'a:V. ALL a::real. x [+] y : V & a [*] x : V"; by (asm_simp);
qed;

lemma subspace_trans: "[| is_subspace U V; is_subspace V W |] ==> is_subspace U W";
proof (rule subspace_I); 
  assume "is_subspace U V" "is_subspace V W";
  show "<0> : U"; by (rule zero_in_subspace);;
  from subspace_subset [of U] subspace_subset [of V]; show uw: "U <= W"; by force;
  show "ALL x:U. ALL y:U. x [+] y : U"; 
  proof (intro ballI);
    fix x y; assume "x:U" "y:U";
    show "x [+] y : U"; by (rule subspace_add_closed);
  qed;
  show "ALL x:U. ALL a. a [*] x : U";
  proof (intro ballI allI);
    fix x a; assume "x:U";
    show "a [*] x : U"; by (rule subspace_mult_closed);
  qed;
qed;


section {* linear closure *};

constdefs
  lin :: "'a => 'a set"
  "lin x == {y. ? a. y = a [*] x}";

lemma linD: "x : lin v = (? a::real. x = a [*] v)";
  by (unfold lin_def) fast;

lemma x_lin_x: "[| is_vectorspace V; x:V |] ==> x:lin x";
proof (unfold lin_def, intro CollectI exI);
  assume "is_vectorspace V" "x:V";
  show "x = 1r [*] x"; by (asm_simp);
qed;

lemma lin_subspace: "[| is_vectorspace V; x:V |] ==> is_subspace (lin x) V";
proof (rule subspace_I);
  assume "is_vectorspace V" "x:V";
  show "<0> : lin x"; 
  proof (unfold lin_def, intro CollectI exI);
    show "<0> = 0r [*] x"; by asm_simp;
  qed;
  show "lin x <= V";
  proof (unfold lin_def, intro subsetI, elim CollectD [elimify] exE); 
    fix xa a; assume "xa = a [*] x"; show "xa:V"; by asm_simp;
  qed;
  show "ALL x1 : lin x. ALL x2 : lin x. x1 [+] x2 : lin x"; 
  proof (intro ballI);
    fix x1 x2; assume "x1 : lin x" "x2 : lin x"; show "x1 [+] x2 : lin x";
    proof (unfold lin_def, elim CollectD [elimify] exE, intro CollectI exI);
      fix a1 a2; assume "x1 = a1 [*] x" "x2 = a2 [*] x";
      show "x1 [+] x2 = (a1 + a2) [*] x"; by (asm_simp add: vs_add_mult_distrib2);
    qed;
  qed;
  show "ALL xa:lin x. ALL a. a [*] xa : lin x"; 
  proof (intro ballI allI);
    fix x1 a; assume "x1 : lin x"; show "a [*] x1 : lin x";
    proof (unfold lin_def, elim CollectD [elimify] exE, intro CollectI exI);
      fix a1; assume "x1 = a1 [*] x";
      show "a [*] x1 = (a * a1) [*] x"; by asm_simp;
    qed;
  qed; 
qed;


lemma lin_vs [intro!!]: "[| is_vectorspace V; x:V |] ==> is_vectorspace (lin x)";
proof (rule subspace_vs);
  assume "is_vectorspace V" "x:V";
  show "is_subspace (lin x) V"; by (rule lin_subspace);
qed;

section {* sum of two vectorspaces *};

constdefs 
  vectorspace_sum :: "['a set, 'a set] => 'a set"
  "vectorspace_sum U V == {x. ? u:U. ? v:V. x = u [+] v}";

lemma vs_sumD: "x:vectorspace_sum U V = (? u:U. ? v:V. x = u [+] v)";
  by (unfold vectorspace_sum_def) fast;

lemma vs_sum_I: "[| x: U; y:V; (t::'a) = x [+] y |] ==> (t::'a) : vectorspace_sum U V";
  by (unfold vectorspace_sum_def, intro CollectI bexI); 

lemma subspace_vs_sum1 [intro!!]: 
  "[| is_vectorspace U; is_vectorspace V |] ==> is_subspace U (vectorspace_sum U V)";
proof (rule subspace_I);
  assume "is_vectorspace U" "is_vectorspace V";
  show "<0> : U"; by (rule zero_in_vs);
  show "U <= vectorspace_sum U V";
  proof (intro subsetI vs_sum_I);
  fix x; assume "x:U";
    show "x = x [+] <0>"; by asm_simp;
    show "<0> : V"; by asm_simp;
  qed;
  show "ALL x:U. ALL y:U. x [+] y : U"; 
  proof (intro ballI);
    fix x y; assume "x:U" "y:U"; show "x [+] y : U"; by asm_simp;
  qed;
  show "ALL x:U. ALL a. a [*] x : U"; 
  proof (intro ballI allI);
    fix x a; assume "x:U"; show "a [*] x : U"; by asm_simp;
  qed;
qed;

lemma vs_sum_subspace: 
  "[| is_subspace U E; is_subspace V E; is_vectorspace E |] ==> is_subspace (vectorspace_sum U V) E";
proof (rule subspace_I);
  assume u: "is_subspace U E" and v: "is_subspace V E" and e: "is_vectorspace E";

  show "<0> : vectorspace_sum U V";
  by (intro vs_sum_I, rule vs_add_zero_left [RS sym], 
      rule zero_in_subspace, rule zero_in_subspace, rule zero_in_vs); 

  show "vectorspace_sum U V <= E";
  proof (intro subsetI, elim vs_sumD [RS iffD1, elimify] bexE);
    fix x u v; assume "u : U" "v : V" "x = u [+] v";
    show "x:E"; by (asm_simp);
  qed;
  
  show "ALL x:vectorspace_sum U V. ALL y:vectorspace_sum U V. x [+] y : vectorspace_sum U V";
  proof (intro ballI, elim vs_sumD [RS iffD1, elimify] bexE, intro vs_sum_I);
    fix x y ux vx uy vy; assume "ux : U" "vx : V" "x = ux [+] vx" "uy : U" "vy : V" "y = uy [+] vy";
    show "x [+] y = (ux [+] uy) [+] (vx [+] vy)"; by asm_simp;
  qed asm_simp+;

  show "ALL x:vectorspace_sum U V. ALL a. a [*] x : vectorspace_sum U V";
  proof (intro ballI allI, elim vs_sumD [RS iffD1, elimify] bexE, intro vs_sum_I);
    fix a x u v; assume "u : U" "v : V" "x = u [+] v";
    show "a [*] x = (a [*] u) [+] (a [*] v)"; by (asm_simp add: vs_add_mult_distrib1 [OF e]);
  qed asm_simp+;
qed;

lemma vs_sum_vs: 
  "[| is_subspace U E; is_subspace V E; is_vectorspace E |] ==> is_vectorspace (vectorspace_sum U V)";
  by (rule subspace_vs [OF vs_sum_subspace]);


section {* special case: direct sum of a vectorspace and a linear closure of a vector *};


lemma lemma4: "[| is_vectorspace E; is_subspace H E; y1 : H; y2 : H; x0 ~: H; x0 :E; 
  x0 ~= <0>; y1 [+] a1 [*] x0 = y2 [+] a2 [*] x0 |]
  ==> y1 = y2 & a1 = a2";
proof;
  assume "is_vectorspace E" "is_subspace H E"
         "y1 : H" "y2 : H" "x0 ~: H" "x0 : E" "x0 ~= <0>" 
         "y1 [+] a1 [*] x0 = y2 [+] a2 [*] x0";
  have h: "is_vectorspace H"; by (rule subspace_vs);
  have "y1 [-] y2 = a2 [*] x0 [-] a1 [*] x0"; 
    by (rule vs_add_diff_swap) asm_simp+;
  also; have "... = (a2 - a1) [*] x0";
    by (rule vs_diff_mult_distrib2 [RS sym]);
  finally; have eq: "y1 [-] y2 = (a2 - a1) [*] x0"; .;

  have y: "y1 [-] y2 : H"; by asm_simp;
  have x: "(a2 - a1) [*] x0 : lin x0"; by (asm_simp add: lin_def) force; 
  from y; have y': "y1 [-] y2 : lin x0"; by (simp only: eq x);
  from x; have x': "(a2 - a1) [*] x0 : H"; by (simp only: eq [RS sym] y);

  have int: "H Int (lin x0) = {<0>}"; 
  proof;
    show "H Int lin x0 <= {<0>}"; 
    proof (intro subsetI, unfold lin_def, elim IntE CollectD[elimify] exE,
      rule singleton_iff[RS iffD2]);
      fix x a; assume "x : H" and ax0: "x = a [*] x0";
      show "x = <0>";
      proof (rule case [of "a=0r"]);
        assume "a = 0r"; show ?thesis; by asm_simp;
      next;
        assume "a ~= 0r"; 
        have "(rinv a) [*] a [*] x0 : H"; 
          by (rule vs_mult_closed [OF h]) asm_simp;
        also; have "(rinv a) [*] a [*] x0 = x0"; by asm_simp;
        finally; have "x0 : H"; .;
        thus ?thesis; by contradiction;
      qed;
    qed;
    show "{<0>} <= H Int lin x0"; 
    proof (intro subsetI, elim singletonD[elimify], intro IntI, asm_simp+);
      show "<0> : H"; by (rule zero_in_vs [OF h]);
      show "<0> : lin x0"; by (rule zero_in_vs [OF lin_vs]);
    qed;
  qed;

  from h; show "y1 = y2";
  proof (rule vs_add_minus_eq);
    show "y1 [-] y2 = <0>";
      by (rule Int_singeltonD [OF int y y']); 
  qed;
 
  show "a1 = a2";
  proof (rule real_add_minus_eq [RS sym]);
    show "a2 - a1 = 0r";
    proof (rule vs_mult_zero_uniq);
      show "(a2 - a1) [*] x0 = <0>";  by (rule Int_singeltonD [OF int x' x]);
    qed;
  qed;
qed;

 
lemma lemma1: 
  "[| is_vectorspace E; is_subspace H E; t:H; x0~:H; x0:E; x0 ~= <0> |] 
  ==> (@ (y, a). t = y [+] a [*] x0 & y : H) = (t, 0r)";
proof (rule, unfold split_paired_all);
  assume "is_vectorspace E" "is_subspace H E" "t:H" "x0~:H" "x0:E" "x0 ~= <0>";
  have h: "is_vectorspace H"; by (rule subspace_vs);
  fix y a; presume t1: "t = y [+] a [*] x0" and "y : H";
  have "y = t & a = 0r"; 
    by (rule lemma4) (assumption+, asm_simp); 
  thus "(y, a) = (t, 0r)"; by asm_simp;
qed asm_simp+;


lemma lemma3: "!! x0 h xi x y a H. [| h0 = (%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H) 
                            in (h y) + a * xi);
                  x = y [+] a [*] x0; 
                  is_vectorspace E; is_subspace H E; y:H; x0 ~: H; x0:E; x0 ~= <0> |]
  ==> h0 x = h y + a * xi";
proof -;  
  fix x0 h xi x y a H;
  assume "h0 = (%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H) 
                            in (h y) + a * xi)";
  assume "x = y [+] a [*] x0";
  assume "is_vectorspace E" "is_subspace H E" "y:H" "x0 ~: H" "x0:E" "x0 ~= <0>";

  have "x : vectorspace_sum H (lin x0)"; 
    by (asm_simp add: vectorspace_sum_def lin_def, intro bexI exI conjI) force+;
  have "EX! xa. ((%(y, a). x = y [+] a [*] x0 & y:H) xa)"; 
  proof;
    show "EX xa. ((%(y, a). x = y [+] a [*] x0 & y:H) xa)"; 
      by (asm_simp, rule exI, force);
  next;
    fix xa ya;
    assume "(%(y,a). x = y [+] a [*] x0 & y : H) xa"
           "(%(y,a). x = y [+] a [*] x0 & y : H) ya";
    show "xa = ya"; ;
    proof -;
      show "fst xa = fst ya & snd xa = snd ya ==> xa = ya"; 
        by(rule Pair_fst_snd_eq [RS iffD2]);
      have x: "x = (fst xa) [+] (snd xa) [*] x0 & (fst xa) : H"; by force;
      have y: "x = (fst ya) [+] (snd ya) [*] x0 & (fst ya) : H"; by force;
      from x y; show "fst xa = fst ya & snd xa = snd ya"; 
        by (elim conjE) (rule lemma4, asm_simp+);
    qed;
  qed;
  hence eq: "(@ (y, a). (x = y [+] a [*] x0 & y:H)) = (y, a)"; 
    by (rule select1_equality, force);
  thus "h0 x = h y + a * xi"; 
    by (asm_simp add: Let_def);
qed;  


end;


