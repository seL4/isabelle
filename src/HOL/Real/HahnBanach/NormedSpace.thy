
theory NormedSpace =  Subspace:;


section {* normed vector spaces *};

subsection {* quasinorm *};

constdefs
  is_quasinorm :: "['a set,  'a => real] => bool"
  "is_quasinorm V norm == ALL x: V. ALL y:V. ALL a. 
        0r <= norm x 
      & norm (a [*] x) = (rabs a) * (norm x)
      & norm (x [+] y) <= norm x + norm y";

lemma is_quasinormI[intro]: 
  "[| !! x y a. [| x:V; y:V|] ==>  0r <= norm x;
      !! x a. x:V ==> norm (a [*] x) = (rabs a) * (norm x);
      !! x y. [|x:V; y:V |] ==> norm (x [+] y) <= norm x + norm y |] 
    ==> is_quasinorm V norm";
  by (unfold is_quasinorm_def, force);

lemma quasinorm_ge_zero:
  "[|is_quasinorm V norm; x:V |] ==> 0r <= norm x";
  by (unfold is_quasinorm_def, force);

lemma quasinorm_mult_distrib: 
  "[|is_quasinorm V norm; x:V |] ==> norm (a [*] x) = (rabs a) * (norm x)";
  by (unfold is_quasinorm_def, force);

lemma quasinorm_triangle_ineq: 
  "[|is_quasinorm V norm; x:V; y:V |] ==> norm (x [+] y) <= norm x + norm y";
  by (unfold is_quasinorm_def, force);

lemma quasinorm_diff_triangle_ineq: 
  "[|is_quasinorm V norm; x:V; y:V; is_vectorspace V |] ==> norm (x [-] y) <= norm x + norm y";
proof -;
  assume "is_quasinorm V norm" "x:V" "y:V" "is_vectorspace V";
  have "norm (x [-] y) = norm (x [+] - 1r [*] y)";  by (simp add: diff_def negate_def);
  also; have "... <= norm x + norm  (- 1r [*] y)"; by (rule quasinorm_triangle_ineq, asm_simp+);
  also; have "norm (- 1r [*] y) = rabs (- 1r) * norm y"; by (rule quasinorm_mult_distrib);
  also; have "rabs (- 1r) = 1r"; by (rule rabs_minus_one);
  finally; show "norm (x [-] y) <= norm x + norm y"; by simp;
qed;

lemma quasinorm_minus: 
  "[|is_quasinorm V norm; x:V; is_vectorspace V |] ==> norm ([-] x) = norm x";
proof -;
  assume "is_quasinorm V norm" "x:V" "is_vectorspace V";
  have "norm ([-] x) = norm (-1r [*] x)"; by (unfold negate_def) force;
  also; have "... = rabs (-1r) * norm x"; by (rule quasinorm_mult_distrib);
  also; have "rabs (- 1r) = 1r"; by (rule rabs_minus_one);
  finally; show "norm ([-] x) = norm x"; by simp;
qed;


subsection {* norm *};

constdefs
  is_norm :: "['a set, 'a => real] => bool"
  "is_norm V norm == ALL x: V.  is_quasinorm V norm 
      & (norm x = 0r) = (x = <0>)";

lemma is_norm_I: "ALL x: V.  is_quasinorm V norm  & (norm x = 0r) = (x = <0>) ==> is_norm V norm";
  by (unfold is_norm_def, force);

lemma norm_is_quasinorm: "[| is_norm V norm; x:V |] ==> is_quasinorm V norm";
  by (unfold is_norm_def, force);

lemma norm_zero_iff: "[| is_norm V norm; x:V |] ==> (norm x = 0r) = (x = <0>)";
  by (unfold is_norm_def, force);

lemma norm_ge_zero:
  "[|is_norm V norm; x:V |] ==> 0r <= norm x";
  by (unfold is_norm_def, unfold is_quasinorm_def, force);


subsection {* normed vector space *};

constdefs
  is_normed_vectorspace :: "['a set, 'a => real] => bool"
  "is_normed_vectorspace V norm ==
      is_vectorspace V &
      is_norm V norm";

lemma normed_vsI: "[| is_vectorspace V; is_norm V norm |] ==> is_normed_vectorspace V norm";
  by (unfold is_normed_vectorspace_def, intro conjI);

lemma normed_vs_vs: "is_normed_vectorspace V norm ==> is_vectorspace V";
  by (unfold is_normed_vectorspace_def, force);

lemma normed_vs_norm: "is_normed_vectorspace V norm ==> is_norm V norm";
  by (unfold is_normed_vectorspace_def, force);

lemma normed_vs_norm_ge_zero: "[| is_normed_vectorspace V norm; x:V |] ==> 0r <= norm x";
  by (unfold is_normed_vectorspace_def, elim conjE, rule norm_ge_zero);

lemma normed_vs_norm_gt_zero: 
  "[| is_normed_vectorspace V norm; x:V; x ~= <0> |] ==> 0r < norm x";
proof (unfold is_normed_vectorspace_def, elim conjE);
  assume "x : V" "x ~= <0>" "is_vectorspace V" "is_norm V norm";
  have "0r <= norm x"; by (rule norm_ge_zero);
  also; have "0r ~= norm x";
  proof; 
    presume "norm x = 0r";
    have "x = <0>"; by (asm_simp add: norm_zero_iff);
    thus "False"; by contradiction;
  qed (rule sym);
  finally; show "0r < norm x"; .;
qed;

lemma normed_vs_norm_mult_distrib: 
  "[| is_normed_vectorspace V norm; x:V |] ==> norm (a [*] x) = (rabs a) * (norm x)";
  by (unfold is_normed_vectorspace_def, elim conjE, 
      rule quasinorm_mult_distrib, rule norm_is_quasinorm);

lemma normed_vs_norm_triangle_ineq: 
  "[| is_normed_vectorspace V norm; x:V; y:V |] ==> norm (x [+] y) <= norm x + norm y";
  by (unfold is_normed_vectorspace_def, elim conjE, 
      rule quasinorm_triangle_ineq, rule norm_is_quasinorm);

lemma subspace_normed_vs: 
  "[| is_subspace F E; is_vectorspace E; is_normed_vectorspace E norm |] ==> is_normed_vectorspace F norm";
proof (rule normed_vsI);
  assume "is_subspace F E" "is_vectorspace E" "is_normed_vectorspace E norm";
  show "is_vectorspace F"; by (rule subspace_vs);
  show "is_norm F norm"; 
  proof (intro is_norm_I ballI conjI);
    show "is_quasinorm F norm"; 
    proof (rule is_quasinormI, rule normed_vs_norm_ge_zero [of E norm], 
       rule normed_vs_norm_mult_distrib [of E norm], rule normed_vs_norm_triangle_ineq);
    qed ( rule subsetD [OF subspace_subset], assumption+)+; 

    fix x; assume "x : F";
    have n: "is_norm E norm"; by (unfold is_normed_vectorspace_def, asm_simp);
    have "x:E"; by (rule subsetD [OF subspace_subset]);
    from n this; show "(norm x = 0r) = (x = <0>)"; by (rule norm_zero_iff);
  qed;
qed;

end;

