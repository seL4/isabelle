(*  Title:      HOL/Real/HahnBanach/FunctionNorm.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

theory FunctionNorm = NormedSpace + FunctionOrder:;


constdefs
  is_continous :: "['a set, 'a => real, 'a => real] => bool" 
  "is_continous V norm f == (is_linearform V f
                           & (EX c. ALL x:V. rabs (f x) <= c * norm x))";

lemma lipschitz_continousI [intro]: 
  "[| is_linearform V f; !! x. x:V ==> rabs (f x) <= c * norm x |] 
  ==> is_continous V norm f";
proof (unfold is_continous_def, intro exI conjI ballI);
  assume r: "!! x. x:V ==> rabs (f x) <= c * norm x"; 
  fix x; assume "x:V"; show "rabs (f x) <= c * norm x"; by (rule r);
qed;
  
lemma continous_linearform [intro!!]: "is_continous V norm f ==> is_linearform V f";
  by (unfold is_continous_def) force;

lemma continous_bounded [intro!!]:
  "is_continous V norm f ==> EX c. ALL x:V. rabs (f x) <= c * norm x";
  by (unfold is_continous_def) force;

constdefs
  B:: "[ 'a set, 'a => real, 'a => real ] => real set"
  "B V norm f == {z. z = 0r | (EX x:V. x ~= <0> & z = rabs (f x) * rinv (norm (x)))}";

constdefs 
  function_norm :: " ['a set, 'a => real, 'a => real] => real"
  "function_norm V norm f == 
     Sup UNIV (B V norm f)";

constdefs 
  is_function_norm :: " ['a set, 'a => real, 'a => real] => real => bool"
  "is_function_norm V norm f fn == 
     is_Sup UNIV (B V norm f) fn";

lemma B_not_empty: "0r : B V norm f";
  by (unfold B_def, force);

lemma ex_fnorm [intro!!]: 
  "[| is_normed_vectorspace V norm; is_continous V norm f|]
     ==> is_function_norm V norm f (function_norm V norm f)"; 
proof (unfold function_norm_def is_function_norm_def is_continous_def Sup_def, elim conjE, 
    rule selectI2EX);
  assume "is_normed_vectorspace V norm";
  assume "is_linearform V f" and e: "EX c. ALL x:V. rabs (f x) <= c * norm x";
  show  "EX a. is_Sup UNIV (B V norm f) a"; 
  proof (unfold is_Sup_def, rule reals_complete);
    show "EX X. X : B V norm f"; 
    proof (intro exI);
      show "0r : (B V norm f)"; by (unfold B_def, force);
    qed;

    from e; show "EX Y. isUb UNIV (B V norm f) Y";
    proof;
      fix c; assume a: "ALL x:V. rabs (f x) <= c * norm x";
      def b == "max c 0r";

      show "EX Y. isUb UNIV (B V norm f) Y";
      proof (intro exI isUbI setleI ballI, unfold B_def, 
	elim CollectE disjE bexE conjE);
	fix x y; assume "x:V" "x ~= <0>" "y = rabs (f x) * rinv (norm x)";
        from a; have le: "rabs (f x) <= c * norm x"; ..;
        have "y = rabs (f x) * rinv (norm x)";.;
        also; from _  le; have "... <= c * norm x * rinv (norm x)";
        proof (rule real_mult_le_le_mono2);
          show "0r <= rinv (norm x)";
          proof (rule real_less_imp_le);
            show "0r < rinv (norm x)";
            proof (rule real_rinv_gt_zero);
              show "0r < norm x"; ..;
            qed;
          qed;
     (*** or:  by (rule real_less_imp_le, rule real_rinv_gt_zero, rule normed_vs_norm_gt_zero); ***)
        qed;
        also; have "... = c * (norm x * rinv (norm x))"; by (rule real_mult_assoc);
        also; have "(norm x * rinv (norm x)) = 1r"; 
        proof (rule real_mult_inv_right);
          show "norm x ~= 0r"; 
          proof (rule not_sym);
            show "0r ~= norm x"; 
            proof (rule lt_imp_not_eq);
              show "0r < norm x"; ..;
            qed;
          qed;
     (*** or:  by (rule not_sym, rule lt_imp_not_eq, rule normed_vs_norm_gt_zero); ***)
        qed;
        also; have "c * ... = c"; by (simp!);
        also; have "... <= b"; by (simp! add: le_max1);
	finally; show "y <= b"; .;
      next; 
	fix y; assume "y = 0r"; show "y <= b"; by (simp! add: le_max2);
      qed simp;
    qed;
  qed;
qed;

lemma fnorm_ge_zero [intro!!]: "[| is_continous V norm f; is_normed_vectorspace V norm|]
   ==> 0r <= function_norm V norm f";
proof -;
  assume c: "is_continous V norm f" and n: "is_normed_vectorspace V norm";
  have "is_function_norm V norm f (function_norm V norm f)"; ..;
  hence s: "is_Sup UNIV (B V norm f) (function_norm V norm f)"; 
    by (simp add: is_function_norm_def);
  show ?thesis; 
  proof (unfold function_norm_def, rule sup_ub1);
    show "ALL x:(B V norm f). 0r <= x"; 
    proof (intro ballI, unfold B_def, elim CollectE bexE conjE disjE);
      fix x r; assume "x : V" "x ~= <0>" 
        "r = rabs (f x) * rinv (norm x)"; 
      show  "0r <= r";
      proof (simp!, rule real_le_mult_order);
        show "0r <= rabs (f x)"; by (simp! only: rabs_ge_zero);
        show "0r <= rinv (norm x)";
        proof (rule real_less_imp_le);
          show "0r < rinv (norm x)"; 
          proof (rule real_rinv_gt_zero);
            show "0r < norm x"; ..;
          qed;
        qed;
      qed;
    qed (simp!);
    from ex_fnorm [OF n c]; show "is_Sup UNIV (B V norm f) (Sup UNIV (B V norm f))"; 
      by (simp! add: is_function_norm_def function_norm_def); 
    show "0r : B V norm f"; by (rule B_not_empty);
  qed;
qed;
  

lemma norm_fx_le_norm_f_norm_x: 
  "[| is_normed_vectorspace V norm; x:V; is_continous V norm f |] 
    ==> rabs (f x) <= (function_norm V norm f) * norm x"; 
proof -; 
  assume "is_normed_vectorspace V norm" "x:V" and c: "is_continous V norm f";
  have v: "is_vectorspace V"; ..;
  assume "x:V";
  show "?thesis";
  proof (rule case_split [of "x = <0>"]);
    assume "x ~= <0>";
    show "?thesis";
    proof -;
      have n: "0r <= norm x"; ..;
      have le: "rabs (f x) * rinv (norm x) <= function_norm V norm f"; 
        proof (unfold function_norm_def, rule sup_ub);
          from ex_fnorm [OF _ c]; show "is_Sup UNIV (B V norm f) (Sup UNIV (B V norm f))"; 
             by (simp! add: is_function_norm_def function_norm_def); 
          show "rabs (f x) * rinv (norm x) : B V norm f"; 
            by (unfold B_def, intro CollectI disjI2 bexI [of _ x] conjI, simp);
        qed;
      have "rabs (f x) = rabs (f x) * 1r"; by (simp!);
      also; have "1r = rinv (norm x) * norm x"; 
      proof (rule real_mult_inv_left [RS sym]);
        show "norm x ~= 0r";
        proof (rule lt_imp_not_eq[RS not_sym]);
          show "0r < norm x"; ..;
        qed;
      qed;
      also; have "rabs (f x) * ... = rabs (f x) * rinv (norm x) * norm x"; 
        by (simp! add: real_mult_assoc [of "rabs (f x)"]);
      also; have "rabs (f x) * rinv (norm x) * norm x <= function_norm V norm f * norm x"; 
        by (rule real_mult_le_le_mono2 [OF n le]);
      finally; show "rabs (f x) <= function_norm V norm f * norm x"; .;
    qed;
  next; 
    assume "x = <0>";
    then; show "?thesis";
    proof -;
      have "rabs (f x) = rabs (f <0>)"; by (simp!);
      also; from v continous_linearform; have "f <0> = 0r"; ..;
      also; note rabs_zero;
      also; have" 0r <= function_norm V norm f * norm x";
      proof (rule real_le_mult_order);
        show "0r <= function_norm V norm f"; ..;
        show "0r <= norm x"; ..;
      qed;
      finally; show "rabs (f x) <= function_norm V norm f * norm x"; .;
    qed;
  qed;
qed;




lemma fnorm_le_ub: 
  "[| is_normed_vectorspace V norm; is_continous V norm f;
     ALL x:V. rabs (f x) <= c * norm x; 0r <= c |]
  ==> function_norm V norm f <= c";
proof (unfold function_norm_def);
  assume "is_normed_vectorspace V norm"; 
  assume c: "is_continous V norm f";
  assume fb: "ALL x:V. rabs (f x) <= c * norm x"
         and "0r <= c";
  show "Sup UNIV (B V norm f) <= c"; 
  proof (rule sup_le_ub);
    from ex_fnorm [OF _ c]; show "is_Sup UNIV (B V norm f) (Sup UNIV (B V norm f))"; 
      by (simp! add: is_function_norm_def function_norm_def); 
    show "isUb UNIV (B V norm f) c";  
    proof (intro isUbI setleI ballI);
      fix y; assume "y: B V norm f";
      thus le: "y <= c";
      proof (unfold B_def, elim CollectE disjE bexE);
	fix x; assume Px: "x ~= <0> & y = rabs (f x) * rinv (norm x)";
	assume x: "x : V";
        have lt: "0r < norm x";  by (simp! add: normed_vs_norm_gt_zero);
          
        have neq: "norm x ~= 0r"; 
        proof (rule not_sym);
          from lt; show "0r ~= norm x";
          by (simp! add: order_less_imp_not_eq);
        qed;
            
	from lt; have "0r < rinv (norm x)";
	  by (simp! add: real_rinv_gt_zero);
	then; have inv_leq: "0r <= rinv (norm x)"; by (rule real_less_imp_le);

	from Px; have "y = rabs (f x) * rinv (norm x)"; ..;
	also; from inv_leq; have "... <= c * norm x * rinv (norm x)";
	  proof (rule real_mult_le_le_mono2);
	    from fb x; show "rabs (f x) <= c * norm x"; ..;
	  qed;
	also; have "... <= c";
	  by (simp add: neq real_mult_assoc);
	finally; show ?thesis; .;
      next;
        assume "y = 0r";
        show "y <= c"; by (force!);
      qed;
    qed force;
  qed;
qed;


end;

