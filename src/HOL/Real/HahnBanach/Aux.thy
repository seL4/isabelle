
theory Aux = Main + Real:;


theorem [trans]: "[| (x::'a::order) <= y; x ~= y |] ==> x < y";	    (*  <=  ~=  < *)
  by (asm_simp add: order_less_le);

lemma lt_imp_not_eq: "x < (y::'a::order) ==> x ~= y"; 
  by (rule order_less_le[RS iffD1, RS conjunct2]);

lemma Int_singeltonD: "[| A Int B = {v}; x:A; x:B |] ==> x = v";
  by (fast elim: equalityE);

lemma real_add_minus_eq: "x - y = 0r ==> x = y";
proof -;
  assume "x - y = 0r";
  have "x + - y = x - y"; by simp;
  also; have "... = 0r"; .;
  finally; have "x + - y = 0r"; .;
  hence "x = - (- y)"; by (rule real_add_minus_eq_minus);
  also; have "... = y"; by asm_simp;
  finally; show "x = y"; .;
qed;

lemma rabs_minus_one: "rabs (- 1r) = 1r"; 
proof -; 
  have "rabs (- 1r) = - (- 1r)"; 
  proof (rule rabs_minus_eqI2);
    show "-1r < 0r";
      by (rule real_minus_zero_less_iff[RS iffD1], simp, rule real_zero_less_one);
  qed;
  also; have "... = 1r"; by asm_simp; 
  finally; show ?thesis; by asm_simp;
qed;

axioms real_mult_le_le_mono2: "[| 0r <= z; x <= y |] ==> x * z <= y * z";

axioms real_mult_less_le_anti: "[| z < 0r; x <= y |] ==> z * y <= z * x";

axioms real_mult_less_le_mono: "[| 0r < z; x <= y |] ==> z * x <= z * y";

axioms real_mult_diff_distrib: "a * (- x - y) = - a * x - a * y";

axioms real_mult_diff_distrib2: "a * (x - y) = a * x - a * y";

lemma less_imp_le: "(x::real) < y ==> x <= y";
  by (asm_simp only: real_less_imp_le);

lemma le_noteq_imp_less: "[|x <= (r::'a::order); x ~= r |] ==> x < r";
proof -;
  assume "x <= (r::'a::order)";
  assume "x ~= r";
  then; have "x < r | x = r";
    by (asm_simp add: order_le_less);
  then; show ?thesis;
    by asm_simp;
qed;

lemma minus_le: "- (x::real) <= y ==> - y <= x";
proof -; 
  assume "- x <= y";
  hence "- x < y | - x = y"; by (rule order_le_less [RS iffD1]);
  thus "-y <= x";
  proof;
     assume "- x < y"; show ?thesis; 
     proof -; 
       have "- y < - (- x)"; by (rule real_less_swap_iff [RS iffD1]); 
       hence "- y < x"; by asm_simp;
       thus ?thesis; by (rule real_less_imp_le);
    qed;
  next; 
     assume "- x = y"; show ?thesis; by force;
  qed;
qed;

lemma rabs_interval_iff_1: "(rabs (x::real) <= r) = (-r <= x & x <= r)";
proof (rule case [of "rabs x = r"]);
  assume  a: "rabs x = r";
  show ?thesis; 
  proof;
    assume "rabs x <= r";
    show "- r <= x & x <= r";
    proof;
      have "- x <= rabs x"; by (rule rabs_ge_minus_self);
      hence "- x <= r"; by asm_simp;
      thus "- r <= x"; by (asm_simp add : minus_le [of "x" "r"]);
      have "x <= rabs x"; by (rule rabs_ge_self); 
      thus "x <= r"; by asm_simp; 
    qed;
  next; 
    assume "- r <= x & x <= r";
    show "rabs x <= r";  by fast;  
  qed;
next;   
  assume "rabs x ~= r";
  show ?thesis; 
  proof;
    assume "rabs x <= r"; 
    have "rabs x < r"; by (rule conjI [RS real_less_le [RS iffD2]]);
    hence "- r < x & x < r"; by (rule rabs_interval_iff [RS iffD1]);
    thus "- r <= x & x <= r";
    proof(elim conjE, intro conjI); 
      assume "- r < x";
      show "- r <= x"; by (rule real_less_imp_le); 
      assume "x < r";
      show "x <= r"; by (rule real_less_imp_le); 
    qed;
  next;
    assume "- r <= x & x <= r";
    thus "rabs x <= r";
    proof; 
      assume "- r <= x" "x <= r";
      show ?thesis; 
      proof (rule rabs_disj [RS disjE, of x]);
        assume  "rabs x = x";
        show ?thesis; by asm_simp; 
      next; 
        assume "rabs x = - x";
        from minus_le [of r x]; show ?thesis; by asm_simp;
      qed;
    qed;
  qed;
qed;

lemma set_less_imp_diff_not_empty: "H < E ==> EX x0:E. x0 ~: H";
proof- ;
  assume "H < E ";
  have le: "H <= E"; by (rule conjunct1 [OF psubset_eq[RS iffD1]]);
  have ne: "H ~= E";  by (rule conjunct2 [OF psubset_eq[RS iffD1]]);
  with le; show ?thesis; by force;
qed;


end;