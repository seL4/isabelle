(*  Title:      HOL/Real/HahnBanach/HahnBanach_h0_lemmas.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Lemmas about the extension of a non-maximal function *};

theory HahnBanach_h0_lemmas = FunctionNorm:;

lemma ex_xi: 
  "[| is_vectorspace F;  (!! u v. [| u:F; v:F |] ==> a u <= b v )|]
  ==> EX xi::real. (ALL y:F. (a::'a => real) y <= xi) 
                 & (ALL y:F. xi <= b y)"; 
proof -;
  assume vs: "is_vectorspace F";
  assume r: "(!! u v. [| u:F; v:F |] ==> a u <= (b v::real))";
  have "EX t. isLub UNIV {s::real . EX u:F. s = a u} t";  
  proof (rule reals_complete);
    from vs; have "a <0> : {s. EX u:F. s = a u}"; by (force);
    thus "EX X. X : {s. EX u:F. s = a u}"; ..;

    show "EX Y. isUb UNIV {s. EX u:F. s = a u} Y"; 
    proof; 
      show "isUb UNIV {s. EX u:F. s = a u} (b <0>)";
      proof (intro isUbI setleI ballI, fast);
        fix y; assume y: "y : {s. EX u:F. s = a u}"; 
        show "y <= b <0>"; 
        proof -;
          from y; have "EX u:F. y = a u"; by (fast);
          thus ?thesis;
          proof;
            fix u; assume "u:F"; 
            assume "y = a u";
            also; have "a u <= b <0>"; 
            proof (rule r);
              show "<0> : F"; ..;
            qed;
            finally; show ?thesis;.;
          qed;
        qed;
      qed;
    qed;
  qed;
  thus "EX xi. (ALL y:F. a y <= xi) & (ALL y:F. xi <= b y)"; 
  proof (elim exE);
    fix t; assume "isLub UNIV {s::real . EX u:F. s = a u} t"; 
    show ?thesis;
    proof (intro exI conjI ballI); 
      fix y; assume y: "y:F";
      show "a y <= t";    
      proof (rule isUbD);  
        show"isUb UNIV {s. EX u:F. s = a u} t"; ..;
      qed (force simp add: y);
    next;
      fix y; assume "y:F";
      show "t <= b y";  
      proof (intro isLub_le_isUb isUbI setleI);
        show "ALL ya : {s. EX u:F. s = a u}. ya <= b y"; 
        proof (intro ballI); 
          fix au; 
          assume au: "au : {s. EX u:F. s = a u} ";
          show "au <= b y";
          proof -; 
            from au; have "EX u:F. au = a u"; by (fast); 
            thus "au <= b y";
            proof;
              fix u; assume "u:F";
              assume "au = a u";  
              also; have "... <= b y"; by (rule r);
              finally; show ?thesis; .;
            qed;
          qed;
        qed;
        show "b y : UNIV"; by fast;
      qed; 
    qed;
  qed;
qed;

lemma h0_lf: 
  "[| h0 = (%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H) 
                in (h y) + a * xi);
  H0 = vectorspace_sum H (lin x0); is_subspace H E; is_linearform H h; 
  x0 ~: H; x0 : E; x0 ~= <0>; is_vectorspace E |]
  ==> is_linearform H0 h0";
proof -;
  assume h0_def: 
    "h0 = (%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H) 
               in (h y) + a * xi)"
  and H0_def: "H0 = vectorspace_sum H (lin x0)"
  and vs: "is_subspace H E" "is_linearform H h" "x0 ~: H" "x0 ~= <0>" 
          "x0 : E" "is_vectorspace E";

  have h0: "is_vectorspace H0"; 
  proof (simp only: H0_def, rule vs_sum_vs);
    show "is_subspace (lin x0) E"; by (rule lin_subspace); 
  qed; 

  show ?thesis;
  proof;
    fix x1 x2; assume x1: "x1 : H0" and x2: "x2 : H0"; 
    have x1x2: "x1 [+] x2 : H0"; 
      by (rule vs_add_closed, rule h0);
  
    from x1; have ex_x1: "? y1 a1. (x1 = y1 [+] a1 [*] x0  & y1 : H)"; 
      by (simp add: H0_def vectorspace_sum_def lin_def) blast;
    from x2; have ex_x2: "? y2 a2. (x2 = y2 [+] a2 [*] x0 & y2 : H)"; 
      by (simp add: H0_def vectorspace_sum_def lin_def) blast;
    from x1x2; have ex_x1x2: "? y a. (x1 [+] x2 = y [+] a [*] x0  & y : H)";
      by (simp add: H0_def vectorspace_sum_def lin_def) force;
    from ex_x1 ex_x2 ex_x1x2;
    show "h0 (x1 [+] x2) = h0 x1 + h0 x2";
    proof (elim exE conjE);
      fix y1 y2 y a1 a2 a;
      assume y1: "x1 = y1 [+] a1 [*] x0"       and y1': "y1 : H"
         and y2: "x2 = y2 [+] a2 [*] x0"       and y2': "y2 : H" 
         and y: "x1 [+] x2 = y  [+] a  [*] x0" and y': "y  : H"; 

      have ya: "y1 [+] y2 = y & a1 + a2 = a"; 
      proof (rule decomp4); 
        show "y1 [+] y2 [+] (a1 + a2) [*] x0 = y [+] a [*] x0"; 
        proof -;
          have "y [+] a [*] x0 = x1 [+] x2"; by (rule sym);
          also; from y1 y2; 
          have "... = y1 [+] a1 [*] x0 [+] (y2 [+] a2 [*] x0)"; by simp; 
          also; from vs y1' y2'; 
          have "... = y1 [+] y2 [+] (a1 [*] x0 [+] a2 [*] x0)"; by simp;
          also; from vs y1' y2'; 
          have "... = y1 [+] y2 [+] (a1 + a2) [*] x0"; 
            by (simp add: vs_add_mult_distrib2[of E]);
          finally; show ?thesis; by (rule sym);
        qed;
        show "y1 [+] y2 : H"; ..;
      qed;
      have y: "y1 [+] y2 = y"; by (rule conjunct1 [OF ya]);
      have a: "a1 + a2 = a";  by (rule conjunct2 [OF ya]);

      have "h0 (x1 [+] x2) = h y + a * xi";
	by (rule decomp3);
      also; have "... = h (y1 [+] y2) + (a1 + a2) * xi"; by (simp add: y a);
      also; from vs y1' y2'; have  "... = h y1 + h y2 + a1 * xi + a2 * xi"; 
	by (simp add: linearform_add_linear [of H] real_add_mult_distrib);
      also; have "... = (h y1 + a1 * xi) + (h y2 + a2 * xi)"; by (simp);
      also; have "h y1 + a1 * xi = h0 x1"; by (rule decomp3 [RS sym]);
      also; have "h y2 + a2 * xi = h0 x2"; by (rule decomp3 [RS sym]);
      finally; show ?thesis; .;
    qed;
 
  next;  
    fix c x1; assume x1: "x1 : H0";
    
    have ax1: "c [*] x1 : H0";
      by (rule vs_mult_closed, rule h0);
    from x1; have ex_x1: "? y1 a1. (x1 = y1 [+] a1 [*] x0 & y1 : H)";
      by (simp add: H0_def vectorspace_sum_def lin_def, fast);
    from x1; 
    have ex_x: "!! x. x: H0 ==> ? y a. (x = y [+] a [*] x0 & y : H)"; 
      by (simp add: H0_def vectorspace_sum_def lin_def, fast);
    note ex_ax1 = ex_x [of "c [*] x1", OF ax1];
    from ex_x1 ex_ax1; show "h0 (c [*] x1) = c * (h0 x1)";  
    proof (elim exE conjE);
      fix y1 y a1 a; 
      assume y1: "x1 = y1 [+] a1 [*] x0"        and y1': "y1 : H"
	 and y:  "c [*] x1 = y  [+] a  [*] x0"  and y':  "y  : H"; 

      have ya: "c [*] y1 = y & c * a1 = a"; 
      proof (rule decomp4); 
	show "c [*] y1 [+] (c * a1) [*] x0 = y [+] a [*] x0"; 
	proof -; 
          have "y [+] a [*] x0 = c [*] x1"; by (rule sym);
          also; from y1; have "... = c [*] (y1 [+] a1 [*] x0)"; by simp;
          also; from vs y1'; have "... = c [*] y1 [+] c [*] (a1 [*] x0)"; 
            by (simp add: vs_add_mult_distrib1);
          also; from vs y1'; have "... = c [*] y1 [+] (c * a1) [*] x0"; 
            by simp;
          finally; show ?thesis; by (rule sym);
        qed;
        show "c [*] y1: H"; ..;
      qed;
      have y: "c [*] y1 = y"; by (rule conjunct1 [OF ya]);
      have a: "c * a1 = a"; by (rule conjunct2 [OF ya]);
      
      have "h0 (c [*] x1) = h y + a * xi"; 
	by (rule decomp3);
      also; have "... = h (c [*] y1) + (c * a1) * xi";
        by (simp add: y a);
      also; from vs y1'; have  "... = c * h y1 + c * a1 * xi"; 
	by (simp add: linearform_mult_linear [of H] real_add_mult_distrib);
      also; from vs y1'; have "... = c * (h y1 + a1 * xi)"; 
	by (simp add: real_add_mult_distrib2 real_mult_assoc);
      also; have "h y1 + a1 * xi = h0 x1"; by (rule decomp3 [RS sym]);
      finally; show ?thesis; .;
    qed;
  qed;
qed;

lemma h0_norm_pres:
  "[| h0 = (%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H) 
                in (h y) + a * xi);
  H0 = vectorspace_sum H (lin x0); x0 ~: H; x0 : E; x0 ~= <0>; 
  is_vectorspace E; is_subspace H E; is_quasinorm E p; is_linearform H h; 
  ALL y:H. h y <= p y;
  (ALL y:H. - p (y [+] x0) - h y <= xi) 
  & (ALL y:H. xi <= p (y [+] x0) - h y)|]
   ==> ALL x:H0. h0 x <= p x"; 
proof; 
  assume h0_def: 
    "h0 = (%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H) 
               in (h y) + a * xi)"
    and H0_def: "H0 = vectorspace_sum H (lin x0)" 
    and vs:     "x0 ~: H" "x0 : E" "x0 ~= <0>" "is_vectorspace E" 
                "is_subspace H E" "is_quasinorm E p" "is_linearform H h" 
    and a:      " ALL y:H. h y <= p y";
  presume a1: "(ALL y:H. - p (y [+] x0) - h y <= xi)";
  presume a2: "(ALL y:H. xi <= p (y [+] x0) - h y)";
  fix x; assume "x : H0"; 
  show "h0 x <= p x"; 
  proof -; 
    have ex_x: "!! x. x : H0 ==> ? y a. (x = y [+] a [*] x0 & y : H)";
      by (simp add: H0_def vectorspace_sum_def lin_def, fast);
    have "? y a. (x = y [+] a [*] x0 & y : H)";
      by (rule ex_x);
    thus ?thesis;
    proof (elim exE conjE);
      fix y a; assume x: "x = y [+] a [*] x0" and y: "y : H";
      show ?thesis;
      proof -;
        have "h0 x = h y + a * xi";
          by (rule decomp3);
        also; have "... <= p (y [+] a [*] x0)";
        proof (rule real_linear_split [of a "0r"]); (*** case analysis ***)
          assume lz: "a < 0r"; hence nz: "a ~= 0r"; by force;
          show ?thesis;
          proof -;
            from a1; 
            have "- p (rinv a [*] y [+] x0) - h (rinv a [*] y) <= xi";
              by (rule bspec, simp!);
            
            with lz; 
            have "a * xi <= a * (- p (rinv a [*] y [+] x0) - h (rinv a [*] y))";
              by (rule real_mult_less_le_anti);
            also; have "... = - a * (p (rinv a [*] y [+] x0)) - a * (h (rinv a [*] y))";
              by (rule real_mult_diff_distrib);
            also; from lz vs y; 
            have "- a * (p (rinv a [*] y [+] x0)) = p (a [*] (rinv a [*] y [+] x0))";
              by (simp add: quasinorm_mult_distrib rabs_minus_eqI2 [RS sym]);
            also; from nz vs y; have "... = p (y [+] a [*] x0)";
              by (simp add: vs_add_mult_distrib1);
            also; from nz vs y; have "a * (h (rinv a [*] y)) =  h y";
              by (simp add: linearform_mult_linear [RS sym]);
            finally; have "a * xi <= p (y [+] a [*] x0) - h y"; .;

            hence "h y + a * xi <= h y + (p (y [+] a [*] x0) - h y)";
              by (rule real_add_left_cancel_le [RS iffD2]);
            thus ?thesis; 
              by simp;
	  qed;

        next;
          assume z: "a = 0r"; 
          with vs y a; show ?thesis; by simp;

        next; 
          assume gz: "0r < a"; hence nz: "a ~= 0r"; by force;
          show ?thesis;
          proof -;
            from a2; 
            have "xi <= p (rinv a [*] y [+] x0) - h (rinv a [*] y)";
              by (rule bspec, simp!);

            with gz; 
            have "a * xi <= a * (p (rinv a [*] y [+] x0) - h (rinv a [*] y))";
              by (rule real_mult_less_le_mono);
            also; 
            have "... = a * (p (rinv a [*] y [+] x0)) - a * (h (rinv a [*] y))";
              by (rule real_mult_diff_distrib2); 
            also; from gz vs y; 
            have "a * (p (rinv a [*] y [+] x0)) = p (a [*] (rinv a [*] y [+] x0))";
              by (simp add: quasinorm_mult_distrib rabs_eqI2);
            also; from nz vs y; 
            have "... = p (y [+] a [*] x0)";
              by (simp add: vs_add_mult_distrib1);
            also; from nz vs y; have "a * (h (rinv a [*] y)) = h y";
              by (simp add: linearform_mult_linear [RS sym]); 
            finally; have "a * xi <= p (y [+] a [*] x0) - h y"; .;
 
            hence "h y + a * xi <= h y + (p (y [+] a [*] x0) - h y)";
              by (rule real_add_left_cancel_le [RS iffD2]);
            thus ?thesis; 
              by simp;
          qed;
        qed;
        also; from x; have "... = p x"; by (simp);
        finally; show ?thesis; .;
      qed; 
    qed;
  qed; 
qed blast+;

end;