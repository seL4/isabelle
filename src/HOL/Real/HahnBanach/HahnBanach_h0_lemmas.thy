(*  Title:      HOL/Real/HahnBanach/HahnBanach_h0_lemmas.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

theory HahnBanach_h0_lemmas = FunctionNorm:;


theorems [intro!!] = isLub_isUb;

lemma ex_xi: "[| is_vectorspace F;  (!! u v. [| u:F; v:F |] ==> a u <= b v )|]
       ==> EX xi::real. (ALL y:F. (a::'a => real) y <= xi) & (ALL y:F. xi <= b y)"; 
proof -;
  assume "is_vectorspace F";
  assume r: "(!! u v. [| u:F; v:F |] ==> a u <= (b v::real))";
  have "EX t. isLub UNIV {s::real . EX u:F. s = a u} t";  
  proof (rule reals_complete);
    have "a <0> : {s. EX u:F. s = a u}"; by (force!);
    thus "EX X. X : {s. EX u:F. s = a u}"; ..;

    show "EX Y. isUb UNIV {s. EX u:F. s = a u} Y"; 
    proof; 
      show "isUb UNIV {s. EX u:F. s = a u} (b <0>)";
      proof (intro isUbI setleI ballI, fast);
        fix y; assume "y : {s. EX u:F. s = a u}"; 
        show "y <= b <0>"; 
        proof -;
          have "EX u:F. y = a u"; by (fast!);
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
      fix y; assume "y:F";
      show "a y <= t";    
      proof (rule isUbD);  
        show"isUb UNIV {s. EX u:F. s = a u} t"; ..;
      qed (fast!);
    next;
      fix y; assume "y:F";
      show "t <= b y";  
      proof (intro isLub_le_isUb isUbI setleI);
        show "ALL ya : {s. EX u:F. s = a u}. ya <= b y"; 
        proof (intro ballI); 
          fix au; 
          assume "au : {s. EX u:F. s = a u} ";
          show "au <= b y";
          proof -; 
            have "EX u:F. au = a u"; by (fast!);
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
  "[| h0 = (%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H) in (h y) + a * xi);
      H0 = vectorspace_sum H (lin x0); is_subspace H E; is_linearform H h; x0 ~: H; 
      x0 : E; x0 ~= <0>; is_vectorspace E |]
    ==> is_linearform H0 h0";
proof -;
  assume h0_def:  "h0 = (%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H) in (h y) + a * xi)"
    and H0_def: "H0 = vectorspace_sum H (lin x0)"
    and [simp]: "is_subspace H E" "is_linearform H h" "x0 ~: H" "x0 ~= <0>"
    and [simp]: "x0 : E" "is_vectorspace E";

  have h0: "is_vectorspace H0"; 
  proof ((simp!), rule vs_sum_vs);
    show "is_subspace (lin x0) E"; by (rule lin_subspace); 
  qed simp+; 

  show ?thesis;
  proof;
    fix x1 x2; assume "x1 : H0" "x2 : H0"; 
    have x1x2: "x1 [+] x2 : H0"; 
      by (rule vs_add_closed, rule h0);
  
    have ex_x1: "? y1 a1. (x1 = y1 [+] a1 [*] x0  & y1 : H)"; 
      by (simp! add: vectorspace_sum_def lin_def) blast;
    have ex_x2: "? y2 a2. (x2 = y2 [+] a2 [*] x0 & y2 : H)"; 
      by (simp! add: vectorspace_sum_def lin_def) blast;
    from x1x2; have ex_x1x2: "? y a. (x1 [+] x2 = y [+] a [*] x0  & y : H)";    
      by (simp! add: vectorspace_sum_def lin_def) force;
    from ex_x1 ex_x2 ex_x1x2;
    show "h0 (x1 [+] x2) = h0 x1 + h0 x2";
    proof (elim exE conjE);
      fix y1 y2 y a1 a2 a;
      assume "x1 = y1 [+] a1 [*] x0"        "y1 : H"
             "x2 = y2 [+] a2 [*] x0"        "y2 : H" 
             "x1 [+] x2 = y  [+] a  [*] x0" "y  : H"; 

      have ya: "y1 [+] y2 = y & a1 + a2 = a"; 
      proof (rule decomp4); 
        show "y1 [+] y2 [+] (a1 + a2) [*] x0 = y [+] a [*] x0"; 
        proof -;
          have "y [+] a [*] x0 = x1 [+] x2"; by (simp!); 
          also; have "... = y1 [+] a1 [*] x0 [+] (y2 [+] a2 [*] x0)"; by (simp!); 
          also; from prems; have "... = y1 [+] y2 [+] (a1 [*] x0 [+] a2 [*] x0)";
	    by asm_simp_tac;   (* FIXME !?? *)
         also; have "... = y1 [+] y2 [+] (a1 + a2) [*] x0"; 
            by (simp! add: vs_add_mult_distrib2[of E]);
          finally; show ?thesis; by (rule sym);
        qed;
        show "y1 [+] y2 : H"; ..;
      qed;
      have y: "y1 [+] y2 = y"; by (rule conjunct1 [OF ya]);
      have a: "a1 + a2 = a";  by (rule conjunct2 [OF ya]);

      have "h0 (x1 [+] x2) = h y + a * xi";
	by (rule decomp3);
      also; have "... = h (y1 [+] y2) + (a1 + a2) * xi"; by (simp! add: y a);
      also; have  "... = h y1 + h y2 + a1 * xi + a2 * xi"; 
	by (simp! add: linearform_add_linear [of H] real_add_mult_distrib);
      also; have "... = (h y1 + a1 * xi) + (h y2 + a2 * xi)"; by (simp!);
      also; have "... = h0 x1 + h0 x2"; 
      proof -; 
        have x1: "h0 x1 = h y1 + a1 * xi"; by (rule decomp3);
        have x2: "h0 x2 = h y2 + a2 * xi"; by (rule decomp3);
        from x1 x2; show ?thesis; by (simp!);
      qed;
      finally; show ?thesis; .;
    qed;
 
  next;  
    fix c x1; assume  "x1 : H0";
    
    have ax1: "c [*] x1 : H0";
      by (rule vs_mult_closed, rule h0);
    have ex_x1: "? y1 a1. (x1 = y1 [+] a1 [*] x0 & y1 : H)";
      by (simp! add: vectorspace_sum_def lin_def, fast);
    have ex_x: "!! x. x: H0 ==> ? y a. (x = y [+] a [*] x0 & y : H)"; 
      by (simp! add: vectorspace_sum_def lin_def, fast);
    note ex_ax1 = ex_x [of "c [*] x1", OF ax1];
    from ex_x1 ex_ax1; show "h0 (c [*] x1) = c * (h0 x1)";  
    proof (elim exE conjE);
      fix y1 y a1 a; 
      assume "x1 = y1 [+] a1 [*] x0"       "y1 : H"
	     "c [*] x1 = y  [+] a  [*] x0" "y  : H"; 

      have ya: "c [*] y1 = y & c * a1 = a"; 
      proof (rule decomp4); 
	show "c [*] y1 [+] (c * a1) [*] x0 = y [+] a [*] x0"; 
	proof -; 
          have "y [+] a [*] x0 = c [*] x1"; by (simp!);
          also; have "... = c [*] (y1 [+] a1 [*] x0)"; by (simp!);
          also; from prems; have "... = c [*] y1 [+] c [*] (a1 [*] x0)"; 
            by (asm_simp_tac add: vs_add_mult_distrib1);  (* FIXME *)
          also; from prems; have "... = c [*] y1 [+] (c * a1) [*] x0";
            by asm_simp_tac;
          finally; show ?thesis; by (rule sym);
        qed;
        show "c [*] y1: H"; ..;
      qed;
      have y: "c [*] y1 = y"; by (rule conjunct1 [OF ya]);
      have a: "c * a1 = a"; by (rule conjunct2 [OF ya]);
      
      have "h0 (c [*] x1) = h y + a * xi"; 
	by (rule decomp3);
      also; have "... = h (c [*] y1) + (c * a1) * xi";
        by (simp! add: y a);
      also; have  "... = c * h y1 + c * a1 * xi"; 
	by (simp! add: linearform_mult_linear [of H] real_add_mult_distrib);
      also; have "... = c * (h y1 + a1 * xi)"; 
	by (simp! add: real_add_mult_distrib2 real_mult_assoc);
      also; have "... = c * (h0 x1)"; 
      proof -; 
        have "h0 x1 = h y1 + a1 * xi"; by (rule decomp3);
        thus ?thesis; by (simp!);
      qed;
      finally; show ?thesis; .;
    qed;
  qed;
qed;


lemma h0_norm_prev:
    "[| h0 = (%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H) in (h y) + a * xi);
      H0 = vectorspace_sum H (lin x0); x0 ~: H; x0 : E; x0 ~= <0>; is_vectorspace E; 
      is_subspace H E; is_quasinorm E p; is_linearform H h; ALL y:H. h y <= p y;
      (ALL y:H. - p (y [+] x0) - h y <= xi) & (ALL y:H. xi <= p (y [+] x0) - h y)|]
   ==> ALL x:H0. h0 x <= p x"; 
proof; 
  assume "h0 = (%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H) in (h y) + a * xi)"
         "H0 = vectorspace_sum H (lin x0)" "x0 ~: H" "x0 : E" "x0 ~= <0>" "is_vectorspace E" 
         "is_subspace H E" "is_quasinorm E p" "is_linearform H h" and a: " ALL y:H. h y <= p y";
  presume a1: "(ALL y:H. - p (y [+] x0) - h y <= xi)";
  presume a2: "(ALL y:H. xi <= p (y [+] x0) - h y)";
  fix x; assume "x : H0"; 
  show "h0 x <= p x"; 
  proof -; 
    have ex_x: "!! x. x : H0 ==> ? y a. (x = y [+] a [*] x0 & y : H)";
      by (simp! add: vectorspace_sum_def lin_def, fast);
    have "? y a. (x = y [+] a [*] x0 & y : H)";
      by (rule ex_x);
    thus ?thesis;
    proof (elim exE conjE);
      fix y a; assume "x = y [+] a [*] x0" "y : H";
      show ?thesis;
      proof -;
        have "h0 x = h y + a * xi";
          by (rule decomp3);
        also; have "... <= p (y [+] a [*] x0)";
        proof (rule real_linear [of a "0r", elimify], elim disjE); (*** case distinction ***)
          assume lz: "a < 0r"; 
          hence nz: "a ~= 0r"; by force;
          show ?thesis;
          proof -;
            from a1; have "- p (rinv a [*] y [+] x0) - h (rinv a [*] y) <= xi";
            proof (rule bspec); 
              show "(rinv a) [*] y : H"; ..;
            qed;
            with lz; have "a * xi <= a * (- p (rinv a [*] y [+] x0) - h (rinv a [*] y))";
              by (rule real_mult_less_le_anti);
            also; have "... = - a * (p (rinv a [*] y [+] x0)) - a * (h (rinv a [*] y))";
              by (rule real_mult_diff_distrib);
            also; have "... = (rabs a) * (p (rinv a [*] y [+] x0)) - a * (h (rinv a [*] y))";
            proof -; 
              from lz; have "rabs a = - a";
                by (rule rabs_minus_eqI2); 
              thus ?thesis; by simp;
            qed;
            also; from prems; have "... =  p (a [*] (rinv a [*] y [+] x0)) - a * (h (rinv a [*] y))";
              by (simp!, asm_simp_tac add: quasinorm_mult_distrib);
            also; have "... = p ((a * rinv a) [*] y [+] a [*] x0) - a * (h (rinv a [*] y))";
            proof simp;
              have "a [*] (rinv a [*] y [+] x0) = a [*] rinv a [*] y [+] a [*] x0";
                by (rule vs_add_mult_distrib1) (simp!)+;
              also; have "... = (a * rinv a) [*] y [+] a [*] x0";
                by (simp!);
              finally; have "a [*] (rinv a [*] y [+] x0) = (a * rinv a) [*] y [+] a [*] x0";.;
              thus "p (a [*] (rinv a [*] y [+] x0)) = p ((a * rinv a) [*] y [+] a [*] x0)";
                by simp;
            qed;
            also; from nz; have "... = p (y [+] a [*] x0) - (a * (h (rinv a [*] y)))"; 
              by (simp!);
            also; have "a * (h (rinv a [*] y)) = h y";
	    proof -;
              from prems; have "a * (h (rinv a [*] y)) = h (a [*] (rinv a [*] y))"; 
                by (asm_simp_tac add: linearform_mult_linear [RS sym]); 
	      also; from nz; have "a [*] (rinv a [*] y) = y"; by (simp!);
              finally; show ?thesis; .;
            qed;
            finally; have "a * xi <= p (y [+] a [*] x0) - ..."; .;
            hence "h y + a * xi <= h y + (p (y [+] a [*] x0) - h y)";
              by (rule real_add_left_cancel_le [RS iffD2]); (* arith *)
            thus ?thesis; 
              by force;
	  qed;
        next;
          assume "a = 0r"; show ?thesis; 
          proof -;
            have "h y + a * xi = h y"; by (simp!);
            also; from a; have "... <= p y"; ..; 
            also; have "... = p (y [+] a [*] x0)";
            proof -; 
              have "y = y [+] <0>"; by (simp!);
              also; have "... = y [+] a [*] x0"; 
              proof -; 
                have "<0> = 0r [*] x0";
                  by (simp!);
                also; have "... = a [*] x0"; by (simp!);
                finally; have "<0> = a [*] x0";.;
                thus ?thesis; by simp;
              qed; 
              finally; have "y = y [+] a [*] x0"; by simp;
              thus ?thesis; by simp;
            qed;
            finally; show ?thesis; .;
          qed;

        next; 
          assume gz: "0r < a"; hence nz: "a ~= 0r"; by force;
          show ?thesis;
          proof -;
            from a2; have "xi <= p (rinv a [*] y [+] x0) - h (rinv a [*] y)";
            proof (rule bspec);
              show "rinv a [*] y : H"; ..;
            qed;
            with gz; have "a * xi <= a * (p (rinv a [*] y [+] x0) - h (rinv a [*] y))";
              by (rule real_mult_less_le_mono);
            also; have "... = a * (p (rinv a [*] y [+] x0)) - a * (h (rinv a [*] y))";
              by (rule real_mult_diff_distrib2); 
            also; have "... = (rabs a) * (p (rinv a [*] y [+] x0)) - a * (h (rinv a [*] y))";
            proof -; 
              from gz; have "rabs a = a";
                by (rule rabs_eqI2); 
              thus ?thesis; by simp;
            qed;
            also; from prems; have "... =  p (a [*] (rinv a [*] y [+] x0)) - a * (h (rinv a [*] y))";
              by (simp, asm_simp_tac add: quasinorm_mult_distrib);
            also; have "... = p ((a * rinv a) [*] y [+] a [*] x0) - a * (h (rinv a [*] y))"; 
            proof simp;
              have "a [*] (rinv a [*] y [+] x0) = a [*] rinv a [*] y [+] a [*] x0";
                by (rule vs_add_mult_distrib1) (simp!)+;
              also; have "... = (a * rinv a) [*] y [+] a [*] x0";
                by (simp!);
              finally; have "a [*] (rinv a [*] y [+] x0) = (a * rinv a) [*] y [+] a [*] x0";.;
              thus "p (a [*] (rinv a [*] y [+] x0)) = p ((a * rinv a) [*] y [+] a [*] x0)";
                by simp;
            qed;
            also; from nz; have "... = p (y [+] a [*] x0) - (a * (h (rinv a [*] y)))"; 
              by (simp!);
            also; from nz; have "... = p (y [+] a [*] x0) - (h y)"; 
            proof (simp!);
              have "a * (h (rinv a [*] y)) = h (a [*] (rinv a [*] y))"; 
                by (rule linearform_mult_linear [RS sym]) (simp!)+;
              also; have "... = h y"; 
              proof -;
                from nz; have "a [*] (rinv a [*] y) = y"; by (simp!);
                thus ?thesis; by simp;
              qed;
              finally; have "a * (h (rinv a [*] y)) = h y"; .;
              thus "- (a * (h (rinv a [*] y))) = - (h y)"; by simp;
            qed;
            finally; have "a * xi <= p (y [+] a [*] x0) - h y"; .;
            hence "h y + a * xi <= h y + (p (y [+] a [*] x0) - h y)";
              by (rule real_add_left_cancel_le [RS iffD2]); (* arith *)
            thus ?thesis; 
              by force;
          qed;
        qed;
        also; have "... = p x"; by (simp!);
        finally; show ?thesis; .;
      qed; 
    qed;
  qed; 
qed blast+;


end;