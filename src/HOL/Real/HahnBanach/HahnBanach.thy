(*  Title:      HOL/Real/HahnBanach/HahnBanach.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

theory HahnBanach = HahnBanach_lemmas + HahnBanach_h0_lemmas:;


theorems [elim!!] = psubsetI;

theorem hahnbanach: 
  "[| is_vectorspace E; is_subspace F E; is_quasinorm E p; is_linearform F f;
      ALL x:F. f x <= p x |]
  ==> EX h. is_linearform E h
          & (ALL x:F. h x = f x)
          & (ALL x:E. h x <= p x)";
proof -;
  assume "is_vectorspace E" "is_subspace F E" "is_quasinorm E p" "is_linearform F f"
    and "ALL x:F. f x <= p x";
  def M == "norm_prev_extensions E p F f";
 
  have aM: "graph F f : norm_prev_extensions E p F f";
  proof (rule norm_prev_extensionI2);
    show "is_subspace F F"; 
    proof;
      show "is_vectorspace F"; ..;
    qed;
  qed (blast!)+;


  sect {* Part I a of the proof of the Hahn-Banach Theorem, 
     H. Heuser, Funktionalanalysis, p.231 *};


  have "!! (c:: 'a graph set). c : chain M ==> EX x. x:c ==> (Union c) : M";  
  proof -;
    fix c; assume "c:chain M"; assume "EX x. x:c";
    show "(Union c) : M"; 

    proof (unfold M_def, rule norm_prev_extensionI);
      show "EX (H::'a set) h::'a => real. graph H h = Union c
              & is_linearform H h 
              & is_subspace H E 
              & is_subspace F H 
              & (graph F f <= graph H h)
              & (ALL x::'a:H. h x <= p x)" (is "EX (H::'a set) h::'a => real. ?Q H h");
      proof;
        let ?H = "domain (Union c)";
	show "EX h. ?Q ?H h";
	proof;
	  let ?h = "funct (Union c)";
	  show "?Q ?H ?h";
	  proof (intro conjI);
 	    show a: "graph ?H ?h = Union c"; 
            proof (rule graph_domain_funct);
              fix x y z; assume "(x, y) : Union c" "(x, z) : Union c";
              show "z = y"; by (rule sup_uniq);
            qed;
            
	    show "is_linearform ?H ?h";
              by (simp! add: sup_lf a);       

	    show "is_subspace ?H E";
              by (rule sup_subE, rule a) (simp!)+;

	    show "is_subspace F ?H";
              by (rule sup_supF, rule a) (simp!)+;

	    show "graph F f <= graph ?H ?h";       
               by (rule sup_ext, rule a) (simp!)+;

	    show "ALL x::'a:?H. ?h x <= p x"; 
               by (rule sup_norm_prev, rule a) (simp!)+;
	  qed;
	qed;
      qed;
    qed;
  qed;
      
  
  with aM; have bex_g: "EX g:M. ALL x:M. g <= x --> g = x";
    by (simp! add: Zorn's_Lemma);
  thus ?thesis;
  proof;
    fix g; assume g: "g:M" "ALL x:M. g <= x --> g = x";
 
    have ex_Hh: "EX H h. graph H h = g 
                         & is_linearform H h 
                         & is_subspace H E 
                         & is_subspace F H
                         & (graph F f <= graph H h)
                         & (ALL x:H. h x <= p x) "; 
      by (simp! add: norm_prev_extension_D);
    thus ?thesis;
    proof (elim exE conjE);
      fix H h; assume "graph H h = g" "is_linearform (H::'a set) h"
	"is_subspace H E" "is_subspace F H"
        "(graph F f <= graph H h)"; assume h_bound: "ALL x:H. h x <= p x";
      show ?thesis; 
      proof;
        have h: "is_vectorspace H"; ..;
        have f: "is_vectorspace F"; ..;


        sect {* Part I a of the proof of the Hahn-Banach Theorem,
            H. Heuser, Funktionalanalysis, p.230 *};

	have eq: "H = E"; 
	proof (rule classical);
          assume "H ~= E";
          show ?thesis; 
          proof -;
            have "EX x:M. g <= x & g ~= x";
            proof -;
	      have "EX H0 h0. g <= graph H0 h0 & g ~= graph H0 h0 & graph H0 h0 : M";
	      proof-;
                have "H <= E"; ..;
                hence "H < E"; ..;
                hence "EX x0:E. x0~:H"; by (rule set_less_imp_diff_not_empty);
                thus ?thesis;
                proof;
                  fix x0; assume "x0:E" "x0~:H";
                  have x0:  "x0 ~= <0>";
                  proof (rule classical);
                    presume "x0 = <0>";
                    also; have "<0> : H"; ..;
                    finally; have "x0 : H"; .;
                    thus ?thesis; by contradiction;
                  qed force;

       		  def H0 == "vectorspace_sum H (lin x0)";
                  have "EX h0. g <= graph H0 h0 & g ~= graph H0 h0 & graph H0 h0 : M"; 
                  proof -;
                    from h; have xi: "EX xi. (ALL y:H. - p (y [+] x0) - h y <= xi) 
                                   & (ALL y:H. xi <= p (y [+] x0) - h y)"; 
                    proof (rule ex_xi);
                      fix u v; assume "u:H" "v:H"; 
                      show "- p (u [+] x0) - h u <= p (v [+] x0) - h v";
                      proof -;
                        show "!! a b c d::real. d - b <= c + a ==> - a - b <= c - d";
                        proof -; (* arith *)
			  fix a b c d; assume "d - b <= c + (a::real)";
                          have "- a - b = d - b + (- d - a)"; by (simp!);
                          also; have "... <= c + a + (- d - a)";
                            by (rule real_add_le_mono1);
                          also; have "... = c - d"; by (simp!);
                          finally; show "- a - b <= c - d"; .;
                        qed;
                        show "h v - h u <= p (v [+] x0) + p (u [+] x0)"; 
                        proof -;
                          from h; have "h v - h u = h (v [-] u)";
                            by  (rule linearform_diff_linear [RS sym]);
                          also; have "... <= p (v [-] u)";
			  proof -;  
			    from h; have "v [-] u : H"; by (simp!); 
                            with h_bound; show ?thesis; ..;
			  qed;
                          also; have "v [-] u  = x0 [+] [-] x0 [+] v [+] [-] u"; 
                            by (simp! add: vs_add_minus_eq_diff);
                          also; have "... = v [+] x0 [+] [-] (u [+] x0)"; 
                            by (simp!);
                          also; have "... = (v [+] x0) [-] (u [+] x0)";  
                            by (simp! only: vs_add_minus_eq_diff);
                          also; have "p ... <= p (v [+] x0) + p (u [+] x0)"; 
                            by (rule quasinorm_diff_triangle_ineq) (simp!)+;
                          finally; show ?thesis; .;
                        qed;
                      qed;
                    qed;
                    
                    thus ?thesis;
                    proof (elim exE, intro exI conjI);
                      fix xi; assume a: "(ALL y:H. - p (y [+] x0) - h y <= xi) &
                                         (ALL y:H. xi <= p (y [+] x0) - h y)";
                      def h0 == "%x. let (y, a) = @ (y, a). (x = y [+] a [*] x0 & y:H )
                                            in (h y) + a * xi";

	              have "graph H h <= graph H0 h0"; 
                      proof (rule graph_extI);
                        fix t; assume "t:H"; 
                        show "h t = h0 t";
                        proof -;
                          have "(@ (y, a). t = y [+] a [*] x0 & y : H) = (t, 0r)";
                            by (rule decomp1, rule x0); 
                          thus ?thesis; by (simp! add: Let_def);
                        qed;
                      next;
                        show "H <= H0";
		        proof (rule subspace_subset);
			  show "is_subspace H H0";
			  proof (unfold H0_def, rule subspace_vs_sum1);
			    show "is_vectorspace H"; ..;
			    show "is_vectorspace (lin x0)"; ..;
			  qed;
			qed;
		      qed;
                      thus "g <= graph H0 h0"; by (simp!);

                      have "graph H h ~= graph H0 h0";
                      proof;
                        assume "graph H h = graph H0 h0";
                        have x1: "(x0, h0 x0) : graph H0 h0";
                        proof (rule graphI);
                          show "x0:H0";
                          proof (unfold H0_def, rule vs_sumI);
                            from h; show "<0> : H"; ..;
                            show "x0 : lin x0"; by (rule x_lin_x);
                            show "x0 = <0> [+] x0"; by (simp!);
                          qed;
                        qed;
                        have "(x0, h0 x0) ~: graph H h";
                        proof;
                          assume "(x0, h0 x0) : graph H h";
                          have "x0:H"; ..;
                          thus "False"; by contradiction;
                        qed;
                        hence "(x0, h0 x0) ~: graph H0 h0"; by (simp!);
                        with x1; show "False"; by contradiction;
                      qed;
                      thus "g ~= graph H0 h0"; by (simp!);

                      have "graph H0 h0 : norm_prev_extensions E p F f";
                      proof (rule norm_prev_extensionI2);

                        show "is_linearform H0 h0";
                          by (rule h0_lf, rule x0) (simp!)+;

                        show "is_subspace H0 E";
                        proof -;
                        have "is_subspace (vectorspace_sum H (lin x0)) E"; 
			  by (rule vs_sum_subspace, rule lin_subspace);
                          thus ?thesis; by (simp!);
                        qed;

                        show f_h0: "is_subspace F H0";
                        proof (rule subspace_trans [of F H H0]);
                          from h lin_vs; have "is_subspace H (vectorspace_sum H (lin x0))";
                            by (rule subspace_vs_sum1);
                          thus "is_subspace H H0"; by (simp!);
                        qed;

                        show "graph F f <= graph H0 h0";
                        proof(rule graph_extI);
                          fix x; assume "x:F";
                          show "f x = h0 x";
                          proof -;
                            have "x:H"; 
                            proof (rule subsetD);
                              show "F <= H"; ..;
                            qed;
                            have eq: "(@ (y, a). x = y [+] a [*] x0 & y : H) = (x, 0r)";
                              by (rule decomp1, rule x0) (simp!)+;
 
                            have "h0 x = (let (y,a) = @ (y,a). x = y [+] a [*] x0 & y : H
                                          in h y + a * xi)"; 
                              by (simp!);
                            also; from eq; have "... = (let (y,a) = (x, 0r) in h y + a * xi)";
                              by simp;
                            also; have " ... = h x + 0r * xi";
                              by (simp! add: Let_def);
                            also; have "... = h x"; by (simp!);
                            also; have "... = f x"; 
                            proof (rule sym);
                              show "f x = h x"; ..;
                            qed;
                            finally; show ?thesis; by (rule sym);
                          qed;
                        next;
                          from f_h0; show "F <= H0"; ..;
                        qed;

                        show "ALL x:H0. h0 x <= p x";
                          by (rule h0_norm_prev, rule x0) (assumption | (simp!))+;
                      qed;
                      thus "graph H0 h0 : M"; by (simp!);
                    qed;
                  qed;
                  thus ?thesis; ..;
                qed;
              qed;

              thus ?thesis;
                by (elim exE conjE, intro bexI conjI);
            qed;
            hence "~ (ALL x:M. g <= x --> g = x)"; by force;
            thus ?thesis; by contradiction;
          qed;
	qed; 

        show "is_linearform E h & (ALL x:F. h x = f x) & (ALL x:E. h x <= p x)";
        proof (intro conjI); 
          from eq; show "is_linearform E h"; by (simp!);
          show "ALL x:F. h x = f x"; 
          proof (intro ballI, rule sym);
            fix x; assume "x:F"; show "f x = h x "; ..;
          qed;
          from eq; show "ALL x:E. h x <= p x"; by (force!);
        qed;
      qed;  
    qed; 
  qed;
qed;


theorem rabs_hahnbanach:
  "[| is_vectorspace E; is_subspace F E; is_quasinorm E p; is_linearform F f;
     ALL x:F. rabs (f x) <= p x |]
 ==> EX g. is_linearform E g
         & (ALL x:F. g x = f x)
         & (ALL x:E. rabs (g x) <= p x)";
proof -; 

 sect {* Part I (for real linear spaces) of the proof of the Hahn-banach Theorem,
   H. Heuser, Funktionalanalysis, p.229 *};

  assume e: "is_vectorspace E"; 
  assume "is_subspace F E" "is_quasinorm E p" "is_linearform F f" "ALL x:F. rabs (f x) <= p x";
  have "ALL x:F. f x <= p x"; by (rule rabs_ineq [RS iffD1]);
  hence  "EX g. is_linearform E g & (ALL x:F. g x = f x) & (ALL x:E. g x <= p x)";
    by (simp! only: hahnbanach);
  thus ?thesis;
  proof (elim exE conjE);
    fix g; assume "is_linearform E g" "ALL x:F. g x = f x" "ALL x:E. g x <= p x";
    show ?thesis;
    proof (intro exI conjI)+;
      from e; show "ALL x:E. rabs (g x) <= p x"; 
        by (simp! add: rabs_ineq [OF subspace_refl]);
    qed;
  qed;
qed;


theorem norm_hahnbanach:
  "[| is_normed_vectorspace E norm; is_subspace F E; is_linearform F f;
      is_continous F norm f |] 
  ==> EX g. is_linearform E g
         & is_continous E norm g 
         & (ALL x:F. g x = f x) 
         & function_norm E norm g = function_norm F norm f"
  (concl is "EX g::'a=>real. ?P g");

proof -;
sect {* Proof of the Hahn-Banach Theorem for normed spaces,
   H. Heuser, Funktionalanalysis, p.232 *};

  assume a: "is_normed_vectorspace E norm";
  assume b: "is_subspace F E" "is_linearform F f";
  assume c: "is_continous F norm f";
  have e: "is_vectorspace E"; ..;
  from _ e;
  have f: "is_normed_vectorspace F norm"; ..;
  def p == "%x::'a. (function_norm F norm f) * norm x";
  
  let ?P' = "%g. is_linearform E g & (ALL x:F. g x = f x) & (ALL x:E. rabs (g x) <= p x)";

  have q: "is_quasinorm E p";
  proof;
    fix x y a; assume "x:E" "y:E";

    show "0r <= p x";
    proof (unfold p_def, rule real_le_mult_order);
      from _ f; show "0r <= function_norm F norm f"; ..;
      show "0r <= norm x"; ..;
    qed;

    show "p (a [*] x) = (rabs a) * (p x)";
    proof -; 
      have "p (a [*] x) = (function_norm F norm f) * norm (a [*] x)"; by (simp!);
      also; have "norm (a [*] x) = rabs a * norm x"; by (rule normed_vs_norm_mult_distrib);
      also; have "(function_norm F norm f) * ... = rabs a * ((function_norm F norm f) * norm x)";
        by (simp! only: real_mult_left_commute);
      also; have "... = (rabs a) * (p x)"; by (simp!);
      finally; show ?thesis; .;
    qed;

    show "p (x [+] y) <= p x + p y";
    proof -;
      have "p (x [+] y) = (function_norm F norm f) * norm (x [+] y)"; by (simp!);
      also; have "... <=  (function_norm F norm f) * (norm x + norm y)";
      proof (rule real_mult_le_le_mono1);
        from _ f; show "0r <= function_norm F norm f"; ..;
        show "norm (x [+] y) <= norm x + norm y"; ..;
      qed;
      also; have "... = (function_norm F norm f) * (norm x) + (function_norm F norm f) * (norm y)";
        by (simp! only: real_add_mult_distrib2);
      finally; show ?thesis; by (simp!);
    qed;
  qed;
 
  have "ALL x:F. rabs (f x) <= p x";
  proof;
    fix x; assume "x:F";
     from f; show "rabs (f x) <= p x"; by (simp! add: norm_fx_le_norm_f_norm_x);
  qed;

  with e b q; have "EX g. ?P' g";
    by (simp! add: rabs_hahnbanach);

  thus "?thesis";
  proof (elim exE conjE, intro exI conjI);
    fix g;
    assume "is_linearform E g" and a: "ALL x:F. g x = f x" and "ALL x:E. rabs (g x) <= p x";
    show ce: "is_continous E norm g";
    proof (rule lipschitz_continousI);
      fix x; assume "x:E";
      show "rabs (g x) <= function_norm F norm f * norm x";
        by (rule bspec [of _ _ x], (simp!));
    qed;
    show "function_norm E norm g = function_norm F norm f";
    proof (rule order_antisym);
      from _ ce; show "function_norm E norm g <= function_norm F norm f";
      proof (rule fnorm_le_ub);
        show "ALL x:E. rabs (g x) <=  function_norm F norm f * norm x";
        proof;
          fix x; assume "x:E"; 
          show "rabs (g x) <= function_norm F norm f * norm x";
            by (rule bspec [of _ _ x], (simp!));
        qed;
        from c f; show "0r <= function_norm F norm f"; ..;
      qed;
      show "function_norm F norm f <= function_norm E norm g"; 
      proof (rule fnorm_le_ub);
        show "ALL x:F. rabs (f x) <=  function_norm E norm g * norm x";
        proof;
          fix x; assume "x : F"; 
          from a; have "g x = f x"; ..;
          hence "rabs (f x) = rabs (g x)"; by simp;
          also; from _ _ ce; have "... <= function_norm E norm g * norm x"; 
          proof (rule norm_fx_le_norm_f_norm_x);
            show "x : E";
            proof (rule subsetD); 
              show "F <= E"; ..;
            qed;
          qed;
          finally; show "rabs (f x) <= function_norm E norm g * norm x"; .;
        qed;
        from _ e; show "is_normed_vectorspace F norm"; ..;
        from ce; show "0r <= function_norm E norm g"; ..;
      qed;
    qed;
  qed;
qed;


end;

