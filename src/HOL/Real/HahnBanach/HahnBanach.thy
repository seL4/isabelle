(*  Title:      HOL/Real/HahnBanach/HahnBanach.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* The Hahn-Banach Theorem *};

theory HahnBanach
     = HahnBanachSupLemmas + HahnBanachExtLemmas + ZornLemma:;

text {*
  We present the proof of two different versions of the Hahn-Banach 
  Theorem, closely following \cite[\S36]{Heuser:1986}.
*};

subsection {* The Hahn-Banach Theorem for vector spaces *};

text {* {\bf Theorem.} Let $f$ be a linear form defined on a subspace 
 $F$ of a real vector space $E$, such that $f$ is bounded by a seminorm 
 $p$. 

 Then $f$ can be extended  to a linear form $h$  on $E$ that is again
 bounded by $p$.

 \bigskip{\bf Proof Outline.}
 First we define the set $M$ of all norm-preserving extensions of $f$.
 We show that every chain in $M$ has an upper bound in $M$.
 With Zorn's lemma we can conclude that $M$ has a maximal element $g$.
 We further show by contradiction that the domain $H$ of $g$ is the whole
 vector space $E$. 
 If $H \neq E$, then $g$ can be extended in 
 a norm-preserving way to a greater vector space $H_0$. 
 So $g$ cannot be maximal in $M$.
 \bigskip
*};

theorem HahnBanach: "[| is_vectorspace E; is_subspace F E; 
 is_seminorm E p; is_linearform F f; ALL x:F. f x <= p x |]
  ==> EX h. is_linearform E h & (ALL x:F. h x = f x)
          & (ALL x:E. h x <= p x)";
proof -;

txt {* Let $E$ be a vector space, $F$ a subspace of $E$, $p$ a seminorm on $E$ and $f$ a linear form on $F$ such that $f$ is bounded by $p$. *};

  assume "is_vectorspace E" "is_subspace F E" "is_seminorm E p" 
    "is_linearform F f" "ALL x:F. f x <= p x";

txt {* Define $M$ as the set of all norm-preserving extensions of $F$.  *};

  def M == "norm_pres_extensions E p F f";
  {{;
    fix c; assume "c : chain M" "EX x. x:c";

txt {* Show that every non-empty chain $c$ in $M$ has an upper bound in $M$: $\Union c$ is greater that every element of the chain $c$, so $\Union c$ is an upper bound of $c$ that lies in $M$. *};

    have "Union c : M";
    proof (unfold M_def, rule norm_pres_extensionI);
      show "EX (H::'a set) h::'a => real. graph H h = Union c
              & is_linearform H h 
              & is_subspace H E 
              & is_subspace F H 
              & graph F f <= graph H h
              & (ALL x::'a:H. h x <= p x)";
      proof (intro exI conjI);
        let ?H = "domain (Union c)";
        let ?h = "funct (Union c)";

        show a: "graph ?H ?h = Union c"; 
        proof (rule graph_domain_funct);
          fix x y z; assume "(x, y) : Union c" "(x, z) : Union c";
          show "z = y"; by (rule sup_definite);
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
          by (rule sup_norm_pres, rule a) (simp!)+;
      qed;
    qed;
  }};
  
txt {* With Zorn's Lemma we can conclude that there is a maximal element $g$ in $M$. *};

  hence "EX g:M. ALL x:M. g <= x --> g = x";
  proof (rule Zorn's_Lemma);
    txt {* We show that $M$ is non-empty: *};
    have "graph F f : norm_pres_extensions E p F f";
    proof (rule norm_pres_extensionI2);
      have "is_vectorspace F"; ..;
      thus "is_subspace F F"; ..;
    qed (blast!)+; 
    thus "graph F f : M"; by (simp!);
  qed;
  thus ?thesis;
  proof;

txt {* We take this maximal element $g$.  *};

    fix g; assume "g:M" "ALL x:M. g <= x --> g = x";
    show ?thesis;

      txt {* $g$ is a norm-preserving extension of $f$, that is: $g$
      is the graph of a linear form $h$, defined on a subspace $H$ of
      $E$, which is a superspace of $F$. $h$ is an extension of $f$
      and $h$ is again bounded by $p$. *};

      obtain H h in "graph H h = g" and "is_linearform H h" 
        "is_subspace H E" "is_subspace F H" "graph F f <= graph H h" 
        "ALL x:H. h x <= p x";
      proof -;
        have "EX H h. graph H h = g & is_linearform H h 
          & is_subspace H E & is_subspace F H
          & graph F f <= graph H h
          & (ALL x:H. h x <= p x)"; by (simp! add: norm_pres_extension_D);
        thus ?thesis; by blast;
      qed;
      have h: "is_vectorspace H"; ..;

txt {* We show that $h$ is defined on whole $E$ by classical contradiction.  *}; 

      have "H = E"; 
      proof (rule classical);

	txt {* Assume $h$ is not defined on whole $E$. *};

        assume "H ~= E";

txt {* Then show that $h$ can be extended in a norm-preserving way to a function $h_0$ with the graph $g_{h0}$.  *};

        have "EX g_h0 : M. g <= g_h0 & g ~= g_h0"; 

	  txt {* Consider $x_0 \in E \setminus H$. *};

          obtain x0 in "x0:E" "x0~:H"; 
          proof -;
            have "EX x0:E. x0~:H";
            proof (rule set_less_imp_diff_not_empty);
              have "H <= E"; ..;
              thus "H < E"; ..;
            qed;
            thus ?thesis; by blast;
          qed;
          have x0: "x0 ~= <0>";
          proof (rule classical);
            presume "x0 = <0>";
            with h; have "x0:H"; by simp;
            thus ?thesis; by contradiction;
          qed blast;

txt {* Define $H_0$ as the direct sum of $H$ and the linear closure of $x_0$.  *};

          def H0 == "H + lin x0";
          show ?thesis;

	    txt {* Pick a real number $\xi$ that fulfills certain
	    inequations, which will be used to establish that $h_0$ is
	    a norm-preserving extension of $h$. *};

            obtain xi in "ALL y:H. - p (y + x0) - h y <= xi 
                              & xi <= p (y + x0) - h y";
            proof -;
	      from h; have "EX xi. ALL y:H. - p (y + x0) - h y <= xi 
                              & xi <= p (y + x0) - h y"; 
              proof (rule ex_xi);
                fix u v; assume "u:H" "v:H";
                from h; have "h v - h u = h (v - u)";
                  by (simp! add: linearform_diff);
                also; have "... <= p (v - u)";
                  by (simp!);
                also; have "v - u = x0 + - x0 + v + - u";
                  by (simp! add: diff_eq1);
                also; have "... = v + x0 + - (u + x0)";
                  by (simp!);
                also; have "... = (v + x0) - (u + x0)";
                  by (simp! add: diff_eq1);
                also; have "p ... <= p (v + x0) + p (u + x0)";
                  by (rule seminorm_diff_subadditive) (simp!)+;
                finally; have "h v - h u <= p (v + x0) + p (u + x0)"; .;

                thus "- p (u + x0) - h u <= p (v + x0) - h v";
                  by (rule real_diff_ineq_swap);
              qed;
              thus ?thesis; by blast;
            qed;

txt {* Define the extension $h_0$ of $h$ to $H_0$ using $\xi$.  *};

            def h0 == "\<lambda>x. let (y,a) = SOME (y, a). x = y + a <*> x0 
                                                  & y:H
                           in (h y) + a * xi";
            show ?thesis;
            proof;
 
txt {* Show that $h_0$ is an extension of $h$  *};
 
              show "g <= graph H0 h0 & g ~= graph H0 h0";
              proof;
		show "g <= graph H0 h0";
		proof -;
		  have  "graph H h <= graph H0 h0";
                  proof (rule graph_extI);
		    fix t; assume "t:H"; 
		    have "(SOME (y, a). t = y + a <*> x0 & y : H) 
                         = (t,0r)";
		      by (rule decomp_H0_H, rule x0); 
		    thus "h t = h0 t"; by (simp! add: Let_def);
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
		  thus ?thesis; by (simp!);
		qed;
                show "g ~= graph H0 h0";
		proof -;
		  have "graph H h ~= graph H0 h0";
		  proof;
		    assume e: "graph H h = graph H0 h0";
		    have "x0 : H0"; 
		    proof (unfold H0_def, rule vs_sumI);
		      show "x0 = <0> + x0"; by (simp!);
		      from h; show "<0> : H"; ..;
		      show "x0 : lin x0"; by (rule x_lin_x);
		    qed;
		    hence "(x0, h0 x0) : graph H0 h0"; ..;
		    with e; have "(x0, h0 x0) : graph H h"; by simp;
		    hence "x0 : H"; ..;
		    thus False; by contradiction;
		  qed;
		  thus ?thesis; by (simp!);
		qed;
              qed;
	      
txt {* and $h_0$ is norm-preserving.  *}; 

              show "graph H0 h0 : M";
	      proof -;
		have "graph H0 h0 : norm_pres_extensions E p F f";
		proof (rule norm_pres_extensionI2);
		  show "is_linearform H0 h0";
		    by (rule h0_lf, rule x0) (simp!)+;
		  show "is_subspace H0 E";
		    by (unfold H0_def, rule vs_sum_subspace, 
                        rule lin_subspace);
		  have "is_subspace F H"; .;
		  also; from h lin_vs; 
		  have [fold H0_def]: "is_subspace H (H + lin x0)"; ..;
		  finally (subspace_trans [OF _ h]); 
		  show f_h0: "is_subspace F H0"; .;
		
		  show "graph F f <= graph H0 h0";
		  proof (rule graph_extI);
		    fix x; assume "x:F";
		    have "f x = h x"; ..;
		    also; have " ... = h x + 0r * xi"; by simp;
		    also; have "... = (let (y,a) = (x, 0r) in h y + a * xi)";
		      by (simp add: Let_def);
		    also; have 
		      "(x, 0r) = (SOME (y, a). x = y + a <*> x0 & y : H)";
		      by (rule decomp_H0_H [RS sym], rule x0) (simp!)+;
		    also; have 
		      "(let (y,a) = (SOME (y,a). x = y + a <*> x0 & y : H)
                        in h y + a * xi) 
                      = h0 x"; by (simp!);
		    finally; show "f x = h0 x"; .;
		  next;
		    from f_h0; show "F <= H0"; ..;
		  qed;
		
		  show "ALL x:H0. h0 x <= p x";
		    by (rule h0_norm_pres, rule x0);
		qed;
		thus "graph H0 h0 : M"; by (simp!);
	      qed;
            qed;
          qed;
        qed;

txt {* So the graph $g$ of $h$ cannot be maximal. Contradiction.  *}; 

        hence "~ (ALL x:M. g <= x --> g = x)"; by simp;
        thus ?thesis; by contradiction;
      qed; 

txt {* Now we have a linear extension $h$ of $f$ to $E$ that is 
bounded by $p$. *};

      thus "EX h. is_linearform E h & (ALL x:F. h x = f x) 
                & (ALL x:E. h x <= p x)";
      proof (intro exI conjI);
        assume eq: "H = E";
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
(*
theorem HahnBanach: 
  "[| is_vectorspace E; is_subspace F E; is_seminorm E p; 
  is_linearform F f; ALL x:F. f x <= p x |]
  ==> EX h. is_linearform E h
          & (ALL x:F. h x = f x)
          & (ALL x:E. h x <= p x)";
proof -;
  assume "is_vectorspace E" "is_subspace F E" "is_seminorm E p"
         "is_linearform F f" "ALL x:F. f x <= p x";
  
  txt{* We define $M$ to be the set of all linear extensions 
  of $f$ to superspaces of $F$, which are bounded by $p$. *};

  def M == "norm_pres_extensions E p F f";
  
  txt{* We show that $M$ is non-empty: *};
 
  have aM: "graph F f : norm_pres_extensions E p F f";
  proof (rule norm_pres_extensionI2);
    have "is_vectorspace F"; ..;
    thus "is_subspace F F"; ..;
  qed (blast!)+;

  subsubsect {* Existence of a limit function *}; 

  txt {* For every non-empty chain of norm-preserving extensions
  the union of all functions in the chain is again a norm-preserving
  extension. (The union is an upper bound for all elements. 
  It is even the least upper bound, because every upper bound of $M$
  is also an upper bound for $\Union c$, as $\Union c\in M$) *};

  {{;
    fix c; assume "c:chain M" "EX x. x:c";
    have "Union c : M";

    proof (unfold M_def, rule norm_pres_extensionI);
      show "EX (H::'a set) h::'a => real. graph H h = Union c
              & is_linearform H h 
              & is_subspace H E 
              & is_subspace F H 
              & graph F f <= graph H h
              & (ALL x::'a:H. h x <= p x)";
      proof (intro exI conjI);
        let ?H = "domain (Union c)";
        let ?h = "funct (Union c)";

        show a: "graph ?H ?h = Union c"; 
        proof (rule graph_domain_funct);
          fix x y z; assume "(x, y) : Union c" "(x, z) : Union c";
          show "z = y"; by (rule sup_definite);
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
          by (rule sup_norm_pres, rule a) (simp!)+;
      qed;
    qed;
  }};
 
  txt {* According to Zorn's Lemma there is
  a maximal norm-preserving extension $g\in M$. *};
  
  with aM; have bex_g: "EX g:M. ALL x:M. g <= x --> g = x";
    by (simp! add: Zorn's_Lemma);

  thus ?thesis;
  proof;
    fix g; assume g: "g:M" "ALL x:M. g <= x --> g = x";
 
    have ex_Hh: 
      "EX H h. graph H h = g 
           & is_linearform H h 
           & is_subspace H E 
           & is_subspace F H
           & graph F f <= graph H h
           & (ALL x:H. h x <= p x) "; 
      by (simp! add: norm_pres_extension_D);
    thus ?thesis;
    proof (elim exE conjE, intro exI);
      fix H h; 
      assume "graph H h = g" "is_linearform (H::'a set) h" 
             "is_subspace H E" "is_subspace F H"
        and h_ext: "graph F f <= graph H h"
        and h_bound: "ALL x:H. h x <= p x";

      have h: "is_vectorspace H"; ..;
      have f: "is_vectorspace F"; ..;

subsubsect {* The domain of the limit function *};

have eq: "H = E"; 
proof (rule classical);

txt {* Assume that the domain of the supremum is not $E$, *};

  assume "H ~= E";
  have "H <= E"; ..;
  hence "H < E"; ..;
 
  txt{* then there exists an element $x_0$ in $E \setminus H$: *};

  hence "EX x0:E. x0~:H"; 
    by (rule set_less_imp_diff_not_empty);

  txt {* We get that $h$ can be extended  in a 
  norm-preserving way to some $H_0$. *};

  hence "EX H0 h0. g <= graph H0 h0 & g ~= graph H0 h0 
                 & graph H0 h0 : M";
  proof;
    fix x0; assume "x0:E" "x0~:H";

    have x0: "x0 ~= <0>";
    proof (rule classical);
      presume "x0 = <0>";
      with h; have "x0:H"; by simp;
      thus ?thesis; by contradiction;
    qed blast;

    txt {* Define $H_0$ as the (direct) sum of H and the 
    linear closure of $x_0$. \label{ex-xi-use}*};

    def H0 == "H + lin x0";

    from h; have xi: "EX xi. ALL y:H. - p (y + x0) - h y <= xi 
                                    & xi <= p (y + x0) - h y";
    proof (rule ex_xi);
      fix u v; assume "u:H" "v:H";
      from h; have "h v - h u = h (v - u)";
         by (simp! add: linearform_diff);
      also; from h_bound; have "... <= p (v - u)";
        by (simp!);
      also; have "v - u = x0 + - x0 + v + - u";
        by (simp! add: diff_eq1);
      also; have "... = v + x0 + - (u + x0)";
        by (simp!);
      also; have "... = (v + x0) - (u + x0)";
        by (simp! add: diff_eq1);
      also; have "p ... <= p (v + x0) + p (u + x0)";
         by (rule seminorm_diff_subadditive) (simp!)+;
      finally; have "h v - h u <= p (v + x0) + p (u + x0)"; .;

      thus "- p (u + x0) - h u <= p (v + x0) - h v";
        by (rule real_diff_ineq_swap);
    qed;
    hence "EX h0. g <= graph H0 h0 & g ~= graph H0 h0
               & graph H0 h0 : M"; 
    proof (elim exE, intro exI conjI);
      fix xi; 
      assume a: "ALL y:H. - p (y + x0) - h y <= xi 
                        & xi <= p (y + x0) - h y";
     
      txt {* Define $h_0$ as the canonical linear extension 
      of $h$ on $H_0$:*};  

      def h0 ==
          "\<lambda>x. let (y,a) = SOME (y, a). x = y + a <*> x0 & y:H
               in (h y) + a * xi";

      txt {* We get that the graph of $h_0$ extends that of
      $h$. *};
        
      have  "graph H h <= graph H0 h0"; 
      proof (rule graph_extI);
        fix t; assume "t:H"; 
        have "(SOME (y, a). t = y + a <*> x0 & y : H) = (t,0r)";
          by (rule decomp_H0_H, rule x0); 
        thus "h t = h0 t"; by (simp! add: Let_def);
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

      txt {* Apparently $h_0$ is not equal to $h$. *};

      have "graph H h ~= graph H0 h0";
      proof;
        assume e: "graph H h = graph H0 h0";
        have "x0 : H0"; 
        proof (unfold H0_def, rule vs_sumI);
          show "x0 = <0> + x0"; by (simp!);
          from h; show "<0> : H"; ..;
          show "x0 : lin x0"; by (rule x_lin_x);
        qed;
        hence "(x0, h0 x0) : graph H0 h0"; ..;
        with e; have "(x0, h0 x0) : graph H h"; by simp;
        hence "x0 : H"; ..;
        thus False; by contradiction;
      qed;
      thus "g ~= graph H0 h0"; by (simp!);

      txt {* Furthermore  $h_0$ is a norm-preserving extension 
     of $f$. *};

      have "graph H0 h0 : norm_pres_extensions E p F f";
      proof (rule norm_pres_extensionI2);
        show "is_linearform H0 h0";
          by (rule h0_lf, rule x0) (simp!)+;
        show "is_subspace H0 E";
          by (unfold H0_def, rule vs_sum_subspace, 
             rule lin_subspace);

        have "is_subspace F H"; .;
        also; from h lin_vs; 
	have [fold H0_def]: "is_subspace H (H + lin x0)"; ..;
        finally (subspace_trans [OF _ h]); 
	show f_h0: "is_subspace F H0"; .; (*** 
        backwards:
        show f_h0: "is_subspace F H0"; .;
        proof (rule subspace_trans [of F H H0]);
          from h lin_vs; 
          have "is_subspace H (H + lin x0)"; ..;
          thus "is_subspace H H0"; by (unfold H0_def);
        qed; ***)

        show "graph F f <= graph H0 h0";
        proof (rule graph_extI);
          fix x; assume "x:F";
          have "f x = h x"; ..;
          also; have " ... = h x + 0r * xi"; by simp;
          also; have "... = (let (y,a) = (x, 0r) in h y + a * xi)";
            by (simp add: Let_def);
          also; have 
            "(x, 0r) = (SOME (y, a). x = y + a <*> x0 & y : H)";
            by (rule decomp_H0_H [RS sym], rule x0) (simp!)+;
          also; have 
            "(let (y,a) = (SOME (y,a). x = y + a <*> x0 & y : H)
              in h y + a * xi) 
             = h0 x"; by (simp!);
          finally; show "f x = h0 x"; .;
        next;
          from f_h0; show "F <= H0"; ..;
        qed;

        show "ALL x:H0. h0 x <= p x";
          by (rule h0_norm_pres, rule x0) (assumption | simp!)+;
      qed;
      thus "graph H0 h0 : M"; by (simp!);
    qed;
    thus ?thesis; ..;
  qed;

  txt {* We have shown that $h$ can still be extended to 
  some $h_0$, in contradiction to the assumption that 
  $h$ is a maximal element. *};

  hence "EX x:M. g <= x & g ~= x"; 
    by (elim exE conjE, intro bexI conjI);
  hence "~ (ALL x:M. g <= x --> g = x)"; by simp;
  thus ?thesis; by contradiction;
qed; 

txt{* It follows $H = E$, and the thesis can be shown. *};

show "is_linearform E h & (ALL x:F. h x = f x) 
     & (ALL x:E. h x <= p x)";
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
*)


subsection  {* Alternative formulation *};

text {* The following alternative formulation of the Hahn-Banach
Theorem\label{rabs-HahnBanach} uses the fact that for a real linear form
$f$ and a seminorm $p$ the
following inequations are equivalent:\footnote{This was shown in lemma
$\idt{rabs{\dsh}ineq{\dsh}iff}$ (see page \pageref{rabs-ineq-iff}).}
\begin{matharray}{ll}
\forall x\in H.\ap |h\ap x|\leq p\ap x& {\rm and}\\
\forall x\in H.\ap h\ap x\leq p\ap x\\
\end{matharray}
*};

theorem rabs_HahnBanach:
  "[| is_vectorspace E; is_subspace F E; is_linearform F f; 
  is_seminorm E p; ALL x:F. rabs (f x) <= p x |]
  ==> EX g. is_linearform E g & (ALL x:F. g x = f x)
   & (ALL x:E. rabs (g x) <= p x)";
proof -;
  assume "is_vectorspace E" "is_subspace F E" "is_seminorm E p" 
    "is_linearform F f"  "ALL x:F. rabs (f x) <= p x";
  have "ALL x:F. f x <= p x";  by (rule rabs_ineq_iff [RS iffD1]);
  hence "EX g. is_linearform E g & (ALL x:F. g x = f x) 
              & (ALL x:E. g x <= p x)";
    by (simp! only: HahnBanach);
  thus ?thesis; 
  proof (elim exE conjE);
    fix g; assume "is_linearform E g" "ALL x:F. g x = f x" 
                  "ALL x:E. g x <= p x";
    hence "ALL x:E. rabs (g x) <= p x";
      by (simp! add: rabs_ineq_iff [OF subspace_refl]);
    thus ?thesis; by (intro exI conjI);
  qed;
qed;

subsection {* The Hahn-Banach Theorem for normed spaces *};

text {* Every continuous linear form $f$ on a subspace $F$ of a
norm space $E$, can be extended to a continuous linear form $g$ on
$E$ such that $\fnorm{f} = \fnorm {g}$. *};

theorem norm_HahnBanach:
  "[| is_normed_vectorspace E norm; is_subspace F E; 
  is_linearform F f; is_continuous F norm f |] 
  ==> EX g. is_linearform E g
         & is_continuous E norm g 
         & (ALL x:F. g x = f x) 
         & function_norm E norm g = function_norm F norm f";
proof -;
  assume e_norm: "is_normed_vectorspace E norm";
  assume f: "is_subspace F E" "is_linearform F f";
  assume f_cont: "is_continuous F norm f";
  have e: "is_vectorspace E"; ..;
  with _; have f_norm: "is_normed_vectorspace F norm"; ..;

  txt{* We define a function $p$ on $E$ as follows:
  \begin{matharray}{l}
  p \: x = \fnorm f \cdot \norm x\\
  \end{matharray}
  *};

  def p == "\<lambda>x. function_norm F norm f * norm x";
  
  txt{* $p$ is a seminorm on $E$: *};

  have q: "is_seminorm E p";
  proof;
    fix x y a; assume "x:E" "y:E";

    txt{* $p$ is positive definite: *};

    show "0r <= p x";
    proof (unfold p_def, rule real_le_mult_order);
      from _ f_norm; show "0r <= function_norm F norm f"; ..;
      show "0r <= norm x"; ..;
    qed;

    txt{* $p$ is absolutely homogenous: *};

    show "p (a <*> x) = rabs a * p x";
    proof -; 
      have "p (a <*> x) = function_norm F norm f * norm (a <*> x)";
        by (simp!);
      also; have "norm (a <*> x) = rabs a * norm x"; 
        by (rule normed_vs_norm_rabs_homogenous);
      also; have "function_norm F norm f * (rabs a * norm x) 
        = rabs a * (function_norm F norm f * norm x)";
        by (simp! only: real_mult_left_commute);
      also; have "... = rabs a * p x"; by (simp!);
      finally; show ?thesis; .;
    qed;

    txt{* Furthermore, $p$ is subadditive: *};

    show "p (x + y) <= p x + p y";
    proof -;
      have "p (x + y) = function_norm F norm f * norm (x + y)";
        by (simp!);
      also; 
      have "... <= function_norm F norm f * (norm x + norm y)";
      proof (rule real_mult_le_le_mono1);
        from _ f_norm; show "0r <= function_norm F norm f"; ..;
        show "norm (x + y) <= norm x + norm y"; ..;
      qed;
      also; have "... = function_norm F norm f * norm x 
                        + function_norm F norm f * norm y";
        by (simp! only: real_add_mult_distrib2);
      finally; show ?thesis; by (simp!);
    qed;
  qed;

  txt{* $f$ is bounded by $p$. *}; 

  have "ALL x:F. rabs (f x) <= p x";
  proof;
    fix x; assume "x:F";
     from f_norm; show "rabs (f x) <= p x"; 
       by (simp! add: norm_fx_le_norm_f_norm_x);
  qed;

  txt{* Using the fact that $p$ is a seminorm and 
  $f$ is bounded by $p$ we can apply the Hahn-Banach Theorem 
  for real vector spaces. 
  So $f$ can be extended in a norm-preserving way to some function
  $g$ on the whole vector space $E$. *};

  with e f q; 
  have "EX g. is_linearform E g & (ALL x:F. g x = f x) 
            & (ALL x:E. rabs (g x) <= p x)";
    by (simp! add: rabs_HahnBanach);

  thus ?thesis;
  proof (elim exE conjE); 
    fix g;
    assume "is_linearform E g" and a: "ALL x:F. g x = f x" 
       and b: "ALL x:E. rabs (g x) <= p x";

    show "EX g. is_linearform E g 
            & is_continuous E norm g 
            & (ALL x:F. g x = f x) 
            & function_norm E norm g = function_norm F norm f";
    proof (intro exI conjI);

    txt{* We furthermore have to show that 
    $g$ is also continuous: *};

      show g_cont: "is_continuous E norm g";
      proof;
        fix x; assume "x:E";
        from b [RS bspec, OF this]; 
        show "rabs (g x) <= function_norm F norm f * norm x";
          by (unfold p_def);
      qed; 

      txt {* To complete the proof, we show that 
      $\fnorm g = \fnorm f$. \label{order_antisym} *};

      show "function_norm E norm g = function_norm F norm f"
        (is "?L = ?R");
      proof (rule order_antisym);

        txt{* First we show $\fnorm g \leq \fnorm f$.  The function norm
        $\fnorm g$ is defined as the smallest $c\in\bbbR$ such that
        \begin{matharray}{l}
        \All {x\in E} {|g\ap x| \leq c \cdot \norm x}
        \end{matharray}
        Furthermore holds
        \begin{matharray}{l}
        \All {x\in E} {|g\ap x| \leq \fnorm f \cdot \norm x}
        \end{matharray}
        *};
 
        have "ALL x:E. rabs (g x) <= function_norm F norm f * norm x";
        proof;
          fix x; assume "x:E"; 
          show "rabs (g x) <= function_norm F norm f * norm x";
            by (simp!);
        qed;

        with _ g_cont; show "?L <= ?R";
        proof (rule fnorm_le_ub);
          from f_cont f_norm; show "0r <= function_norm F norm f"; ..;
        qed;

        txt{* The other direction is achieved by a similar 
        argument. *};

        have "ALL x:F. rabs (f x) <= function_norm E norm g * norm x";
        proof;
          fix x; assume "x : F"; 
          from a; have "g x = f x"; ..;
          hence "rabs (f x) = rabs (g x)"; by simp;
          also; from g_cont;
          have "... <= function_norm E norm g * norm x";
          proof (rule norm_fx_le_norm_f_norm_x);
            show "x:E"; ..;
          qed;
          finally; show "rabs (f x) <= function_norm E norm g * norm x"; .;
        qed; 
        thus "?R <= ?L"; 
        proof (rule fnorm_le_ub [OF f_norm f_cont]);
          from g_cont; show "0r <= function_norm E norm g"; ..;
        qed;
      qed;
    qed;
  qed;
qed;

end;