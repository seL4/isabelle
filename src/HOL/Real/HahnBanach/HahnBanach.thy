(*  Title:      HOL/Real/HahnBanach/HahnBanach.thy
    ID:         $Id$
    Author:     Gertrud Baueer, TU Munich
*)

header {* The Hahn-Banach Theorem *};

theory HahnBanach
     = HahnBanachSupLemmas + HahnBanachExtLemmas + ZornLemma:;

text {*
  We present the proof of two different versions of the Hahn-Banach 
  Theorem, closely following \cite[\S36]{Heuser:1986}.
*};

subsection {* The case of general linear spaces *};

text  {* Every linearform $f$ on a subspace $F$ of $E$, which is 
 bounded by some  quasinorm $q$ on $E$, can be extended 
 to a function on $E$ in a norm preseving way. *};

theorem HahnBanach: 
  "[| is_vectorspace E; is_subspace F E; is_quasinorm E p; 
  is_linearform F f; ALL x:F. f x <= p x |]
  ==> EX h. is_linearform E h
          & (ALL x:F. h x = f x)
          & (ALL x:E. h x <= p x)";
proof -;
  assume "is_vectorspace E" "is_subspace F E" "is_quasinorm E p"
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

  subsubsect {* Existence of a limit function of the norm preserving
  extensions *}; 

  txt {* For every non-empty chain of norm preserving functions
  the union of all functions in the chain is again a norm preserving
  function. (The union is an upper bound for all elements. 
  It is even the least upper bound, because every upper bound of $M$
  is also an upper bound for $\Union c$.) *};

  have "!! c. [| c : chain M; EX x. x:c |] ==> Union c : M";  
  proof -;
    fix c; assume "c:chain M" "EX x. x:c";
    show "Union c : M";

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

        show a [simp]: "graph ?H ?h = Union c"; 
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
  qed;
 
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

subsubsect {* The domain of the limit function. *};

have eq: "H = E"; 
proof (rule classical);

txt {* Assume the domain of the supremum is not $E$. *};
;
  assume "H ~= E";
  have "H <= E"; ..;
  hence "H < E"; ..;
 
  txt{* Then there exists an element $x_0$ in 
  the difference of $E$ and $H$. *};

  hence "EX x0:E. x0~:H"; 
    by (rule set_less_imp_diff_not_empty);

  txt {* We get that $h$ can be extended  in a 
  norm-preserving way to some $H_0$. *};
;  
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
    linear closure of $x_0$.*};

    def H0 == "H + lin x0";

    from h; have xi: "EX xi. (ALL y:H. - p (y + x0) - h y <= xi)
                     & (ALL y:H. xi <= p (y + x0) - h y)";
    proof (rule ex_xi);
      fix u v; assume "u:H" "v:H";
      from h; have "h v - h u = h (v - u)";
         by (simp! add: linearform_diff_linear);
      also; from h_bound; have "... <= p (v - u)";
        by (simp!);
      also; have "v - u = x0 + - x0 + v + - u";
        by (simp! add: diff_eq1);
      also; have "... = v + x0 + - (u + x0)";
        by (simp!);
      also; have "... = (v + x0) - (u + x0)";
        by (simp! add: diff_eq1);
      also; have "p ... <= p (v + x0) + p (u + x0)";
         by (rule quasinorm_diff_triangle_ineq) (simp!)+;
      finally; have "h v - h u <= p (v + x0) + p (u + x0)"; .;

      thus "- p (u + x0) - h u <= p (v + x0) - h v";
        by (rule real_diff_ineq_swap);
    qed;
    hence "EX h0. g <= graph H0 h0 & g ~= graph H0 h0
               & graph H0 h0 : M"; 
    proof (elim exE, intro exI conjI);
      fix xi; 
      assume a: "(ALL y:H. - p (y + x0) - h y <= xi) 
               & (ALL y:H. xi <= p (y + x0) - h y)";
     
      txt {* Define $h_0$ as the linear extension of $h$ on $H_0$:*};  

      def h0 ==
          "\<lambda>x. let (y,a) = SOME (y, a). (x = y + a <*> x0 & y:H)
               in (h y) + a * xi";

      txt {* We get that the graph of $h_0$ extend that of
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

      txt {* Furthermore  $h_0$ is a norm preserving extension 
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
          by (rule h0_norm_pres, rule x0) (assumption | (simp!))+;
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



subsection  {* An alternative formulation of the theorem *};

text {* The following alternative formulation of the 
Hahn-Banach Theorem uses the fact that for
real numbers the following inequations are equivalent:
\begin{matharray}{ll}
\forall x\in H.\ap |h\ap x|\leq p\ap x& {\rm and}\\
\forall x\in H.\ap h\ap x\leq p\ap x\\
\end{matharray}
(This was shown in lemma $\idt{rabs{\dsh}ineq}$.) *};

theorem rabs_HahnBanach:
  "[| is_vectorspace E; is_subspace F E; is_quasinorm E p; 
  is_linearform F f; ALL x:F. rabs (f x) <= p x |]
  ==> EX g. is_linearform E g
          & (ALL x:F. g x = f x)
          & (ALL x:E. rabs (g x) <= p x)";
proof -; 
  assume e: "is_vectorspace E" "is_subspace F E" "is_quasinorm E p" 
            "is_linearform F f"  "ALL x:F. rabs (f x) <= p x";
  have "ALL x:F. f x <= p x"; 
    by (rule rabs_ineq_iff [RS iffD1]);
  hence "EX g. is_linearform E g & (ALL x:F. g x = f x) 
              & (ALL x:E. g x <= p x)";
    by (simp! only: HahnBanach);
  thus ?thesis;
  proof (elim exE conjE);
    fix g; assume "is_linearform E g" "ALL x:F. g x = f x" 
                  "ALL x:E. g x <= p x";
    show ?thesis;
    proof (intro exI conjI);
      from e; show "ALL x:E. rabs (g x) <= p x"; 
        by (simp! add: rabs_ineq_iff [OF subspace_refl]);
    qed;
  qed;
qed;


subsection {* The Hahn-Banach Theorem for normed spaces *};

text  {* Every continous linear function $f$ on a subspace of $E$, 
  can be extended to a continous function on $E$ with the same 
  function norm. *};

theorem norm_HahnBanach:
  "[| is_normed_vectorspace E norm; is_subspace F E; 
  is_linearform F f; is_continous F norm f |] 
  ==> EX g. is_linearform E g
         & is_continous E norm g 
         & (ALL x:F. g x = f x) 
         & function_norm E norm g = function_norm F norm f";
proof -;
  assume e_norm: "is_normed_vectorspace E norm";
  assume f: "is_subspace F E" "is_linearform F f";
  assume f_cont: "is_continous F norm f";
  have e: "is_vectorspace E"; ..;
  with _; have f_norm: "is_normed_vectorspace F norm"; ..;

  txt{* We define the function $p$ on $E$ as follows:
  \begin{matharray}{l}
  p\ap x = \fnorm f \cdot \norm x\\
  % p\ap x = \fnorm f \cdot \fnorm x\\
  \end{matharray}
  *};

  def p == "\<lambda>x. function_norm F norm f * norm x";
  
  txt{* $p$ is a quasinorm on $E$: *};

  have q: "is_quasinorm E p";
  proof;
    fix x y a; assume "x:E" "y:E";

    txt{* $p$ is positive definite: *};

    show "0r <= p x";
    proof (unfold p_def, rule real_le_mult_order);
      from _ f_norm; show "0r <= function_norm F norm f"; ..;
      show "0r <= norm x"; ..;
    qed;

    txt{* $p$ is multiplicative: *};

    show "p (a <*> x) = rabs a * p x";
    proof -; 
      have "p (a <*> x) = function_norm F norm f * norm (a <*> x)";
        by (simp!);
      also; have "norm (a <*> x) = rabs a * norm x"; 
        by (rule normed_vs_norm_mult_distrib);
      also; have "function_norm F norm f * (rabs a * norm x) 
        = rabs a * (function_norm F norm f * norm x)";
        by (simp! only: real_mult_left_commute);
      also; have "... = rabs a * p x"; by (simp!);
      finally; show ?thesis; .;
    qed;

    txt{* Furthermore, $p$ obeys the triangle inequation: *};

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

  txt{* Using the facts that $p$ is a quasinorm and 
  $f$ is bounded we can apply the Hahn-Banach Theorem for real
  vector spaces. 
  So $f$ can be extended in a norm preserving way to some function
  $g$ on the whole vector space $E$. *};

  with e f q; 
  have "EX g. is_linearform E g & (ALL x:F. g x = f x) 
            & (ALL x:E. rabs (g x) <= p x)";
    by (simp! add: rabs_HahnBanach);

  thus ?thesis;
  proof (elim exE conjE); 
    fix g;
    assume "is_linearform E g" and a: "ALL x:F. g x = f x" 
       and "ALL x:E. rabs (g x) <= p x";

    show "EX g. is_linearform E g 
            & is_continous E norm g 
            & (ALL x:F. g x = f x) 
            & function_norm E norm g = function_norm F norm f";
    proof (intro exI conjI);

    txt{* To complete the proof, we show that this function
    $g$ is also continous and has the same function norm as
    $f$. *};

      show g_cont: "is_continous E norm g";
      proof;
        fix x; assume "x:E";
        show "rabs (g x) <= function_norm F norm f * norm x";
          by (rule bspec [of _ _ x], (simp!));
      qed; 

      show "function_norm E norm g = function_norm F norm f"
        (is "?L = ?R");
      proof (rule order_antisym);

        txt{* $\idt{function{\dsh}norm}\ap F\ap \idt{norm}\ap f$ is 
        a solution
        for the inequation 
        \begin{matharray}{l}
        \forall\ap x\in E.\ap |g\ap x| \leq c \cdot \norm x
        \end{matharray} *};

        have "ALL x:E. rabs (g x) <= function_norm F norm f * norm x";
        proof;
          fix x; assume "x:E"; 
          show "rabs (g x) <= function_norm F norm f * norm x";
            by (simp!);
        qed;

        txt{* Since
         $\idt{function{\dsh}norm}\ap E\ap \idt{norm}\ap g$
        is the smallest solution for this inequation, we have: *};

        with _ g_cont;
        show "?L <= ?R";
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
          also; from _ _ g_cont; 
          have "... <= function_norm E norm g * norm x";
            by (rule norm_fx_le_norm_f_norm_x) (simp!)+;
          finally; 
          show "rabs (f x) <= function_norm E norm g * norm x"; .;
        qed;
  
        with f_norm f_cont; show "?R <= ?L"; 
        proof (rule fnorm_le_ub);
          from g_cont; show "0r <= function_norm E norm g"; ..;
        qed;
      qed;
    qed;
  qed;
qed;

end;