(*  Title:      HOL/Real/HahnBanach/HahnBanachExtLemmas.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Extending non-maximal functions *};

theory HahnBanachExtLemmas = FunctionNorm:;

text{* In this section the following context is presumed.
Let $E$ be a real vector space with a 
seminorm $q$ on $E$. $F$ is a subspace of $E$ and $f$ a linear 
function on $F$. We consider a subspace $H$ of $E$ that is a 
superspace of $F$ and a linear form $h$ on $H$. $H$ is a not equal 
to $E$ and $x_0$ is an element in $E \backslash H$.
$H$ is extended to the direct sum  $H' = H + \idt{lin}\ap x_0$, so for
any $x\in H'$ the decomposition of $x = y + a \mult x$ 
with $y\in H$ is unique. $h'$ is defined on $H'$ by  
$h'\ap x = h\ap y + a \cdot \xi$ for a certain $\xi$.

Subsequently we show some properties of this extension $h'$ of $h$.
*}; 


text {* This lemma will be used to show the existence of a linear
extension of $f$ (see page \pageref{ex-xi-use}). 
It is a consequence
of the completeness of $\bbbR$. To show 
\begin{matharray}{l}
\Ex{\xi}{\All {y\in F}{a\ap y \leq \xi \land \xi \leq b\ap y}}
\end{matharray} 
it suffices to show that 
\begin{matharray}{l} \All
{u\in F}{\All {v\in F}{a\ap u \leq b \ap v}} 
\end{matharray} *};

lemma ex_xi: 
  "[| is_vectorspace F; !! u v. [| u \<in> F; v \<in> F |] ==> a u <= b v |]
  ==> \<exists>xi::real. \<forall>y \<in> F. a y <= xi \<and> xi <= b y"; 
proof -;
  assume vs: "is_vectorspace F";
  assume r: "(!! u v. [| u \<in> F; v \<in> F |] ==> a u <= (b v::real))";

  txt {* From the completeness of the reals follows:
  The set $S = \{a\: u\dt\: u\in F\}$ has a supremum, if
  it is non-empty and has an upper bound. *};

  let ?S = "{a u :: real | u. u \<in> F}";

  have "\<exists>xi. isLub UNIV ?S xi";  
  proof (rule reals_complete);
  
    txt {* The set $S$ is non-empty, since $a\ap\zero \in S$: *};

    from vs; have "a 0 \<in> ?S"; by force;
    thus "\<exists>X. X \<in> ?S"; ..;

    txt {* $b\ap \zero$ is an upper bound of $S$: *};

    show "\<exists>Y. isUb UNIV ?S Y"; 
    proof; 
      show "isUb UNIV ?S (b 0)";
      proof (intro isUbI setleI ballI);
        show "b 0 \<in> UNIV"; ..;
      next;

        txt {* Every element $y\in S$ is less than $b\ap \zero$: *};

        fix y; assume y: "y \<in> ?S"; 
        from y; have "\<exists>u \<in> F. y = a u"; by fast;
        thus "y <= b 0"; 
        proof;
          fix u; assume "u \<in> F"; 
          assume "y = a u";
          also; have "a u <= b 0"; by (rule r) (simp!)+;
          finally; show ?thesis; .;
        qed;
      qed;
    qed;
  qed;

  thus "\<exists>xi. \<forall>y \<in> F. a y <= xi \<and> xi <= b y"; 
  proof (elim exE);
    fix xi; assume "isLub UNIV ?S xi"; 
    show ?thesis;
    proof (intro exI conjI ballI); 
   
      txt {* For all $y\in F$ holds $a\ap y \leq \xi$: *};
     
      fix y; assume y: "y \<in> F";
      show "a y <= xi";    
      proof (rule isUbD);  
        show "isUb UNIV ?S xi"; ..;
      qed (force!);
    next;

      txt {* For all $y\in F$ holds $\xi\leq b\ap y$: *};

      fix y; assume "y \<in> F";
      show "xi <= b y";  
      proof (intro isLub_le_isUb isUbI setleI);
        show "b y \<in> UNIV"; ..;
        show "\<forall>ya \<in> ?S. ya <= b y"; 
        proof;
          fix au; assume au: "au \<in> ?S ";
          hence "\<exists>u \<in> F. au = a u"; by fast;
          thus "au <= b y";
          proof;
            fix u; assume "u \<in> F"; assume "au = a u";  
            also; have "... <= b y"; by (rule r);
            finally; show ?thesis; .;
          qed;
        qed;
      qed; 
    qed;
  qed;
qed;

text{* \medskip The function $h'$ is defined as a
$h'\ap x = h\ap y + a\cdot \xi$ where $x = y + a\mult \xi$
is a linear extension of $h$ to $H'$. *};

lemma h'_lf: 
  "[| h' == (\<lambda>x. let (y, a) = SOME (y, a). x = y + a \<cdot> x0 \<and> y \<in> H 
                in h y + a * xi);
  H' == H + lin x0; is_subspace H E; is_linearform H h; x0 \<notin> H; 
  x0 \<in> E; x0 \<noteq> 0; is_vectorspace E |]
  ==> is_linearform H' h'";
proof -;
  assume h'_def: 
    "h' == (\<lambda>x. let (y, a) = SOME (y, a). x = y + a \<cdot> x0 \<and> y \<in> H 
               in h y + a * xi)"
    and H'_def: "H' == H + lin x0" 
    and vs: "is_subspace H E" "is_linearform H h" "x0 \<notin> H"
      "x0 \<noteq> 0" "x0 \<in> E" "is_vectorspace E";

  have h': "is_vectorspace H'"; 
  proof (unfold H'_def, rule vs_sum_vs);
    show "is_subspace (lin x0) E"; ..;
  qed; 

  show ?thesis;
  proof;
    fix x1 x2; assume x1: "x1 \<in> H'" and x2: "x2 \<in> H'"; 

    txt{* We now have to show that $h'$ is additive, i.~e.\
    $h' \ap (x_1\plus x_2) = h'\ap x_1 + h'\ap x_2$
    for $x_1, x_2\in H$. *}; 

    have x1x2: "x1 + x2 \<in> H'"; 
      by (rule vs_add_closed, rule h'); 
    from x1; 
    have ex_x1: "\<exists>y1 a1. x1 = y1 + a1 \<cdot> x0  \<and> y1 \<in> H"; 
      by (unfold H'_def vs_sum_def lin_def) fast;
    from x2; 
    have ex_x2: "\<exists>y2 a2. x2 = y2 + a2 \<cdot> x0 \<and> y2 \<in> H"; 
      by (unfold H'_def vs_sum_def lin_def) fast;
    from x1x2; 
    have ex_x1x2: "\<exists>y a. x1 + x2 = y + a \<cdot> x0 \<and> y \<in> H";
      by (unfold H'_def vs_sum_def lin_def) fast;

    from ex_x1 ex_x2 ex_x1x2;
    show "h' (x1 + x2) = h' x1 + h' x2";
    proof (elim exE conjE);
      fix y1 y2 y a1 a2 a;
      assume y1: "x1 = y1 + a1 \<cdot> x0"     and y1': "y1 \<in> H"
         and y2: "x2 = y2 + a2 \<cdot> x0"     and y2': "y2 \<in> H" 
         and y: "x1 + x2 = y + a \<cdot> x0"   and y':  "y  \<in> H"; 
      txt {* \label{decomp-H-use}*}
      have ya: "y1 + y2 = y \<and> a1 + a2 = a"; 
      proof (rule decomp_H')
        show "y1 + y2 + (a1 + a2) \<cdot> x0 = y + a \<cdot> x0"; 
          by (simp! add: vs_add_mult_distrib2 [of E]);
        show "y1 + y2 \<in> H"; ..;
      qed;

      have "h' (x1 + x2) = h y + a * xi";
	by (rule h'_definite);
      also; have "... = h (y1 + y2) + (a1 + a2) * xi"; 
        by (simp add: ya);
      also; from vs y1' y2'; 
      have "... = h y1 + h y2 + a1 * xi + a2 * xi"; 
	by (simp add: linearform_add [of H] 
                      real_add_mult_distrib);
      also; have "... = (h y1 + a1 * xi) + (h y2 + a2 * xi)"; 
        by simp;
      also; have "h y1 + a1 * xi = h' x1";
        by (rule h'_definite [symmetric]);
      also; have "h y2 + a2 * xi = h' x2"; 
        by (rule h'_definite [symmetric]);
      finally; show ?thesis; .;
    qed;
 
    txt{* We further have to show that $h'$ is multiplicative, 
    i.~e.\ $h'\ap (c \mult x_1) = c \cdot h'\ap x_1$
    for $x\in H$ and $c\in \bbbR$. 
    *}; 

  next;  
    fix c x1; assume x1: "x1 \<in> H'";    
    have ax1: "c \<cdot> x1 \<in> H'";
      by (rule vs_mult_closed, rule h');
    from x1; 
    have ex_x: "!! x. x\<in> H' ==> \<exists>y a. x = y + a \<cdot> x0 \<and> y \<in> H";
      by (unfold H'_def vs_sum_def lin_def) fast;

    from x1; have ex_x1: "\<exists>y1 a1. x1 = y1 + a1 \<cdot> x0 \<and> y1 \<in> H";
      by (unfold H'_def vs_sum_def lin_def) fast;
    with ex_x [of "c \<cdot> x1", OF ax1];
    show "h' (c \<cdot> x1) = c * (h' x1)";  
    proof (elim exE conjE);
      fix y1 y a1 a; 
      assume y1: "x1 = y1 + a1 \<cdot> x0"     and y1': "y1 \<in> H"
        and y: "c \<cdot> x1 = y  + a \<cdot> x0"    and y': "y \<in> H"; 

      have ya: "c \<cdot> y1 = y \<and> c * a1 = a"; 
      proof (rule decomp_H'); 
	show "c \<cdot> y1 + (c * a1) \<cdot> x0 = y + a \<cdot> x0"; 
          by (simp! add: vs_add_mult_distrib1);
        show "c \<cdot> y1 \<in> H"; ..;
      qed;

      have "h' (c \<cdot> x1) = h y + a * xi"; 
	by (rule h'_definite);
      also; have "... = h (c \<cdot> y1) + (c * a1) * xi";
        by (simp add: ya);
      also; from vs y1'; have "... = c * h y1 + c * a1 * xi"; 
	by (simp add: linearform_mult [of H]);
      also; from vs y1'; have "... = c * (h y1 + a1 * xi)"; 
	by (simp add: real_add_mult_distrib2 real_mult_assoc);
      also; have "h y1 + a1 * xi = h' x1"; 
        by (rule h'_definite [symmetric]);
      finally; show ?thesis; .;
    qed;
  qed;
qed;

text{* \medskip The linear extension $h'$ of $h$
is bounded by the seminorm $p$. *};

lemma h'_norm_pres:
  "[| h' == (\<lambda>x. let (y, a) = SOME (y, a). x = y + a \<cdot> x0 \<and> y \<in> H 
                 in h y + a * xi);
  H' == H + lin x0; x0 \<notin> H; x0 \<in> E; x0 \<noteq> 0; is_vectorspace E; 
  is_subspace H E; is_seminorm E p; is_linearform H h; 
  \<forall>y \<in> H. h y <= p y; 
  \<forall>y \<in> H. - p (y + x0) - h y <= xi \<and> xi <= p (y + x0) - h y |]
   ==> \<forall>x \<in> H'. h' x <= p x"; 
proof; 
  assume h'_def: 
    "h' == (\<lambda>x. let (y, a) = SOME (y, a). x = y + a \<cdot> x0 \<and> y \<in> H 
               in (h y) + a * xi)"
    and H'_def: "H' == H + lin x0" 
    and vs: "x0 \<notin> H" "x0 \<in> E" "x0 \<noteq> 0" "is_vectorspace E" 
            "is_subspace H E" "is_seminorm E p" "is_linearform H h" 
    and a: "\<forall>y \<in> H. h y <= p y";
  presume a1: "\<forall>ya \<in> H. - p (ya + x0) - h ya <= xi";
  presume a2: "\<forall>ya \<in> H. xi <= p (ya + x0) - h ya";
  fix x; assume "x \<in> H'"; 
  have ex_x: 
    "!! x. x \<in> H' ==> \<exists>y a. x = y + a \<cdot> x0 \<and> y \<in> H";
    by (unfold H'_def vs_sum_def lin_def) fast;
  have "\<exists>y a. x = y + a \<cdot> x0 \<and> y \<in> H";
    by (rule ex_x);
  thus "h' x <= p x";
  proof (elim exE conjE);
    fix y a; assume x: "x = y + a \<cdot> x0" and y: "y \<in> H";
    have "h' x = h y + a * xi";
      by (rule h'_definite);

    txt{* Now we show  
    $h\ap y + a \cdot \xi\leq  p\ap (y\plus a \mult x_0)$ 
    by case analysis on $a$. *};

    also; have "... <= p (y + a \<cdot> x0)";
    proof (rule linorder_cases);

      assume z: "a = #0"; 
      with vs y a; show ?thesis; by simp;

    txt {* In the case $a < 0$, we use $a_1$ with $\idt{ya}$ 
    taken as $y/a$: *};

    next;
      assume lz: "a < #0"; hence nz: "a \<noteq> #0"; by simp;
      from a1; 
      have "- p (rinv a \<cdot> y + x0) - h (rinv a \<cdot> y) <= xi";
        by (rule bspec) (simp!);

      txt {* The thesis for this case now follows by a short  
      calculation. *};      
      hence "a * xi <= a * (- p (rinv a \<cdot> y + x0) - h (rinv a \<cdot> y))";
        by (rule real_mult_less_le_anti [OF lz]);
      also; 
      have "... = - a * (p (rinv a \<cdot> y + x0)) - a * (h (rinv a \<cdot> y))";
        by (rule real_mult_diff_distrib);
      also; from lz vs y; 
      have "- a * (p (rinv a \<cdot> y + x0)) = p (a \<cdot> (rinv a \<cdot> y + x0))";
        by (simp add: seminorm_abs_homogenous abs_minus_eqI2);
      also; from nz vs y; have "... = p (y + a \<cdot> x0)";
        by (simp add: vs_add_mult_distrib1);
      also; from nz vs y; have "a * (h (rinv a \<cdot> y)) =  h y";
        by (simp add: linearform_mult [symmetric]);
      finally; have "a * xi <= p (y + a \<cdot> x0) - h y"; .;

      hence "h y + a * xi <= h y + p (y + a \<cdot> x0) - h y";
        by (simp add: real_add_left_cancel_le);
      thus ?thesis; by simp;

      txt {* In the case $a > 0$, we use $a_2$ with $\idt{ya}$ 
      taken as $y/a$: *};

    next; 
      assume gz: "#0 < a"; hence nz: "a \<noteq> #0"; by simp;
      from a2; have "xi <= p (rinv a \<cdot> y + x0) - h (rinv a \<cdot> y)";
        by (rule bspec) (simp!);

      txt {* The thesis for this case follows by a short
      calculation: *};

      with gz; 
      have "a * xi <= a * (p (rinv a \<cdot> y + x0) - h (rinv a \<cdot> y))";
        by (rule real_mult_less_le_mono);
      also; have "... = a * p (rinv a \<cdot> y + x0) - a * h (rinv a \<cdot> y)";
        by (rule real_mult_diff_distrib2); 
      also; from gz vs y; 
      have "a * p (rinv a \<cdot> y + x0) = p (a \<cdot> (rinv a \<cdot> y + x0))";
        by (simp add: seminorm_abs_homogenous abs_eqI2);
      also; from nz vs y; have "... = p (y + a \<cdot> x0)";
        by (simp add: vs_add_mult_distrib1);
      also; from nz vs y; have "a * h (rinv a \<cdot> y) = h y";
        by (simp add: linearform_mult [symmetric]); 
      finally; have "a * xi <= p (y + a \<cdot> x0) - h y"; .;
 
      hence "h y + a * xi <= h y + (p (y + a \<cdot> x0) - h y)";
        by (simp add: real_add_left_cancel_le);
      thus ?thesis; by simp;
    qed;
    also; from x; have "... = p x"; by simp;
    finally; show ?thesis; .;
  qed;
qed blast+; 

end;
