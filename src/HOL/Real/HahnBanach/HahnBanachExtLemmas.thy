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
$H$ is extended to the direct sum  $H_0 = H + \idt{lin}\ap x_0$, so for
any $x\in H_0$ the decomposition of $x = y + a \mult x$ 
with $y\in H$ is unique. $h_0$ is defined on $H_0$ by  
$h_0\ap x = h\ap y + a \cdot \xi$ for a certain $\xi$.

Subsequently we show some properties of this extension $h_0$ of $h$.
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
  "[| is_vectorspace F; !! u v. [| u:F; v:F |] ==> a u <= b v |]
  ==> EX (xi::real). ALL y:F. a y <= xi & xi <= b y"; 
proof -;
  assume vs: "is_vectorspace F";
  assume r: "(!! u v. [| u:F; v:F |] ==> a u <= (b v::real))";

  txt {* From the completeness of the reals follows:
  The set $S = \{a\: u\dt\: u\in F\}$ has a supremum, if
  it is non-empty and has an upper bound. *};

  let ?S = "{a u :: real | u. u:F}";

  have "EX xi. isLub UNIV ?S xi";  
  proof (rule reals_complete);
  
    txt {* The set $S$ is non-empty, since $a\ap\zero \in S$: *};

    from vs; have "a 00 : ?S"; by force;
    thus "EX X. X : ?S"; ..;

    txt {* $b\ap \zero$ is an upper bound of $S$: *};

    show "EX Y. isUb UNIV ?S Y"; 
    proof; 
      show "isUb UNIV ?S (b 00)";
      proof (intro isUbI setleI ballI);
        show "b 00 : UNIV"; ..;
      next;

        txt {* Every element $y\in S$ is less than $b\ap \zero$: *};

        fix y; assume y: "y : ?S"; 
        from y; have "EX u:F. y = a u"; by fast;
        thus "y <= b 00"; 
        proof;
          fix u; assume "u:F"; 
          assume "y = a u";
          also; have "a u <= b 00"; by (rule r) (simp!)+;
          finally; show ?thesis; .;
        qed;
      qed;
    qed;
  qed;

  thus "EX xi. ALL y:F. a y <= xi & xi <= b y"; 
  proof (elim exE);
    fix xi; assume "isLub UNIV ?S xi"; 
    show ?thesis;
    proof (intro exI conjI ballI); 
   
      txt {* For all $y\in F$ holds $a\ap y \leq \xi$: *};
     
      fix y; assume y: "y:F";
      show "a y <= xi";    
      proof (rule isUbD);  
        show "isUb UNIV ?S xi"; ..;
      qed (force!);
    next;

      txt {* For all $y\in F$ holds $\xi\leq b\ap y$: *};

      fix y; assume "y:F";
      show "xi <= b y";  
      proof (intro isLub_le_isUb isUbI setleI);
        show "b y : UNIV"; ..;
        show "ALL ya : ?S. ya <= b y"; 
        proof;
          fix au; assume au: "au : ?S ";
          hence "EX u:F. au = a u"; by fast;
          thus "au <= b y";
          proof;
            fix u; assume "u:F"; assume "au = a u";  
            also; have "... <= b y"; by (rule r);
            finally; show ?thesis; .;
          qed;
        qed;
      qed; 
    qed;
  qed;
qed;

text{* \medskip The function $h_0$ is defined as a
$h_0\ap x = h\ap y + a\cdot \xi$ where $x = y + a\mult \xi$
is a linear extension of $h$ to $H_0$. *};

lemma h0_lf: 
  "[| h0 == (\<lambda>x. let (y, a) = SOME (y, a). x = y + a (*) x0 & y:H 
                in h y + a * xi);
  H0 == H + lin x0; is_subspace H E; is_linearform H h; x0 ~: H; 
  x0 : E; x0 ~= 00; is_vectorspace E |]
  ==> is_linearform H0 h0";
proof -;
  assume h0_def: 
    "h0 == (\<lambda>x. let (y, a) = SOME (y, a). x = y + a (*) x0 & y:H 
               in h y + a * xi)"
    and H0_def: "H0 == H + lin x0" 
    and vs: "is_subspace H E" "is_linearform H h" "x0 ~: H"
      "x0 ~= 00" "x0 : E" "is_vectorspace E";

  have h0: "is_vectorspace H0"; 
  proof (unfold H0_def, rule vs_sum_vs);
    show "is_subspace (lin x0) E"; ..;
  qed; 

  show ?thesis;
  proof;
    fix x1 x2; assume x1: "x1 : H0" and x2: "x2 : H0"; 

    txt{* We now have to show that $h_0$ is additive, i.~e.\
    $h_0 \ap (x_1\plus x_2) = h_0\ap x_1 + h_0\ap x_2$
    for $x_1, x_2\in H$. *}; 

    have x1x2: "x1 + x2 : H0"; 
      by (rule vs_add_closed, rule h0); 
    from x1; 
    have ex_x1: "EX y1 a1. x1 = y1 + a1 (*) x0  & y1 : H"; 
      by (unfold H0_def vs_sum_def lin_def) fast;
    from x2; 
    have ex_x2: "EX y2 a2. x2 = y2 + a2 (*) x0 & y2 : H"; 
      by (unfold H0_def vs_sum_def lin_def) fast;
    from x1x2; 
    have ex_x1x2: "EX y a. x1 + x2 = y + a (*) x0 & y : H";
      by (unfold H0_def vs_sum_def lin_def) fast;

    from ex_x1 ex_x2 ex_x1x2;
    show "h0 (x1 + x2) = h0 x1 + h0 x2";
    proof (elim exE conjE);
      fix y1 y2 y a1 a2 a;
      assume y1: "x1 = y1 + a1 (*) x0"     and y1': "y1 : H"
         and y2: "x2 = y2 + a2 (*) x0"     and y2': "y2 : H" 
         and y: "x1 + x2 = y + a (*) x0"   and y':  "y  : H"; 

      have ya: "y1 + y2 = y & a1 + a2 = a"; 
      proof (rule decomp_H0);;
	txt_raw {* \label{decomp-H0-use} *};;
        show "y1 + y2 + (a1 + a2) (*) x0 = y + a (*) x0"; 
          by (simp! add: vs_add_mult_distrib2 [of E]);
        show "y1 + y2 : H"; ..;
      qed;

      have "h0 (x1 + x2) = h y + a * xi";
	by (rule h0_definite);
      also; have "... = h (y1 + y2) + (a1 + a2) * xi"; 
        by (simp add: ya);
      also; from vs y1' y2'; 
      have "... = h y1 + h y2 + a1 * xi + a2 * xi"; 
	by (simp add: linearform_add [of H] 
                      real_add_mult_distrib);
      also; have "... = (h y1 + a1 * xi) + (h y2 + a2 * xi)"; 
        by simp;
      also; have "h y1 + a1 * xi = h0 x1"; 
        by (rule h0_definite [RS sym]);
      also; have "h y2 + a2 * xi = h0 x2"; 
        by (rule h0_definite [RS sym]);
      finally; show ?thesis; .;
    qed;
 
    txt{* We further have to show that $h_0$ is multiplicative, 
    i.~e.\ $h_0\ap (c \mult x_1) = c \cdot h_0\ap x_1$
    for $x\in H$ and $c\in \bbbR$. 
    *}; 

  next;  
    fix c x1; assume x1: "x1 : H0";    
    have ax1: "c (*) x1 : H0";
      by (rule vs_mult_closed, rule h0);
    from x1; have ex_x: "!! x. x: H0 
                        ==> EX y a. x = y + a (*) x0 & y : H";
      by (unfold H0_def vs_sum_def lin_def) fast;

    from x1; have ex_x1: "EX y1 a1. x1 = y1 + a1 (*) x0 & y1 : H";
      by (unfold H0_def vs_sum_def lin_def) fast;
    with ex_x [of "c (*) x1", OF ax1];
    show "h0 (c (*) x1) = c * (h0 x1)";  
    proof (elim exE conjE);
      fix y1 y a1 a; 
      assume y1: "x1 = y1 + a1 (*) x0"       and y1': "y1 : H"
        and y: "c (*) x1 = y  + a  (*) x0"   and y':  "y  : H"; 

      have ya: "c (*) y1 = y & c * a1 = a"; 
      proof (rule decomp_H0); 
	show "c (*) y1 + (c * a1) (*) x0 = y + a (*) x0"; 
          by (simp! add: add: vs_add_mult_distrib1);
        show "c (*) y1 : H"; ..;
      qed;

      have "h0 (c (*) x1) = h y + a * xi"; 
	by (rule h0_definite);
      also; have "... = h (c (*) y1) + (c * a1) * xi";
        by (simp add: ya);
      also; from vs y1'; have "... = c * h y1 + c * a1 * xi"; 
	by (simp add: linearform_mult [of H]);
      also; from vs y1'; have "... = c * (h y1 + a1 * xi)"; 
	by (simp add: real_add_mult_distrib2 real_mult_assoc);
      also; have "h y1 + a1 * xi = h0 x1"; 
        by (rule h0_definite [RS sym]);
      finally; show ?thesis; .;
    qed;
  qed;
qed;

text{* \medskip The linear extension $h_0$ of $h$
is bounded by the seminorm $p$. *};

lemma h0_norm_pres:
  "[| h0 == (\<lambda>x. let (y, a) = SOME (y, a). x = y + a (*) x0 & y:H 
                in h y + a * xi);
  H0 == H + lin x0; x0 ~: H; x0 : E; x0 ~= 00; is_vectorspace E; 
  is_subspace H E; is_seminorm E p; is_linearform H h; ALL y:H. h y <= p y; 
  ALL y:H. - p (y + x0) - h y <= xi & xi <= p (y + x0) - h y |]
   ==> ALL x:H0. h0 x <= p x"; 
proof; 
  assume h0_def: 
    "h0 == (\<lambda>x. let (y, a) = SOME (y, a). x = y + a (*) x0 & y:H 
               in (h y) + a * xi)"
    and H0_def: "H0 == H + lin x0" 
    and vs: "x0 ~: H" "x0 : E" "x0 ~= 00" "is_vectorspace E" 
            "is_subspace H E" "is_seminorm E p" "is_linearform H h" 
    and a: "ALL y:H. h y <= p y";
  presume a1: "ALL ya:H. - p (ya + x0) - h ya <= xi";
  presume a2: "ALL ya:H. xi <= p (ya + x0) - h ya";
  fix x; assume "x : H0"; 
  have ex_x: 
    "!! x. x : H0 ==> EX y a. x = y + a (*) x0 & y : H";
    by (unfold H0_def vs_sum_def lin_def) fast;
  have "EX y a. x = y + a (*) x0 & y : H";
    by (rule ex_x);
  thus "h0 x <= p x";
  proof (elim exE conjE);
    fix y a; assume x: "x = y + a (*) x0" and y: "y : H";
    have "h0 x = h y + a * xi";
      by (rule h0_definite);

    txt{* Now we show  
    $h\ap y + a \cdot \xi\leq  p\ap (y\plus a \mult x_0)$ 
    by case analysis on $a$. \label{linorder_linear_split}*};

    also; have "... <= p (y + a (*) x0)";
    proof (rule linorder_linear_split); 

      assume z: "a = (#0::real)"; 
      with vs y a; show ?thesis; by simp;

    txt {* In the case $a < 0$, we use $a_1$ with $\idt{ya}$ 
    taken as $y/a$: *};

    next;
      assume lz: "a < #0"; hence nz: "a ~= #0"; by simp;
      from a1; 
      have "- p (rinv a (*) y + x0) - h (rinv a (*) y) <= xi";
        by (rule bspec) (simp!);

      txt {* The thesis for this case now follows by a short  
      calculation. *};      
      hence "a * xi 
            <= a * (- p (rinv a (*) y + x0) - h (rinv a (*) y))";
        by (rule real_mult_less_le_anti [OF lz]);
      also; have "... = - a * (p (rinv a (*) y + x0)) 
                        - a * (h (rinv a (*) y))";
        by (rule real_mult_diff_distrib);
      also; from lz vs y; have "- a * (p (rinv a (*) y + x0)) 
                               = p (a (*) (rinv a (*) y + x0))";
        by (simp add: seminorm_abs_homogenous abs_minus_eqI2);
      also; from nz vs y; have "... = p (y + a (*) x0)";
        by (simp add: vs_add_mult_distrib1);
      also; from nz vs y; have "a * (h (rinv a (*) y)) =  h y";
        by (simp add: linearform_mult [RS sym]);
      finally; have "a * xi <= p (y + a (*) x0) - h y"; .;

      hence "h y + a * xi <= h y + p (y + a (*) x0) - h y";
        by (simp add: real_add_left_cancel_le);
      thus ?thesis; by simp;

      txt {* In the case $a > 0$, we use $a_2$ with $\idt{ya}$ 
      taken as $y/a$: *};

    next; 
      assume gz: "#0 < a"; hence nz: "a ~= #0"; by simp;
      from a2;
      have "xi <= p (rinv a (*) y + x0) - h (rinv a (*) y)";
        by (rule bspec) (simp!);

      txt {* The thesis for this case follows by a short
      calculation: *};

      with gz; have "a * xi 
            <= a * (p (rinv a (*) y + x0) - h (rinv a (*) y))";
        by (rule real_mult_less_le_mono);
      also; have "... = a * p (rinv a (*) y + x0) 
                        - a * h (rinv a (*) y)";
        by (rule real_mult_diff_distrib2); 
      also; from gz vs y; 
      have "a * p (rinv a (*) y + x0) 
           = p (a (*) (rinv a (*) y + x0))";
        by (simp add: seminorm_abs_homogenous abs_eqI2);
      also; from nz vs y; 
      have "... = p (y + a (*) x0)";
        by (simp add: vs_add_mult_distrib1);
      also; from nz vs y; have "a * h (rinv a (*) y) = h y";
        by (simp add: linearform_mult [RS sym]); 
      finally; have "a * xi <= p (y + a (*) x0) - h y"; .;
 
      hence "h y + a * xi <= h y + (p (y + a (*) x0) - h y)";
        by (simp add: real_add_left_cancel_le);
      thus ?thesis; by simp;
    qed;
    also; from x; have "... = p x"; by simp;
    finally; show ?thesis; .;
  qed;
qed blast+; 

end;