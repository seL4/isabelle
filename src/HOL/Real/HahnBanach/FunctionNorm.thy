(*  Title:      HOL/Real/HahnBanach/FunctionNorm.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* The norm of a function *}

theory FunctionNorm = NormedSpace + FunctionOrder:

subsection {* Continuous linear forms*}

text{* A linear form $f$ on a normed vector space $(V, \norm{\cdot})$
is \emph{continuous}, iff it is bounded, i.~e.
\[\Ex {c\in R}{\All {x\in V} {|f\ap x| \leq c \cdot \norm x}}\]
In our application no other functions than linear forms are considered,
so we can define continuous linear forms as bounded linear forms:
*}

constdefs
  is_continuous ::
  "['a::{plus, minus, zero} set, 'a => real, 'a => real] => bool" 
  "is_continuous V norm f == 
    is_linearform V f \<and> (\<exists>c. \<forall>x \<in> V. |f x| <= c * norm x)"

lemma continuousI [intro]: 
  "[| is_linearform V f; !! x. x \<in> V ==> |f x| <= c * norm x |] 
  ==> is_continuous V norm f"
proof (unfold is_continuous_def, intro exI conjI ballI)
  assume r: "!! x. x \<in> V ==> |f x| <= c * norm x" 
  fix x assume "x \<in> V" show "|f x| <= c * norm x" by (rule r)
qed
  
lemma continuous_linearform [intro?]: 
  "is_continuous V norm f ==> is_linearform V f"
  by (unfold is_continuous_def) force

lemma continuous_bounded [intro?]:
  "is_continuous V norm f 
  ==> \<exists>c. \<forall>x \<in> V. |f x| <= c * norm x"
  by (unfold is_continuous_def) force

subsection{* The norm of a linear form *}


text{* The least real number $c$ for which holds
\[\All {x\in V}{|f\ap x| \leq c \cdot \norm x}\]
is called the \emph{norm} of $f$.

For non-trivial vector spaces $V \neq \{\zero\}$ the norm can be defined as 
\[\fnorm {f} =\sup_{x\neq\zero}\frac{|f\ap x|}{\norm x} \] 

For the case $V = \{\zero\}$ the supremum would be taken from an
empty set. Since $\bbbR$ is unbounded, there would be no supremum.  To
avoid this situation it must be guaranteed that there is an element in
this set. This element must be ${} \ge 0$ so that
$\idt{function{\dsh}norm}$ has the norm properties. Furthermore it
does not have to change the norm in all other cases, so it must be
$0$, as all other elements of are ${} \ge 0$.

Thus we define the set $B$ the supremum is taken from as
\[
\{ 0 \} \Union \left\{ \frac{|f\ap x|}{\norm x} \dt x\neq \zero \And x\in F\right\}
 \]
*}

constdefs
  B :: "[ 'a set, 'a => real, 'a::{plus, minus, zero} => real ] => real set"
  "B V norm f == 
  {#0} \<union> {|f x| * inverse (norm x) | x. x \<noteq> 0 \<and> x \<in> V}"

text{* $n$ is the function norm of $f$, iff 
$n$ is the supremum of $B$. 
*}

constdefs 
  is_function_norm :: 
  " ['a::{minus,plus,zero}  => real, 'a set, 'a => real] => real => bool"
  "is_function_norm f V norm fn == is_Sup UNIV (B V norm f) fn"

text{* $\idt{function{\dsh}norm}$ is equal to the supremum of $B$, 
if the supremum exists. Otherwise it is undefined. *}

constdefs 
  function_norm :: " ['a::{minus,plus,zero} => real, 'a set, 'a => real] => real"
  "function_norm f V norm == Sup UNIV (B V norm f)"

syntax   
  function_norm :: " ['a => real, 'a set, 'a => real] => real" ("\<parallel>_\<parallel>_,_")

lemma B_not_empty: "#0 \<in> B V norm f"
  by (unfold B_def, force)

text {* The following lemma states that every continuous linear form
on a normed space $(V, \norm{\cdot})$ has a function norm. *}

lemma ex_fnorm [intro?]: 
  "[| is_normed_vectorspace V norm; is_continuous V norm f|]
     ==> is_function_norm f V norm \<parallel>f\<parallel>V,norm" 
proof (unfold function_norm_def is_function_norm_def 
  is_continuous_def Sup_def, elim conjE, rule someI2_ex)
  assume "is_normed_vectorspace V norm"
  assume "is_linearform V f" 
  and e: "\<exists>c. \<forall>x \<in> V. |f x| <= c * norm x"

  txt {* The existence of the supremum is shown using the 
  completeness of the reals. Completeness means, that
  every non-empty bounded set of reals has a 
  supremum. *}
  show  "\<exists>a. is_Sup UNIV (B V norm f) a" 
  proof (unfold is_Sup_def, rule reals_complete)

    txt {* First we have to show that $B$ is non-empty: *} 

    show "\<exists>X. X \<in> B V norm f" 
    proof (intro exI)
      show "#0 \<in> (B V norm f)" by (unfold B_def, force)
    qed

    txt {* Then we have to show that $B$ is bounded: *}

    from e show "\<exists>Y. isUb UNIV (B V norm f) Y"
    proof

      txt {* We know that $f$ is bounded by some value $c$. *}  
  
      fix c assume a: "\<forall>x \<in> V. |f x| <= c * norm x"
      def b == "max c #0"

      show "?thesis"
      proof (intro exI isUbI setleI ballI, unfold B_def, 
	elim UnE CollectE exE conjE singletonE)

        txt{* To proof the thesis, we have to show that there is 
        some constant $b$, such that $y \leq b$ for all $y\in B$. 
        Due to the definition of $B$ there are two cases for
        $y\in B$. If $y = 0$ then $y \leq \idt{max}\ap c\ap 0$: *}

	fix y assume "y = (#0::real)"
        show "y <= b" by (simp! add: le_maxI2)

        txt{* The second case is 
        $y = {|f\ap x|}/{\norm x}$ for some 
        $x\in V$ with $x \neq \zero$. *}

      next
	fix x y
        assume "x \<in> V" "x \<noteq> 0" (***

         have ge: "#0 <= inverse (norm x)";
          by (rule real_less_imp_le, rule real_inverse_gt_zero, 
                rule normed_vs_norm_gt_zero); ( ***
          proof (rule real_less_imp_le);
            show "#0 < inverse (norm x)";
            proof (rule real_inverse_gt_zero);
              show "#0 < norm x"; ..;
            qed;
          qed; *** )
        have nz: "norm x \<noteq> #0" 
          by (rule not_sym, rule lt_imp_not_eq, 
              rule normed_vs_norm_gt_zero) (***
          proof (rule not_sym);
            show "#0 \<noteq> norm x"; 
            proof (rule lt_imp_not_eq);
              show "#0 < norm x"; ..;
            qed;
          qed; ***)***)

        txt {* The thesis follows by a short calculation using the 
        fact that $f$ is bounded. *}
    
        assume "y = |f x| * inverse (norm x)"
        also have "... <= c * norm x * inverse (norm x)"
        proof (rule real_mult_le_le_mono2)
          show "#0 <= inverse (norm x)"
            by (rule real_less_imp_le, rule real_inverse_gt_zero1, 
                rule normed_vs_norm_gt_zero)
          from a show "|f x| <= c * norm x" ..
        qed
        also have "... = c * (norm x * inverse (norm x))" 
          by (rule real_mult_assoc)
        also have "(norm x * inverse (norm x)) = (#1::real)" 
        proof (rule real_mult_inv_right1)
          show nz: "norm x \<noteq> #0" 
            by (rule not_sym, rule lt_imp_not_eq, 
              rule normed_vs_norm_gt_zero)
        qed
        also have "c * ... <= b " by (simp! add: le_maxI1)
	finally show "y <= b" .
      qed simp
    qed
  qed
qed

text {* The norm of a continuous function is always $\geq 0$. *}

lemma fnorm_ge_zero [intro?]: 
  "[| is_continuous V norm f; is_normed_vectorspace V norm |]
   ==> #0 <= \<parallel>f\<parallel>V,norm"
proof -
  assume c: "is_continuous V norm f" 
     and n: "is_normed_vectorspace V norm"

  txt {* The function norm is defined as the supremum of $B$. 
  So it is $\geq 0$ if all elements in $B$ are $\geq 0$, provided
  the supremum exists and $B$ is not empty. *}

  show ?thesis 
  proof (unfold function_norm_def, rule sup_ub1)
    show "\<forall>x \<in> (B V norm f). #0 <= x" 
    proof (intro ballI, unfold B_def,
           elim UnE singletonE CollectE exE conjE) 
      fix x r
      assume "x \<in> V" "x \<noteq> 0" 
        and r: "r = |f x| * inverse (norm x)"

      have ge: "#0 <= |f x|" by (simp! only: abs_ge_zero)
      have "#0 <= inverse (norm x)" 
        by (rule real_less_imp_le, rule real_inverse_gt_zero1, rule)(***
        proof (rule real_less_imp_le);
          show "#0 < inverse (norm x)"; 
          proof (rule real_inverse_gt_zero);
            show "#0 < norm x"; ..;
          qed;
        qed; ***)
      with ge show "#0 <= r"
       by (simp only: r, rule real_le_mult_order1a)
    qed (simp!)

    txt {* Since $f$ is continuous the function norm exists: *}

    have "is_function_norm f V norm \<parallel>f\<parallel>V,norm" ..
    thus "is_Sup UNIV (B V norm f) (Sup UNIV (B V norm f))" 
      by (unfold is_function_norm_def function_norm_def)

    txt {* $B$ is non-empty by construction: *}

    show "#0 \<in> B V norm f" by (rule B_not_empty)
  qed
qed
  
text{* \medskip The fundamental property of function norms is: 
\begin{matharray}{l}
| f\ap x | \leq {\fnorm {f}} \cdot {\norm x}  
\end{matharray}
*}

lemma norm_fx_le_norm_f_norm_x: 
  "[| is_continuous V norm f; is_normed_vectorspace V norm; x \<in> V |] 
    ==> |f x| <= \<parallel>f\<parallel>V,norm * norm x"
proof - 
  assume "is_normed_vectorspace V norm" "x \<in> V" 
  and c: "is_continuous V norm f"
  have v: "is_vectorspace V" ..

 txt{* The proof is by case analysis on $x$. *}
 
  show ?thesis
  proof cases

    txt {* For the case $x = \zero$ the thesis follows
    from the linearity of $f$: for every linear function
    holds $f\ap \zero = 0$. *}

    assume "x = 0"
    have "|f x| = |f 0|" by (simp!)
    also from v continuous_linearform have "f 0 = #0" ..
    also note abs_zero
    also have "#0 <= \<parallel>f\<parallel>V,norm * norm x"
    proof (rule real_le_mult_order1a)
      show "#0 <= \<parallel>f\<parallel>V,norm" ..
      show "#0 <= norm x" ..
    qed
    finally 
    show "|f x| <= \<parallel>f\<parallel>V,norm * norm x" .

  next
    assume "x \<noteq> 0"
    have n: "#0 < norm x" ..
    hence nz: "norm x \<noteq> #0" 
      by (simp only: lt_imp_not_eq)

    txt {* For the case $x\neq \zero$ we derive the following
    fact from the definition of the function norm:*}

    have l: "|f x| * inverse (norm x) <= \<parallel>f\<parallel>V,norm"
    proof (unfold function_norm_def, rule sup_ub)
      from ex_fnorm [OF _ c]
      show "is_Sup UNIV (B V norm f) (Sup UNIV (B V norm f))"
         by (simp! add: is_function_norm_def function_norm_def)
      show "|f x| * inverse (norm x) \<in> B V norm f" 
        by (unfold B_def, intro UnI2 CollectI exI [of _ x]
            conjI, simp)
    qed

    txt {* The thesis now follows by a short calculation: *}

    have "|f x| = |f x| * #1" by (simp!)
    also from nz have "#1 = inverse (norm x) * norm x" 
      by (simp add: real_mult_inv_left1)
    also have "|f x| * ... = |f x| * inverse (norm x) * norm x"
      by (simp! add: real_mult_assoc)
    also from n l have "... <= \<parallel>f\<parallel>V,norm * norm x"
      by (simp add: real_mult_le_le_mono2)
    finally show "|f x| <= \<parallel>f\<parallel>V,norm * norm x" .
  qed
qed

text{* \medskip The function norm is the least positive real number for 
which the following inequation holds:
\begin{matharray}{l}
| f\ap x | \leq c \cdot {\norm x}  
\end{matharray} 
*}

lemma fnorm_le_ub: 
  "[| is_continuous V norm f; is_normed_vectorspace V norm; 
     \<forall>x \<in> V. |f x| <= c * norm x; #0 <= c |]
  ==> \<parallel>f\<parallel>V,norm <= c"
proof (unfold function_norm_def)
  assume "is_normed_vectorspace V norm" 
  assume c: "is_continuous V norm f"
  assume fb: "\<forall>x \<in> V. |f x| <= c * norm x"
    and "#0 <= c"

  txt {* Suppose the inequation holds for some $c\geq 0$.
  If $c$ is an upper bound of $B$, then $c$ is greater 
  than the function norm since the function norm is the
  least upper bound.
  *}

  show "Sup UNIV (B V norm f) <= c" 
  proof (rule sup_le_ub)
    from ex_fnorm [OF _ c] 
    show "is_Sup UNIV (B V norm f) (Sup UNIV (B V norm f))" 
      by (simp! add: is_function_norm_def function_norm_def) 
  
    txt {* $c$ is an upper bound of $B$, i.e. every
    $y\in B$ is less than $c$. *}

    show "isUb UNIV (B V norm f) c"  
    proof (intro isUbI setleI ballI)
      fix y assume "y \<in> B V norm f"
      thus le: "y <= c"
      proof (unfold B_def, elim UnE CollectE exE conjE singletonE)

       txt {* The first case for $y\in B$ is $y=0$. *}

        assume "y = #0"
        show "y <= c" by (force!)

        txt{* The second case is 
        $y = {|f\ap x|}/{\norm x}$ for some 
        $x\in V$ with $x \neq \zero$. *}  

      next
	fix x 
        assume "x \<in> V" "x \<noteq> 0" 

        have lz: "#0 < norm x" 
          by (simp! add: normed_vs_norm_gt_zero)
          
        have nz: "norm x \<noteq> #0" 
        proof (rule not_sym)
          from lz show "#0 \<noteq> norm x"
            by (simp! add: order_less_imp_not_eq)
        qed
            
	from lz have "#0 < inverse (norm x)"
	  by (simp! add: real_inverse_gt_zero1)
	hence inverse_gez: "#0 <= inverse (norm x)"
          by (rule real_less_imp_le)

	assume "y = |f x| * inverse (norm x)" 
	also from inverse_gez have "... <= c * norm x * inverse (norm x)"
	  proof (rule real_mult_le_le_mono2)
	    show "|f x| <= c * norm x" by (rule bspec)
	  qed
	also have "... <= c" by (simp add: nz real_mult_assoc)
	finally show ?thesis .
      qed
    qed force
  qed
qed

end