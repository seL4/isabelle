(*  Title:      HOL/Real/HahnBanach/HahnBanachSupLemmas.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* The supremum w.r.t.~the function order *}

theory HahnBanachSupLemmas = FunctionNorm + ZornLemma:

text{* This section contains some lemmas that will be used in the
proof of the Hahn-Banach Theorem.
In this section the following context is presumed. 
Let $E$ be a real vector space with a seminorm $p$ on $E$. 
$F$ is a subspace of $E$ and $f$ a linear form on $F$. We 
consider a chain $c$ of norm-preserving extensions of $f$, such that
$\Union c = \idt{graph}\ap H\ap h$. 
We will show some properties about the limit function $h$, 
i.e.\ the supremum of the chain $c$.
*} 

text{* Let $c$ be a chain of norm-preserving extensions of the 
function $f$ and let $\idt{graph}\ap H\ap h$ be the supremum of $c$. 
Every element in $H$ is member of
one of the elements of the chain. *}

lemma some_H'h't:
  "[| M = norm_pres_extensions E p F f; c \<in> chain M; 
  graph H h = \<Union> c; x \<in> H |]
   ==> \<exists>H' h'. graph H' h' \<in> c \<and> (x, h x) \<in> graph H' h' 
       \<and> is_linearform H' h' \<and> is_subspace H' E 
       \<and> is_subspace F H' \<and> graph F f \<subseteq> graph H' h' 
       \<and> (\<forall>x \<in> H'. h' x \<le> p x)"
proof -
  assume m: "M = norm_pres_extensions E p F f" and "c \<in> chain M"
     and u: "graph H h = \<Union> c" "x \<in> H"

  have h: "(x, h x) \<in> graph H h" ..
  with u have "(x, h x) \<in> \<Union> c" by simp
  hence ex1: "\<exists>g \<in> c. (x, h x) \<in> g" 
    by (simp only: Union_iff)
  thus ?thesis
  proof (elim bexE)
    fix g assume g: "g \<in> c" "(x, h x) \<in> g"
    have "c \<subseteq> M" by (rule chainD2)
    hence "g \<in> M" ..
    hence "g \<in> norm_pres_extensions E p F f" by (simp only: m)
    hence "\<exists>H' h'. graph H' h' = g 
                  \<and> is_linearform H' h'
                  \<and> is_subspace H' E
                  \<and> is_subspace F H'
                  \<and> graph F f \<subseteq> graph H' h'
                  \<and> (\<forall>x \<in> H'. h' x \<le> p x)"
      by (rule norm_pres_extension_D)
    thus ?thesis
    proof (elim exE conjE) 
      fix H' h' 
      assume "graph H' h' = g" "is_linearform H' h'" 
        "is_subspace H' E" "is_subspace F H'" 
        "graph F f \<subseteq> graph H' h'" "\<forall>x \<in> H'. h' x \<le> p x"
      show ?thesis 
      proof (intro exI conjI)
        show "graph H' h' \<in> c" by (simp!)
        show "(x, h x) \<in> graph H' h'" by (simp!)
      qed
    qed
  qed
qed


text{*  \medskip Let $c$ be a chain of norm-preserving extensions of the
function $f$ and let $\idt{graph}\ap H\ap h$ be the supremum of $c$. 
Every element in the domain $H$ of the supremum function is member of
the domain $H'$ of some function $h'$, such that $h$ extends $h'$.
*}

lemma some_H'h': 
  "[| M = norm_pres_extensions E p F f; c \<in> chain M; 
  graph H h = \<Union> c; x \<in> H |] 
  ==> \<exists>H' h'. x \<in> H' \<and> graph H' h' \<subseteq> graph H h 
      \<and> is_linearform H' h' \<and> is_subspace H' E \<and> is_subspace F H'
      \<and> graph F f \<subseteq> graph H' h' \<and> (\<forall>x \<in> H'. h' x \<le> p x)" 
proof -
  assume "M = norm_pres_extensions E p F f" and cM: "c \<in> chain M"
     and u: "graph H h = \<Union> c" "x \<in> H"  

  have "\<exists>H' h'. graph H' h' \<in> c \<and> (x, h x) \<in> graph H' h' 
       \<and> is_linearform H' h' \<and> is_subspace H' E 
       \<and> is_subspace F H' \<and> graph F f \<subseteq> graph H' h' 
       \<and> (\<forall>x \<in> H'. h' x \<le> p x)"
    by (rule some_H'h't)
  thus ?thesis 
  proof (elim exE conjE)
    fix H' h' assume "(x, h x) \<in> graph H' h'" "graph H' h' \<in> c"
      "is_linearform H' h'" "is_subspace H' E" "is_subspace F H'" 
      "graph F f \<subseteq> graph H' h'" "\<forall>x \<in> H'. h' x \<le> p x"
    show ?thesis
    proof (intro exI conjI)
      show "x \<in> H'" by (rule graphD1)
      from cM u show "graph H' h' \<subseteq> graph H h" 
        by (simp! only: chain_ball_Union_upper)
    qed
  qed
qed


text{* \medskip Any two elements $x$ and $y$ in the domain $H$ of the 
supremum function $h$ are both in the domain $H'$ of some function 
$h'$, such that $h$ extends $h'$. *}

lemma some_H'h'2: 
  "[| M = norm_pres_extensions E p F f; c \<in> chain M; 
  graph H h = \<Union> c;  x \<in> H; y \<in> H |] 
  ==> \<exists>H' h'. x \<in> H' \<and> y \<in> H' \<and> graph H' h' \<subseteq> graph H h 
      \<and> is_linearform H' h' \<and> is_subspace H' E \<and> is_subspace F H'
      \<and> graph F f \<subseteq> graph H' h' \<and> (\<forall>x \<in> H'. h' x \<le> p x)" 
proof -
  assume "M = norm_pres_extensions E p F f" "c \<in> chain M" 
         "graph H h = \<Union> c" "x \<in> H" "y \<in> H"

  txt {* $x$ is in the domain $H'$ of some function $h'$, 
  such that $h$ extends $h'$. *} 

  have e1: "\<exists>H' h'. graph H' h' \<in> c \<and> (x, h x) \<in> graph H' h'
       \<and> is_linearform H' h' \<and> is_subspace H' E 
       \<and> is_subspace F H' \<and> graph F f \<subseteq> graph H' h' 
       \<and> (\<forall>x \<in> H'. h' x \<le> p x)"
    by (rule some_H'h't)

  txt {* $y$ is in the domain $H''$ of some function $h''$,
  such that $h$ extends $h''$. *} 

  have e2: "\<exists>H'' h''. graph H'' h'' \<in> c \<and> (y, h y) \<in> graph H'' h''
       \<and> is_linearform H'' h'' \<and> is_subspace H'' E 
       \<and> is_subspace F H'' \<and> graph F f \<subseteq> graph H'' h'' 
       \<and> (\<forall>x \<in> H''. h'' x \<le> p x)"
    by (rule some_H'h't)

  from e1 e2 show ?thesis 
  proof (elim exE conjE)
    fix H' h' assume "(y, h y) \<in> graph H' h'" "graph H' h' \<in> c"
      "is_linearform H' h'" "is_subspace H' E" "is_subspace F H'" 
      "graph F f \<subseteq> graph H' h'" "\<forall>x \<in> H'. h' x \<le> p x"

    fix H'' h'' assume "(x, h x) \<in> graph H'' h''" "graph H'' h'' \<in> c"
      "is_linearform H'' h''" "is_subspace H'' E" "is_subspace F H''"
      "graph F f \<subseteq> graph H'' h''" "\<forall>x \<in> H''. h'' x \<le> p x"

   txt {* Since both $h'$ and $h''$ are elements of the chain,  
   $h''$ is an extension of $h'$ or vice versa. Thus both 
   $x$ and $y$ are contained in the greater one. \label{cases1}*}

    have "graph H'' h'' \<subseteq> graph H' h' | graph H' h' \<subseteq> graph H'' h''"
      (is "?case1 | ?case2")
      by (rule chainD)
    thus ?thesis
    proof 
      assume ?case1
      show ?thesis
      proof (intro exI conjI)
        have "(x, h x) \<in> graph H'' h''" .
        also have "... \<subseteq> graph H' h'" .
        finally have xh:"(x, h x) \<in> graph H' h'" .
        thus x: "x \<in> H'" ..
        show y: "y \<in> H'" ..
        show "graph H' h' \<subseteq> graph H h"
          by (simp! only: chain_ball_Union_upper)
      qed
    next
      assume ?case2
      show ?thesis
      proof (intro exI conjI)
        show x: "x \<in> H''" ..
        have "(y, h y) \<in> graph H' h'" by (simp!)
        also have "... \<subseteq> graph H'' h''" .
        finally have yh: "(y, h y) \<in> graph H'' h''" .
        thus y: "y \<in> H''" ..
        show "graph H'' h'' \<subseteq> graph H h"
          by (simp! only: chain_ball_Union_upper)
      qed
    qed
  qed
qed



text{* \medskip The relation induced by the graph of the supremum
of a chain $c$ is definite, i.~e.~t is the graph of a function. *}

lemma sup_definite: 
  "[| M == norm_pres_extensions E p F f; c \<in> chain M; 
  (x, y) \<in> \<Union> c; (x, z) \<in> \<Union> c |] ==> z = y"
proof - 
  assume "c \<in> chain M" "M == norm_pres_extensions E p F f"
    "(x, y) \<in> \<Union> c" "(x, z) \<in> \<Union> c"
  thus ?thesis
  proof (elim UnionE chainE2)

    txt{* Since both $(x, y) \in \Union c$ and $(x, z) \in \Union c$
    they are members of some graphs $G_1$ and $G_2$, resp., such that
    both $G_1$ and $G_2$ are members of $c$.*}

    fix G1 G2 assume
      "(x, y) \<in> G1" "G1 \<in> c" "(x, z) \<in> G2" "G2 \<in> c" "c \<subseteq> M"

    have "G1 \<in> M" ..
    hence e1: "\<exists> H1 h1. graph H1 h1 = G1"  
      by (force! dest: norm_pres_extension_D)
    have "G2 \<in> M" ..
    hence e2: "\<exists> H2 h2. graph H2 h2 = G2"  
      by (force! dest: norm_pres_extension_D)
    from e1 e2 show ?thesis 
    proof (elim exE)
      fix H1 h1 H2 h2 
      assume "graph H1 h1 = G1" "graph H2 h2 = G2"

      txt{* $G_1$ is contained in $G_2$ or vice versa, 
      since both $G_1$ and $G_2$ are members of $c$. \label{cases2}*}

      have "G1 \<subseteq> G2 | G2 \<subseteq> G1" (is "?case1 | ?case2") ..
      thus ?thesis
      proof
        assume ?case1
        have "(x, y) \<in> graph H2 h2" by (force!)
        hence "y = h2 x" ..
        also have "(x, z) \<in> graph H2 h2" by (simp!)
        hence "z = h2 x" ..
        finally show ?thesis .
      next
        assume ?case2
        have "(x, y) \<in> graph H1 h1" by (simp!)
        hence "y = h1 x" ..
        also have "(x, z) \<in> graph H1 h1" by (force!)
        hence "z = h1 x" ..
        finally show ?thesis .
      qed
    qed
  qed
qed

text{* \medskip The limit function $h$ is linear. Every element $x$ in the
domain of $h$ is in the domain of a function $h'$ in the chain of norm
preserving extensions.  Furthermore, $h$ is an extension of $h'$ so
the function values of $x$ are identical for $h'$ and $h$.  Finally, the
function $h'$ is linear by construction of $M$.  *}

lemma sup_lf: 
  "[| M = norm_pres_extensions E p F f; c \<in> chain M; 
  graph H h = \<Union> c |] ==> is_linearform H h"
proof - 
  assume "M = norm_pres_extensions E p F f" "c \<in> chain M"
         "graph H h = \<Union> c"
 
  show "is_linearform H h"
  proof
    fix x y assume "x \<in> H" "y \<in> H" 
    have "\<exists>H' h'. x \<in> H' \<and> y \<in> H' \<and> graph H' h' \<subseteq> graph H h 
            \<and> is_linearform H' h' \<and> is_subspace H' E 
            \<and> is_subspace F H' \<and> graph F f \<subseteq> graph H' h'
            \<and> (\<forall>x \<in> H'. h' x \<le> p x)"
      by (rule some_H'h'2)

    txt {* We have to show that $h$ is additive. *}

    thus "h (x + y) = h x + h y" 
    proof (elim exE conjE)
      fix H' h' assume "x \<in> H'" "y \<in> H'" 
        and b: "graph H' h' \<subseteq> graph H h" 
        and "is_linearform H' h'" "is_subspace H' E"
      have "h' (x + y) = h' x + h' y" 
        by (rule linearform_add)
      also have "h' x = h x" ..
      also have "h' y = h y" ..
      also have "x + y \<in> H'" ..
      with b have "h' (x + y) = h (x + y)" ..
      finally show ?thesis .
    qed
  next  
    fix a x assume "x \<in> H"
    have "\<exists> H' h'. x \<in> H' \<and> graph H' h' \<subseteq> graph H h 
            \<and> is_linearform H' h' \<and> is_subspace H' E
            \<and> is_subspace F H' \<and> graph F f \<subseteq> graph H' h' 
            \<and> (\<forall> x \<in> H'. h' x \<le> p x)"
      by (rule some_H'h')

    txt{* We have to show that $h$ is multiplicative. *}

    thus "h (a \<cdot> x) = a * h x"
    proof (elim exE conjE)
      fix H' h' assume "x \<in> H'"
        and b: "graph H' h' \<subseteq> graph H h" 
        and "is_linearform H' h'" "is_subspace H' E"
      have "h' (a \<cdot> x) = a * h' x" 
        by (rule linearform_mult)
      also have "h' x = h x" ..
      also have "a \<cdot> x \<in> H'" ..
      with b have "h' (a \<cdot> x) = h (a \<cdot> x)" ..
      finally show ?thesis .
    qed
  qed
qed

text{* \medskip The limit of a non-empty chain of norm
preserving extensions of $f$ is an extension of $f$,
since every element of the chain is an extension
of $f$ and the supremum is an extension
for every element of the chain.*}

lemma sup_ext:
  "[| graph H h = \<Union> c; M = norm_pres_extensions E p F f; 
  c \<in> chain M; \<exists>x. x \<in> c |] ==> graph F f \<subseteq> graph H h"
proof -
  assume "M = norm_pres_extensions E p F f" "c \<in> chain M" 
         "graph H h = \<Union> c"
  assume "\<exists>x. x \<in> c"
  thus ?thesis 
  proof
    fix x assume "x \<in> c" 
    have "c \<subseteq> M" by (rule chainD2)
    hence "x \<in> M" ..
    hence "x \<in> norm_pres_extensions E p F f" by (simp!)

    hence "\<exists>G g. graph G g = x
             \<and> is_linearform G g 
             \<and> is_subspace G E
             \<and> is_subspace F G
             \<and> graph F f \<subseteq> graph G g 
             \<and> (\<forall>x \<in> G. g x \<le> p x)"
      by (simp! add: norm_pres_extension_D)

    thus ?thesis 
    proof (elim exE conjE) 
      fix G g assume "graph F f \<subseteq> graph G g"
      also assume "graph G g = x"
      also have "... \<in> c" .
      hence "x \<subseteq> \<Union> c" by fast
      also have [RS sym]: "graph H h = \<Union> c" .
      finally show ?thesis .
    qed
  qed
qed

text{* \medskip The domain $H$ of the limit function is a superspace of $F$,
since $F$ is a subset of $H$. The existence of the $\zero$ element in
$F$ and the closure properties follow from the fact that $F$ is a
vector space. *}

lemma sup_supF: 
  "[|  graph H h = \<Union> c; M = norm_pres_extensions E p F f; 
  c \<in> chain M; \<exists>x. x \<in> c; is_subspace F E; is_vectorspace E |] 
  ==> is_subspace F H"
proof - 
  assume "M = norm_pres_extensions E p F f" "c \<in> chain M" "\<exists>x. x \<in> c"
    "graph H h = \<Union> c" "is_subspace F E" "is_vectorspace E"

  show ?thesis 
  proof
    show "0 \<in> F" ..
    show "F \<subseteq> H" 
    proof (rule graph_extD2)
      show "graph F f \<subseteq> graph H h"
        by (rule sup_ext)
    qed
    show "\<forall>x \<in> F. \<forall>y \<in> F. x + y \<in> F" 
    proof (intro ballI) 
      fix x y assume "x \<in> F" "y \<in> F"
      show "x + y \<in> F" by (simp!)
    qed
    show "\<forall>x \<in> F. \<forall>a. a \<cdot> x \<in> F"
    proof (intro ballI allI)
      fix x a assume "x\<in>F"
      show "a \<cdot> x \<in> F" by (simp!)
    qed
  qed
qed

text{* \medskip The domain $H$ of the limit function is a subspace
of $E$. *}

lemma sup_subE: 
  "[| graph H h = \<Union> c; M = norm_pres_extensions E p F f; 
  c \<in> chain M; \<exists>x. x \<in> c; is_subspace F E; is_vectorspace E |] 
  ==> is_subspace H E"
proof - 
  assume "M = norm_pres_extensions E p F f" "c \<in> chain M" "\<exists>x. x \<in> c"
    "graph H h = \<Union> c" "is_subspace F E" "is_vectorspace E"
  show ?thesis 
  proof
 
    txt {* The $\zero$ element is in $H$, as $F$ is a subset 
    of $H$: *}

    have "0 \<in> F" ..
    also have "is_subspace F H" by (rule sup_supF) 
    hence "F \<subseteq> H" ..
    finally show "0 \<in> H" .

    txt{* $H$ is a subset of $E$: *}

    show "H \<subseteq> E" 
    proof
      fix x assume "x \<in> H"
      have "\<exists>H' h'. x \<in> H' \<and> graph H' h' \<subseteq> graph H h
              \<and> is_linearform H' h' \<and> is_subspace H' E 
              \<and> is_subspace F H' \<and> graph F f \<subseteq> graph H' h' 
              \<and> (\<forall>x \<in> H'. h' x \<le> p x)" 
	by (rule some_H'h')
      thus "x \<in> E" 
      proof (elim exE conjE)
	fix H' h' assume "x \<in> H'" "is_subspace H' E"
        have "H' \<subseteq> E" ..
	thus "x \<in> E" ..
      qed
    qed

    txt{* $H$ is closed under addition: *}

    show "\<forall>x \<in> H. \<forall>y \<in> H. x + y \<in> H" 
    proof (intro ballI) 
      fix x y assume "x \<in> H" "y \<in> H"
      have "\<exists>H' h'. x \<in> H' \<and> y \<in> H' \<and> graph H' h' \<subseteq> graph H h 
              \<and> is_linearform H' h' \<and> is_subspace H' E 
              \<and> is_subspace F H' \<and> graph F f \<subseteq> graph H' h' 
              \<and> (\<forall>x \<in> H'. h' x \<le> p x)" 
	by (rule some_H'h'2) 
      thus "x + y \<in> H" 
      proof (elim exE conjE) 
	fix H' h' 
        assume "x \<in> H'" "y \<in> H'" "is_subspace H' E" 
          "graph H' h' \<subseteq> graph H h"
        have "x + y \<in> H'" ..
	also have "H' \<subseteq> H" ..
	finally show ?thesis .
      qed
    qed      

    txt{* $H$ is closed under scalar multiplication: *}

    show "\<forall>x \<in> H. \<forall>a. a \<cdot> x \<in> H" 
    proof (intro ballI allI) 
      fix x a assume "x \<in> H" 
      have "\<exists>H' h'. x \<in> H' \<and> graph H' h' \<subseteq> graph H h
              \<and> is_linearform H' h' \<and> is_subspace H' E 
              \<and> is_subspace F H' \<and> graph F f \<subseteq> graph H' h' 
              \<and> (\<forall>x \<in> H'. h' x \<le> p x)" 
	by (rule some_H'h') 
      thus "a \<cdot> x \<in> H" 
      proof (elim exE conjE)
	fix H' h' 
        assume "x \<in> H'" "is_subspace H' E" "graph H' h' \<subseteq> graph H h"
        have "a \<cdot> x \<in> H'" ..
        also have "H' \<subseteq> H" ..
	finally show ?thesis .
      qed
    qed
  qed
qed

text {* \medskip The limit function is bounded by 
the norm $p$ as well, since all elements in the chain are
bounded by $p$.
*}

lemma sup_norm_pres:
  "[| graph H h = \<Union> c; M = norm_pres_extensions E p F f; c \<in> chain M |] 
  ==> \<forall> x \<in> H. h x \<le> p x"
proof
  assume "M = norm_pres_extensions E p F f" "c \<in> chain M" 
         "graph H h = \<Union> c"
  fix x assume "x \<in> H"
  have "\<exists>H' h'. x \<in> H' \<and> graph H' h' \<subseteq> graph H h 
          \<and> is_linearform H' h' \<and> is_subspace H' E \<and> is_subspace F H'
          \<and> graph F f \<subseteq> graph H' h' \<and> (\<forall> x \<in> H'. h' x \<le> p x)" 
    by (rule some_H'h')
  thus "h x \<le> p x" 
  proof (elim exE conjE)
    fix H' h' 
    assume "x \<in> H'" "graph H' h' \<subseteq> graph H h" 
      and a: "\<forall>x \<in> H'. h' x \<le> p x"
    have [RS sym]: "h' x = h x" ..
    also from a have "h' x \<le> p x " ..
    finally show ?thesis .  
  qed
qed


text{* \medskip The following lemma is a property of linear forms on 
real vector spaces. It will be used for the lemma 
$\idt{abs{\dsh}HahnBanach}$ (see page \pageref{abs-HahnBanach}). \label{abs-ineq-iff}
For real vector spaces the following inequations are equivalent:
\begin{matharray}{ll} 
\forall x\in H.\ap |h\ap x|\leq p\ap x& {\rm and}\\ 
\forall x\in H.\ap h\ap x\leq p\ap x\\ 
\end{matharray}
*}

lemma abs_ineq_iff: 
  "[| is_subspace H E; is_vectorspace E; is_seminorm E p; 
  is_linearform H h |] 
  ==> (\<forall>x \<in> H. |h x| \<le> p x) = (\<forall>x \<in> H. h x \<le> p x)" 
  (concl is "?L = ?R")
proof -
  assume "is_subspace H E" "is_vectorspace E" "is_seminorm E p" 
         "is_linearform H h"
  have h: "is_vectorspace H" ..
  show ?thesis
  proof 
    assume l: ?L
    show ?R
    proof
      fix x assume x: "x \<in> H"
      have "h x \<le> |h x|" by (rule abs_ge_self)
      also from l have "... \<le> p x" ..
      finally show "h x \<le> p x" .
    qed
  next
    assume r: ?R
    show ?L
    proof 
      fix x assume "x \<in> H"
      show "!! a b :: real. [| - a \<le> b; b \<le> a |] ==> |b| \<le> a"
        by arith
      show "- p x \<le> h x"
      proof (rule real_minus_le)
	from h have "- h x = h (- x)" 
          by (rule linearform_neg [RS sym])
	also from r have "... \<le> p (- x)" by (simp!)
	also have "... = p x" 
          by (rule seminorm_minus [OF _ subspace_subsetD])
	finally show "- h x \<le> p x" . 
      qed
      from r show "h x \<le> p x" .. 
    qed
  qed
qed  


end