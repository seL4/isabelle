(*  Title:      HOL/Real/HahnBanach/HahnBanachSupLemmas.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* The supremum w.r.t.~the function order *};

theory HahnBanachSupLemmas = FunctionNorm + ZornLemma:;



text{* This section contains some lemmas that will be used in the
proof of the Hahn-Banach Theorem.
In this section the following context is presumed. 
Let $E$ be a real vector space with a seminorm $p$ on $E$. 
$F$ is a subspace of $E$ and $f$ a linear form on $F$. We 
consider a chain $c$ of norm-preserving extensions of $f$, such that
$\Union c = \idt{graph}\ap H\ap h$. 
We will show some properties about the limit function $h$, 
i.e.\ the supremum of the chain $c$.
*}; 

(***
lemma some_H'h't:
  "[| M = norm_pres_extensions E p F f; c: chain M; 
  graph H h = Union c; x:H |]
   ==> EX H' h' t. t : graph H h & t = (x, h x) & graph H' h':c 
       & t:graph H' h' & is_linearform H' h' & is_subspace H' E 
       & is_subspace F H' & graph F f <= graph H' h' 
       & (ALL x:H'. h' x <= p x)";
proof -;
  assume m: "M = norm_pres_extensions E p F f" and cM: "c: chain M"
     and u: "graph H h = Union c" "x:H";

  let ?P = "\\<lambda>H h. is_linearform H h
                & is_subspace H E
                & is_subspace F H
                & graph F f <= graph H h
                & (ALL x:H. h x <= p x)";

  have "EX t : graph H h. t = (x, h x)"; 
    by (rule graphI2);
  thus ?thesis;
  proof (elim bexE); 
    fix t; assume t: "t : graph H h" "t = (x, h x)";
    with u; have ex1: "EX g:c. t:g";
      by (simp only: Union_iff);
    thus ?thesis;
    proof (elim bexE);
      fix g; assume g: "g:c" "t:g";
      from cM; have "c <= M"; by (rule chainD2);
      hence "g : M"; ..;
      hence "g : norm_pres_extensions E p F f"; by (simp only: m);
      hence "EX H' h'. graph H' h' = g & ?P H' h'"; 
        by (rule norm_pres_extension_D);
      thus ?thesis; 
       by (elim exE conjE, intro exI conjI) (simp | simp!)+;
    qed;
  qed;
qed;
***)

text{* Let $c$ be a chain of norm-preserving extensions of the 
function $f$ and let $\idt{graph}\ap H\ap h$ be the supremum of $c$. 
Every element in $H$ is member of
one of the elements of the chain. *};

lemma some_H'h't:
  "[| M = norm_pres_extensions E p F f; c: chain M; 
  graph H h = Union c; x:H |]
   ==> EX H' h'. graph H' h' : c & (x, h x) : graph H' h' 
       & is_linearform H' h' & is_subspace H' E 
       & is_subspace F H' & graph F f <= graph H' h' 
       & (ALL x:H'. h' x <= p x)";
proof -;
  assume m: "M = norm_pres_extensions E p F f" and "c: chain M"
     and u: "graph H h = Union c" "x:H";

  have h: "(x, h x) : graph H h"; ..;
  with u; have "(x, h x) : Union c"; by simp;
  hence ex1: "EX g:c. (x, h x) : g"; 
    by (simp only: Union_iff);
  thus ?thesis;
  proof (elim bexE);
    fix g; assume g: "g:c" "(x, h x) : g";
    have "c <= M"; by (rule chainD2);
    hence "g : M"; ..;
    hence "g : norm_pres_extensions E p F f"; by (simp only: m);
    hence "EX H' h'. graph H' h' = g 
                  & is_linearform H' h'
                  & is_subspace H' E
                  & is_subspace F H'
                  & graph F f <= graph H' h'
                  & (ALL x:H'. h' x <= p x)";
      by (rule norm_pres_extension_D);
    thus ?thesis;
    proof (elim exE conjE); 
      fix H' h'; 
      assume "graph H' h' = g" "is_linearform H' h'" 
        "is_subspace H' E" "is_subspace F H'" 
        "graph F f <= graph H' h'" "ALL x:H'. h' x <= p x";
      show ?thesis; 
      proof (intro exI conjI);
        show "graph H' h' : c"; by (simp!);
        show "(x, h x) : graph H' h'"; by (simp!);
      qed;
    qed;
  qed;
qed;


text{*  \medskip Let $c$ be a chain of norm-preserving extensions of the
function $f$ and let $\idt{graph}\ap H\ap h$ be the supremum of $c$. 
Every element in the domain $H$ of the supremum function is member of
the domain $H'$ of some function $h'$, such that $h$ extends $h'$.
*};

lemma some_H'h': 
  "[| M = norm_pres_extensions E p F f; c: chain M; 
  graph H h = Union c; x:H |] 
  ==> EX H' h'. x:H' & graph H' h' <= graph H h 
      & is_linearform H' h' & is_subspace H' E & is_subspace F H'
      & graph F f <= graph H' h' & (ALL x:H'. h' x <= p x)"; 
proof -;
  assume "M = norm_pres_extensions E p F f" and cM: "c: chain M"
     and u: "graph H h = Union c" "x:H";  

  have "EX H' h'. graph H' h' : c & (x, h x) : graph H' h' 
       & is_linearform H' h' & is_subspace H' E 
       & is_subspace F H' & graph F f <= graph H' h' 
       & (ALL x:H'. h' x <= p x)";
    by (rule some_H'h't);
  thus ?thesis; 
  proof (elim exE conjE);
    fix H' h'; assume "(x, h x) : graph H' h'" "graph H' h' : c"
      "is_linearform H' h'" "is_subspace H' E" "is_subspace F H'" 
      "graph F f <= graph H' h'" "ALL x:H'. h' x <= p x";
    show ?thesis;
    proof (intro exI conjI);
      show "x:H'"; by (rule graphD1);
      from cM u; show "graph H' h' <= graph H h"; 
        by (simp! only: chain_ball_Union_upper);
    qed;
  qed;
qed;

(***
lemma some_H'h': 
  "[| M = norm_pres_extensions E p F f; c: chain M; 
  graph H h = Union c; x:H |] 
  ==> EX H' h'. x:H' & graph H' h' <= graph H h 
      & is_linearform H' h' & is_subspace H' E & is_subspace F H'
      & graph F f <= graph H' h' & (ALL x:H'. h' x <= p x)"; 
proof -;
  assume m: "M = norm_pres_extensions E p F f" and cM: "c: chain M"
     and u: "graph H h = Union c" "x:H";  
  have "(x, h x): graph H h"; by (rule graphI); 
  hence "(x, h x) : Union c"; by (simp!);
  hence "EX g:c. (x, h x):g"; by (simp only: Union_iff);
  thus ?thesis; 
  proof (elim bexE);
    fix g; assume g: "g:c" "(x, h x):g";
    from cM; have "c <= M"; by (rule chainD2);
    hence "g : M"; ..;
    hence "g : norm_pres_extensions E p F f"; by (simp only: m);
    hence "EX H' h'. graph H' h' = g 
                   & is_linearform H' h'
                   & is_subspace H' E
                   & is_subspace F H'
                   & graph F f <= graph H' h'
                   & (ALL x:H'. h' x <= p x)"; 
      by (rule norm_pres_extension_D);
    thus ?thesis; 
    proof (elim exE conjE, intro exI conjI);
      fix H' h'; assume g': "graph H' h' = g";
      with g; have "(x, h x): graph H' h'"; by simp;
      thus "x:H'"; by (rule graphD1);
      from g g'; have "graph H' h' : c"; by simp;
      with cM u; show "graph H' h' <= graph H h"; 
        by (simp only: chain_ball_Union_upper);
    qed simp+;
  qed;
qed;
***)


text{* \medskip Any two elements $x$ and $y$ in the domain $H$ of the 
supremum function $h$ are both in the domain $H'$ of some function 
$h'$, such that $h$ extends $h'$. *};

lemma some_H'h'2: 
  "[| M = norm_pres_extensions E p F f; c: chain M; 
  graph H h = Union c;  x:H; y:H |] 
  ==> EX H' h'. x:H' & y:H' & graph H' h' <= graph H h 
      & is_linearform H' h' & is_subspace H' E & is_subspace F H'
      & graph F f <= graph H' h' & (ALL x:H'. h' x <= p x)"; 
proof -;
  assume "M = norm_pres_extensions E p F f" "c: chain M" 
         "graph H h = Union c" "x:H" "y:H";

  txt {* $x$ is in the domain $H'$ of some function $h'$, 
  such that $h$ extends $h'$. *}; 

  have e1: "EX H' h'. graph H' h' : c & (x, h x) : graph H' h'
       & is_linearform H' h' & is_subspace H' E 
       & is_subspace F H' & graph F f <= graph H' h' 
       & (ALL x:H'. h' x <= p x)";
    by (rule some_H'h't);

  txt {* $y$ is in the domain $H''$ of some function $h''$,
  such that $h$ extends $h''$. *}; 

  have e2: "EX H'' h''. graph H'' h'' : c & (y, h y) : graph H'' h''
       & is_linearform H'' h'' & is_subspace H'' E 
       & is_subspace F H'' & graph F f <= graph H'' h'' 
       & (ALL x:H''. h'' x <= p x)";
    by (rule some_H'h't);

  from e1 e2; show ?thesis; 
  proof (elim exE conjE);
    fix H' h'; assume "(y, h y): graph H' h'" "graph H' h' : c"
      "is_linearform H' h'" "is_subspace H' E" "is_subspace F H'" 
      "graph F f <= graph H' h'" "ALL x:H'. h' x <= p x";

    fix H'' h''; assume "(x, h x): graph H'' h''" "graph H'' h'' : c"
      "is_linearform H'' h''" "is_subspace H'' E" "is_subspace F H''"
      "graph F f <= graph H'' h''" "ALL x:H''. h'' x <= p x";

   txt {* Since both $h'$ and $h''$ are elements of the chain,  
   $h''$ is an extension of $h'$ or vice versa. Thus both 
   $x$ and $y$ are contained in the greater one. \label{cases1}*};

    have "graph H'' h'' <= graph H' h' | graph H' h' <= graph H'' h''"
      (is "?case1 | ?case2");
      by (rule chainD);
    thus ?thesis;
    proof; 
      assume ?case1;
      show ?thesis;
      proof (intro exI conjI);
        have "(x, h x) : graph H'' h''"; .;
        also; have "... <= graph H' h'"; .;
        finally; have xh: "(x, h x): graph H' h'"; .;
        thus x: "x:H'"; ..;
        show y: "y:H'"; ..;
        show "graph H' h' <= graph H h";
          by (simp! only: chain_ball_Union_upper);
      qed;
    next;
      assume ?case2;
      show ?thesis;
      proof (intro exI conjI);
        show x: "x:H''"; ..;
        have "(y, h y) : graph H' h'"; by (simp!);
        also; have "... <= graph H'' h''"; .;
        finally; have yh: "(y, h y): graph H'' h''"; .;
        thus y: "y:H''"; ..;
        show "graph H'' h'' <= graph H h";
          by (simp! only: chain_ball_Union_upper);
      qed;
    qed;
  qed;
qed;

(***
lemma some_H'h'2: 
  "[| M = norm_pres_extensions E p F f; c: chain M; 
  graph H h = Union c;  x:H; y:H |] 
  ==> EX H' h'. x:H' & y:H' & graph H' h' <= graph H h 
      & is_linearform H' h' & is_subspace H' E & is_subspace F H' 
      & graph F f <= graph H' h' & (ALL x:H'. h' x <= p x)"; 
proof -;
  assume "M = norm_pres_extensions E p F f" "c: chain M" 
         "graph H h = Union c";
 
  let ?P = "\\<lambda>H h. is_linearform H h 
                & is_subspace H E 
                & is_subspace F H
                & graph F f <= graph H h
                & (ALL x:H. h x <= p x)";
  assume "x:H";
  have e1: "EX H' h' t. t : graph H h & t = (x, h x) 
            & graph H' h' : c & t : graph H' h' & ?P H' h'";
    by (rule some_H'h't); 
  assume "y:H";
  have e2: "EX H' h' t. t : graph H h & t = (y, h y) 
            & graph H' h' : c & t:graph H' h' & ?P H' h'";
    by (rule some_H'h't); 

  from e1 e2; show ?thesis; 
  proof (elim exE conjE);
    fix H' h' t' H'' h'' t''; 
    assume 
      "t' : graph H h"             "t'' : graph H h" 
      "t' = (y, h y)"              "t'' = (x, h x)"
      "graph H' h' : c"            "graph H'' h'' : c"
      "t' : graph H' h'"           "t'' : graph H'' h''" 
      "is_linearform H' h'"        "is_linearform H'' h''"
      "is_subspace H' E"           "is_subspace H'' E"
      "is_subspace F H'"           "is_subspace F H''"
      "graph F f <= graph H' h'"   "graph F f <= graph H'' h''"
      "ALL x:H'. h' x <= p x"      "ALL x:H''. h'' x <= p x";

    have "graph H'' h'' <= graph H' h' 
         | graph H' h' <= graph H'' h''";
      by (rule chainD);
    thus "?thesis";
    proof; 
      assume "graph H'' h'' <= graph H' h'";
      show ?thesis;
      proof (intro exI conjI);
        note [trans] = subsetD;
        have "(x, h x) : graph H'' h''"; by (simp!);
	also; have "... <= graph H' h'"; .;
        finally; have xh: "(x, h x): graph H' h'"; .;
	thus x: "x:H'"; by (rule graphD1);
	show y: "y:H'"; by (simp!, rule graphD1);
	show "graph H' h' <= graph H h";
	  by (simp! only: chain_ball_Union_upper);
      qed;
    next;
      assume "graph H' h' <= graph H'' h''";
      show ?thesis;
      proof (intro exI conjI);
	show x: "x:H''"; by (simp!, rule graphD1);
        have "(y, h y) : graph H' h'"; by (simp!);
        also; have "... <= graph H'' h''"; .;
	finally; have yh: "(y, h y): graph H'' h''"; .;
        thus y: "y:H''"; by (rule graphD1);
        show "graph H'' h'' <= graph H h";
          by (simp! only: chain_ball_Union_upper);
      qed;
    qed;
  qed;
qed;

***)

text{* \medskip The relation induced by the graph of the supremum
of a chain $c$ is definite, i.~e.~it is the graph of a function. *};

lemma sup_definite: 
  "[| M == norm_pres_extensions E p F f; c : chain M; 
  (x, y) : Union c; (x, z) : Union c |] ==> z = y";
proof -; 
  assume "c:chain M" "M == norm_pres_extensions E p F f"
    "(x, y) : Union c" "(x, z) : Union c";
  thus ?thesis;
  proof (elim UnionE chainE2);

    txt{* Since both $(x, y) \in \Union c$ and $(x, z) \in \Union c$
    they are members of some graphs $G_1$ and $G_2$, resp., such that
    both $G_1$ and $G_2$ are members of $c$.*};

    fix G1 G2; assume
      "(x, y) : G1" "G1 : c" "(x, z) : G2" "G2 : c" "c <= M";

    have "G1 : M"; ..;
    hence e1: "EX H1 h1. graph H1 h1 = G1";  
      by (force! dest: norm_pres_extension_D);
    have "G2 : M"; ..;
    hence e2: "EX H2 h2. graph H2 h2 = G2";  
      by (force! dest: norm_pres_extension_D);
    from e1 e2; show ?thesis; 
    proof (elim exE);
      fix H1 h1 H2 h2; 
      assume "graph H1 h1 = G1" "graph H2 h2 = G2";

      txt{* $G_1$ is contained in $G_2$ or vice versa, 
      since both $G_1$ and $G_2$ are members of $c$. \label{cases2}*};

      have "G1 <= G2 | G2 <= G1" (is "?case1 | ?case2"); ..;
      thus ?thesis;
      proof;
        assume ?case1;
        have "(x, y) : graph H2 h2"; by (force!);
        hence "y = h2 x"; ..;
        also; have "(x, z) : graph H2 h2"; by (simp!);
        hence "z = h2 x"; ..;
        finally; show ?thesis; .;
      next;
        assume ?case2;
        have "(x, y) : graph H1 h1"; by (simp!);
        hence "y = h1 x"; ..;
        also; have "(x, z) : graph H1 h1"; by (force!);
        hence "z = h1 x"; ..;
        finally; show ?thesis; .;
      qed;
    qed;
  qed;
qed;

text{* \medskip The limit function $h$ is linear. Every element $x$ in the
domain of $h$ is in the domain of a function $h'$ in the chain of norm
preserving extensions.  Furthermore, $h$ is an extension of $h'$ so
the function values of $x$ are identical for $h'$ and $h$.  Finally, the
function $h'$ is linear by construction of $M$.  *};

lemma sup_lf: 
  "[| M = norm_pres_extensions E p F f; c: chain M; 
  graph H h = Union c |] ==> is_linearform H h";
proof -; 
  assume "M = norm_pres_extensions E p F f" "c: chain M"
         "graph H h = Union c";
 
  show "is_linearform H h";
  proof;
    fix x y; assume "x : H" "y : H"; 
    have "EX H' h'. x:H' & y:H' & graph H' h' <= graph H h 
            & is_linearform H' h' & is_subspace H' E 
            & is_subspace F H' & graph F f <= graph H' h'
            & (ALL x:H'. h' x <= p x)";
      by (rule some_H'h'2);

    txt {* We have to show that $h$ is additive. *};

    thus "h (x + y) = h x + h y"; 
    proof (elim exE conjE);
      fix H' h'; assume "x:H'" "y:H'" 
        and b: "graph H' h' <= graph H h" 
        and "is_linearform H' h'" "is_subspace H' E";
      have "h' (x + y) = h' x + h' y"; 
        by (rule linearform_add);
      also; have "h' x = h x"; ..;
      also; have "h' y = h y"; ..;
      also; have "x + y : H'"; ..;
      with b; have "h' (x + y) = h (x + y)"; ..;
      finally; show ?thesis; .;
    qed;
  next;  
    fix a x; assume "x : H";
    have "EX H' h'. x:H' & graph H' h' <= graph H h 
            & is_linearform H' h' & is_subspace H' E
            & is_subspace F H' & graph F f <= graph H' h' 
            & (ALL x:H'. h' x <= p x)";
      by (rule some_H'h');

    txt{* We have to show that $h$ is multiplicative. *};

    thus "h (a (*) x) = a * h x";
    proof (elim exE conjE);
      fix H' h'; assume "x:H'"
        and b: "graph H' h' <= graph H h" 
        and "is_linearform H' h'" "is_subspace H' E";
      have "h' (a (*) x) = a * h' x"; 
        by (rule linearform_mult);
      also; have "h' x = h x"; ..;
      also; have "a (*) x : H'"; ..;
      with b; have "h' (a (*) x) = h (a (*) x)"; ..;
      finally; show ?thesis; .;
    qed;
  qed;
qed;

text{* \medskip The limit of a non-empty chain of norm
preserving extensions of $f$ is an extension of $f$,
since every element of the chain is an extension
of $f$ and the supremum is an extension
for every element of the chain.*};

lemma sup_ext:
  "[| M = norm_pres_extensions E p F f; c: chain M; EX x. x:c; 
  graph H h = Union c |] ==> graph F f <= graph H h";
proof -;
  assume "M = norm_pres_extensions E p F f" "c: chain M" 
         "graph H h = Union c";
  assume "EX x. x:c";
  thus ?thesis; 
  proof;
    fix x; assume "x:c"; 
    have "c <= M"; by (rule chainD2);
    hence "x:M"; ..;
    hence "x : norm_pres_extensions E p F f"; by (simp!);

    hence "EX G g. graph G g = x
             & is_linearform G g 
             & is_subspace G E
             & is_subspace F G
             & graph F f <= graph G g 
             & (ALL x:G. g x <= p x)";
      by (simp! add: norm_pres_extension_D);

    thus ?thesis; 
    proof (elim exE conjE); 
      fix G g; assume "graph F f <= graph G g";
      also; assume "graph G g = x";
      also; have "... : c"; .;
      hence "x <= Union c"; by fast;
      also; have [RS sym]: "graph H h = Union c"; .;
      finally; show ?thesis; .;
    qed;
  qed;
qed;

text{* \medskip The domain $H$ of the limit function is a superspace of $F$,
since $F$ is a subset of $H$. The existence of the $\zero$ element in
$F$ and the closure properties follow from the fact that $F$ is a
vector space. *};

lemma sup_supF: 
  "[| M = norm_pres_extensions E p F f; c: chain M; EX x. x:c;
  graph H h = Union c; is_subspace F E; is_vectorspace E |] 
  ==> is_subspace F H";
proof -; 
  assume "M = norm_pres_extensions E p F f" "c: chain M" "EX x. x:c"
    "graph H h = Union c" "is_subspace F E" "is_vectorspace E";

  show ?thesis; 
  proof;
    show "00 : F"; ..;
    show "F <= H"; 
    proof (rule graph_extD2);
      show "graph F f <= graph H h";
        by (rule sup_ext);
    qed;
    show "ALL x:F. ALL y:F. x + y : F"; 
    proof (intro ballI); 
      fix x y; assume "x:F" "y:F";
      show "x + y : F"; by (simp!);
    qed;
    show "ALL x:F. ALL a. a (*) x : F";
    proof (intro ballI allI);
      fix x a; assume "x:F";
      show "a (*) x : F"; by (simp!);
    qed;
  qed;
qed;

text{* \medskip The domain $H$ of the limit function is a subspace
of $E$. *};

lemma sup_subE: 
  "[| M = norm_pres_extensions E p F f; c: chain M; EX x. x:c; 
  graph H h = Union c; is_subspace F E; is_vectorspace E |] 
  ==> is_subspace H E";
proof -; 
  assume "M = norm_pres_extensions E p F f" "c: chain M" "EX x. x:c"
    "graph H h = Union c" "is_subspace F E" "is_vectorspace E";
  show ?thesis; 
  proof;
 
    txt {* The $\zero$ element is in $H$, as $F$ is a subset 
    of $H$: *};

    have "00 : F"; ..;
    also; have "is_subspace F H"; by (rule sup_supF); 
    hence "F <= H"; ..;
    finally; show "00 : H"; .;

    txt{* $H$ is a subset of $E$: *};

    show "H <= E"; 
    proof;
      fix x; assume "x:H";
      have "EX H' h'. x:H' & graph H' h' <= graph H h
              & is_linearform H' h' & is_subspace H' E 
              & is_subspace F H' & graph F f <= graph H' h' 
              & (ALL x:H'. h' x <= p x)"; 
	by (rule some_H'h');
      thus "x:E"; 
      proof (elim exE conjE);
	fix H' h'; assume "x:H'" "is_subspace H' E";
        have "H' <= E"; ..;
	thus "x:E"; ..;
      qed;
    qed;

    txt{* $H$ is closed under addition: *};

    show "ALL x:H. ALL y:H. x + y : H"; 
    proof (intro ballI); 
      fix x y; assume "x:H" "y:H";
      have "EX H' h'. x:H' & y:H' & graph H' h' <= graph H h 
              & is_linearform H' h' & is_subspace H' E 
              & is_subspace F H' & graph F f <= graph H' h' 
              & (ALL x:H'. h' x <= p x)"; 
	by (rule some_H'h'2); 
      thus "x + y : H"; 
      proof (elim exE conjE); 
	fix H' h'; 
        assume "x:H'" "y:H'" "is_subspace H' E" 
          "graph H' h' <= graph H h";
        have "x + y : H'"; ..;
	also; have "H' <= H"; ..;
	finally; show ?thesis; .;
      qed;
    qed;      

    txt{* $H$ is closed under scalar multiplication: *};

    show "ALL x:H. ALL a. a (*) x : H"; 
    proof (intro ballI allI); 
      fix x a; assume "x:H"; 
      have "EX H' h'. x:H' & graph H' h' <= graph H h
              & is_linearform H' h' & is_subspace H' E 
              & is_subspace F H' & graph F f <= graph H' h' 
              & (ALL x:H'. h' x <= p x)"; 
	by (rule some_H'h'); 
      thus "a (*) x : H"; 
      proof (elim exE conjE);
	fix H' h'; 
        assume "x:H'" "is_subspace H' E" "graph H' h' <= graph H h";
        have "a (*) x : H'"; ..;
        also; have "H' <= H"; ..;
	finally; show ?thesis; .;
      qed;
    qed;
  qed;
qed;

text {* \medskip The limit function is bounded by 
the norm $p$ as well, since all elements in the chain are
bounded by $p$.
*};

lemma sup_norm_pres: 
  "[| M = norm_pres_extensions E p F f; c: chain M; 
  graph H h = Union c |] ==> ALL x:H. h x <= p x";
proof;
  assume "M = norm_pres_extensions E p F f" "c: chain M" 
         "graph H h = Union c";
  fix x; assume "x:H";
  have "EX H' h'. x:H' & graph H' h' <= graph H h 
          & is_linearform H' h' & is_subspace H' E & is_subspace F H'
          & graph F f <= graph H' h' & (ALL x:H'. h' x <= p x)"; 
    by (rule some_H'h');
  thus "h x <= p x"; 
  proof (elim exE conjE);
    fix H' h'; 
    assume "x: H'" "graph H' h' <= graph H h" 
      and a: "ALL x: H'. h' x <= p x";
    have [RS sym]: "h' x = h x"; ..;
    also; from a; have "h' x <= p x "; ..;
    finally; show ?thesis; .;  
  qed;
qed;


text{* \medskip The following lemma is a property of linear forms on 
real vector spaces. It will be used for the lemma 
$\idt{rabs{\dsh}HahnBanach}$ (see page \pageref{rabs-HahnBanach}). \label{rabs-ineq-iff}
For real vector spaces the following inequations are equivalent:
\begin{matharray}{ll} 
\forall x\in H.\ap |h\ap x|\leq p\ap x& {\rm and}\\ 
\forall x\in H.\ap h\ap x\leq p\ap x\\ 
\end{matharray}
*};

lemma rabs_ineq_iff: 
  "[| is_subspace H E; is_vectorspace E; is_seminorm E p; 
  is_linearform H h |] 
  ==> (ALL x:H. rabs (h x) <= p x) = (ALL x:H. h x <= p x)" 
  (concl is "?L = ?R");
proof -;
  assume "is_subspace H E" "is_vectorspace E" "is_seminorm E p" 
         "is_linearform H h";
  have h: "is_vectorspace H"; ..;
  show ?thesis;
  proof; 
    assume l: ?L;
    show ?R;
    proof;
      fix x; assume x: "x:H";
      have "h x <= rabs (h x)"; by (rule rabs_ge_self);
      also; from l; have "... <= p x"; ..;
      finally; show "h x <= p x"; .;
    qed;
  next;
    assume r: ?R;
    show ?L;
    proof; 
      fix x; assume "x:H";
      show "!! a b. [| - a <= b; b <= a |] ==> rabs b <= a";
        by arith;
      show "- p x <= h x";
      proof (rule real_minus_le);
	from h; have "- h x = h (- x)"; 
          by (rule linearform_neg [RS sym]);
	also; from r; have "... <= p (- x)"; by (simp!);
	also; have "... = p x";
          by (rule seminorm_minus [OF _ subspace_subsetD]);
	finally; show "- h x <= p x"; .; 
      qed;
      from r; show "h x <= p x"; ..; 
    qed;
  qed;
qed;  


end;