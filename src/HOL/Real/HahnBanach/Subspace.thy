(*  Title:      HOL/Real/HahnBanach/Subspace.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)


header {* Subspaces *}

theory Subspace = VectorSpace:


subsection {* Definition *}

text {* A non-empty subset $U$ of a vector space $V$ is a 
\emph{subspace} of $V$, iff $U$ is closed under addition and 
scalar multiplication. *}

constdefs 
  is_subspace ::  "['a::{minus, plus} set, 'a set] => bool"
  "is_subspace U V == U ~= {} & U <= V 
     & (ALL x:U. ALL y:U. ALL a. x + y : U & a (*) x : U)"

lemma subspaceI [intro]: 
  "[| 00 : U; U <= V; ALL x:U. ALL y:U. (x + y : U); 
  ALL x:U. ALL a. a (*) x : U |]
  ==> is_subspace U V"
proof (unfold is_subspace_def, intro conjI) 
  assume "00 : U" thus "U ~= {}" by fast
qed (simp+)

lemma subspace_not_empty [intro??]: "is_subspace U V ==> U ~= {}"
  by (unfold is_subspace_def) simp 

lemma subspace_subset [intro??]: "is_subspace U V ==> U <= V"
  by (unfold is_subspace_def) simp

lemma subspace_subsetD [simp, intro??]: 
  "[| is_subspace U V; x:U |] ==> x:V"
  by (unfold is_subspace_def) force

lemma subspace_add_closed [simp, intro??]: 
  "[| is_subspace U V; x:U; y:U |] ==> x + y : U"
  by (unfold is_subspace_def) simp

lemma subspace_mult_closed [simp, intro??]: 
  "[| is_subspace U V; x:U |] ==> a (*) x : U"
  by (unfold is_subspace_def) simp

lemma subspace_diff_closed [simp, intro??]: 
  "[| is_subspace U V; is_vectorspace V; x:U; y:U |] 
  ==> x - y : U"
  by (simp! add: diff_eq1 negate_eq1)

text {* Similar as for linear spaces, the existence of the 
zero element in every subspace follows from the non-emptiness 
of the carrier set and by vector space laws.*}

lemma zero_in_subspace [intro??]:
  "[| is_subspace U V; is_vectorspace V |] ==> 00 : U"
proof - 
  assume "is_subspace U V" and v: "is_vectorspace V"
  have "U ~= {}" ..
  hence "EX x. x:U" by force
  thus ?thesis 
  proof 
    fix x assume u: "x:U" 
    hence "x:V" by (simp!)
    with v have "00 = x - x" by (simp!)
    also have "... : U" by (rule subspace_diff_closed)
    finally show ?thesis .
  qed
qed

lemma subspace_neg_closed [simp, intro??]: 
  "[| is_subspace U V; is_vectorspace V; x:U |] ==> - x : U"
  by (simp add: negate_eq1)

text_raw {* \medskip *}
text {* Further derived laws: every subspace is a vector space. *}

lemma subspace_vs [intro??]:
  "[| is_subspace U V; is_vectorspace V |] ==> is_vectorspace U"
proof -
  assume "is_subspace U V" "is_vectorspace V"
  show ?thesis
  proof 
    show "00 : U" ..
    show "ALL x:U. ALL a. a (*) x : U" by (simp!)
    show "ALL x:U. ALL y:U. x + y : U" by (simp!)
    show "ALL x:U. - x = -#1 (*) x" by (simp! add: negate_eq1)
    show "ALL x:U. ALL y:U. x - y =  x + - y" 
      by (simp! add: diff_eq1)
  qed (simp! add: vs_add_mult_distrib1 vs_add_mult_distrib2)+
qed

text {* The subspace relation is reflexive. *}

lemma subspace_refl [intro]: "is_vectorspace V ==> is_subspace V V"
proof 
  assume "is_vectorspace V"
  show "00 : V" ..
  show "V <= V" ..
  show "ALL x:V. ALL y:V. x + y : V" by (simp!)
  show "ALL x:V. ALL a. a (*) x : V" by (simp!)
qed

text {* The subspace relation is transitive. *}

lemma subspace_trans: 
  "[| is_subspace U V; is_vectorspace V; is_subspace V W |] 
  ==> is_subspace U W"
proof 
  assume "is_subspace U V" "is_subspace V W" "is_vectorspace V"
  show "00 : U" ..

  have "U <= V" ..
  also have "V <= W" ..
  finally show "U <= W" .

  show "ALL x:U. ALL y:U. x + y : U" 
  proof (intro ballI)
    fix x y assume "x:U" "y:U"
    show "x + y : U" by (simp!)
  qed

  show "ALL x:U. ALL a. a (*) x : U"
  proof (intro ballI allI)
    fix x a assume "x:U"
    show "a (*) x : U" by (simp!)
  qed
qed



subsection {* Linear closure *}

text {* The \emph{linear closure} of a vector $x$ is the set of all
scalar multiples of $x$. *}

constdefs
  lin :: "'a => 'a set"
  "lin x == {a (*) x | a. True}" 

lemma linD: "x : lin v = (EX a::real. x = a (*) v)"
  by (unfold lin_def) fast

lemma linI [intro??]: "a (*) x0 : lin x0"
  by (unfold lin_def) fast

text {* Every vector is contained in its linear closure. *}

lemma x_lin_x: "[| is_vectorspace V; x:V |] ==> x : lin x"
proof (unfold lin_def, intro CollectI exI conjI)
  assume "is_vectorspace V" "x:V"
  show "x = #1 (*) x" by (simp!)
qed simp

text {* Any linear closure is a subspace. *}

lemma lin_subspace [intro??]: 
  "[| is_vectorspace V; x:V |] ==> is_subspace (lin x) V"
proof
  assume "is_vectorspace V" "x:V"
  show "00 : lin x" 
  proof (unfold lin_def, intro CollectI exI conjI)
    show "00 = (#0::real) (*) x" by (simp!)
  qed simp

  show "lin x <= V"
  proof (unfold lin_def, intro subsetI, elim CollectE exE conjE) 
    fix xa a assume "xa = a (*) x" 
    show "xa:V" by (simp!)
  qed

  show "ALL x1 : lin x. ALL x2 : lin x. x1 + x2 : lin x" 
  proof (intro ballI)
    fix x1 x2 assume "x1 : lin x" "x2 : lin x" 
    thus "x1 + x2 : lin x"
    proof (unfold lin_def, elim CollectE exE conjE, 
      intro CollectI exI conjI)
      fix a1 a2 assume "x1 = a1 (*) x" "x2 = a2 (*) x"
      show "x1 + x2 = (a1 + a2) (*) x" 
        by (simp! add: vs_add_mult_distrib2)
    qed simp
  qed

  show "ALL xa:lin x. ALL a. a (*) xa : lin x" 
  proof (intro ballI allI)
    fix x1 a assume "x1 : lin x" 
    thus "a (*) x1 : lin x"
    proof (unfold lin_def, elim CollectE exE conjE,
      intro CollectI exI conjI)
      fix a1 assume "x1 = a1 (*) x"
      show "a (*) x1 = (a * a1) (*) x" by (simp!)
    qed simp
  qed 
qed

text {* Any linear closure is a vector space. *}

lemma lin_vs [intro??]: 
  "[| is_vectorspace V; x:V |] ==> is_vectorspace (lin x)"
proof (rule subspace_vs)
  assume "is_vectorspace V" "x:V"
  show "is_subspace (lin x) V" ..
qed



subsection {* Sum of two vectorspaces *}

text {* The \emph{sum} of two vectorspaces $U$ and $V$ is the set of
all sums of elements from $U$ and $V$. *}

instance set :: (plus) plus by intro_classes

defs vs_sum_def:
  "U + V == {u + v | u v. u:U & v:V}" (***

constdefs 
  vs_sum :: 
  "['a::{minus, plus} set, 'a set] => 'a set"         (infixl "+" 65)
  "vs_sum U V == {x. EX u:U. EX v:V. x = u + v}";
***)

lemma vs_sumD: 
  "x: U + V = (EX u:U. EX v:V. x = u + v)"
    by (unfold vs_sum_def) fast

lemmas vs_sumE = vs_sumD [RS iffD1, elimify]

lemma vs_sumI [intro??]: 
  "[| x:U; y:V; t= x + y |] ==> t : U + V"
  by (unfold vs_sum_def) fast

text{* $U$ is a subspace of $U + V$. *}

lemma subspace_vs_sum1 [intro??]: 
  "[| is_vectorspace U; is_vectorspace V |]
  ==> is_subspace U (U + V)"
proof 
  assume "is_vectorspace U" "is_vectorspace V"
  show "00 : U" ..
  show "U <= U + V"
  proof (intro subsetI vs_sumI)
  fix x assume "x:U"
    show "x = x + 00" by (simp!)
    show "00 : V" by (simp!)
  qed
  show "ALL x:U. ALL y:U. x + y : U" 
  proof (intro ballI)
    fix x y assume "x:U" "y:U" show "x + y : U" by (simp!)
  qed
  show "ALL x:U. ALL a. a (*) x : U" 
  proof (intro ballI allI)
    fix x a assume "x:U" show "a (*) x : U" by (simp!)
  qed
qed

text{* The sum of two subspaces is again a subspace.*}

lemma vs_sum_subspace [intro??]: 
  "[| is_subspace U E; is_subspace V E; is_vectorspace E |] 
  ==> is_subspace (U + V) E"
proof 
  assume "is_subspace U E" "is_subspace V E" "is_vectorspace E"
  show "00 : U + V"
  proof (intro vs_sumI)
    show "00 : U" ..
    show "00 : V" ..
    show "(00::'a) = 00 + 00" by (simp!)
  qed
  
  show "U + V <= E"
  proof (intro subsetI, elim vs_sumE bexE)
    fix x u v assume "u : U" "v : V" "x = u + v"
    show "x:E" by (simp!)
  qed
  
  show "ALL x: U + V. ALL y: U + V. x + y : U + V"
  proof (intro ballI)
    fix x y assume "x : U + V" "y : U + V"
    thus "x + y : U + V"
    proof (elim vs_sumE bexE, intro vs_sumI)
      fix ux vx uy vy 
      assume "ux : U" "vx : V" "x = ux + vx" 
	and "uy : U" "vy : V" "y = uy + vy"
      show "x + y = (ux + uy) + (vx + vy)" by (simp!)
    qed (simp!)+
  qed

  show "ALL x : U + V. ALL a. a (*) x : U + V"
  proof (intro ballI allI)
    fix x a assume "x : U + V"
    thus "a (*) x : U + V"
    proof (elim vs_sumE bexE, intro vs_sumI)
      fix a x u v assume "u : U" "v : V" "x = u + v"
      show "a (*) x = (a (*) u) + (a (*) v)" 
        by (simp! add: vs_add_mult_distrib1)
    qed (simp!)+
  qed
qed

text{* The sum of two subspaces is a vectorspace. *}

lemma vs_sum_vs [intro??]: 
  "[| is_subspace U E; is_subspace V E; is_vectorspace E |] 
  ==> is_vectorspace (U + V)"
proof (rule subspace_vs)
  assume "is_subspace U E" "is_subspace V E" "is_vectorspace E"
  show "is_subspace (U + V) E" ..
qed



subsection {* Direct sums *}


text {* The sum of $U$ and $V$ is called \emph{direct}, iff the zero 
element is the only common element of $U$ and $V$. For every element
$x$ of the direct sum of $U$ and $V$ the decomposition in
$x = u + v$ with $u \in U$ and $v \in V$ is unique.*} 

lemma decomp: 
  "[| is_vectorspace E; is_subspace U E; is_subspace V E; 
  U Int V = {00}; u1:U; u2:U; v1:V; v2:V; u1 + v1 = u2 + v2 |] 
  ==> u1 = u2 & v1 = v2" 
proof 
  assume "is_vectorspace E" "is_subspace U E" "is_subspace V E"  
    "U Int V = {00}" "u1:U" "u2:U" "v1:V" "v2:V" 
    "u1 + v1 = u2 + v2" 
  have eq: "u1 - u2 = v2 - v1" by (simp! add: vs_add_diff_swap)
  have u: "u1 - u2 : U" by (simp!) 
  with eq have v': "v2 - v1 : U" by simp 
  have v: "v2 - v1 : V" by (simp!) 
  with eq have u': "u1 - u2 : V" by simp
  
  show "u1 = u2"
  proof (rule vs_add_minus_eq)
    show "u1 - u2 = 00" by (rule Int_singletonD [OF _ u u']) 
    show "u1 : E" ..
    show "u2 : E" ..
  qed

  show "v1 = v2"
  proof (rule vs_add_minus_eq [RS sym])
    show "v2 - v1 = 00" by (rule Int_singletonD [OF _ v' v])
    show "v1 : E" ..
    show "v2 : E" ..
  qed
qed

text {* An application of the previous lemma will be used in the proof
of the Hahn-Banach Theorem (see page \pageref{decomp-H0-use}): for any
element $y + a \mult x_0$ of the direct sum of a vectorspace $H$ and
the linear closure of $x_0$ the components $y \in H$ and $a$ are
uniquely determined. *}

lemma decomp_H0: 
  "[| is_vectorspace E; is_subspace H E; y1 : H; y2 : H; 
  x0 ~: H; x0 : E; x0 ~= 00; y1 + a1 (*) x0 = y2 + a2 (*) x0 |]
  ==> y1 = y2 & a1 = a2"
proof
  assume "is_vectorspace E" and h: "is_subspace H E"
     and "y1 : H" "y2 : H" "x0 ~: H" "x0 : E" "x0 ~= 00" 
         "y1 + a1 (*) x0 = y2 + a2 (*) x0"

  have c: "y1 = y2 & a1 (*) x0 = a2 (*) x0"
  proof (rule decomp) 
    show "a1 (*) x0 : lin x0" .. 
    show "a2 (*) x0 : lin x0" ..
    show "H Int (lin x0) = {00}" 
    proof
      show "H Int lin x0 <= {00}" 
      proof (intro subsetI, elim IntE, rule singleton_iff[RS iffD2])
        fix x assume "x:H" "x : lin x0" 
        thus "x = 00"
        proof (unfold lin_def, elim CollectE exE conjE)
          fix a assume "x = a (*) x0"
          show ?thesis
          proof cases
            assume "a = (#0::real)" show ?thesis by (simp!)
          next
            assume "a ~= (#0::real)" 
            from h have "rinv a (*) a (*) x0 : H" 
              by (rule subspace_mult_closed) (simp!)
            also have "rinv a (*) a (*) x0 = x0" by (simp!)
            finally have "x0 : H" .
            thus ?thesis by contradiction
          qed
       qed
      qed
      show "{00} <= H Int lin x0"
      proof -
	have "00: H Int lin x0"
	proof (rule IntI)
	  show "00:H" ..
	  from lin_vs show "00 : lin x0" ..
	qed
	thus ?thesis by simp
      qed
    qed
    show "is_subspace (lin x0) E" ..
  qed
  
  from c show "y1 = y2" by simp
  
  show  "a1 = a2" 
  proof (rule vs_mult_right_cancel [RS iffD1])
    from c show "a1 (*) x0 = a2 (*) x0" by simp
  qed
qed

text {* Since for any element $y + a \mult x_0$ of the direct sum 
of a vectorspace $H$ and the linear closure of $x_0$ the components
$y\in H$ and $a$ are unique, it follows from $y\in H$ that 
$a = 0$.*} 

lemma decomp_H0_H: 
  "[| is_vectorspace E; is_subspace H E; t:H; x0 ~: H; x0:E;
  x0 ~= 00 |] 
  ==> (SOME (y, a). t = y + a (*) x0 & y : H) = (t, (#0::real))"
proof (rule, unfold split_tupled_all)
  assume "is_vectorspace E" "is_subspace H E" "t:H" "x0 ~: H" "x0:E"
    "x0 ~= 00"
  have h: "is_vectorspace H" ..
  fix y a presume t1: "t = y + a (*) x0" and "y:H"
  have "y = t & a = (#0::real)" 
    by (rule decomp_H0) (assumption | (simp!))+
  thus "(y, a) = (t, (#0::real))" by (simp!)
qed (simp!)+

text {* The components $y\in H$ and $a$ in $y \plus a \mult x_0$ 
are unique, so the function $h_0$ defined by 
$h_0 (y \plus a \mult x_0) = h y + a \cdot \xi$ is definite. *}

lemma h0_definite:
  "[| h0 == (\\<lambda>x. let (y, a) = SOME (y, a). (x = y + a (*) x0 & y:H)
                in (h y) + a * xi);
  x = y + a (*) x0; is_vectorspace E; is_subspace H E;
  y:H; x0 ~: H; x0:E; x0 ~= 00 |]
  ==> h0 x = h y + a * xi"
proof -  
  assume 
    "h0 == (\\<lambda>x. let (y, a) = SOME (y, a). (x = y + a (*) x0 & y:H)
               in (h y) + a * xi)"
    "x = y + a (*) x0" "is_vectorspace E" "is_subspace H E"
    "y:H" "x0 ~: H" "x0:E" "x0 ~= 00"
  have "x : H + (lin x0)" 
    by (simp! add: vs_sum_def lin_def) force+
  have "EX! xa. ((\\<lambda>(y, a). x = y + a (*) x0 & y:H) xa)" 
  proof
    show "EX xa. ((\\<lambda>(y, a). x = y + a (*) x0 & y:H) xa)"
      by (force!)
  next
    fix xa ya
    assume "(\\<lambda>(y,a). x = y + a (*) x0 & y : H) xa"
           "(\\<lambda>(y,a). x = y + a (*) x0 & y : H) ya"
    show "xa = ya" 
    proof -
      show "fst xa = fst ya & snd xa = snd ya ==> xa = ya" 
        by (simp add: Pair_fst_snd_eq)
      have x: "x = fst xa + snd xa (*) x0 & fst xa : H" 
        by (force!)
      have y: "x = fst ya + snd ya (*) x0 & fst ya : H" 
        by (force!)
      from x y show "fst xa = fst ya & snd xa = snd ya" 
        by (elim conjE) (rule decomp_H0, (simp!)+)
    qed
  qed
  hence eq: "(SOME (y, a). x = y + a (*) x0 & y:H) = (y, a)" 
    by (rule select1_equality) (force!)
  thus "h0 x = h y + a * xi" by (simp! add: Let_def)
qed

end