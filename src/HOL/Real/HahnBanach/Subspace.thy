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
  is_subspace ::  "['a::{plus, minus, zero} set, 'a set] => bool"
  "is_subspace U V == U \<noteq> {} \<and> U <= V 
     \<and> (\<forall>x \<in> U. \<forall>y \<in> U. \<forall>a. x + y \<in> U \<and> a \<cdot> x\<in> U)"

lemma subspaceI [intro]: 
  "[| 0 \<in> U; U <= V; \<forall>x \<in> U. \<forall>y \<in> U. (x + y \<in> U); 
  \<forall>x \<in> U. \<forall>a. a \<cdot> x \<in> U |]
  ==> is_subspace U V"
proof (unfold is_subspace_def, intro conjI) 
  assume "0 \<in> U" thus "U \<noteq> {}" by fast
qed (simp+)

lemma subspace_not_empty [intro?]: "is_subspace U V ==> U \<noteq> {}"
  by (unfold is_subspace_def) simp 

lemma subspace_subset [intro?]: "is_subspace U V ==> U <= V"
  by (unfold is_subspace_def) simp

lemma subspace_subsetD [simp, intro?]: 
  "[| is_subspace U V; x \<in> U |] ==> x \<in> V"
  by (unfold is_subspace_def) force

lemma subspace_add_closed [simp, intro?]: 
  "[| is_subspace U V; x \<in> U; y \<in> U |] ==> x + y \<in> U"
  by (unfold is_subspace_def) simp

lemma subspace_mult_closed [simp, intro?]: 
  "[| is_subspace U V; x \<in> U |] ==> a \<cdot> x \<in> U"
  by (unfold is_subspace_def) simp

lemma subspace_diff_closed [simp, intro?]: 
  "[| is_subspace U V; is_vectorspace V; x \<in> U; y \<in> U |] 
  ==> x - y \<in> U"
  by (simp! add: diff_eq1 negate_eq1)

text {* Similar as for linear spaces, the existence of the 
zero element in every subspace follows from the non-emptiness 
of the carrier set and by vector space laws.*}

lemma zero_in_subspace [intro?]:
  "[| is_subspace U V; is_vectorspace V |] ==> 0 \<in> U"
proof - 
  assume "is_subspace U V" and v: "is_vectorspace V"
  have "U \<noteq> {}" ..
  hence "\<exists>x. x \<in> U" by force
  thus ?thesis 
  proof 
    fix x assume u: "x \<in> U" 
    hence "x \<in> V" by (simp!)
    with v have "0 = x - x" by (simp!)
    also have "... \<in> U" by (rule subspace_diff_closed)
    finally show ?thesis .
  qed
qed

lemma subspace_neg_closed [simp, intro?]: 
  "[| is_subspace U V; is_vectorspace V; x \<in> U |] ==> - x \<in> U"
  by (simp add: negate_eq1)

text_raw {* \medskip *}
text {* Further derived laws: every subspace is a vector space. *}

lemma subspace_vs [intro?]:
  "[| is_subspace U V; is_vectorspace V |] ==> is_vectorspace U"
proof -
  assume "is_subspace U V" "is_vectorspace V"
  show ?thesis
  proof 
    show "0 \<in> U" ..
    show "\<forall>x \<in> U. \<forall>a. a \<cdot> x \<in> U" by (simp!)
    show "\<forall>x \<in> U. \<forall>y \<in> U. x + y \<in> U" by (simp!)
    show "\<forall>x \<in> U. - x = -#1 \<cdot> x" by (simp! add: negate_eq1)
    show "\<forall>x \<in> U. \<forall>y \<in> U. x - y =  x + - y" 
      by (simp! add: diff_eq1)
  qed (simp! add: vs_add_mult_distrib1 vs_add_mult_distrib2)+
qed

text {* The subspace relation is reflexive. *}

lemma subspace_refl [intro]: "is_vectorspace V ==> is_subspace V V"
proof 
  assume "is_vectorspace V"
  show "0 \<in> V" ..
  show "V <= V" ..
  show "\<forall>x \<in> V. \<forall>y \<in> V. x + y \<in> V" by (simp!)
  show "\<forall>x \<in> V. \<forall>a. a \<cdot> x \<in> V" by (simp!)
qed

text {* The subspace relation is transitive. *}

lemma subspace_trans: 
  "[| is_subspace U V; is_vectorspace V; is_subspace V W |] 
  ==> is_subspace U W"
proof 
  assume "is_subspace U V" "is_subspace V W" "is_vectorspace V"
  show "0 \<in> U" ..

  have "U <= V" ..
  also have "V <= W" ..
  finally show "U <= W" .

  show "\<forall>x \<in> U. \<forall>y \<in> U. x + y \<in> U" 
  proof (intro ballI)
    fix x y assume "x \<in> U" "y \<in> U"
    show "x + y \<in> U" by (simp!)
  qed

  show "\<forall>x \<in> U. \<forall>a. a \<cdot> x \<in> U"
  proof (intro ballI allI)
    fix x a assume "x \<in> U"
    show "a \<cdot> x \<in> U" by (simp!)
  qed
qed



subsection {* Linear closure *}

text {* The \emph{linear closure} of a vector $x$ is the set of all
scalar multiples of $x$. *}

constdefs
  lin :: "('a::{minus,plus,zero}) => 'a set"
  "lin x == {a \<cdot> x | a. True}" 

lemma linD: "x \<in> lin v = (\<exists>a::real. x = a \<cdot> v)"
  by (unfold lin_def) fast

lemma linI [intro?]: "a \<cdot> x0 \<in> lin x0"
  by (unfold lin_def) fast

text {* Every vector is contained in its linear closure. *}

lemma x_lin_x: "[| is_vectorspace V; x \<in> V |] ==> x \<in> lin x"
proof (unfold lin_def, intro CollectI exI conjI)
  assume "is_vectorspace V" "x \<in> V"
  show "x = #1 \<cdot> x" by (simp!)
qed simp

text {* Any linear closure is a subspace. *}

lemma lin_subspace [intro?]: 
  "[| is_vectorspace V; x \<in> V |] ==> is_subspace (lin x) V"
proof
  assume "is_vectorspace V" "x \<in> V"
  show "0 \<in> lin x" 
  proof (unfold lin_def, intro CollectI exI conjI)
    show "0 = (#0::real) \<cdot> x" by (simp!)
  qed simp

  show "lin x <= V"
  proof (unfold lin_def, intro subsetI, elim CollectE exE conjE) 
    fix xa a assume "xa = a \<cdot> x" 
    show "xa \<in> V" by (simp!)
  qed

  show "\<forall>x1 \<in> lin x. \<forall>x2 \<in> lin x. x1 + x2 \<in> lin x" 
  proof (intro ballI)
    fix x1 x2 assume "x1 \<in> lin x" "x2 \<in> lin x" 
    thus "x1 + x2 \<in> lin x"
    proof (unfold lin_def, elim CollectE exE conjE, 
      intro CollectI exI conjI)
      fix a1 a2 assume "x1 = a1 \<cdot> x" "x2 = a2 \<cdot> x"
      show "x1 + x2 = (a1 + a2) \<cdot> x" 
        by (simp! add: vs_add_mult_distrib2)
    qed simp
  qed

  show "\<forall>xa \<in> lin x. \<forall>a. a \<cdot> xa \<in> lin x" 
  proof (intro ballI allI)
    fix x1 a assume "x1 \<in> lin x" 
    thus "a \<cdot> x1 \<in> lin x"
    proof (unfold lin_def, elim CollectE exE conjE,
      intro CollectI exI conjI)
      fix a1 assume "x1 = a1 \<cdot> x"
      show "a \<cdot> x1 = (a * a1) \<cdot> x" by (simp!)
    qed simp
  qed 
qed

text {* Any linear closure is a vector space. *}

lemma lin_vs [intro?]: 
  "[| is_vectorspace V; x \<in> V |] ==> is_vectorspace (lin x)"
proof (rule subspace_vs)
  assume "is_vectorspace V" "x \<in> V"
  show "is_subspace (lin x) V" ..
qed



subsection {* Sum of two vectorspaces *}

text {* The \emph{sum} of two vectorspaces $U$ and $V$ is the set of
all sums of elements from $U$ and $V$. *}

instance set :: (plus) plus ..

defs vs_sum_def:
  "U + V == {u + v | u v. u \<in> U \<and> v \<in> V}" (***

constdefs 
  vs_sum :: 
  "['a::{plus, minus, zero} set, 'a set] => 'a set"         (infixl "+" 65)
  "vs_sum U V == {x. \<exists>u \<in> U. \<exists>v \<in> V. x = u + v}";
***)

lemma vs_sumD: 
  "x \<in> U + V = (\<exists>u \<in> U. \<exists>v \<in> V. x = u + v)"
    by (unfold vs_sum_def) fast

lemmas vs_sumE = vs_sumD [THEN iffD1, elim_format, standard]

lemma vs_sumI [intro?]: 
  "[| x \<in> U; y \<in> V; t= x + y |] ==> t \<in> U + V"
  by (unfold vs_sum_def) fast

text{* $U$ is a subspace of $U + V$. *}

lemma subspace_vs_sum1 [intro?]: 
  "[| is_vectorspace U; is_vectorspace V |]
  ==> is_subspace U (U + V)"
proof 
  assume "is_vectorspace U" "is_vectorspace V"
  show "0 \<in> U" ..
  show "U <= U + V"
  proof (intro subsetI vs_sumI)
  fix x assume "x \<in> U"
    show "x = x + 0" by (simp!)
    show "0 \<in> V" by (simp!)
  qed
  show "\<forall>x \<in> U. \<forall>y \<in> U. x + y \<in> U" 
  proof (intro ballI)
    fix x y assume "x \<in> U" "y \<in> U" show "x + y \<in> U" by (simp!)
  qed
  show "\<forall>x \<in> U. \<forall>a. a \<cdot> x \<in> U" 
  proof (intro ballI allI)
    fix x a assume "x \<in> U" show "a \<cdot> x \<in> U" by (simp!)
  qed
qed

text{* The sum of two subspaces is again a subspace.*}

lemma vs_sum_subspace [intro?]: 
  "[| is_subspace U E; is_subspace V E; is_vectorspace E |] 
  ==> is_subspace (U + V) E"
proof 
  assume "is_subspace U E" "is_subspace V E" "is_vectorspace E"
  show "0 \<in> U + V"
  proof (intro vs_sumI)
    show "0 \<in> U" ..
    show "0 \<in> V" ..
    show "(0::'a) = 0 + 0" by (simp!)
  qed
  
  show "U + V <= E"
  proof (intro subsetI, elim vs_sumE bexE)
    fix x u v assume "u \<in> U" "v \<in> V" "x = u + v"
    show "x \<in> E" by (simp!)
  qed
  
  show "\<forall>x \<in> U + V. \<forall>y \<in> U + V. x + y \<in> U + V"
  proof (intro ballI)
    fix x y assume "x \<in> U + V" "y \<in> U + V"
    thus "x + y \<in> U + V"
    proof (elim vs_sumE bexE, intro vs_sumI)
      fix ux vx uy vy 
      assume "ux \<in> U" "vx \<in> V" "x = ux + vx" 
	and "uy \<in> U" "vy \<in> V" "y = uy + vy"
      show "x + y = (ux + uy) + (vx + vy)" by (simp!)
    qed (simp!)+
  qed

  show "\<forall>x \<in> U + V. \<forall>a. a \<cdot> x \<in> U + V"
  proof (intro ballI allI)
    fix x a assume "x \<in> U + V"
    thus "a \<cdot> x \<in> U + V"
    proof (elim vs_sumE bexE, intro vs_sumI)
      fix a x u v assume "u \<in> U" "v \<in> V" "x = u + v"
      show "a \<cdot> x = (a \<cdot> u) + (a \<cdot> v)" 
        by (simp! add: vs_add_mult_distrib1)
    qed (simp!)+
  qed
qed

text{* The sum of two subspaces is a vectorspace. *}

lemma vs_sum_vs [intro?]: 
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
  U \<inter> V = {0}; u1 \<in> U; u2 \<in> U; v1 \<in> V; v2 \<in> V; u1 + v1 = u2 + v2 |] 
  ==> u1 = u2 \<and> v1 = v2" 
proof 
  assume "is_vectorspace E" "is_subspace U E" "is_subspace V E"  
    "U \<inter> V = {0}" "u1 \<in> U" "u2 \<in> U" "v1 \<in> V" "v2 \<in> V" 
    "u1 + v1 = u2 + v2" 
  have eq: "u1 - u2 = v2 - v1" by (simp! add: vs_add_diff_swap)
  have u: "u1 - u2 \<in> U" by (simp!) 
  with eq have v': "v2 - v1 \<in> U" by simp 
  have v: "v2 - v1 \<in> V" by (simp!) 
  with eq have u': "u1 - u2 \<in> V" by simp
  
  show "u1 = u2"
  proof (rule vs_add_minus_eq)
    show "u1 - u2 = 0" by (rule Int_singletonD [OF _ u u']) 
    show "u1 \<in> E" ..
    show "u2 \<in> E" ..
  qed

  show "v1 = v2"
  proof (rule vs_add_minus_eq [symmetric])
    show "v2 - v1 = 0" by (rule Int_singletonD [OF _ v' v])
    show "v1 \<in> E" ..
    show "v2 \<in> E" ..
  qed
qed

text {* An application of the previous lemma will be used in the proof
of the Hahn-Banach Theorem (see page \pageref{decomp-H-use}): for any
element $y + a \mult x_0$ of the direct sum of a vectorspace $H$ and
the linear closure of $x_0$ the components $y \in H$ and $a$ are
uniquely determined. *}

lemma decomp_H': 
  "[| is_vectorspace E; is_subspace H E; y1 \<in> H; y2 \<in> H; 
  x' \<notin> H; x' \<in> E; x' \<noteq> 0; y1 + a1 \<cdot> x' = y2 + a2 \<cdot> x' |]
  ==> y1 = y2 \<and> a1 = a2"
proof
  assume "is_vectorspace E" and h: "is_subspace H E"
     and "y1 \<in> H" "y2 \<in> H" "x' \<notin> H" "x' \<in> E" "x' \<noteq> 0" 
         "y1 + a1 \<cdot> x' = y2 + a2 \<cdot> x'"

  have c: "y1 = y2 \<and> a1 \<cdot> x' = a2 \<cdot> x'"
  proof (rule decomp) 
    show "a1 \<cdot> x' \<in> lin x'" .. 
    show "a2 \<cdot> x' \<in> lin x'" ..
    show "H \<inter> (lin x') = {0}" 
    proof
      show "H \<inter> lin x' <= {0}" 
      proof (intro subsetI, elim IntE, rule singleton_iff [THEN iffD2])
        fix x assume "x \<in> H" "x \<in> lin x'" 
        thus "x = 0"
        proof (unfold lin_def, elim CollectE exE conjE)
          fix a assume "x = a \<cdot> x'"
          show ?thesis
          proof cases
            assume "a = (#0::real)" show ?thesis by (simp!)
          next
            assume "a \<noteq> (#0::real)" 
            from h have "rinv a \<cdot> a \<cdot> x' \<in> H" 
              by (rule subspace_mult_closed) (simp!)
            also have "rinv a \<cdot> a \<cdot> x' = x'" by (simp!)
            finally have "x' \<in> H" .
            thus ?thesis by contradiction
          qed
       qed
      qed
      show "{0} <= H \<inter> lin x'"
      proof -
	have "0 \<in> H \<inter> lin x'"
	proof (rule IntI)
	  show "0 \<in> H" ..
	  from lin_vs show "0 \<in> lin x'" ..
	qed
	thus ?thesis by simp
      qed
    qed
    show "is_subspace (lin x') E" ..
  qed
  
  from c show "y1 = y2" by simp
  
  show  "a1 = a2" 
  proof (rule vs_mult_right_cancel [THEN iffD1])
    from c show "a1 \<cdot> x' = a2 \<cdot> x'" by simp
  qed
qed

text {* Since for any element $y + a \mult x'$ of the direct sum 
of a vectorspace $H$ and the linear closure of $x'$ the components
$y\in H$ and $a$ are unique, it follows from $y\in H$ that 
$a = 0$.*} 

lemma decomp_H'_H: 
  "[| is_vectorspace E; is_subspace H E; t \<in> H; x' \<notin> H; x' \<in> E;
  x' \<noteq> 0 |] 
  ==> (SOME (y, a). t = y + a \<cdot> x' \<and> y \<in> H) = (t, (#0::real))"
proof (rule, unfold split_tupled_all)
  assume "is_vectorspace E" "is_subspace H E" "t \<in> H" "x' \<notin> H" "x' \<in> E"
    "x' \<noteq> 0"
  have h: "is_vectorspace H" ..
  fix y a presume t1: "t = y + a \<cdot> x'" and "y \<in> H"
  have "y = t \<and> a = (#0::real)" 
    by (rule decomp_H') (assumption | (simp!))+
  thus "(y, a) = (t, (#0::real))" by (simp!)
qed (simp!)+

text {* The components $y\in H$ and $a$ in $y \plus a \mult x'$ 
are unique, so the function $h'$ defined by 
$h' (y \plus a \mult x') = h y + a \cdot \xi$ is definite. *}

lemma h'_definite:
  "[| h' == (\<lambda>x. let (y, a) = SOME (y, a). (x = y + a \<cdot> x' \<and> y \<in> H)
                in (h y) + a * xi);
  x = y + a \<cdot> x'; is_vectorspace E; is_subspace H E;
  y \<in> H; x' \<notin> H; x' \<in> E; x' \<noteq> 0 |]
  ==> h' x = h y + a * xi"
proof -  
  assume 
    "h' == (\<lambda>x. let (y, a) = SOME (y, a). (x = y + a \<cdot> x' \<and> y \<in> H)
               in (h y) + a * xi)"
    "x = y + a \<cdot> x'" "is_vectorspace E" "is_subspace H E"
    "y \<in> H" "x' \<notin> H" "x' \<in> E" "x' \<noteq> 0"
  have "x \<in> H + (lin x')" 
    by (simp! add: vs_sum_def lin_def) force+
  have "\<exists>! xa. ((\<lambda>(y, a). x = y + a \<cdot> x' \<and> y \<in> H) xa)" 
  proof
    show "\<exists>xa. ((\<lambda>(y, a). x = y + a \<cdot> x' \<and> y \<in> H) xa)"
      by (force!)
  next
    fix xa ya
    assume "(\<lambda>(y,a). x = y + a \<cdot> x' \<and> y \<in> H) xa"
           "(\<lambda>(y,a). x = y + a \<cdot> x' \<and> y \<in> H) ya"
    show "xa = ya" 
    proof -
      show "fst xa = fst ya \<and> snd xa = snd ya ==> xa = ya" 
        by (simp add: Pair_fst_snd_eq)
      have x: "x = fst xa + snd xa \<cdot> x' \<and> fst xa \<in> H" 
        by (force!)
      have y: "x = fst ya + snd ya \<cdot> x' \<and> fst ya \<in> H" 
        by (force!)
      from x y show "fst xa = fst ya \<and> snd xa = snd ya" 
        by (elim conjE) (rule decomp_H', (simp!)+)
    qed
  qed
  hence eq: "(SOME (y, a). x = y + a \<cdot> x' \<and> y \<in> H) = (y, a)" 
    by (rule some1_equality) (force!)
  thus "h' x = h y + a * xi" by (simp! add: Let_def)
qed

end