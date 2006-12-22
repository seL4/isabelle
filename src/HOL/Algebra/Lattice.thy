(*
  Title:     HOL/Algebra/Lattice.thy
  Id:        $Id$
  Author:    Clemens Ballarin, started 7 November 2003
  Copyright: Clemens Ballarin
*)

theory Lattice imports Main begin


section {* Orders and Lattices *}

text {* Object with a carrier set. *}

record 'a partial_object =
  carrier :: "'a set"


subsection {* Partial Orders *}

text {* Locale @{text order_syntax} is required since we want to refer
  to definitions (and their derived theorems) outside of @{text partial_order}.
  *}

locale order_syntax =
  fixes L :: "'a set" and le :: "['a, 'a] => bool" (infix "\<sqsubseteq>" 50)

text {* Note that the type constraints above are necessary, because the
  definition command cannot specialise the types. *}

definition (in order_syntax)
  less (infixl "\<sqsubset>" 50) where "x \<sqsubset> y == x \<sqsubseteq> y & x ~= y"

text {* Upper and lower bounds of a set. *}

definition (in order_syntax)
  Upper :: "'a set => 'a set" where
  "Upper A == {u. (ALL x. x \<in> A \<inter> L --> x \<sqsubseteq> u)} \<inter> L"

definition (in order_syntax)
  Lower :: "'a set => 'a set" where
  "Lower A == {l. (ALL x. x \<in> A \<inter> L --> l \<sqsubseteq> x)} \<inter> L"

text {* Least and greatest, as predicate. *}

definition (in order_syntax)
  least :: "['a, 'a set] => bool" where
  "least l A == A \<subseteq> L & l \<in> A & (ALL x : A. l \<sqsubseteq> x)"

definition (in order_syntax)
  greatest :: "['a, 'a set] => bool" where
  "greatest g A == A \<subseteq> L & g \<in> A & (ALL x : A. x \<sqsubseteq> g)"

text {* Supremum and infimum *}

definition (in order_syntax)
  sup :: "'a set => 'a" ("\<Squnion>_" [90] 90) where
  "\<Squnion>A == THE x. least x (Upper A)"

definition (in order_syntax)
  inf :: "'a set => 'a" ("\<Sqinter>_" [90] 90) where
  "\<Sqinter>A == THE x. greatest x (Lower A)"

definition (in order_syntax)
  join :: "['a, 'a] => 'a" (infixl "\<squnion>" 65) where
  "x \<squnion> y == sup {x, y}"

definition (in order_syntax)
  meet :: "['a, 'a] => 'a" (infixl "\<sqinter>" 70) where
  "x \<sqinter> y == inf {x, y}"

locale partial_order = order_syntax +
  assumes refl [intro, simp]:
                  "x \<in> L ==> x \<sqsubseteq> x"
    and anti_sym [intro]:
                  "[| x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> L; y \<in> L |] ==> x = y"
    and trans [trans]:
                  "[| x \<sqsubseteq> y; y \<sqsubseteq> z;
                   x \<in> L; y \<in> L; z \<in> L |] ==> x \<sqsubseteq> z"


subsubsection {* Upper *}

lemma (in order_syntax) Upper_closed [intro, simp]:
  "Upper A \<subseteq> L"
  by (unfold Upper_def) clarify

lemma (in order_syntax) UpperD [dest]:
  "[| u \<in> Upper A; x \<in> A; A \<subseteq> L |] ==> x \<sqsubseteq> u"
  by (unfold Upper_def) blast

lemma (in order_syntax) Upper_memI:
  "[| !! y. y \<in> A ==> y \<sqsubseteq> x; x \<in> L |] ==> x \<in> Upper A"
  by (unfold Upper_def) blast

lemma (in order_syntax) Upper_antimono:
  "A \<subseteq> B ==> Upper B \<subseteq> Upper A"
  by (unfold Upper_def) blast


subsubsection {* Lower *}

lemma (in order_syntax) Lower_closed [intro, simp]:
  "Lower A \<subseteq> L"
  by (unfold Lower_def) clarify

lemma (in order_syntax) LowerD [dest]:
  "[| l \<in> Lower A; x \<in> A; A \<subseteq> L |] ==> l \<sqsubseteq> x"
  by (unfold Lower_def) blast

lemma (in order_syntax) Lower_memI:
  "[| !! y. y \<in> A ==> x \<sqsubseteq> y; x \<in> L |] ==> x \<in> Lower A"
  by (unfold Lower_def) blast

lemma (in order_syntax) Lower_antimono:
  "A \<subseteq> B ==> Lower B \<subseteq> Lower A"
  by (unfold Lower_def) blast


subsubsection {* least *}

lemma (in order_syntax) least_closed [intro, simp]:
  "least l A ==> l \<in> L"
  by (unfold least_def) fast

lemma (in order_syntax) least_mem:
  "least l A ==> l \<in> A"
  by (unfold least_def) fast

lemma (in partial_order) least_unique:
  "[| least x A; least y A |] ==> x = y"
  by (unfold least_def) blast

lemma (in order_syntax) least_le:
  "[| least x A; a \<in> A |] ==> x \<sqsubseteq> a"
  by (unfold least_def) fast

lemma (in order_syntax) least_UpperI:
  assumes above: "!! x. x \<in> A ==> x \<sqsubseteq> s"
    and below: "!! y. y \<in> Upper A ==> s \<sqsubseteq> y"
    and L: "A \<subseteq> L"  "s \<in> L"
  shows "least s (Upper A)"
proof -
  have "Upper A \<subseteq> L" by simp
  moreover from above L have "s \<in> Upper A" by (simp add: Upper_def)
  moreover from below have "ALL x : Upper A. s \<sqsubseteq> x" by fast
  ultimately show ?thesis by (simp add: least_def)
qed


subsubsection {* greatest *}

lemma (in order_syntax) greatest_closed [intro, simp]:
  "greatest l A ==> l \<in> L"
  by (unfold greatest_def) fast

lemma (in order_syntax) greatest_mem:
  "greatest l A ==> l \<in> A"
  by (unfold greatest_def) fast

lemma (in partial_order) greatest_unique:
  "[| greatest x A; greatest y A |] ==> x = y"
  by (unfold greatest_def) blast

lemma (in order_syntax) greatest_le:
  "[| greatest x A; a \<in> A |] ==> a \<sqsubseteq> x"
  by (unfold greatest_def) fast

lemma (in order_syntax) greatest_LowerI:
  assumes below: "!! x. x \<in> A ==> i \<sqsubseteq> x"
    and above: "!! y. y \<in> Lower A ==> y \<sqsubseteq> i"
    and L: "A \<subseteq> L"  "i \<in> L"
  shows "greatest i (Lower A)"
proof -
  have "Lower A \<subseteq> L" by simp
  moreover from below L have "i \<in> Lower A" by (simp add: Lower_def)
  moreover from above have "ALL x : Lower A. x \<sqsubseteq> i" by fast
  ultimately show ?thesis by (simp add: greatest_def)
qed


subsection {* Lattices *}

locale lattice = partial_order +
  assumes sup_of_two_exists:
    "[| x \<in> L; y \<in> L |] ==> EX s. order_syntax.least L le s (order_syntax.Upper L le {x, y})"
    and inf_of_two_exists:
    "[| x \<in> L; y \<in> L |] ==> EX s. order_syntax.greatest L le s (order_syntax.Lower L le {x, y})"

lemma (in order_syntax) least_Upper_above:
  "[| least s (Upper A); x \<in> A; A \<subseteq> L |] ==> x \<sqsubseteq> s"
  by (unfold least_def) blast

lemma (in order_syntax) greatest_Lower_above:
  "[| greatest i (Lower A); x \<in> A; A \<subseteq> L |] ==> i \<sqsubseteq> x"
  by (unfold greatest_def) blast


subsubsection {* Supremum *}

lemma (in lattice) joinI:
  "[| !!l. least l (Upper {x, y}) ==> P l; x \<in> L; y \<in> L |]
  ==> P (x \<squnion> y)"
proof (unfold join_def sup_def)
  assume L: "x \<in> L"  "y \<in> L"
    and P: "!!l. least l (Upper {x, y}) ==> P l"
  with sup_of_two_exists obtain s where "least s (Upper {x, y})" by fast
  with L show "P (THE l. least l (Upper {x, y}))"
    by (fast intro: theI2 least_unique P)
qed

lemma (in lattice) join_closed [simp]:
  "[| x \<in> L; y \<in> L |] ==> x \<squnion> y \<in> L"
  by (rule joinI) (rule least_closed)

lemma (in partial_order) sup_of_singletonI:     (* only reflexivity needed ? *)
  "x \<in> L ==> least x (Upper {x})"
  by (rule least_UpperI) fast+

lemma (in partial_order) sup_of_singleton [simp]:
  "x \<in> L ==> \<Squnion>{x} = x"
  by (unfold sup_def) (blast intro: least_unique least_UpperI sup_of_singletonI)


text {* Condition on @{text A}: supremum exists. *}

lemma (in lattice) sup_insertI:
  "[| !!s. least s (Upper (insert x A)) ==> P s;
  least a (Upper A); x \<in> L; A \<subseteq> L |]
  ==> P (\<Squnion>(insert x A))"
proof (unfold sup_def)
  assume L: "x \<in> L"  "A \<subseteq> L"
    and P: "!!l. least l (Upper (insert x A)) ==> P l"
    and least_a: "least a (Upper A)"
  from least_a have La: "a \<in> L" by simp
  from L sup_of_two_exists least_a
  obtain s where least_s: "least s (Upper {a, x})" by blast
  show "P (THE l. least l (Upper (insert x A)))"
  proof (rule theI2)
    show "least s (Upper (insert x A))"
    proof (rule least_UpperI)
      fix z
      assume "z \<in> insert x A"
      then show "z \<sqsubseteq> s"
      proof
        assume "z = x" then show ?thesis
          by (simp add: least_Upper_above [OF least_s] L La)
      next
        assume "z \<in> A"
        with L least_s least_a show ?thesis
          by (rule_tac trans [where y = a]) (auto dest: least_Upper_above)
      qed
    next
      fix y
      assume y: "y \<in> Upper (insert x A)"
      show "s \<sqsubseteq> y"
      proof (rule least_le [OF least_s], rule Upper_memI)
	fix z
	assume z: "z \<in> {a, x}"
	then show "z \<sqsubseteq> y"
	proof
          have y': "y \<in> Upper A"
            apply (rule subsetD [where A = "Upper (insert x A)"])
            apply (rule Upper_antimono) apply clarify apply assumption
            done
          assume "z = a"
          with y' least_a show ?thesis by (fast dest: least_le)
	next
	  assume "z \<in> {x}"  (* FIXME "z = x"; declare specific elim rule for "insert x {}" (!?) *)
          with y L show ?thesis by blast
	qed
      qed (rule Upper_closed [THEN subsetD])
    next
      from L show "insert x A \<subseteq> L" by simp
      from least_s show "s \<in> L" by simp
    qed
  next
    fix l
    assume least_l: "least l (Upper (insert x A))"
    show "l = s"
    proof (rule least_unique)
      show "least s (Upper (insert x A))"
      proof (rule least_UpperI)
        fix z
        assume "z \<in> insert x A"
        then show "z \<sqsubseteq> s"
	proof
          assume "z = x" then show ?thesis
            by (simp add: least_Upper_above [OF least_s] L La)
	next
          assume "z \<in> A"
          with L least_s least_a show ?thesis
            by (rule_tac trans [where y = a]) (auto dest: least_Upper_above)
	qed
      next
        fix y
        assume y: "y \<in> Upper (insert x A)"
        show "s \<sqsubseteq> y"
        proof (rule least_le [OF least_s], rule Upper_memI)
          fix z
          assume z: "z \<in> {a, x}"
          then show "z \<sqsubseteq> y"
          proof
            have y': "y \<in> Upper A"
	      apply (rule subsetD [where A = "Upper (insert x A)"])
	      apply (rule Upper_antimono) apply clarify apply assumption
	      done
            assume "z = a"
            with y' least_a show ?thesis by (fast dest: least_le)
	  next
            assume "z \<in> {x}"
            with y L show ?thesis by blast
          qed
        qed (rule Upper_closed [THEN subsetD])
      next
        from L show "insert x A \<subseteq> L" by simp
        from least_s show "s \<in> L" by simp
      qed
    qed
  qed
qed

lemma (in lattice) finite_sup_least:
  "[| finite A; A \<subseteq> L; A ~= {} |] ==> least (\<Squnion>A) (Upper A)"
proof (induct set: Finites)
  case empty
  then show ?case by simp
next
  case (insert x A)
  show ?case
  proof (cases "A = {}")
    case True
    with insert show ?thesis by (simp add: sup_of_singletonI)
  next
    case False
    with insert have "least (\<Squnion>A) (Upper A)" by simp
    with _ show ?thesis
      by (rule sup_insertI) (simp_all add: insert [simplified])
  qed
qed

lemma (in lattice) finite_sup_insertI:
  assumes P: "!!l. least l (Upper (insert x A)) ==> P l"
    and xA: "finite A"  "x \<in> L"  "A \<subseteq> L"
  shows "P (\<Squnion> (insert x A))"
proof (cases "A = {}")
  case True with P and xA show ?thesis
    by (simp add: sup_of_singletonI)
next
  case False with P and xA show ?thesis
    by (simp add: sup_insertI finite_sup_least)
qed

lemma (in lattice) finite_sup_closed:
  "[| finite A; A \<subseteq> L; A ~= {} |] ==> \<Squnion>A \<in> L"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case insert then show ?case
    by - (rule finite_sup_insertI, simp_all)
qed

lemma (in lattice) join_left:
  "[| x \<in> L; y \<in> L |] ==> x \<sqsubseteq> x \<squnion> y"
  by (rule joinI [folded join_def]) (blast dest: least_mem)

lemma (in lattice) join_right:
  "[| x \<in> L; y \<in> L |] ==> y \<sqsubseteq> x \<squnion> y"
  by (rule joinI [folded join_def]) (blast dest: least_mem)

lemma (in lattice) sup_of_two_least:
  "[| x \<in> L; y \<in> L |] ==> least (\<Squnion>{x, y}) (Upper {x, y})"
proof (unfold sup_def)
  assume L: "x \<in> L"  "y \<in> L"
  with sup_of_two_exists obtain s where "least s (Upper {x, y})" by fast
  with L show "least (THE xa. least xa (Upper {x, y})) (Upper {x, y})"
  by (fast intro: theI2 least_unique)  (* blast fails *)
qed

lemma (in lattice) join_le:
  assumes sub: "x \<sqsubseteq> z"  "y \<sqsubseteq> z"
    and L: "x \<in> L"  "y \<in> L"  "z \<in> L"
  shows "x \<squnion> y \<sqsubseteq> z"
proof (rule joinI)
  fix s
  assume "least s (Upper {x, y})"
  with sub L show "s \<sqsubseteq> z" by (fast elim: least_le intro: Upper_memI)
qed

lemma (in lattice) join_assoc_lemma:
  assumes L: "x \<in> L"  "y \<in> L"  "z \<in> L"
  shows "x \<squnion> (y \<squnion> z) = \<Squnion>{x, y, z}"
proof (rule finite_sup_insertI)
  -- {* The textbook argument in Jacobson I, p 457 *}
  fix s
  assume sup: "least s (Upper {x, y, z})"
  show "x \<squnion> (y \<squnion> z) = s"
  proof (rule anti_sym)
    from sup L show "x \<squnion> (y \<squnion> z) \<sqsubseteq> s"
      by (fastsimp intro!: join_le elim: least_Upper_above)
  next
    from sup L show "s \<sqsubseteq> x \<squnion> (y \<squnion> z)"
    by (erule_tac least_le)
      (blast intro!: Upper_memI intro: trans join_left join_right join_closed)
  qed (simp_all add: L least_closed [OF sup])
qed (simp_all add: L)

lemma (in order_syntax) join_comm:
  "x \<squnion> y = y \<squnion> x"
  by (unfold join_def) (simp add: insert_commute)

lemma (in lattice) join_assoc:
  assumes L: "x \<in> L"  "y \<in> L"  "z \<in> L"
  shows "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
proof -
  have "(x \<squnion> y) \<squnion> z = z \<squnion> (x \<squnion> y)" by (simp only: join_comm)
  also from L have "... = \<Squnion>{z, x, y}" by (simp add: join_assoc_lemma)
  also from L have "... = \<Squnion>{x, y, z}" by (simp add: insert_commute)
  also from L have "... = x \<squnion> (y \<squnion> z)" by (simp add: join_assoc_lemma)
  finally show ?thesis .
qed


subsubsection {* Infimum *}

lemma (in lattice) meetI:
  "[| !!i. greatest i (Lower {x, y}) ==> P i; x \<in> L; y \<in> L |]
  ==> P (x \<sqinter> y)"
proof (unfold meet_def inf_def)
  assume L: "x \<in> L"  "y \<in> L"
    and P: "!!g. greatest g (Lower {x, y}) ==> P g"
  with inf_of_two_exists obtain i where "greatest i (Lower {x, y})" by fast
  with L show "P (THE g. greatest g (Lower {x, y}))"
  by (fast intro: theI2 greatest_unique P)
qed

lemma (in lattice) meet_closed [simp]:
  "[| x \<in> L; y \<in> L |] ==> x \<sqinter> y \<in> L"
  by (rule meetI) (rule greatest_closed)

lemma (in partial_order) inf_of_singletonI:      (* only reflexivity needed ? *)
  "x \<in> L ==> greatest x (Lower {x})"
  by (rule greatest_LowerI) fast+

lemma (in partial_order) inf_of_singleton [simp]:
  "x \<in> L ==> \<Sqinter> {x} = x"
  by (unfold inf_def) (blast intro: greatest_unique greatest_LowerI inf_of_singletonI)

text {* Condition on A: infimum exists. *}

lemma (in lattice) inf_insertI:
  "[| !!i. greatest i (Lower (insert x A)) ==> P i;
  greatest a (Lower A); x \<in> L; A \<subseteq> L |]
  ==> P (\<Sqinter>(insert x A))"
proof (unfold inf_def)
  assume L: "x \<in> L"  "A \<subseteq> L"
    and P: "!!g. greatest g (Lower (insert x A)) ==> P g"
    and greatest_a: "greatest a (Lower A)"
  from greatest_a have La: "a \<in> L" by simp
  from L inf_of_two_exists greatest_a
  obtain i where greatest_i: "greatest i (Lower {a, x})" by blast
  show "P (THE g. greatest g (Lower (insert x A)))"
  proof (rule theI2)
    show "greatest i (Lower (insert x A))"
    proof (rule greatest_LowerI)
      fix z
      assume "z \<in> insert x A"
      then show "i \<sqsubseteq> z"
      proof
        assume "z = x" then show ?thesis
          by (simp add: greatest_Lower_above [OF greatest_i] L La)
      next
        assume "z \<in> A"
        with L greatest_i greatest_a show ?thesis
          by (rule_tac trans [where y = a]) (auto dest: greatest_Lower_above)
      qed
    next
      fix y
      assume y: "y \<in> Lower (insert x A)"
      show "y \<sqsubseteq> i"
      proof (rule greatest_le [OF greatest_i], rule Lower_memI)
	fix z
	assume z: "z \<in> {a, x}"
	then show "y \<sqsubseteq> z"
	proof
          have y': "y \<in> Lower A"
            apply (rule subsetD [where A = "Lower (insert x A)"])
            apply (rule Lower_antimono) apply clarify apply assumption
            done
          assume "z = a"
          with y' greatest_a show ?thesis by (fast dest: greatest_le)
	next
          assume "z \<in> {x}"
          with y L show ?thesis by blast
	qed
      qed (rule Lower_closed [THEN subsetD])
    next
      from L show "insert x A \<subseteq> L" by simp
      from greatest_i show "i \<in> L" by simp
    qed
  next
    fix g
    assume greatest_g: "greatest g (Lower (insert x A))"
    show "g = i"
    proof (rule greatest_unique)
      show "greatest i (Lower (insert x A))"
      proof (rule greatest_LowerI)
        fix z
        assume "z \<in> insert x A"
        then show "i \<sqsubseteq> z"
	proof
          assume "z = x" then show ?thesis
            by (simp add: greatest_Lower_above [OF greatest_i] L La)
	next
          assume "z \<in> A"
          with L greatest_i greatest_a show ?thesis
            by (rule_tac trans [where y = a]) (auto dest: greatest_Lower_above)
        qed
      next
        fix y
        assume y: "y \<in> Lower (insert x A)"
        show "y \<sqsubseteq> i"
        proof (rule greatest_le [OF greatest_i], rule Lower_memI)
          fix z
          assume z: "z \<in> {a, x}"
          then show "y \<sqsubseteq> z"
          proof
            have y': "y \<in> Lower A"
	      apply (rule subsetD [where A = "Lower (insert x A)"])
	      apply (rule Lower_antimono) apply clarify apply assumption
	      done
            assume "z = a"
            with y' greatest_a show ?thesis by (fast dest: greatest_le)
	  next
            assume "z \<in> {x}"
            with y L show ?thesis by blast
	  qed
        qed (rule Lower_closed [THEN subsetD])
      next
        from L show "insert x A \<subseteq> L" by simp
        from greatest_i show "i \<in> L" by simp
      qed
    qed
  qed
qed

lemma (in lattice) finite_inf_greatest:
  "[| finite A; A \<subseteq> L; A ~= {} |] ==> greatest (\<Sqinter>A) (Lower A)"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case (insert x A)
  show ?case
  proof (cases "A = {}")
    case True
    with insert show ?thesis by (simp add: inf_of_singletonI)
  next
    case False
    from insert show ?thesis
    proof (rule_tac inf_insertI)
      from False insert show "greatest (\<Sqinter>A) (Lower A)" by simp
    qed simp_all
  qed
qed

lemma (in lattice) finite_inf_insertI:
  assumes P: "!!i. greatest i (Lower (insert x A)) ==> P i"
    and xA: "finite A"  "x \<in> L"  "A \<subseteq> L"
  shows "P (\<Sqinter> (insert x A))"
proof (cases "A = {}")
  case True with P and xA show ?thesis
    by (simp add: inf_of_singletonI)
next
  case False with P and xA show ?thesis
    by (simp add: inf_insertI finite_inf_greatest)
qed

lemma (in lattice) finite_inf_closed:
  "[| finite A; A \<subseteq> L; A ~= {} |] ==> \<Sqinter>A \<in> L"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case insert then show ?case
    by (rule_tac finite_inf_insertI) (simp_all)
qed

lemma (in lattice) meet_left:
  "[| x \<in> L; y \<in> L |] ==> x \<sqinter> y \<sqsubseteq> x"
  by (rule meetI [folded meet_def]) (blast dest: greatest_mem)

lemma (in lattice) meet_right:
  "[| x \<in> L; y \<in> L |] ==> x \<sqinter> y \<sqsubseteq> y"
  by (rule meetI [folded meet_def]) (blast dest: greatest_mem)

lemma (in lattice) inf_of_two_greatest:
  "[| x \<in> L; y \<in> L |] ==> greatest (\<Sqinter> {x, y}) (Lower {x, y})"
proof (unfold inf_def)
  assume L: "x \<in> L"  "y \<in> L"
  with inf_of_two_exists obtain s where "greatest s (Lower {x, y})" by fast
  with L
  show "greatest (THE xa. greatest xa (Lower {x, y})) (Lower {x, y})"
  by (fast intro: theI2 greatest_unique)  (* blast fails *)
qed

lemma (in lattice) meet_le:
  assumes sub: "z \<sqsubseteq> x"  "z \<sqsubseteq> y"
    and L: "x \<in> L"  "y \<in> L"  "z \<in> L"
  shows "z \<sqsubseteq> x \<sqinter> y"
proof (rule meetI)
  fix i
  assume "greatest i (Lower {x, y})"
  with sub L show "z \<sqsubseteq> i" by (fast elim: greatest_le intro: Lower_memI)
qed

lemma (in lattice) meet_assoc_lemma:
  assumes L: "x \<in> L"  "y \<in> L"  "z \<in> L"
  shows "x \<sqinter> (y \<sqinter> z) = \<Sqinter>{x, y, z}"
proof (rule finite_inf_insertI)
  txt {* The textbook argument in Jacobson I, p 457 *}
  fix i
  assume inf: "greatest i (Lower {x, y, z})"
  show "x \<sqinter> (y \<sqinter> z) = i"
  proof (rule anti_sym)
    from inf L show "i \<sqsubseteq> x \<sqinter> (y \<sqinter> z)"
      by (fastsimp intro!: meet_le elim: greatest_Lower_above)
  next
    from inf L show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> i"
    by (erule_tac greatest_le)
      (blast intro!: Lower_memI intro: trans meet_left meet_right meet_closed)
  qed (simp_all add: L greatest_closed [OF inf])
qed (simp_all add: L)

lemma (in order_syntax) meet_comm:
  "x \<sqinter> y = y \<sqinter> x"
  by (unfold meet_def) (simp add: insert_commute)

lemma (in lattice) meet_assoc:
  assumes L: "x \<in> L"  "y \<in> L"  "z \<in> L"
  shows "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
proof -
  have "(x \<sqinter> y) \<sqinter> z = z \<sqinter> (x \<sqinter> y)" by (simp only: meet_comm)
  also from L have "... = \<Sqinter> {z, x, y}" by (simp add: meet_assoc_lemma)
  also from L have "... = \<Sqinter> {x, y, z}" by (simp add: insert_commute)
  also from L have "... = x \<sqinter> (y \<sqinter> z)" by (simp add: meet_assoc_lemma)
  finally show ?thesis .
qed


subsection {* Total Orders *}

locale total_order = lattice +
  assumes total: "[| x \<in> L; y \<in> L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"


text {* Introduction rule: the usual definition of total order *}

lemma (in partial_order) total_orderI:
  assumes total: "!!x y. [| x \<in> L; y \<in> L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"
  shows "total_order L le"
proof intro_locales
  show "lattice_axioms L le"
  proof (rule lattice_axioms.intro)
    fix x y
    assume L: "x \<in> L"  "y \<in> L"
    show "EX s. least s (Upper {x, y})"
    proof -
      note total L
      moreover
      {
        assume "x \<sqsubseteq> y"
        with L have "least y (Upper {x, y})"
          by (rule_tac least_UpperI) auto
      }
      moreover
      {
        assume "y \<sqsubseteq> x"
        with L have "least x (Upper {x, y})"
          by (rule_tac least_UpperI) auto
      }
      ultimately show ?thesis by blast
    qed
  next
    fix x y
    assume L: "x \<in> L"  "y \<in> L"
    show "EX i. greatest i (Lower {x, y})"
    proof -
      note total L
      moreover
      {
        assume "y \<sqsubseteq> x"
        with L have "greatest y (Lower {x, y})"
          by (rule_tac greatest_LowerI) auto
      }
      moreover
      {
        assume "x \<sqsubseteq> y"
        with L have "greatest x (Lower {x, y})"
          by (rule_tac greatest_LowerI) auto
      }
      ultimately show ?thesis by blast
    qed
  qed
qed (assumption | rule total_order_axioms.intro)+


subsection {* Complete lattices *}

locale complete_lattice = lattice +
  assumes sup_exists:
    "[| A \<subseteq> L |] ==> EX s. order_syntax.least L le s (order_syntax.Upper L le A)"
    and inf_exists:
    "[| A \<subseteq> L |] ==> EX i. order_syntax.greatest L le i (order_syntax.Lower L le A)"

text {* Introduction rule: the usual definition of complete lattice *}

lemma (in partial_order) complete_latticeI:
  assumes sup_exists:
    "!!A. [| A \<subseteq> L |] ==> EX s. least s (Upper A)"
    and inf_exists:
    "!!A. [| A \<subseteq> L |] ==> EX i. greatest i (Lower A)"
  shows "complete_lattice L le"
proof intro_locales
  show "lattice_axioms L le"
    by (rule lattice_axioms.intro) (blast intro: sup_exists inf_exists)+
qed (assumption | rule complete_lattice_axioms.intro)+

definition (in order_syntax)
  top ("\<top>") where
  "\<top> == sup L"

definition (in order_syntax)
  bottom ("\<bottom>") where
  "\<bottom> == inf L"


lemma (in complete_lattice) supI:
  "[| !!l. least l (Upper A) ==> P l; A \<subseteq> L |]
  ==> P (\<Squnion>A)"
proof (unfold sup_def)
  assume L: "A \<subseteq> L"
    and P: "!!l. least l (Upper A) ==> P l"
  with sup_exists obtain s where "least s (Upper A)" by blast
  with L show "P (THE l. least l (Upper A))"
  by (fast intro: theI2 least_unique P)
qed

lemma (in complete_lattice) sup_closed [simp]:
  "A \<subseteq> L ==> \<Squnion>A \<in> L"
  by (rule supI) simp_all

lemma (in complete_lattice) top_closed [simp, intro]:
  "\<top> \<in> L"
  by (unfold top_def) simp

lemma (in complete_lattice) infI:
  "[| !!i. greatest i (Lower A) ==> P i; A \<subseteq> L |]
  ==> P (\<Sqinter>A)"
proof (unfold inf_def)
  assume L: "A \<subseteq> L"
    and P: "!!l. greatest l (Lower A) ==> P l"
  with inf_exists obtain s where "greatest s (Lower A)" by blast
  with L show "P (THE l. greatest l (Lower A))"
  by (fast intro: theI2 greatest_unique P)
qed

lemma (in complete_lattice) inf_closed [simp]:
  "A \<subseteq> L ==> \<Sqinter>A \<in> L"
  by (rule infI) simp_all

lemma (in complete_lattice) bottom_closed [simp, intro]:
  "\<bottom> \<in> L"
  by (unfold bottom_def) simp

text {* Jacobson: Theorem 8.1 *}

lemma (in order_syntax) Lower_empty [simp]:
  "Lower {} = L"
  by (unfold Lower_def) simp

lemma (in order_syntax) Upper_empty [simp]:
  "Upper {} = L"
  by (unfold Upper_def) simp

theorem (in partial_order) complete_lattice_criterion1:
  assumes top_exists: "EX g. greatest g L"
    and inf_exists:
      "!!A. [| A \<subseteq> L; A ~= {} |] ==> EX i. greatest i (Lower A)"
  shows "complete_lattice L le"
proof (rule complete_latticeI)
  from top_exists obtain top where top: "greatest top L" ..
  fix A
  assume L: "A \<subseteq> L"
  let ?B = "Upper A"
  from L top have "top \<in> ?B" by (fast intro!: Upper_memI intro: greatest_le)
  then have B_non_empty: "?B ~= {}" by fast
  have B_L: "?B \<subseteq> L" by simp
  from inf_exists [OF B_L B_non_empty]
  obtain b where b_inf_B: "greatest b (Lower ?B)" ..
  have "least b (Upper A)"
apply (rule least_UpperI)
   apply (rule greatest_le [where A = "Lower ?B"])
    apply (rule b_inf_B)
   apply (rule Lower_memI)
    apply (erule UpperD)
     apply assumption
    apply (rule L)
   apply (fast intro: L [THEN subsetD])
  apply (erule greatest_Lower_above [OF b_inf_B])
  apply simp
 apply (rule L)
apply (rule greatest_closed [OF b_inf_B]) (* rename rule: _closed *)
done
  then show "EX s. least s (Upper A)" ..
next
  fix A
  assume L: "A \<subseteq> L"
  show "EX i. greatest i (Lower A)"
  proof (cases "A = {}")
    case True then show ?thesis
      by (simp add: top_exists)
  next
    case False with L show ?thesis
      by (rule inf_exists)
  qed
qed

(* TODO: prove dual version *)


subsection {* Examples *}

subsubsection {* Powerset of a Set is a Complete Lattice *}

theorem powerset_is_complete_lattice:
  "complete_lattice (Pow A) (op \<subseteq>)"
  (is "complete_lattice ?L ?le")
proof (rule partial_order.complete_latticeI)
  show "partial_order ?L ?le"
    by (rule partial_order.intro) auto
next
  fix B
  assume "B \<subseteq> ?L"
  then have "order_syntax.least ?L ?le (\<Union> B) (order_syntax.Upper ?L ?le B)"
    by (fastsimp intro!: order_syntax.least_UpperI simp: order_syntax.Upper_def)
  then show "EX s. order_syntax.least ?L ?le s (order_syntax.Upper ?L ?le B)" ..
next
  fix B
  assume "B \<subseteq> ?L"
  then have "order_syntax.greatest ?L ?le (\<Inter> B \<inter> A) (order_syntax.Lower ?L ?le B)"
    txt {* @{term "\<Inter> B"} is not the infimum of @{term B}:
      @{term "\<Inter> {} = UNIV"} which is in general bigger than @{term "A"}! *}
    by (fastsimp intro!: order_syntax.greatest_LowerI simp: order_syntax.Lower_def)
  then show "EX i. order_syntax.greatest ?L ?le i (order_syntax.Lower ?L ?le B)" ..
qed

text {* An other example, that of the lattice of subgroups of a group,
  can be found in Group theory (Section~\ref{sec:subgroup-lattice}). *}

end
