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

(*
record 'a order = "'a partial_object" +
  le :: "['a, 'a] => bool" (infixl "\<sqsubseteq>\<index>" 50)
*)

text {* Locale @{text order_syntax} is required since we want to refer
  to definitions (and their derived theorems) outside of @{text partial_order}.
  *}

locale order_syntax =
  fixes carrier :: "'a set" and le :: "['a, 'a] => bool" (infix "\<sqsubseteq>" 50)

text {* Note that the type constraints above are necessary, because the
  definition command cannot specialise the types. *}

definition (in order_syntax)
  less (infixl "\<sqsubset>" 50) "x \<sqsubset> y == x \<sqsubseteq> y & x ~= y"

text {* Upper and lower bounds of a set. *}

definition (in order_syntax)
  Upper where
  "Upper A == {u. (ALL x. x \<in> A \<inter> carrier --> x \<sqsubseteq> u)} \<inter>
              carrier"

definition (in order_syntax)
  Lower :: "'a set => 'a set"
  "Lower A == {l. (ALL x. x \<in> A \<inter> carrier --> l \<sqsubseteq> x)} \<inter>
              carrier"

text {* Least and greatest, as predicate. *}

definition (in order_syntax)
  least :: "['a, 'a set] => bool"
  "least l A == A \<subseteq> carrier & l \<in> A & (ALL x : A. l \<sqsubseteq> x)"

definition (in order_syntax)
  greatest :: "['a, 'a set] => bool"
  "greatest g A == A \<subseteq> carrier & g \<in> A & (ALL x : A. x \<sqsubseteq> g)"

text {* Supremum and infimum *}

definition (in order_syntax)
  sup :: "'a set => 'a" ("\<Squnion>")  (* FIXME precedence [90] 90 *)
  "\<Squnion>A == THE x. least x (Upper A)"

definition (in order_syntax)
  inf :: "'a set => 'a" ("\<Sqinter>") (* FIXME precedence *)
  "\<Sqinter>A == THE x. greatest x (Lower A)"

definition (in order_syntax)
  join :: "['a, 'a] => 'a" (infixl "\<squnion>" 65)
  "x \<squnion> y == sup {x, y}"

definition (in order_syntax)
  meet :: "['a, 'a] => 'a" (infixl "\<sqinter>" 70)
  "x \<sqinter> y == inf {x, y}"

locale partial_order = order_syntax +
  assumes refl [intro, simp]:
                  "x \<in> carrier ==> x \<sqsubseteq> x"
    and anti_sym [intro]:
                  "[| x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> carrier; y \<in> carrier |] ==> x = y"
    and trans [trans]:
                  "[| x \<sqsubseteq> y; y \<sqsubseteq> z;
                   x \<in> carrier; y \<in> carrier; z \<in> carrier |] ==> x \<sqsubseteq> z"

abbreviation (in partial_order)
  less (infixl "\<sqsubset>" 50) "less == order_syntax.less le"
abbreviation (in partial_order)
  Upper where "Upper == order_syntax.Upper carrier le"
abbreviation (in partial_order)
  Lower where "Lower == order_syntax.Lower carrier le"
abbreviation (in partial_order)
  least where "least == order_syntax.least carrier le"
abbreviation (in partial_order)
  greatest where "greatest == order_syntax.greatest carrier le"
abbreviation (in partial_order)
  sup ("\<Squnion>") (* FIXME precedence *) "sup == order_syntax.sup carrier le"
abbreviation (in partial_order)
  inf ("\<Sqinter>") (* FIXME precedence *) "inf == order_syntax.inf carrier le"
abbreviation (in partial_order)
  join (infixl "\<squnion>" 65) "join == order_syntax.join carrier le"
abbreviation (in partial_order)
  meet (infixl "\<sqinter>" 70) "meet == order_syntax.meet carrier le"


subsubsection {* Upper *}

lemma (in order_syntax) Upper_closed [intro, simp]:
  "Upper A \<subseteq> carrier"
  by (unfold Upper_def) clarify

lemma (in order_syntax) UpperD [dest]:
  fixes L (structure)
  shows "[| u \<in> Upper A; x \<in> A; A \<subseteq> carrier |] ==> x \<sqsubseteq> u"
  by (unfold Upper_def) blast

lemma (in order_syntax) Upper_memI:
  fixes L (structure)
  shows "[| !! y. y \<in> A ==> y \<sqsubseteq> x; x \<in> carrier |] ==> x \<in> Upper A"
  by (unfold Upper_def) blast

lemma (in order_syntax) Upper_antimono:
  "A \<subseteq> B ==> Upper B \<subseteq> Upper A"
  by (unfold Upper_def) blast


subsubsection {* Lower *}

lemma (in order_syntax) Lower_closed [intro, simp]:
  "Lower A \<subseteq> carrier"
  by (unfold Lower_def) clarify

lemma (in order_syntax) LowerD [dest]:
  "[| l \<in> Lower A; x \<in> A; A \<subseteq> carrier |] ==> l \<sqsubseteq> x"
  by (unfold Lower_def) blast

lemma (in order_syntax) Lower_memI:
  "[| !! y. y \<in> A ==> x \<sqsubseteq> y; x \<in> carrier |] ==> x \<in> Lower A"
  by (unfold Lower_def) blast

lemma (in order_syntax) Lower_antimono:
  "A \<subseteq> B ==> Lower B \<subseteq> Lower A"
  by (unfold Lower_def) blast


subsubsection {* least *}

lemma (in order_syntax) least_carrier [intro, simp]:
  "least l A ==> l \<in> carrier"
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
    and L: "A \<subseteq> carrier"  "s \<in> carrier"
  shows "least s (Upper A)"
proof -
  have "Upper A \<subseteq> carrier" by simp
  moreover from above L have "s \<in> Upper A" by (simp add: Upper_def)
  moreover from below have "ALL x : Upper A. s \<sqsubseteq> x" by fast
  ultimately show ?thesis by (simp add: least_def)
qed


subsubsection {* greatest *}

lemma (in order_syntax) greatest_carrier [intro, simp]:
  "greatest l A ==> l \<in> carrier"
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
    and L: "A \<subseteq> carrier"  "i \<in> carrier"
  shows "greatest i (Lower A)"
proof -
  have "Lower A \<subseteq> carrier" by simp
  moreover from below L have "i \<in> Lower A" by (simp add: Lower_def)
  moreover from above have "ALL x : Lower A. x \<sqsubseteq> i" by fast
  ultimately show ?thesis by (simp add: greatest_def)
qed


subsection {* Lattices *}

locale lattice = partial_order +
  assumes sup_of_two_exists:
    "[| x \<in> carrier; y \<in> carrier |] ==> EX s. order_syntax.least carrier le s (order_syntax.Upper carrier le {x, y})"
    and inf_of_two_exists:
    "[| x \<in> carrier; y \<in> carrier |] ==> EX s. order_syntax.greatest carrier le s (order_syntax.Lower carrier le {x, y})"

abbreviation (in lattice)
  less (infixl "\<sqsubset>" 50) "less == order_syntax.less le"
abbreviation (in lattice)
  Upper where "Upper == order_syntax.Upper carrier le"
abbreviation (in lattice)
  Lower where "Lower == order_syntax.Lower carrier le"
abbreviation (in lattice)
  least where "least == order_syntax.least carrier le"
abbreviation (in lattice)
  greatest where "greatest == order_syntax.greatest carrier le"
abbreviation (in lattice)
  sup ("\<Squnion>") (* FIXME precedence *) "sup == order_syntax.sup carrier le"
abbreviation (in lattice)
  inf ("\<Sqinter>") (* FIXME precedence *) "inf == order_syntax.inf carrier le"
abbreviation (in lattice)
  join (infixl "\<squnion>" 65) "join == order_syntax.join carrier le"
abbreviation (in lattice)
  meet (infixl "\<sqinter>" 70) "meet == order_syntax.meet carrier le"

lemma (in order_syntax) least_Upper_above:
  "[| least s (Upper A); x \<in> A; A \<subseteq> carrier |] ==> x \<sqsubseteq> s"
  by (unfold least_def) blast

lemma (in order_syntax) greatest_Lower_above:
  "[| greatest i (Lower A); x \<in> A; A \<subseteq> carrier |] ==> i \<sqsubseteq> x"
  by (unfold greatest_def) blast


subsubsection {* Supremum *}

lemma (in lattice) joinI:
  "[| !!l. least l (Upper {x, y}) ==> P l; x \<in> carrier; y \<in> carrier |]
  ==> P (x \<squnion> y)"
proof (unfold join_def sup_def)
  assume L: "x \<in> carrier"  "y \<in> carrier"
    and P: "!!l. least l (Upper {x, y}) ==> P l"
  with sup_of_two_exists obtain s where "least s (Upper {x, y})" by fast
  with L show "P (THE l. least l (Upper {x, y}))"
    by (fast intro: theI2 least_unique P)
qed

lemma (in lattice) join_closed [simp]:
  "[| x \<in> carrier; y \<in> carrier |] ==> x \<squnion> y \<in> carrier"
  by (rule joinI) (rule least_carrier)

lemma (in partial_order) sup_of_singletonI:     (* only reflexivity needed ? *)
  "x \<in> carrier ==> least x (Upper {x})"
  by (rule least_UpperI) fast+

lemma (in partial_order) sup_of_singleton [simp]:
  "x \<in> carrier ==> \<Squnion>{x} = x"
  by (unfold sup_def) (blast intro: least_unique least_UpperI sup_of_singletonI)


text {* Condition on @{text A}: supremum exists. *}

lemma (in lattice) sup_insertI:
  "[| !!s. least s (Upper (insert x A)) ==> P s;
  least a (Upper A); x \<in> carrier; A \<subseteq> carrier |]
  ==> P (\<Squnion>(insert x A))"
proof (unfold sup_def)
  assume L: "x \<in> carrier"  "A \<subseteq> carrier"
    and P: "!!l. least l (Upper (insert x A)) ==> P l"
    and least_a: "least a (Upper A)"
  from least_a have La: "a \<in> carrier" by simp
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
      from L show "insert x A \<subseteq> carrier" by simp
      from least_s show "s \<in> carrier" by simp
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
        from L show "insert x A \<subseteq> carrier" by simp
        from least_s show "s \<in> carrier" by simp
      qed
    qed
  qed
qed

lemma (in lattice) finite_sup_least:
  "[| finite A; A \<subseteq> carrier; A ~= {} |] ==> least (\<Squnion>A) (Upper A)"
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
    and xA: "finite A"  "x \<in> carrier"  "A \<subseteq> carrier"
  shows "P (\<Squnion> (insert x A))"
proof (cases "A = {}")
  case True with P and xA show ?thesis
    by (simp add: sup_of_singletonI)
next
  case False with P and xA show ?thesis
    by (simp add: sup_insertI finite_sup_least)
qed

lemma (in lattice) finite_sup_closed:
  "[| finite A; A \<subseteq> carrier; A ~= {} |] ==> \<Squnion>A \<in> carrier"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case insert then show ?case
    by - (rule finite_sup_insertI, simp_all)
qed

lemma (in lattice) join_left:
  "[| x \<in> carrier; y \<in> carrier |] ==> x \<sqsubseteq> x \<squnion> y"
  by (rule joinI [folded join_def]) (blast dest: least_mem)

lemma (in lattice) join_right:
  "[| x \<in> carrier; y \<in> carrier |] ==> y \<sqsubseteq> x \<squnion> y"
  by (rule joinI [folded join_def]) (blast dest: least_mem)

lemma (in lattice) sup_of_two_least:
  "[| x \<in> carrier; y \<in> carrier |] ==> least (\<Squnion>{x, y}) (Upper {x, y})"
proof (unfold sup_def)
  assume L: "x \<in> carrier"  "y \<in> carrier"
  with sup_of_two_exists obtain s where "least s (Upper {x, y})" by fast
  with L show "least (THE xa. least xa (Upper {x, y})) (Upper {x, y})"
  by (fast intro: theI2 least_unique)  (* blast fails *)
qed

lemma (in lattice) join_le:
  assumes sub: "x \<sqsubseteq> z"  "y \<sqsubseteq> z"
    and L: "x \<in> carrier"  "y \<in> carrier"  "z \<in> carrier"
  shows "x \<squnion> y \<sqsubseteq> z"
proof (rule joinI)
  fix s
  assume "least s (Upper {x, y})"
  with sub L show "s \<sqsubseteq> z" by (fast elim: least_le intro: Upper_memI)
qed

lemma (in lattice) join_assoc_lemma:
  assumes L: "x \<in> carrier"  "y \<in> carrier"  "z \<in> carrier"
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
  qed (simp_all add: L least_carrier [OF sup])
qed (simp_all add: L)

lemma (in order_syntax) join_comm:
  "x \<squnion> y = y \<squnion> x"
  by (unfold join_def) (simp add: insert_commute)

lemma (in lattice) join_assoc:
  assumes L: "x \<in> carrier"  "y \<in> carrier"  "z \<in> carrier"
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
  "[| !!i. greatest i (Lower {x, y}) ==> P i;
  x \<in> carrier; y \<in> carrier |]
  ==> P (x \<sqinter> y)"
proof (unfold meet_def inf_def)
  assume L: "x \<in> carrier"  "y \<in> carrier"
    and P: "!!g. greatest g (Lower {x, y}) ==> P g"
  with inf_of_two_exists obtain i where "greatest i (Lower {x, y})" by fast
  with L show "P (THE g. greatest g (Lower {x, y}))"
  by (fast intro: theI2 greatest_unique P)
qed

lemma (in lattice) meet_closed [simp]:
  "[| x \<in> carrier; y \<in> carrier |] ==> x \<sqinter> y \<in> carrier"
  by (rule meetI) (rule greatest_carrier)

lemma (in partial_order) inf_of_singletonI:      (* only reflexivity needed ? *)
  "x \<in> carrier ==> greatest x (Lower {x})"
  by (rule greatest_LowerI) fast+

lemma (in partial_order) inf_of_singleton [simp]:
  "x \<in> carrier ==> \<Sqinter> {x} = x"
  by (unfold inf_def) (blast intro: greatest_unique greatest_LowerI inf_of_singletonI)

text {* Condition on A: infimum exists. *}

lemma (in lattice) inf_insertI:
  "[| !!i. greatest i (Lower (insert x A)) ==> P i;
  greatest a (Lower A); x \<in> carrier; A \<subseteq> carrier |]
  ==> P (\<Sqinter>(insert x A))"
proof (unfold inf_def)
  assume L: "x \<in> carrier"  "A \<subseteq> carrier"
    and P: "!!g. greatest g (Lower (insert x A)) ==> P g"
    and greatest_a: "greatest a (Lower A)"
  from greatest_a have La: "a \<in> carrier" by simp
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
      from L show "insert x A \<subseteq> carrier" by simp
      from greatest_i show "i \<in> carrier" by simp
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
        from L show "insert x A \<subseteq> carrier" by simp
        from greatest_i show "i \<in> carrier" by simp
      qed
    qed
  qed
qed

lemma (in lattice) finite_inf_greatest:
  "[| finite A; A \<subseteq> carrier; A ~= {} |] ==> greatest (\<Sqinter>A) (Lower A)"
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
    and xA: "finite A"  "x \<in> carrier"  "A \<subseteq> carrier"
  shows "P (\<Sqinter> (insert x A))"
proof (cases "A = {}")
  case True with P and xA show ?thesis
    by (simp add: inf_of_singletonI)
next
  case False with P and xA show ?thesis
    by (simp add: inf_insertI finite_inf_greatest)
qed

lemma (in lattice) finite_inf_closed:
  "[| finite A; A \<subseteq> carrier; A ~= {} |] ==> \<Sqinter>A \<in> carrier"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case insert then show ?case
    by (rule_tac finite_inf_insertI) (simp_all)
qed

lemma (in lattice) meet_left:
  "[| x \<in> carrier; y \<in> carrier |] ==> x \<sqinter> y \<sqsubseteq> x"
  by (rule meetI [folded meet_def]) (blast dest: greatest_mem)

lemma (in lattice) meet_right:
  "[| x \<in> carrier; y \<in> carrier |] ==> x \<sqinter> y \<sqsubseteq> y"
  by (rule meetI [folded meet_def]) (blast dest: greatest_mem)

lemma (in lattice) inf_of_two_greatest:
  "[| x \<in> carrier; y \<in> carrier |] ==>
  greatest (\<Sqinter> {x, y}) (Lower {x, y})"
proof (unfold inf_def)
  assume L: "x \<in> carrier"  "y \<in> carrier"
  with inf_of_two_exists obtain s where "greatest s (Lower {x, y})" by fast
  with L
  show "greatest (THE xa. greatest xa (Lower {x, y})) (Lower {x, y})"
  by (fast intro: theI2 greatest_unique)  (* blast fails *)
qed

lemma (in lattice) meet_le:
  assumes sub: "z \<sqsubseteq> x"  "z \<sqsubseteq> y"
    and L: "x \<in> carrier"  "y \<in> carrier"  "z \<in> carrier"
  shows "z \<sqsubseteq> x \<sqinter> y"
proof (rule meetI)
  fix i
  assume "greatest i (Lower {x, y})"
  with sub L show "z \<sqsubseteq> i" by (fast elim: greatest_le intro: Lower_memI)
qed

lemma (in lattice) meet_assoc_lemma:
  assumes L: "x \<in> carrier"  "y \<in> carrier"  "z \<in> carrier"
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
  qed (simp_all add: L greatest_carrier [OF inf])
qed (simp_all add: L)

lemma (in order_syntax) meet_comm:
  "x \<sqinter> y = y \<sqinter> x"
  by (unfold meet_def) (simp add: insert_commute)

lemma (in lattice) meet_assoc:
  assumes L: "x \<in> carrier"  "y \<in> carrier"  "z \<in> carrier"
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
  assumes total: "[| x \<in> carrier; y \<in> carrier |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"

abbreviation (in total_order)
  less (infixl "\<sqsubset>" 50) "less == order_syntax.less le"
abbreviation (in total_order)
  Upper where "Upper == order_syntax.Upper carrier le"
abbreviation (in total_order)
  Lower where "Lower == order_syntax.Lower carrier le"
abbreviation (in total_order)
  least where "least == order_syntax.least carrier le"
abbreviation (in total_order)
  greatest where "greatest == order_syntax.greatest carrier le"
abbreviation (in total_order)
  sup ("\<Squnion>") (* FIXME precedence *) "sup == order_syntax.sup carrier le"
abbreviation (in total_order)
  inf ("\<Sqinter>") (* FIXME precedence *) "inf == order_syntax.inf carrier le"
abbreviation (in total_order)
  join (infixl "\<squnion>" 65) "join == order_syntax.join carrier le"
abbreviation (in total_order)
  meet (infixl "\<sqinter>" 70) "meet == order_syntax.meet carrier le"

text {* Introduction rule: the usual definition of total order *}

lemma (in partial_order) total_orderI:
  assumes total: "!!x y. [| x \<in> carrier; y \<in> carrier |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"
  shows "total_order carrier le"
proof intro_locales
  show "lattice_axioms carrier le"
  proof (rule lattice_axioms.intro)
    fix x y
    assume L: "x \<in> carrier"  "y \<in> carrier"
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
    assume L: "x \<in> carrier"  "y \<in> carrier"
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
    "[| A \<subseteq> carrier |] ==> EX s. order_syntax.least carrier le s (order_syntax.Upper carrier le A)"
    and inf_exists:
    "[| A \<subseteq> carrier |] ==> EX i. order_syntax.greatest carrier le i (order_syntax.Lower carrier le A)"

abbreviation (in complete_lattice)
  less (infixl "\<sqsubset>" 50) "less == order_syntax.less le"
abbreviation (in complete_lattice)
  Upper where "Upper == order_syntax.Upper carrier le"
abbreviation (in complete_lattice)
  Lower where "Lower == order_syntax.Lower carrier le"
abbreviation (in complete_lattice)
  least where "least == order_syntax.least carrier le"
abbreviation (in complete_lattice)
  greatest where "greatest == order_syntax.greatest carrier le"
abbreviation (in complete_lattice)
  sup ("\<Squnion>") (* FIXME precedence *) "sup == order_syntax.sup carrier le"
abbreviation (in complete_lattice)
  inf ("\<Sqinter>") (* FIXME precedence *) "inf == order_syntax.inf carrier le"
abbreviation (in complete_lattice)
  join (infixl "\<squnion>" 65) "join == order_syntax.join carrier le"
abbreviation (in complete_lattice)
  meet (infixl "\<sqinter>" 70) "meet == order_syntax.meet carrier le"

text {* Introduction rule: the usual definition of complete lattice *}

lemma (in partial_order) complete_latticeI:
  assumes sup_exists:
    "!!A. [| A \<subseteq> carrier |] ==> EX s. least s (Upper A)"
    and inf_exists:
    "!!A. [| A \<subseteq> carrier |] ==> EX i. greatest i (Lower A)"
  shows "complete_lattice carrier le"
proof intro_locales
  show "lattice_axioms carrier le"
    by (rule lattice_axioms.intro) (blast intro: sup_exists inf_exists)+
qed (assumption | rule complete_lattice_axioms.intro)+

definition (in order_syntax)
  top ("\<top>")
  "\<top> == sup carrier"

definition (in order_syntax)
  bottom ("\<bottom>")
  "\<bottom> == inf carrier"

abbreviation (in partial_order)
  top ("\<top>") "top == order_syntax.top carrier le"
abbreviation (in partial_order)
  bottom ("\<bottom>") "bottom == order_syntax.bottom carrier le"
abbreviation (in lattice)
  top ("\<top>") "top == order_syntax.top carrier le"
abbreviation (in lattice)
  bottom ("\<bottom>") "bottom == order_syntax.bottom carrier le"
abbreviation (in total_order)
  top ("\<top>") "top == order_syntax.top carrier le"
abbreviation (in total_order)
  bottom ("\<bottom>") "bottom == order_syntax.bottom carrier le"
abbreviation (in complete_lattice)
  top ("\<top>") "top == order_syntax.top carrier le"
abbreviation (in complete_lattice)
  bottom ("\<bottom>") "bottom == order_syntax.bottom carrier le"


lemma (in complete_lattice) supI:
  "[| !!l. least l (Upper A) ==> P l; A \<subseteq> carrier |]
  ==> P (\<Squnion>A)"
proof (unfold sup_def)
  assume L: "A \<subseteq> carrier"
    and P: "!!l. least l (Upper A) ==> P l"
  with sup_exists obtain s where "least s (Upper A)" by blast
  with L show "P (THE l. least l (Upper A))"
  by (fast intro: theI2 least_unique P)
qed

lemma (in complete_lattice) sup_closed [simp]:
  "A \<subseteq> carrier ==> \<Squnion>A \<in> carrier"
  by (rule supI) simp_all

lemma (in complete_lattice) top_closed [simp, intro]:
  "\<top> \<in> carrier"
  by (unfold top_def) simp

lemma (in complete_lattice) infI:
  "[| !!i. greatest i (Lower A) ==> P i; A \<subseteq> carrier |]
  ==> P (\<Sqinter>A)"
proof (unfold inf_def)
  assume L: "A \<subseteq> carrier"
    and P: "!!l. greatest l (Lower A) ==> P l"
  with inf_exists obtain s where "greatest s (Lower A)" by blast
  with L show "P (THE l. greatest l (Lower A))"
  by (fast intro: theI2 greatest_unique P)
qed

lemma (in complete_lattice) inf_closed [simp]:
  "A \<subseteq> carrier ==> \<Sqinter>A \<in> carrier"
  by (rule infI) simp_all

lemma (in complete_lattice) bottom_closed [simp, intro]:
  "\<bottom> \<in> carrier"
  by (unfold bottom_def) simp

text {* Jacobson: Theorem 8.1 *}

lemma (in order_syntax) Lower_empty [simp]:
  "Lower {} = carrier"
  by (unfold Lower_def) simp

lemma (in order_syntax) Upper_empty [simp]:
  "Upper {} = carrier"
  by (unfold Upper_def) simp

theorem (in partial_order) complete_lattice_criterion1:
  assumes top_exists: "EX g. greatest g (carrier)"
    and inf_exists:
      "!!A. [| A \<subseteq> carrier; A ~= {} |] ==> EX i. greatest i (Lower A)"
  shows "complete_lattice carrier le"
proof (rule complete_latticeI)
  from top_exists obtain top where top: "greatest top (carrier)" ..
  fix A
  assume L: "A \<subseteq> carrier"
  let ?B = "Upper A"
  from L top have "top \<in> ?B" by (fast intro!: Upper_memI intro: greatest_le)
  then have B_non_empty: "?B ~= {}" by fast
  have B_L: "?B \<subseteq> carrier" by simp
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
apply (rule greatest_carrier [OF b_inf_B]) (* rename rule: _closed *)
done
  then show "EX s. least s (Upper A)" ..
next
  fix A
  assume L: "A \<subseteq> carrier"
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
  (is "complete_lattice ?car ?le")
proof (rule partial_order.complete_latticeI)
  show "partial_order ?car ?le"
    by (rule partial_order.intro) auto
next
  fix B
  assume "B \<subseteq> ?car"
  then have "order_syntax.least ?car ?le (\<Union> B) (order_syntax.Upper ?car ?le B)"
    by (fastsimp intro!: order_syntax.least_UpperI simp: order_syntax.Upper_def)
  then show "EX s. order_syntax.least ?car ?le s (order_syntax.Upper ?car ?le B)" ..
next
  fix B
  assume "B \<subseteq> ?car"
  then have "order_syntax.greatest ?car ?le (\<Inter> B \<inter> A) (order_syntax.Lower ?car ?le B)"
    txt {* @{term "\<Inter> B"} is not the infimum of @{term B}:
      @{term "\<Inter> {} = UNIV"} which is in general bigger than @{term "A"}! *}
    by (fastsimp intro!: order_syntax.greatest_LowerI simp: order_syntax.Lower_def)
  then show "EX i. order_syntax.greatest ?car ?le i (order_syntax.Lower ?car ?le B)" ..
qed

text {* An other example, that of the lattice of subgroups of a group,
  can be found in Group theory (Section~\ref{sec:subgroup-lattice}). *}

end
