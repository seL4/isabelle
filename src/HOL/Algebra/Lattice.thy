(*  Title:      HOL/Algebra/Lattice.thy
    Author:     Clemens Ballarin, started 7 November 2003
    Copyright:  Clemens Ballarin

Most congruence rules by Stephan Hohe.
With additional contributions from Alasdair Armstrong and Simon Foster.
*)

theory Lattice
imports Order
begin

section \<open>Lattices\<close>
  
subsection \<open>Supremum and infimum\<close>

definition
  sup :: "[_, 'a set] => 'a" (\<open>(\<open>open_block notation=\<open>prefix \<Squnion>\<close>\<close>\<Squnion>\<index>_)\<close> [90] 90)
  where "\<Squnion>\<^bsub>L\<^esub>A = (SOME x. least L x (Upper L A))"

definition
  inf :: "[_, 'a set] => 'a" (\<open>(\<open>open_block notation=\<open>prefix \<Sqinter>\<close>\<close>\<Sqinter>\<index>_)\<close> [90] 90)
  where "\<Sqinter>\<^bsub>L\<^esub>A = (SOME x. greatest L x (Lower L A))"

definition supr :: 
  "('a, 'b) gorder_scheme \<Rightarrow> 'c set \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'a "
  where "supr L A f = \<Squnion>\<^bsub>L\<^esub>(f ` A)"

definition infi :: 
  "('a, 'b) gorder_scheme \<Rightarrow> 'c set \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'a "
  where "infi L A f = \<Sqinter>\<^bsub>L\<^esub>(f ` A)"

syntax
  "_inf1"     :: "('a, 'b) gorder_scheme \<Rightarrow> pttrns \<Rightarrow> 'a \<Rightarrow> 'a"
    (\<open>(\<open>indent=3 notation=\<open>binder IINF\<close>\<close>IINF\<index> _./ _)\<close> [0, 10] 10)
  "_inf"      :: "('a, 'b) gorder_scheme \<Rightarrow> pttrn \<Rightarrow> 'c set \<Rightarrow> 'a \<Rightarrow> 'a"
    (\<open>(\<open>indent=3 notation=\<open>binder IINF\<close>\<close>IINF\<index> _:_./ _)\<close> [0, 0, 10] 10)
  "_sup1"     :: "('a, 'b) gorder_scheme \<Rightarrow> pttrns \<Rightarrow> 'a \<Rightarrow> 'a"
    (\<open>(\<open>indent=3 notation=\<open>binder SSUP\<close>\<close>SSUP\<index> _./ _)\<close> [0, 10] 10)
  "_sup"      :: "('a, 'b) gorder_scheme \<Rightarrow> pttrn \<Rightarrow> 'c set \<Rightarrow> 'a \<Rightarrow> 'a"
    (\<open>(\<open>indent=3 notation=\<open>binder SSUP\<close>\<close>SSUP\<index> _:_./ _)\<close> [0, 0, 10] 10)
syntax_consts
  "_inf1" "_inf" == infi and
  "_sup1" "_sup" == supr
translations
  "IINF\<^bsub>L\<^esub> x. B"     == "CONST infi L CONST UNIV (%x. B)"
  "IINF\<^bsub>L\<^esub> x:A. B"   == "CONST infi L A (%x. B)"
  "SSUP\<^bsub>L\<^esub> x. B"     == "CONST supr L CONST UNIV (%x. B)"
  "SSUP\<^bsub>L\<^esub> x:A. B"   == "CONST supr L A (%x. B)"

definition
  join :: "[_, 'a, 'a] => 'a" (infixl \<open>\<squnion>\<index>\<close> 65)
  where "x \<squnion>\<^bsub>L\<^esub> y = \<Squnion>\<^bsub>L\<^esub>{x, y}"

definition
  meet :: "[_, 'a, 'a] => 'a" (infixl \<open>\<sqinter>\<index>\<close> 70)
  where "x \<sqinter>\<^bsub>L\<^esub> y = \<Sqinter>\<^bsub>L\<^esub>{x, y}"

definition
  LEAST_FP :: "('a, 'b) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" (\<open>LFP\<index>\<close>) where
  "LEAST_FP L f = \<Sqinter>\<^bsub>L\<^esub> {u \<in> carrier L. f u \<sqsubseteq>\<^bsub>L\<^esub> u}"    \<comment> \<open>least fixed point\<close>

definition
  GREATEST_FP:: "('a, 'b) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" (\<open>GFP\<index>\<close>) where
  "GREATEST_FP L f = \<Squnion>\<^bsub>L\<^esub> {u \<in> carrier L. u \<sqsubseteq>\<^bsub>L\<^esub> f u}"    \<comment> \<open>greatest fixed point\<close>


subsection \<open>Dual operators\<close>

lemma sup_dual [simp]: 
  "\<Squnion>\<^bsub>inv_gorder L\<^esub>A = \<Sqinter>\<^bsub>L\<^esub>A"
  by (simp add: sup_def inf_def)

lemma inf_dual [simp]: 
  "\<Sqinter>\<^bsub>inv_gorder L\<^esub>A = \<Squnion>\<^bsub>L\<^esub>A"
  by (simp add: sup_def inf_def)

lemma join_dual [simp]:
  "p \<squnion>\<^bsub>inv_gorder L\<^esub> q = p \<sqinter>\<^bsub>L\<^esub> q"
  by (simp add:join_def meet_def)

lemma meet_dual [simp]:
  "p \<sqinter>\<^bsub>inv_gorder L\<^esub> q = p \<squnion>\<^bsub>L\<^esub> q"
  by (simp add:join_def meet_def)

lemma top_dual [simp]:
  "\<top>\<^bsub>inv_gorder L\<^esub> = \<bottom>\<^bsub>L\<^esub>"
  by (simp add: top_def bottom_def)

lemma bottom_dual [simp]:
  "\<bottom>\<^bsub>inv_gorder L\<^esub> = \<top>\<^bsub>L\<^esub>"
  by (simp add: top_def bottom_def)

lemma LFP_dual [simp]:
  "LEAST_FP (inv_gorder L) f = GREATEST_FP L f"
  by (simp add:LEAST_FP_def GREATEST_FP_def)

lemma GFP_dual [simp]:
  "GREATEST_FP (inv_gorder L) f = LEAST_FP L f"
  by (simp add:LEAST_FP_def GREATEST_FP_def)


subsection \<open>Lattices\<close>

locale weak_upper_semilattice = weak_partial_order +
  assumes sup_of_two_exists:
    "[| x \<in> carrier L; y \<in> carrier L |] ==> \<exists>s. least L s (Upper L {x, y})"

locale weak_lower_semilattice = weak_partial_order +
  assumes inf_of_two_exists:
    "[| x \<in> carrier L; y \<in> carrier L |] ==> \<exists>s. greatest L s (Lower L {x, y})"

locale weak_lattice = weak_upper_semilattice + weak_lower_semilattice

lemma (in weak_lattice) dual_weak_lattice:
  "weak_lattice (inv_gorder L)"
proof -
  interpret dual: weak_partial_order "inv_gorder L"
    by (metis dual_weak_order)
  show ?thesis
  proof qed (simp_all add: inf_of_two_exists sup_of_two_exists)
qed


subsubsection \<open>Supremum\<close>

lemma (in weak_upper_semilattice) joinI:
  "[| !!l. least L l (Upper L {x, y}) ==> P l; x \<in> carrier L; y \<in> carrier L |]
  ==> P (x \<squnion> y)"
proof (unfold join_def sup_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
    and P: "!!l. least L l (Upper L {x, y}) ==> P l"
  with sup_of_two_exists obtain s where "least L s (Upper L {x, y})" by fast
  with L show "P (SOME l. least L l (Upper L {x, y}))"
    by (fast intro: someI2 P)
qed

lemma (in weak_upper_semilattice) join_closed [simp]:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<squnion> y \<in> carrier L"
  by (rule joinI) (rule least_closed)

lemma (in weak_upper_semilattice) join_cong_l:
  assumes carr: "x \<in> carrier L" "x' \<in> carrier L" "y \<in> carrier L"
    and xx': "x .= x'"
  shows "x \<squnion> y .= x' \<squnion> y"
proof (rule joinI, rule joinI)
  fix a b
  from xx' carr
      have seq: "{x, y} {.=} {x', y}" by (rule set_eq_pairI)

  assume leasta: "least L a (Upper L {x, y})"
  assume "least L b (Upper L {x', y})"
  with carr
      have leastb: "least L b (Upper L {x, y})"
      by (simp add: least_Upper_cong_r[OF _ _ seq])

  from leasta leastb
      show "a .= b" by (rule weak_least_unique)
qed (rule carr)+

lemma (in weak_upper_semilattice) join_cong_r:
  assumes carr: "x \<in> carrier L" "y \<in> carrier L" "y' \<in> carrier L"
    and yy': "y .= y'"
  shows "x \<squnion> y .= x \<squnion> y'"
proof (rule joinI, rule joinI)
  fix a b
  have "{x, y} = {y, x}" by fast
  also from carr yy'
      have "{y, x} {.=} {y', x}" by (intro set_eq_pairI)
  also have "{y', x} = {x, y'}" by fast
  finally
      have seq: "{x, y} {.=} {x, y'}" .

  assume leasta: "least L a (Upper L {x, y})"
  assume "least L b (Upper L {x, y'})"
  with carr
      have leastb: "least L b (Upper L {x, y})"
      by (simp add: least_Upper_cong_r[OF _ _ seq])

  from leasta leastb
      show "a .= b" by (rule weak_least_unique)
qed (rule carr)+

lemma (in weak_partial_order) sup_of_singletonI:      (* only reflexivity needed ? *)
  "x \<in> carrier L ==> least L x (Upper L {x})"
  by (rule least_UpperI) auto

lemma (in weak_partial_order) weak_sup_of_singleton [simp]:
  "x \<in> carrier L ==> \<Squnion>{x} .= x"
  unfolding sup_def
  by (rule someI2) (auto intro: weak_least_unique sup_of_singletonI)

lemma (in weak_partial_order) sup_of_singleton_closed [simp]:
  "x \<in> carrier L \<Longrightarrow> \<Squnion>{x} \<in> carrier L"
  unfolding sup_def
  by (rule someI2) (auto intro: sup_of_singletonI)

text \<open>Condition on \<open>A\<close>: supremum exists.\<close>

lemma (in weak_upper_semilattice) sup_insertI:
  "[| !!s. least L s (Upper L (insert x A)) ==> P s;
  least L a (Upper L A); x \<in> carrier L; A \<subseteq> carrier L |]
  ==> P (\<Squnion>(insert x A))"
proof (unfold sup_def)
  assume L: "x \<in> carrier L"  "A \<subseteq> carrier L"
    and P: "!!l. least L l (Upper L (insert x A)) ==> P l"
    and least_a: "least L a (Upper L A)"
  from L least_a have La: "a \<in> carrier L" by simp
  from L sup_of_two_exists least_a
  obtain s where least_s: "least L s (Upper L {a, x})" by blast
  show "P (SOME l. least L l (Upper L (insert x A)))"
  proof (rule someI2)
    show "least L s (Upper L (insert x A))"
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
          by (rule_tac le_trans [where y = a]) (auto dest: least_Upper_above)
      qed
    next
      fix y
      assume y: "y \<in> Upper L (insert x A)"
      show "s \<sqsubseteq> y"
      proof (rule least_le [OF least_s], rule Upper_memI)
        fix z
        assume z: "z \<in> {a, x}"
        then show "z \<sqsubseteq> y"
        proof
          have y': "y \<in> Upper L A"
            by (meson Upper_antimono in_mono subset_insertI y)
          assume "z = a"
          with y' least_a show ?thesis by (fast dest: least_le)
        next
          assume "z \<in> {x}"
          with y L show ?thesis by blast
        qed
      qed (rule Upper_closed [THEN subsetD, OF y])
    next
      from L show "insert x A \<subseteq> carrier L" by simp
      from least_s show "s \<in> carrier L" by simp
    qed
  qed (rule P)
qed

lemma (in weak_upper_semilattice) finite_sup_least:
  "[| finite A; A \<subseteq> carrier L; A \<noteq> {} |] ==> least L (\<Squnion>A) (Upper L A)"
proof (induct set: finite)
  case empty
  then show ?case by simp
next
  case (insert x A)
  show ?case
  proof (cases "A = {}")
    case True
    with insert show ?thesis
      by simp (simp add: least_cong [OF weak_sup_of_singleton] sup_of_singletonI)
        (* The above step is hairy; least_cong can make simp loop.
        Would want special version of simp to apply least_cong. *)
  next
    case False
    with insert have "least L (\<Squnion>A) (Upper L A)" by simp
    with _ show ?thesis
      by (rule sup_insertI) (simp_all add: insert [simplified])
  qed
qed

lemma (in weak_upper_semilattice) finite_sup_insertI:
  assumes P: "!!l. least L l (Upper L (insert x A)) ==> P l"
    and xA: "finite A"  "x \<in> carrier L"  "A \<subseteq> carrier L"
  shows "P (\<Squnion> (insert x A))"
proof (cases "A = {}")
  case True with P and xA show ?thesis
    by (simp add: finite_sup_least)
next
  case False with P and xA show ?thesis
    by (simp add: sup_insertI finite_sup_least)
qed

lemma (in weak_upper_semilattice) finite_sup_closed [simp]:
  "[| finite A; A \<subseteq> carrier L; A \<noteq> {} |] ==> \<Squnion>A \<in> carrier L"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case
    by - (rule finite_sup_insertI, simp_all)
qed

lemma (in weak_upper_semilattice) join_left:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> x \<squnion> y"
  by (rule joinI [folded join_def]) (blast dest: least_mem)

lemma (in weak_upper_semilattice) join_right:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> y \<sqsubseteq> x \<squnion> y"
  by (rule joinI [folded join_def]) (blast dest: least_mem)

lemma (in weak_upper_semilattice) sup_of_two_least:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> least L (\<Squnion>{x, y}) (Upper L {x, y})"
proof (unfold sup_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  with sup_of_two_exists obtain s where "least L s (Upper L {x, y})" by fast
  with L show "least L (SOME z. least L z (Upper L {x, y})) (Upper L {x, y})"
  by (fast intro: someI2 weak_least_unique)  (* blast fails *)
qed

lemma (in weak_upper_semilattice) join_le:
  assumes sub: "x \<sqsubseteq> z"  "y \<sqsubseteq> z"
    and x: "x \<in> carrier L" and y: "y \<in> carrier L" and z: "z \<in> carrier L"
  shows "x \<squnion> y \<sqsubseteq> z"
proof (rule joinI [OF _ x y])
  fix s
  assume "least L s (Upper L {x, y})"
  with sub z show "s \<sqsubseteq> z" by (fast elim: least_le intro: Upper_memI)
qed

lemma (in weak_lattice) weak_le_iff_meet:
  assumes "x \<in> carrier L" "y \<in> carrier L"
  shows "x \<sqsubseteq> y \<longleftrightarrow> (x \<squnion> y) .= y"
  by (meson assms(1) assms(2) join_closed join_le join_left join_right le_cong_r local.le_refl weak_le_antisym)
  
lemma (in weak_upper_semilattice) weak_join_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<squnion> (y \<squnion> z) .= \<Squnion>{x, y, z}"
proof (rule finite_sup_insertI)
  \<comment> \<open>The textbook argument in Jacobson I, p 457\<close>
  fix s
  assume sup: "least L s (Upper L {x, y, z})"
  show "x \<squnion> (y \<squnion> z) .= s"
  proof (rule weak_le_antisym)
    from sup L show "x \<squnion> (y \<squnion> z) \<sqsubseteq> s"
      by (fastforce intro!: join_le elim: least_Upper_above)
  next
    from sup L show "s \<sqsubseteq> x \<squnion> (y \<squnion> z)"
    by (erule_tac least_le)
      (blast intro!: Upper_memI intro: le_trans join_left join_right join_closed)
  qed (simp_all add: L least_closed [OF sup])
qed (simp_all add: L)

text \<open>Commutativity holds for \<open>=\<close>.\<close>

lemma join_comm:
  fixes L (structure)
  shows "x \<squnion> y = y \<squnion> x"
  by (unfold join_def) (simp add: insert_commute)

lemma (in weak_upper_semilattice) weak_join_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<squnion> y) \<squnion> z .= x \<squnion> (y \<squnion> z)"
proof -
  (* FIXME: could be simplified by improved simp: uniform use of .=,
     omit [symmetric] in last step. *)
  have "(x \<squnion> y) \<squnion> z = z \<squnion> (x \<squnion> y)" by (simp only: join_comm)
  also from L have "... .= \<Squnion>{z, x, y}" by (simp add: weak_join_assoc_lemma)
  also from L have "... = \<Squnion>{x, y, z}" by (simp add: insert_commute)
  also from L have "... .= x \<squnion> (y \<squnion> z)" by (simp add: weak_join_assoc_lemma [symmetric])
  finally show ?thesis by (simp add: L)
qed


subsubsection \<open>Infimum\<close>

lemma (in weak_lower_semilattice) meetI:
  "[| !!i. greatest L i (Lower L {x, y}) ==> P i;
  x \<in> carrier L; y \<in> carrier L |]
  ==> P (x \<sqinter> y)"
proof (unfold meet_def inf_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
    and P: "!!g. greatest L g (Lower L {x, y}) ==> P g"
  with inf_of_two_exists obtain i where "greatest L i (Lower L {x, y})" by fast
  with L show "P (SOME g. greatest L g (Lower L {x, y}))"
  by (fast intro: someI2 weak_greatest_unique P)
qed

lemma (in weak_lower_semilattice) meet_closed [simp]:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqinter> y \<in> carrier L"
  by (rule meetI) (rule greatest_closed)

lemma (in weak_lower_semilattice) meet_cong_l:
  assumes carr: "x \<in> carrier L" "x' \<in> carrier L" "y \<in> carrier L"
    and xx': "x .= x'"
  shows "x \<sqinter> y .= x' \<sqinter> y"
proof (rule meetI, rule meetI)
  fix a b
  from xx' carr
      have seq: "{x, y} {.=} {x', y}" by (rule set_eq_pairI)

  assume greatesta: "greatest L a (Lower L {x, y})"
  assume "greatest L b (Lower L {x', y})"
  with carr
      have greatestb: "greatest L b (Lower L {x, y})"
      by (simp add: greatest_Lower_cong_r[OF _ _ seq])

  from greatesta greatestb
      show "a .= b" by (rule weak_greatest_unique)
qed (rule carr)+

lemma (in weak_lower_semilattice) meet_cong_r:
  assumes carr: "x \<in> carrier L" "y \<in> carrier L" "y' \<in> carrier L"
    and yy': "y .= y'"
  shows "x \<sqinter> y .= x \<sqinter> y'"
proof (rule meetI, rule meetI)
  fix a b
  have "{x, y} = {y, x}" by fast
  also from carr yy'
      have "{y, x} {.=} {y', x}" by (intro set_eq_pairI)
  also have "{y', x} = {x, y'}" by fast
  finally
      have seq: "{x, y} {.=} {x, y'}" .

  assume greatesta: "greatest L a (Lower L {x, y})"
  assume "greatest L b (Lower L {x, y'})"
  with carr
      have greatestb: "greatest L b (Lower L {x, y})"
      by (simp add: greatest_Lower_cong_r[OF _ _ seq])

  from greatesta greatestb
      show "a .= b" by (rule weak_greatest_unique)
qed (rule carr)+

lemma (in weak_partial_order) inf_of_singletonI:      (* only reflexivity needed ? *)
  "x \<in> carrier L ==> greatest L x (Lower L {x})"
  by (rule greatest_LowerI) auto

lemma (in weak_partial_order) weak_inf_of_singleton [simp]:
  "x \<in> carrier L ==> \<Sqinter>{x} .= x"
  unfolding inf_def
  by (rule someI2) (auto intro: weak_greatest_unique inf_of_singletonI)

lemma (in weak_partial_order) inf_of_singleton_closed:
  "x \<in> carrier L ==> \<Sqinter>{x} \<in> carrier L"
  unfolding inf_def
  by (rule someI2) (auto intro: inf_of_singletonI)

text \<open>Condition on \<open>A\<close>: infimum exists.\<close>

lemma (in weak_lower_semilattice) inf_insertI:
  "[| !!i. greatest L i (Lower L (insert x A)) ==> P i;
  greatest L a (Lower L A); x \<in> carrier L; A \<subseteq> carrier L |]
  ==> P (\<Sqinter>(insert x A))"
proof (unfold inf_def)
  assume L: "x \<in> carrier L"  "A \<subseteq> carrier L"
    and P: "!!g. greatest L g (Lower L (insert x A)) ==> P g"
    and greatest_a: "greatest L a (Lower L A)"
  from L greatest_a have La: "a \<in> carrier L" by simp
  from L inf_of_two_exists greatest_a
  obtain i where greatest_i: "greatest L i (Lower L {a, x})" by blast
  show "P (SOME g. greatest L g (Lower L (insert x A)))"
  proof (rule someI2)
    show "greatest L i (Lower L (insert x A))"
    proof (rule greatest_LowerI)
      fix z
      assume "z \<in> insert x A"
      then show "i \<sqsubseteq> z"
      proof
        assume "z = x" then show ?thesis
          by (simp add: greatest_Lower_below [OF greatest_i] L La)
      next
        assume "z \<in> A"
        with L greatest_i greatest_a show ?thesis
          by (rule_tac le_trans [where y = a]) (auto dest: greatest_Lower_below)
      qed
    next
      fix y
      assume y: "y \<in> Lower L (insert x A)"
      show "y \<sqsubseteq> i"
      proof (rule greatest_le [OF greatest_i], rule Lower_memI)
        fix z
        assume z: "z \<in> {a, x}"
        then show "y \<sqsubseteq> z"
        proof
          have y': "y \<in> Lower L A"
            by (meson Lower_antimono in_mono subset_insertI y)
          assume "z = a"
          with y' greatest_a show ?thesis by (fast dest: greatest_le)
        next
          assume "z \<in> {x}"
          with y L show ?thesis by blast
        qed
      qed (rule Lower_closed [THEN subsetD, OF y])
    next
      from L show "insert x A \<subseteq> carrier L" by simp
      from greatest_i show "i \<in> carrier L" by simp
    qed
  qed (rule P)
qed

lemma (in weak_lower_semilattice) finite_inf_greatest:
  "[| finite A; A \<subseteq> carrier L; A \<noteq> {} |] ==> greatest L (\<Sqinter>A) (Lower L A)"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case (insert x A)
  show ?case
  proof (cases "A = {}")
    case True
    with insert show ?thesis
      by simp (simp add: greatest_cong [OF weak_inf_of_singleton]
        inf_of_singleton_closed inf_of_singletonI)
  next
    case False
    from insert show ?thesis
    proof (rule_tac inf_insertI)
      from False insert show "greatest L (\<Sqinter>A) (Lower L A)" by simp
    qed simp_all
  qed
qed

lemma (in weak_lower_semilattice) finite_inf_insertI:
  assumes P: "!!i. greatest L i (Lower L (insert x A)) ==> P i"
    and xA: "finite A"  "x \<in> carrier L"  "A \<subseteq> carrier L"
  shows "P (\<Sqinter> (insert x A))"
proof (cases "A = {}")
  case True with P and xA show ?thesis
    by (simp add: finite_inf_greatest)
next
  case False with P and xA show ?thesis
    by (simp add: inf_insertI finite_inf_greatest)
qed

lemma (in weak_lower_semilattice) finite_inf_closed [simp]:
  "[| finite A; A \<subseteq> carrier L; A \<noteq> {} |] ==> \<Sqinter>A \<in> carrier L"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case
    by (rule_tac finite_inf_insertI) (simp_all)
qed

lemma (in weak_lower_semilattice) meet_left:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqinter> y \<sqsubseteq> x"
  by (rule meetI [folded meet_def]) (blast dest: greatest_mem)

lemma (in weak_lower_semilattice) meet_right:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqinter> y \<sqsubseteq> y"
  by (rule meetI [folded meet_def]) (blast dest: greatest_mem)

lemma (in weak_lower_semilattice) inf_of_two_greatest:
  "[| x \<in> carrier L; y \<in> carrier L |] ==>
  greatest L (\<Sqinter>{x, y}) (Lower L {x, y})"
proof (unfold inf_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  with inf_of_two_exists obtain s where "greatest L s (Lower L {x, y})" by fast
  with L
  show "greatest L (SOME z. greatest L z (Lower L {x, y})) (Lower L {x, y})"
  by (fast intro: someI2 weak_greatest_unique)  (* blast fails *)
qed

lemma (in weak_lower_semilattice) meet_le:
  assumes sub: "z \<sqsubseteq> x"  "z \<sqsubseteq> y"
    and x: "x \<in> carrier L" and y: "y \<in> carrier L" and z: "z \<in> carrier L"
  shows "z \<sqsubseteq> x \<sqinter> y"
proof (rule meetI [OF _ x y])
  fix i
  assume "greatest L i (Lower L {x, y})"
  with sub z show "z \<sqsubseteq> i" by (fast elim: greatest_le intro: Lower_memI)
qed

lemma (in weak_lattice) weak_le_iff_join:
  assumes "x \<in> carrier L" "y \<in> carrier L"
  shows "x \<sqsubseteq> y \<longleftrightarrow> x .= (x \<sqinter> y)"
  by (meson assms(1) assms(2) local.le_refl local.le_trans meet_closed meet_le meet_left meet_right weak_le_antisym weak_refl)
  
lemma (in weak_lower_semilattice) weak_meet_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<sqinter> (y \<sqinter> z) .= \<Sqinter>{x, y, z}"
proof (rule finite_inf_insertI)
  txt \<open>The textbook argument in Jacobson I, p 457\<close>
  fix i
  assume inf: "greatest L i (Lower L {x, y, z})"
  show "x \<sqinter> (y \<sqinter> z) .= i"
  proof (rule weak_le_antisym)
    from inf L show "i \<sqsubseteq> x \<sqinter> (y \<sqinter> z)"
      by (fastforce intro!: meet_le elim: greatest_Lower_below)
  next
    from inf L show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> i"
    by (erule_tac greatest_le)
      (blast intro!: Lower_memI intro: le_trans meet_left meet_right meet_closed)
  qed (simp_all add: L greatest_closed [OF inf])
qed (simp_all add: L)

lemma meet_comm:
  fixes L (structure)
  shows "x \<sqinter> y = y \<sqinter> x"
  by (unfold meet_def) (simp add: insert_commute)

lemma (in weak_lower_semilattice) weak_meet_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<sqinter> y) \<sqinter> z .= x \<sqinter> (y \<sqinter> z)"
proof -
  (* FIXME: improved simp, see weak_join_assoc above *)
  have "(x \<sqinter> y) \<sqinter> z = z \<sqinter> (x \<sqinter> y)" by (simp only: meet_comm)
  also from L have "... .= \<Sqinter> {z, x, y}" by (simp add: weak_meet_assoc_lemma)
  also from L have "... = \<Sqinter> {x, y, z}" by (simp add: insert_commute)
  also from L have "... .= x \<sqinter> (y \<sqinter> z)" by (simp add: weak_meet_assoc_lemma [symmetric])
  finally show ?thesis by (simp add: L)
qed

text \<open>Total orders are lattices.\<close>

sublocale weak_total_order \<subseteq> weak?: weak_lattice
proof
  fix x y
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  show "\<exists>s. least L s (Upper L {x, y})"
  proof -
    note total L
    moreover
    {
      assume "x \<sqsubseteq> y"
      with L have "least L y (Upper L {x, y})"
        by (rule_tac least_UpperI) auto
    }
    moreover
    {
      assume "y \<sqsubseteq> x"
      with L have "least L x (Upper L {x, y})"
        by (rule_tac least_UpperI) auto
    }
    ultimately show ?thesis by blast
  qed
next
  fix x y
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  show "\<exists>i. greatest L i (Lower L {x, y})"
  proof -
    note total L
    moreover
    {
      assume "y \<sqsubseteq> x"
      with L have "greatest L y (Lower L {x, y})"
        by (rule_tac greatest_LowerI) auto
    }
    moreover
    {
      assume "x \<sqsubseteq> y"
      with L have "greatest L x (Lower L {x, y})"
        by (rule_tac greatest_LowerI) auto
    }
    ultimately show ?thesis by blast
  qed
qed


subsection \<open>Weak Bounded Lattices\<close>

locale weak_bounded_lattice = 
  weak_lattice + 
  weak_partial_order_bottom + 
  weak_partial_order_top
begin

lemma bottom_meet: "x \<in> carrier L \<Longrightarrow> \<bottom> \<sqinter> x .= \<bottom>"
  by (metis bottom_least least_def meet_closed meet_left weak_le_antisym)

lemma bottom_join: "x \<in> carrier L \<Longrightarrow> \<bottom> \<squnion> x .= x"
  by (metis bottom_least join_closed join_le join_right le_refl least_def weak_le_antisym)

lemma bottom_weak_eq:
  "\<lbrakk> b \<in> carrier L; \<And> x. x \<in> carrier L \<Longrightarrow> b \<sqsubseteq> x \<rbrakk> \<Longrightarrow> b .= \<bottom>"
  by (metis bottom_closed bottom_lower weak_le_antisym)

lemma top_join: "x \<in> carrier L \<Longrightarrow> \<top> \<squnion> x .= \<top>"
  by (metis join_closed join_left top_closed top_higher weak_le_antisym)

lemma top_meet: "x \<in> carrier L \<Longrightarrow> \<top> \<sqinter> x .= x"
  by (metis le_refl meet_closed meet_le meet_right top_closed top_higher weak_le_antisym)

lemma top_weak_eq:  "\<lbrakk> t \<in> carrier L; \<And> x. x \<in> carrier L \<Longrightarrow> x \<sqsubseteq> t \<rbrakk> \<Longrightarrow> t .= \<top>"
  by (metis top_closed top_higher weak_le_antisym)

end

sublocale weak_bounded_lattice \<subseteq> weak_partial_order ..


subsection \<open>Lattices where \<open>eq\<close> is the Equality\<close>

locale upper_semilattice = partial_order +
  assumes sup_of_two_exists:
    "[| x \<in> carrier L; y \<in> carrier L |] ==> \<exists>s. least L s (Upper L {x, y})"

sublocale upper_semilattice \<subseteq> weak?: weak_upper_semilattice
  by unfold_locales (rule sup_of_two_exists)

locale lower_semilattice = partial_order +
  assumes inf_of_two_exists:
    "[| x \<in> carrier L; y \<in> carrier L |] ==> \<exists>s. greatest L s (Lower L {x, y})"

sublocale lower_semilattice \<subseteq> weak?: weak_lower_semilattice
  by unfold_locales (rule inf_of_two_exists)

locale lattice = upper_semilattice + lower_semilattice

sublocale lattice \<subseteq> weak_lattice ..

lemma (in lattice) dual_lattice:
  "lattice (inv_gorder L)"
proof -
  interpret dual: weak_lattice "inv_gorder L"
    by (metis dual_weak_lattice)

  show ?thesis
    apply (unfold_locales)
    apply (simp_all add: inf_of_two_exists sup_of_two_exists)
    apply (rule eq_is_equal)
  done
qed
  
lemma (in lattice) le_iff_join:
  assumes "x \<in> carrier L" "y \<in> carrier L"
  shows "x \<sqsubseteq> y \<longleftrightarrow> x = (x \<sqinter> y)"
  by (simp add: assms(1) assms(2) eq_is_equal weak_le_iff_join)

lemma (in lattice) le_iff_meet:
  assumes "x \<in> carrier L" "y \<in> carrier L"
  shows "x \<sqsubseteq> y \<longleftrightarrow> (x \<squnion> y) = y"
  by (simp add: assms eq_is_equal weak_le_iff_meet)

text \<open> Total orders are lattices. \<close>

sublocale total_order \<subseteq> weak?: lattice
  by standard (auto intro: weak.weak.sup_of_two_exists weak.weak.inf_of_two_exists)
    
text \<open>Functions that preserve joins and meets\<close>
  
definition join_pres :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
"join_pres X Y f \<equiv> lattice X \<and> lattice Y \<and> (\<forall> x \<in> carrier X. \<forall> y \<in> carrier X. f (x \<squnion>\<^bsub>X\<^esub> y) = f x \<squnion>\<^bsub>Y\<^esub> f y)"

definition meet_pres :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
"meet_pres X Y f \<equiv> lattice X \<and> lattice Y \<and> (\<forall> x \<in> carrier X. \<forall> y \<in> carrier X. f (x \<sqinter>\<^bsub>X\<^esub> y) = f x \<sqinter>\<^bsub>Y\<^esub> f y)"

lemma join_pres_isotone:
  assumes "f \<in> carrier X \<rightarrow> carrier Y" "join_pres X Y f"
  shows "isotone X Y f"
proof (rule isotoneI)
  show "weak_partial_order X" "weak_partial_order Y"
    using assms unfolding join_pres_def lattice_def upper_semilattice_def lower_semilattice_def
    by (meson partial_order.axioms(1))+
  show "\<And>x y. \<lbrakk>x \<in> carrier X; y \<in> carrier X; x \<sqsubseteq>\<^bsub>X\<^esub> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^bsub>Y\<^esub> f y"
    by (metis (no_types, lifting) PiE assms join_pres_def lattice.le_iff_meet)
qed

lemma meet_pres_isotone:
  assumes "f \<in> carrier X \<rightarrow> carrier Y" "meet_pres X Y f"
  shows "isotone X Y f"
proof (rule isotoneI)
  show "weak_partial_order X" "weak_partial_order Y"
    using assms unfolding meet_pres_def lattice_def upper_semilattice_def lower_semilattice_def
    by (meson partial_order.axioms(1))+
  show "\<And>x y. \<lbrakk>x \<in> carrier X; y \<in> carrier X; x \<sqsubseteq>\<^bsub>X\<^esub> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^bsub>Y\<^esub> f y"
    by (metis (no_types, lifting) PiE assms lattice.le_iff_join meet_pres_def)
qed


subsection \<open>Bounded Lattices\<close>

locale bounded_lattice = 
  lattice + 
  weak_partial_order_bottom + 
  weak_partial_order_top

sublocale bounded_lattice \<subseteq> weak_bounded_lattice ..

context bounded_lattice
begin

lemma bottom_eq:  
  "\<lbrakk> b \<in> carrier L; \<And> x. x \<in> carrier L \<Longrightarrow> b \<sqsubseteq> x \<rbrakk> \<Longrightarrow> b = \<bottom>"
  by (metis bottom_closed bottom_lower le_antisym)

lemma top_eq:  "\<lbrakk> t \<in> carrier L; \<And> x. x \<in> carrier L \<Longrightarrow> x \<sqsubseteq> t \<rbrakk> \<Longrightarrow> t = \<top>"
  by (metis le_antisym top_closed top_higher)

end

hide_const (open) Lattice.inf
hide_const (open) Lattice.sup

end
