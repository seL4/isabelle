(*  Title:      HOL/Isar_examples/MutilatedCheckerboard.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory (original script)
                Markus Wenzel, TU Muenchen (Isar document)

The Mutilated Chess Board Problem, formalized inductively.
  Originator is Max Black, according to J A Robinson.
  Popularized as the Mutilated Checkerboard Problem by J McCarthy.
*)

theory MutilatedCheckerboard = Main:;


section {* Tilings *};

consts
  tiling :: "'a set set => 'a set set";

inductive "tiling A"
  intrs
    empty: "{} : tiling A"
    Un:    "[| a : A;  t : tiling A;  a <= - t |] ==> a Un t : tiling A";


text "The union of two disjoint tilings is a tiling";

lemma tiling_Un: "t : tiling A --> u : tiling A --> t Int u = {} --> t Un u : tiling A";
proof;
  assume "t : tiling A" (is "_ : ??T");
  thus "u : ??T --> t Int u = {} --> t Un u : ??T" (is "??P t");
  proof (induct t set: tiling);
    show "??P {}"; by simp;

    fix a t;
    assume "a:A" "t : ??T" "??P t" "a <= - t";
    show "??P (a Un t)";
    proof (intro impI);
      assume "u : ??T" "(a Un t) Int u = {}";
      have hyp: "t Un u: ??T"; by blast;
      have "a <= - (t Un u)"; by blast;
      with _ hyp; have "a Un (t Un u) : ??T"; by (rule tiling.Un);
      also; have "a Un (t Un u) = (a Un t) Un u"; by (simp only: Un_assoc);
      finally; show "... : ??T"; .;
    qed;
  qed;
qed;

lemma tiling_UnI: "[| t : tiling A; u : tiling A; t Int u = {} |] ==> t Un u : tiling A";
  by (rule tiling_Un [rulify]);
  

section {* Basic properties of below *};

constdefs
  below :: "nat => nat set"
  "below n == {i. i < n}";

lemma below_less_iff [iff]: "(i: below k) = (i < k)";
  by (simp add: below_def);

lemma below_0 [simp]: "below 0 = {}";
  by (simp add: below_def);

lemma Sigma_Suc1: "below (Suc n) Times B = ({n} Times B) Un (below n Times B)";
  by (simp add: below_def less_Suc_eq) blast;

lemma Sigma_Suc2: "A Times below (Suc n) = (A Times {n}) Un (A Times (below n))";
  by (simp add: below_def less_Suc_eq) blast;

lemmas Sigma_Suc = Sigma_Suc1 Sigma_Suc2;


section {* Basic properties of evnodd *};

constdefs
  evnodd :: "[(nat * nat) set, nat] => (nat * nat) set"
  "evnodd A b == A Int {(i, j). (i + j) mod 2 = b}";

lemma evnodd_iff: "(i, j): evnodd A b = ((i, j): A  & (i + j) mod 2 = b)";
  by (simp add: evnodd_def);

lemma evnodd_subset: "evnodd A b <= A";
proof (unfold evnodd_def);
  show "!!B. A Int B <= A"; by (rule Int_lower1);
qed;

lemma evnoddD: "x : evnodd A b ==> x : A";
  by (rule subsetD, rule evnodd_subset);

lemma evnodd_finite [simp]: "finite A ==> finite (evnodd A b)";
  by (rule finite_subset, rule evnodd_subset);

lemma evnodd_Un [simp]: "evnodd (A Un B) b = evnodd A b Un evnodd B b";
  by (unfold evnodd_def) blast;

lemma evnodd_Diff [simp]: "evnodd (A - B) b = evnodd A b - evnodd B b";
  by (unfold evnodd_def) blast;

lemma evnodd_empty [simp]: "evnodd {} b = {}";
  by (simp add: evnodd_def);

lemma evnodd_insert [simp]: "evnodd (insert (i, j) C) b =
  (if (i + j) mod 2 = b then insert (i, j) (evnodd C b) else evnodd C b)";
  by (simp add: evnodd_def) blast;


section {* Dominoes *};

consts 
  domino  :: "(nat * nat) set set";

inductive domino
  intrs
    horiz:  "{(i, j), (i, Suc j)} : domino"
    vertl:  "{(i, j), (Suc i, j)} : domino";


lemma dominoes_tile_row: "{i} Times below (n + n) : tiling domino"
  (is "??P n" is "??B n : ??T");
proof (induct n);
  have "??B 0 = {}"; by simp;
  also; have "... : ??T"; by (rule tiling.empty);
  finally; show "??P 0"; .;

  fix n; assume hyp: "??P n";
  let ??a = "{i} Times {Suc (n + n)} Un {i} Times {n + n}";

  have "??B (Suc n) = ??a Un ??B n"; by (simp add: Sigma_Suc Un_assoc);
  also; have "... : ??T";
  proof (rule tiling.Un);
    have "{(i, n + n), (i, Suc (n + n))} : domino"; by (rule domino.horiz);
    also; have "{(i, n + n), (i, Suc (n + n))} = ??a"; by blast;
    finally; show "??a : domino"; .;
    show "??B n : ??T"; by (rule hyp);
    show "??a <= - ??B n"; by force;
  qed;
  finally; show "??P (Suc n)"; .;
qed;

lemma dominoes_tile_matrix: "below m Times below (n + n) : tiling domino"
  (is "??P m" is "??B m : ??T");
proof (induct m);
  show "??P 0"; by (simp add: tiling.empty) -- {* same as above *};

  fix m; assume hyp: "??P m";
  let ??t = "{m} Times below (n + n)";

  have "??B (Suc m) = ??t Un ??B m"; by (simp add: Sigma_Suc);
  also; have "... : ??T";
  proof (rule tiling_UnI);
    show "??t : ??T"; by (rule dominoes_tile_row);
    show "??B m : ??T"; by (rule hyp);
    show "??t Int ??B m = {}"; by blast;
  qed;
  finally; show "??P (Suc m)"; .;
qed;


lemma domino_singleton: "[| d : domino; b < 2 |] ==> EX i j. evnodd d b = {(i, j)}";
proof -;
  assume "b < 2";
  assume "d : domino";
  thus ??thesis (is "??P d");
  proof (induct d set: domino);
    fix i j;
    have b_cases: "b = 0 | b = 1"; by arith;
    note [simp] = less_Suc_eq mod_Suc;
    from b_cases; show "??P {(i, j), (i, Suc j)}"; by rule auto;
    from b_cases; show "??P {(i, j), (Suc i, j)}"; by rule auto;
  qed;
qed;

lemma domino_finite: "d: domino ==> finite d";
proof (induct set: domino);
  fix i j;
  show "finite {(i, j), (i, Suc j)}"; by (intro Finites.intrs);
  show "finite {(i, j), (Suc i, j)}"; by (intro Finites.intrs);
qed;


section {* Tilings of dominoes *};

lemma tiling_domino_finite: "t : tiling domino ==> finite t" (is "t : ??T ==> ??F t");
proof -;
  assume "t : ??T";
  thus "??F t";
  proof (induct set: tiling);
    show "??F {}"; by (rule Finites.emptyI);
    fix a t; assume "??F t";
    assume "a : domino"; hence "??F a"; by (rule domino_finite);
    thus "??F (a Un t)"; by (rule finite_UnI);
  qed;
qed;

lemma tiling_domino_01: "t : tiling domino ==> card (evnodd t 0) = card (evnodd t 1)"
  (is "t : ??T ==> ??P t");
proof -;
  assume "t : ??T";
  thus "??P t";
  proof (induct set: tiling);
    show "??P {}"; by (simp add: evnodd_def);

    fix a t;
    let ??e = evnodd;
    assume "a : domino" "t : ??T"
      and hyp: "card (??e t 0) = card (??e t 1)"
      and "a <= - t";

    have card_suc: "!!b. b < 2 ==> card (??e (a Un t) b) = Suc (card (??e t b))";
    proof -;
      fix b; assume "b < 2";
      have "EX i j. ??e a b = {(i, j)}"; by (rule domino_singleton);
      thus "??thesis b";
      proof (elim exE);
	have "??e (a Un t) b = ??e a b Un ??e t b"; by (rule evnodd_Un);
	also; fix i j; assume "??e a b = {(i, j)}";
	also; have "... Un ??e t b = insert (i, j) (??e t b)"; by simp;
	finally; have "card (??e (a Un t) b) = card (insert (i, j) (??e t b))"; by simp;
	also; have "... = Suc (card (??e t b))";
	proof (rule card_insert_disjoint);
	  show "finite (??e t b)"; by (rule evnodd_finite, rule tiling_domino_finite);
	  have "(i, j) : ??e a b"; by asm_simp;
	  thus "(i, j) ~: ??e t b"; by (force dest: evnoddD);
	qed;
	finally; show ??thesis; .;
      qed;
    qed;
    hence "card (??e (a Un t) 0) = Suc (card (??e t 0))"; by simp;
    also; have "card (??e t 0) = card (??e t 1)"; by (rule hyp);
    also; from card_suc; have "Suc ... = card (??e (a Un t) 1)"; by simp;
    finally; show "??P (a Un t)"; .;
  qed;
qed;


section {* Main theorem *};

constdefs
  mutilated_board :: "nat => nat => (nat * nat) set"
  "mutilated_board m n == below (Suc m + Suc m) Times below (Suc n + Suc n)
    - {(0, 0)} - {(Suc (m + m), Suc (n + n))}";

theorem mutil_not_tiling: "mutilated_board m n ~: tiling domino" (is "_ ~: ??T");
proof (unfold mutilated_board_def);
  let ??t = "below (Suc m + Suc m) Times below (Suc n + Suc n)";
  let ??t' = "??t - {(0, 0)}";
  let ??t'' = "??t' - {(Suc (m + m), Suc (n + n))}";
  show "??t'' ~: ??T";
  proof;
    let ??e = evnodd;
    note [simp] = evnodd_iff;
    assume t'': "??t'' : ??T";

    have t: "??t : ??T"; by (rule dominoes_tile_matrix);
    have fin: "finite (??e ??t 0)"; by (rule evnodd_finite, rule tiling_domino_finite, rule t);

    have "card (??e ??t'' 0) < card (??e ??t' 0)";
    proof -;
      have "card (??e ??t' 0 - {(Suc (m + m), Suc (n + n))}) < card (??e ??t' 0)";
      proof (rule card_Diff1_less);
	show "finite (??e ??t' 0)"; by (rule finite_subset, rule fin) force;
	show "(Suc (m + m), Suc (n + n)) : ??e ??t' 0"; by simp;
      qed;
      thus ??thesis; by simp;
    qed;
    also; have "... < card (??e ??t 0)";
    proof -;
      have "(0, 0) : ??e ??t 0"; by simp;
      with fin; have "card (??e ??t 0 - {(0, 0)}) < card (??e ??t 0)"; by (rule card_Diff1_less);
      thus ??thesis; by simp;
    qed;
    also; from t; have "... = card (??e ??t 1)"; by (rule tiling_domino_01);
    also; have "??e ??t 1 = ??e ??t'' 1"; by simp;
    also; have "card ... = card (??e ??t'' 0)"; by (rule sym, rule tiling_domino_01);
    finally; show False; ..;
  qed;
qed;


end;