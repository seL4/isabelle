(*  Title:      FOL/ex/LocaleInst.thy
    ID:         $Id$
    Author:     Clemens Ballarin
    Copyright (c) 2004 by Clemens Ballarin

Test of locale instantiation mechanism, also provides a few examples.
*)

header {* Test of Locale instantiation *}

theory LocaleInst = FOL:

ML {* set show_hyps *}

subsection {* Locale without assumptions *}

locale L1 = notes rev_conjI [intro] = conjI [THEN iffD1 [OF conj_commute]]

lemma "[| A; B |] ==> A & B"
proof -
  instantiate my: L1           txt {* No chained fact required. *}
  assume B and A               txt {* order reversed *}
  then show "A & B" ..         txt {* Applies @{thm my.rev_conjI}. *}
qed

locale L11 = notes rev_conjI = conjI [THEN iffD1 [OF conj_commute]]

lemma "[| A; B |] ==> A & B"
proof -
  instantiate [intro]: L11     txt {* Attribute supplied at instantiation. *}
  assume B and A
  then show "A & B" ..
qed

subsection {* Simple locale with assumptions *}

typedecl i
arities  i :: "term"

consts bin :: "[i, i] => i" (infixl "#" 60)

axioms i_assoc: "(x # y) # z = x # (y # z)"
  i_comm: "x # y = y # x"

locale L2 =
  fixes OP (infixl "+" 60)
  assumes assoc: "(x + y) + z = x + (y + z)"
    and comm: "x + y = y + x"

lemma (in L2) lcomm: "x + (y + z) = y + (x + z)"
proof -
  have "x + (y + z) = (x + y) + z" by (simp add: assoc)
  also have "... = (y + x) + z" by (simp add: comm)
  also have "... = y + (x + z)" by (simp add: assoc)
  finally show ?thesis .
qed

lemmas (in L2) AC = comm assoc lcomm

lemma "(x::i) # y # z # w = y # x # w # z"
proof -
  have "L2 (op #)" by (rule L2.intro [of "op #", OF i_assoc i_comm])
  then instantiate my: L2
    txt {* Chained fact required to discharge assumptions of @{text L2}
      and instantiate parameters. *}
  show ?thesis by (simp only: my.OP.AC)  (* or simply AC *)
qed

subsection {* Nested locale with assumptions *}

locale L3 =
  fixes OP (infixl "+" 60)
  assumes assoc: "(x + y) + z = x + (y + z)"

locale L4 = L3 +
  assumes comm: "x + y = y + x"

lemma (in L4) lcomm: "x + (y + z) = y + (x + z)"
proof -
  have "x + (y + z) = (x + y) + z" by (simp add: assoc)
  also have "... = (y + x) + z" by (simp add: comm)
  also have "... = y + (x + z)" by (simp add: assoc)
  finally show ?thesis .
qed

lemmas (in L4) AC = comm assoc lcomm

text {* Conceptually difficult locale:
   2nd context fragment contains facts with differing metahyps. *}

lemma L4_intro:
  fixes OP (infixl "+" 60)
  assumes assoc: "!!x y z. (x + y) + z = x + (y + z)"
    and comm: "!!x y. x + y = y + x"
  shows "L4 (op+)"
    by (blast intro: L4.intro L3.intro assoc L4_axioms.intro comm)

lemma "(x::i) # y # z # w = y # x # w # z"
proof -
  have "L4 (op #)" by (rule L4_intro [of "op #", OF i_assoc i_comm])
  then instantiate my: L4
  show ?thesis by (simp only: my.OP.AC)  (* or simply AC *)
qed

subsection {* Locale with definition *}

text {* This example is admittedly not very creative :-) *}

locale L5 = L4 + var A +
  defines A_def: "A == True"

lemma (in L5) lem: A
  by (unfold A_def) rule

lemma "L5(op #) ==> True"
proof -
  assume "L5(op #)"
  then instantiate my: L5
  show ?thesis by (rule lem)  (* lem instantiated to True *)
qed

subsection {* Instantiation in a context with target *}

lemma (in L4)  (* Target might confuse instantiation command. *)
  fixes A (infixl "$" 60)
  assumes A: "L4(A)"
  shows "(x::i) $ y $ z $ w = y $ x $ w $ z"
proof -
  from A instantiate A: L4
  show ?thesis by (simp only: A.OP.AC)
qed

end
