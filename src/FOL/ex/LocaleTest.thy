(*  Title:      FOL/ex/LocaleTest.thy
    ID:         $Id$
    Author:     Clemens Ballarin
    Copyright (c) 2005 by Clemens Ballarin

Collection of regression tests for locales.
*)

header {* Test of Locale Interpretation *}

theory LocaleTest
imports FOL
begin

ML {* set quick_and_dirty *}    (* allow for thm command in batch mode *)
ML {* set Toplevel.debug *}
ML {* set show_hyps *}
ML {* set show_sorts *}

section {* Renaming with Syntax *}


locale (open) S = var mult +
  assumes "mult(x, y) = mult(y, x)"
(* Making this declaration (open) reveals a problem when mixing open and
   closed locales. *)

print_locale S

locale (open) S' = S mult (infixl "**" 60)

print_locale S'

locale T = var mult (infixl "**" 60) +
  assumes "x ** y = y ** x"

locale U = T mult (infixl "**" 60) + T add (infixl "++" 55) + var h +
  assumes hom: "h(x ** y) = h(x) ++ h(y)"

locale V = U _ add


section {* Constrains *}

locale Z = fixes a (structure)
locale Z' = Z +
  constrains a :: "'a => 'b"
  assumes "a (x :: 'a) = a (y)"
print_locale Z'


section {* Interpretation *}

(* interpretation input syntax *)

locale L
locale M = fixes a and b and c

interpretation test [simp]: L + M a b c [x y z] .

print_interps L    (* output: test *)
print_interps M    (* output: test *)

interpretation test [simp]: L print_interps M .

interpretation L .

(* processing of locale expression *)

locale A = fixes a assumes asm_A: "a = a"

locale (open) B = fixes b assumes asm_B [simp]: "b = b"

locale C = A + B + assumes asm_C: "c = c"
  (* TODO: independent type var in c, prohibit locale declaration *)

locale D = A + B + fixes d defines def_D: "d == (a = b)"

theorem (in A)
  includes D
  shows True ..

theorem (in D) True ..

typedecl i
arities i :: "term"


interpretation p1: C ["X::i" "Y::i"] by (auto intro: A.intro C_axioms.intro)

print_interps A  (* output: p1 *)

(* possible accesses *)
thm p1.a.asm_A thm LocaleTest.p1.a.asm_A
thm p1.asm_A thm LocaleTest.p1.asm_A


(* without prefix *)

interpretation C ["W::i" "Z::i"] .  (* subsumed by p1: C *)
interpretation C ["W::'a" "Z::i"] by (auto intro: A.intro C_axioms.intro)
  (* subsumes p1: A and p1: C *)


print_interps A  (* output: <no prefix>, p1 *)

(* possible accesses *)
thm asm_C thm a_b.asm_C thm LocaleTest.a_b.asm_C thm LocaleTest.a_b.asm_C


interpretation p2: D [X "Y::i" "Y = X"] by (simp add: eq_commute)

print_interps A  (* output: <no prefix>, p1 *)
print_interps D  (* output: p2 *)


interpretation p3: D [X "Y::i"] .

(* duplicate: not registered *)

(* thm p3.a.asm_A *)


print_interps A  (* output: <no prefix>, p1 *)
print_interps B  (* output: p1 *)
print_interps C  (* output: <no name>, p1 *)
print_interps D  (* output: p2, p3 *)

(* schematic vars in instantiation not permitted *)
(*
interpretation p4: A ["?x::?'a1"] apply (rule A.intro) apply rule done
print_interps A
*)

interpretation p10: D + D a' b' d' [X "Y::i" _ u "v::i" _] .

corollary (in D) th_x: True ..

(* possible accesses: for each registration *)

thm p2.th_x thm p3.th_x

lemma (in D) th_y: "d == (a = b)" .

thm p2.th_y thm p3.th_y

lemmas (in D) th_z = th_y

thm p2.th_z

section {* Interpretation in proof contexts *}

locale F = fixes f assumes asm_F: "f & f --> f"

theorem True
proof -
  fix alpha::i and beta::'a and gamma::o
  (* FIXME: omitting type of beta leads to error later at interpret p6 *)
  have alpha_A: "A(alpha)" by (auto intro: A.intro)
  interpret p5: A [alpha] .  (* subsumed *)
  print_interps A  (* output: <no prefix>, p1 *)
  interpret p6: C [alpha beta] by (auto intro: C_axioms.intro)
  print_interps A   (* output: <no prefix>, p1 *)
  print_interps C   (* output: <no prefix>, p1, p6 *)
  interpret p11: F [gamma] by (fast intro: F.intro)
  thm p11.asm_F      (* gamma is a Free *)
qed rule

theorem (in A) True
proof -
  print_interps A
  fix beta and gamma
  interpret p9: D [a beta _]
    (* no proof obligation for A !!! *)
    apply - apply (rule refl) apply assumption done
qed rule


(* Definition involving free variable *)

ML {* reset show_sorts *}

locale E = fixes e defines e_def: "e(x) == x & x"
  notes e_def2 = e_def

lemma (in E) True thm e_def by fast

interpretation p7: E ["(%x. x)"] by simp

(* TODO: goal mustn't be beta-reduced here, is doesn't match meta-hyp *)

thm p7.e_def2

locale E' = fixes e defines e_def: "e == (%x. x & x)"
  notes e_def2 = e_def

interpretation p7': E' ["(%x. x)"] by simp

thm p7'.e_def2

(* Definition involving free variable in assm *)

locale (open) G = fixes g assumes asm_G: "g --> x"
  notes asm_G2 = asm_G

interpretation p8: G ["False"] by fast

thm p8.asm_G2

subsection {* Locale without assumptions *}

locale L1 = notes rev_conjI [intro] = conjI [THEN iffD1 [OF conj_commute]]

lemma "[| P; Q |] ==> P & Q"
proof -
  interpret my: L1 .           txt {* No chained fact required. *}
  assume Q and P               txt {* order reversed *}
  then show "P & Q" ..         txt {* Applies @{thm my.rev_conjI}. *}
qed

locale L11 = notes rev_conjI = conjI [THEN iffD1 [OF conj_commute]]

lemma "[| P; Q |] ==> P & Q"
proof -
  interpret [intro]: L11 .     txt {* Attribute supplied at instantiation. *}
  assume Q and P
  then show "P & Q" ..
qed

subsection {* Simple locale with assumptions *}

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
  interpret my: L2 ["op #"] by (rule L2.intro [of "op #", OF i_assoc i_comm])
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

lemma "(x::i) # y # z # w = y # x # w # z"
proof -
  interpret my: L4 ["op #"]
    by (auto intro: L3.intro L4_axioms.intro i_assoc i_comm)
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
  then interpret L5 ["op #"] by (auto intro: L5.axioms)
  show ?thesis by (rule lem)  (* lem instantiated to True *)
qed

subsection {* Instantiation in a context with target *}

lemma (in L4)
  fixes A (infixl "$" 60)
  assumes A: "L4(A)"
  shows "(x::i) $ y $ z $ w = y $ x $ w $ z"
proof -
  from A interpret A: L4 ["A"] by (auto intro: L4.axioms)
  show ?thesis by (simp only: A.OP.AC)
qed

end
