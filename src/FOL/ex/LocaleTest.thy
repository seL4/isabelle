(*  Title:      FOL/ex/LocaleTest.thy
    ID:         $Id$
    Author:     Clemens Ballarin
    Copyright (c) 2005 by Clemens Ballarin

Collection of regression tests for locales.
*)

header {* Test of Locale instantiation *}

theory LocaleTest = FOL:

(* interpretation input syntax *)

locale L
locale M = fixes a and b and c

interpretation test [simp]: L + M a b c [x y z] .

print_interps L
print_interps M

interpretation test [simp]: L print_interps M .

interpretation L .

(* processing of locale expression *)

ML {* reset show_hyps *}

locale A = fixes a assumes asm_A: "a = a"

locale (open) B = fixes b assumes asm_B [simp]: "b = b"

locale C = A + B + assumes asm_C: "c = c"
  (* TODO: independent type var in c, prohibit locale declaration *)

locale D = A + B + fixes d defines def_D: "d == (a = b)"

ML {* set show_sorts *}

typedecl i
arities i :: "term"

ML {* set Toplevel.debug *}

ML {* set show_hyps *}

interpretation p1: C ["X::'b" "Y::'b"] by (auto intro: A.intro C_axioms.intro)
  (* both X and Y get type 'b since 'b is the internal type of parameter b,
     not wanted, but put up with for now. *)

print_interps A

(* possible accesses
thm p1.a.asm_A thm LocaleTest.p1.a.asm_A
thm LocaleTest.asm_A thm p1.asm_A
*)

(* without prefix *)

interpretation C ["W::'b" "Z::'b"] by (auto intro: A.intro C_axioms.intro)

print_interps A

(* possible accesses
thm a.asm_A thm asm_A thm LocaleTest.a.asm_A thm LocaleTest.asm_A
*)

interpretation p2: D [X Y "Y = X"] by (auto intro: A.intro simp: eq_commute)

print_interps D

(*
thm p2.a.asm_A
*)

interpretation p3: D [X Y] .

(* duplicate: not registered *)
(*
thm p3.a.asm_A
*)

print_interps A
print_interps B
print_interps C
print_interps D

(* not permitted *)
(*
interpretation p4: A ["x::?'a1"] apply (rule A.intro) apply rule done
*)
print_interps A

(* without a prefix *)
(* TODO!!!
interpretation A [Z] apply - apply (auto intro: A.intro) done
*)

theorem True
proof -
  fix alpha::i and beta::i and gamma::i
  assume "A(alpha)"
  then interpret p5: A [alpha] .
  print_interps A
  interpret p6: C [alpha beta] by (auto intro: C_axioms.intro)
  print_interps A   (* p6 not added! *)
  print_interps C
qed rule

(* lemma "bla.bla": True by rule *)


end
