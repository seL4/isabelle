(*  Title:      HOL/HOL.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  University of Cambridge

Higher-Order Logic.
*)

theory HOL = CPure
files ("HOL_lemmas.ML") ("cladata.ML") ("blastdata.ML") ("simpdata.ML"):


(** Core syntax **)

global

classes "term" < logic
defaultsort "term"

typedecl bool

arities
  bool :: "term"
  fun :: ("term", "term") "term"


consts

  (* Constants *)

  Trueprop      :: "bool => prop"                   ("(_)" 5)
  Not           :: "bool => bool"                   ("~ _" [40] 40)
  True          :: bool
  False         :: bool
  If            :: "[bool, 'a, 'a] => 'a"           ("(if (_)/ then (_)/ else (_))" 10)
  arbitrary     :: 'a

  (* Binders *)

  Eps           :: "('a => bool) => 'a"
  All           :: "('a => bool) => bool"           (binder "ALL " 10)
  Ex            :: "('a => bool) => bool"           (binder "EX " 10)
  Ex1           :: "('a => bool) => bool"           (binder "EX! " 10)
  Let           :: "['a, 'a => 'b] => 'b"

  (* Infixes *)

  "="           :: "['a, 'a] => bool"               (infixl 50)
  &             :: "[bool, bool] => bool"           (infixr 35)
  "|"           :: "[bool, bool] => bool"           (infixr 30)
  -->           :: "[bool, bool] => bool"           (infixr 25)


(* Overloaded Constants *)

axclass plus < "term"
axclass minus < "term"
axclass times < "term"
axclass power < "term"

consts
  "+"           :: "['a::plus, 'a]  => 'a"          (infixl 65)
  -             :: "['a::minus, 'a] => 'a"          (infixl 65)
  uminus        :: "['a::minus] => 'a"              ("- _" [81] 80)
  *             :: "['a::times, 'a] => 'a"          (infixl 70)
  (*See Nat.thy for "^"*)



(** Additional concrete syntax **)

nonterminals
  letbinds  letbind
  case_syn  cases_syn

syntax
  ~=            :: "['a, 'a] => bool"                    (infixl 50)
  "_Eps"        :: "[pttrn, bool] => 'a"                 ("(3SOME _./ _)" [0, 10] 10)

  (* Let expressions *)

  "_bind"       :: "[pttrn, 'a] => letbind"              ("(2_ =/ _)" 10)
  ""            :: "letbind => letbinds"                 ("_")
  "_binds"      :: "[letbind, letbinds] => letbinds"     ("_;/ _")
  "_Let"        :: "[letbinds, 'a] => 'a"                ("(let (_)/ in (_))" 10)

  (* Case expressions *)

  "@case"       :: "['a, cases_syn] => 'b"               ("(case _ of/ _)" 10)
  "@case1"      :: "['a, 'b] => case_syn"                ("(2_ =>/ _)" 10)
  ""            :: "case_syn => cases_syn"               ("_")
  "@case2"      :: "[case_syn, cases_syn] => cases_syn"  ("_/ | _")

translations
  "x ~= y"                == "~ (x = y)"
  "SOME x. P"             == "Eps (%x. P)"
  "_Let (_binds b bs) e"  == "_Let b (_Let bs e)"
  "let x = a in e"        == "Let a (%x. e)"

syntax ("" output)
  "op ="        :: "['a, 'a] => bool"                    ("(_ =/ _)" [51, 51] 50)
  "op ~="       :: "['a, 'a] => bool"                    ("(_ ~=/ _)" [51, 51] 50)

syntax (symbols)
  Not           :: "bool => bool"                        ("\\<not> _" [40] 40)
  "op &"        :: "[bool, bool] => bool"                (infixr "\\<and>" 35)
  "op |"        :: "[bool, bool] => bool"                (infixr "\\<or>" 30)
  "op -->"      :: "[bool, bool] => bool"                (infixr "\\<midarrow>\\<rightarrow>" 25)
  "op o"        :: "['b => 'c, 'a => 'b, 'a] => 'c"      (infixl "\\<circ>" 55)
  "op ~="       :: "['a, 'a] => bool"                    (infixl "\\<noteq>" 50)
  "_Eps"        :: "[pttrn, bool] => 'a"                 ("(3\\<epsilon>_./ _)" [0, 10] 10)
  "ALL "        :: "[idts, bool] => bool"                ("(3\\<forall>_./ _)" [0, 10] 10)
  "EX "         :: "[idts, bool] => bool"                ("(3\\<exists>_./ _)" [0, 10] 10)
  "EX! "        :: "[idts, bool] => bool"                ("(3\\<exists>!_./ _)" [0, 10] 10)
  "@case1"      :: "['a, 'b] => case_syn"                ("(2_ \\<Rightarrow>/ _)" 10)
(*"@case2"      :: "[case_syn, cases_syn] => cases_syn"  ("_/ \\<orelse> _")*)

syntax (symbols output)
  "op ~="       :: "['a, 'a] => bool"                    ("(_ \\<noteq>/ _)" [51, 51] 50)

syntax (xsymbols)
  "op -->"      :: "[bool, bool] => bool"                (infixr "\\<longrightarrow>" 25)

syntax (HTML output)
  Not           :: "bool => bool"                        ("\\<not> _" [40] 40)

syntax (HOL)
  "_Eps"        :: "[pttrn, bool] => 'a"                 ("(3@ _./ _)" [0, 10] 10)
  "ALL "        :: "[idts, bool] => bool"                ("(3! _./ _)" [0, 10] 10)
  "EX "         :: "[idts, bool] => bool"                ("(3? _./ _)" [0, 10] 10)
  "EX! "        :: "[idts, bool] => bool"                ("(3?! _./ _)" [0, 10] 10)



(** Rules and definitions **)

local

axioms

  eq_reflection: "(x=y) ==> (x==y)"

  (* Basic Rules *)

  refl:         "t = (t::'a)"
  subst:        "[| s = t; P(s) |] ==> P(t::'a)"

  (*Extensionality is built into the meta-logic, and this rule expresses
    a related property.  It is an eta-expanded version of the traditional
    rule, and similar to the ABS rule of HOL.*)
  ext:          "(!!x::'a. (f x ::'b) = g x) ==> (%x. f x) = (%x. g x)"

  selectI:      "P (x::'a) ==> P (@x. P x)"

  impI:         "(P ==> Q) ==> P-->Q"
  mp:           "[| P-->Q;  P |] ==> Q"

defs

  True_def:     "True      == ((%x::bool. x) = (%x. x))"
  All_def:      "All(P)    == (P = (%x. True))"
  Ex_def:       "Ex(P)     == P(@x. P(x))"
  False_def:    "False     == (!P. P)"
  not_def:      "~ P       == P-->False"
  and_def:      "P & Q     == !R. (P-->Q-->R) --> R"
  or_def:       "P | Q     == !R. (P-->R) --> (Q-->R) --> R"
  Ex1_def:      "Ex1(P)    == ? x. P(x) & (! y. P(y) --> y=x)"

axioms
  (* Axioms *)

  iff:          "(P-->Q) --> (Q-->P) --> (P=Q)"
  True_or_False:  "(P=True) | (P=False)"

defs
  (*misc definitions*)
  Let_def:      "Let s f == f(s)"
  if_def:       "If P x y == @z::'a. (P=True --> z=x) & (P=False --> z=y)"

  (*arbitrary is completely unspecified, but is made to appear as a
    definition syntactically*)
  arbitrary_def:  "False ==> arbitrary == (@x. False)"



(* theory and package setup *)

use "HOL_lemmas.ML"	setup attrib_setup
use "cladata.ML"	setup Classical.setup setup clasetup
use "blastdata.ML"	setup Blast.setup
use "simpdata.ML"	setup Simplifier.setup setup iff_attrib_setup
			setup simpsetup setup Clasimp.setup


end
