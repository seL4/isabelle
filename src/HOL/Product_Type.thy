(*  Title:      HOL/Product_Type.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Ordered Pairs and the Cartesian product type.
The unit type.
*)

theory Product_Type = Fun
files ("Product_Type_lemmas.ML") ("Tools/split_rule.ML"):


(** products **)

(* type definition *)

constdefs
  Pair_Rep :: "['a, 'b] => ['a, 'b] => bool"
  "Pair_Rep == (%a b. %x y. x=a & y=b)"

global

typedef (Prod)
  ('a, 'b) "*"          (infixr 20)
    = "{f. EX a b. f = Pair_Rep (a::'a) (b::'b)}"
proof
  fix a b show "Pair_Rep a b : ?Prod"
    by blast
qed

syntax (symbols)
  "*"      :: "[type, type] => type"         ("(_ \\<times>/ _)" [21, 20] 20)
syntax (HTML output)
  "*"      :: "[type, type] => type"         ("(_ \\<times>/ _)" [21, 20] 20)


(* abstract constants and syntax *)

consts
  fst      :: "'a * 'b => 'a"
  snd      :: "'a * 'b => 'b"
  split    :: "[['a, 'b] => 'c, 'a * 'b] => 'c"
  prod_fun :: "['a => 'b, 'c => 'd, 'a * 'c] => 'b * 'd"
  Pair     :: "['a, 'b] => 'a * 'b"
  Sigma    :: "['a set, 'a => 'b set] => ('a * 'b) set"


(* patterns -- extends pre-defined type "pttrn" used in abstractions *)

nonterminals
  tuple_args patterns

syntax
  "_tuple"      :: "'a => tuple_args => 'a * 'b"        ("(1'(_,/ _'))")
  "_tuple_arg"  :: "'a => tuple_args"                   ("_")
  "_tuple_args" :: "'a => tuple_args => tuple_args"     ("_,/ _")
  "_pattern"    :: "[pttrn, patterns] => pttrn"         ("'(_,/ _')")
  ""            :: "pttrn => patterns"                  ("_")
  "_patterns"   :: "[pttrn, patterns] => patterns"      ("_,/ _")
  "@Sigma" ::"[pttrn, 'a set, 'b set] => ('a * 'b) set" ("(3SIGMA _:_./ _)" 10)
  "@Times" ::"['a set,  'a => 'b set] => ('a * 'b) set" (infixr "<*>" 80)

translations
  "(x, y)"       == "Pair x y"
  "_tuple x (_tuple_args y z)" == "_tuple x (_tuple_arg (_tuple y z))"
  "%(x,y,zs).b"  == "split(%x (y,zs).b)"
  "%(x,y).b"     == "split(%x y. b)"
  "_abs (Pair x y) t" => "%(x,y).t"
  (* The last rule accommodates tuples in `case C ... (x,y) ... => ...'
     The (x,y) is parsed as `Pair x y' because it is logic, not pttrn *)

  "SIGMA x:A. B" => "Sigma A (%x. B)"
  "A <*> B"      => "Sigma A (_K B)"

syntax (symbols)
  "@Sigma" :: "[pttrn, 'a set, 'b set] => ('a * 'b) set"  ("(3\\<Sigma> _\\<in>_./ _)"   10)
  "@Times" :: "['a set,  'a => 'b set] => ('a * 'b) set"  ("_ \\<times> _" [81, 80] 80)

print_translation {* [("Sigma", dependent_tr' ("@Sigma", "@Times"))] *}


(* definitions *)

local

defs
  Pair_def:     "Pair a b == Abs_Prod(Pair_Rep a b)"
  fst_def:      "fst p == THE a. EX b. p = (a, b)"
  snd_def:      "snd p == THE b. EX a. p = (a, b)"
  split_def:    "split == (%c p. c (fst p) (snd p))"
  prod_fun_def: "prod_fun f g == split(%x y.(f(x), g(y)))"
  Sigma_def:    "Sigma A B == UN x:A. UN y:B(x). {(x, y)}"



(** unit **)

global

typedef unit = "{True}"
proof
  show "True : ?unit"
    by blast
qed

consts
  "()"          :: unit                           ("'(')")

local

defs
  Unity_def:    "() == Abs_unit True"



(** lemmas and tool setup **)

use "Product_Type_lemmas.ML"

constdefs
  internal_split :: "('a => 'b => 'c) => 'a * 'b => 'c"
  "internal_split == split"

lemma internal_split_conv: "internal_split c (a, b) = c a b"
  by (simp only: internal_split_def split_conv)

hide const internal_split

use "Tools/split_rule.ML"
setup SplitRule.setup

end
