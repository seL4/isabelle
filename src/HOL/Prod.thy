(*  Title:      HOL/Prod.thy
    ID:         Prod.thy,v 1.5 1994/08/19 09:04:27 lcp Exp
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Ordered Pairs and the Cartesian product type.
The unit type.
*)

Prod = Fun + equalities +


(** products **)

(* type definition *)

constdefs
  Pair_Rep      :: ['a, 'b] => ['a, 'b] => bool
  "Pair_Rep == (%a b. %x y. x=a & y=b)"

global

typedef (Prod)
  ('a, 'b) "*"          (infixr 20)
    = "{f. ? a b. f = Pair_Rep (a::'a) (b::'b)}"

syntax (symbols)
  "*"           :: [type, type] => type         ("(_ \\<times>/ _)" [21, 20] 20)


(* abstract constants and syntax *)

consts
  fst           :: "'a * 'b => 'a"
  snd           :: "'a * 'b => 'b"
  split         :: "[['a, 'b] => 'c, 'a * 'b] => 'c"
  prod_fun      :: "['a => 'b, 'c => 'd, 'a * 'c] => 'b * 'd"
  Pair          :: "['a, 'b] => 'a * 'b"
  Sigma         :: "['a set, 'a => 'b set] => ('a * 'b) set"


(* patterns -- extends pre-defined type "pttrn" used in abstractions *)

types patterns

syntax
  "@Tuple"      :: "['a, args] => 'a * 'b"       ("(1'(_,/ _'))")

  "_pattern"    :: [pttrn, patterns] => pttrn    ("'(_,/_')")
  ""            :: pttrn => patterns             ("_")
  "_patterns"   :: [pttrn, patterns] => patterns ("_,/_")

  "@Sigma"      :: "[pttrn, 'a set, 'b set] => ('a * 'b) set"   ("(3SIGMA _:_./ _)" 10)
  "@Times"      :: "['a set, 'a => 'b set] => ('a * 'b) set"    ("_ Times _" [81, 80] 80)

translations
  "(x, y, z)"    == "(x, (y, z))"
  "(x, y)"       == "Pair x y"

  "%(x,y,zs).b"  == "split(%x (y,zs).b)"
  "%(x,y).b"     == "split(%x y. b)"
  "_abs (Pair x y) t" => "%(x,y).t"
  (* The last rule accommodates tuples in `case C ... (x,y) ... => ...'
     The (x,y) is parsed as `Pair x y' because it is logic, not pttrn *)

  "SIGMA x:A. B" => "Sigma A (%x. B)"
  "A Times B"    => "Sigma A (_K B)"

syntax (symbols)
  "@Sigma"      :: "[pttrn, 'a set, 'b set] => ('a * 'b) set"   ("(3\\<Sigma> _\\<in>_./ _)" 10)
  "@Times"      :: "['a set, 'a => 'b set] => ('a * 'b) set"    ("_ \\<times> _" [81, 80] 80)


(* definitions *)

local

defs
  Pair_def      "Pair a b == Abs_Prod(Pair_Rep a b)"
  fst_def       "fst p == @a. ? b. p = (a, b)"
  snd_def       "snd p == @b. ? a. p = (a, b)"
  split_def     "split == (%c p. c (fst p) (snd p))"
  prod_fun_def  "prod_fun f g == split(%x y.(f(x), g(y)))"
  Sigma_def     "Sigma A B == UN x:A. UN y:B(x). {(x, y)}"



(** unit **)

global

typedef  unit = "{True}"

consts
  "()"          :: unit                           ("'(')")

local

defs
  Unity_def     "() == Abs_unit True"

end

ML

val print_translation = [("Sigma", dependent_tr' ("@Sigma", "@Times"))];
