(*  Title:      CCL/set.thy
    ID:         $Id$

Modified version of HOL/set.thy that extends FOL

*)

Set = FOL +

types
  set 1

arities
  set :: (term) term

consts
  Collect       :: "['a => o] => 'a set"                    (*comprehension*)
  Compl         :: "('a set) => 'a set"                     (*complement*)
  Int           :: "['a set, 'a set] => 'a set"         (infixl 70)
  Un            :: "['a set, 'a set] => 'a set"         (infixl 65)
  Union, Inter  :: "(('a set)set) => 'a set"                (*...of a set*)
  UNION, INTER  :: "['a set, 'a => 'b set] => 'b set"       (*general*)
  Ball, Bex     :: "['a set, 'a => o] => o"                 (*bounded quants*)
  mono          :: "['a set => 'b set] => o"                (*monotonicity*)
  ":"           :: "['a, 'a set] => o"                  (infixl 50) (*membership*)
  "<="          :: "['a set, 'a set] => o"              (infixl 50)
  singleton     :: "'a => 'a set"                       ("{_}")
  empty         :: "'a set"                             ("{}")
  "oo"          :: "['b => 'c, 'a => 'b, 'a] => 'c"     (infixr 50) (*composition*)

  "@Coll"       :: "[idt, o] => 'a set"                 ("(1{_./ _})") (*collection*)

  (* Big Intersection / Union *)

  "@INTER"      :: "[idt, 'a set, 'b set] => 'b set"    ("(INT _:_./ _)" [0, 0, 0] 10)
  "@UNION"      :: "[idt, 'a set, 'b set] => 'b set"    ("(UN _:_./ _)" [0, 0, 0] 10)

  (* Bounded Quantifiers *)

  "@Ball"       :: "[idt, 'a set, o] => o"              ("(ALL _:_./ _)" [0, 0, 0] 10)
  "@Bex"        :: "[idt, 'a set, o] => o"              ("(EX _:_./ _)" [0, 0, 0] 10)


translations
  "{x. P}"      == "Collect(%x. P)"
  "INT x:A. B"  == "INTER(A, %x. B)"
  "UN x:A. B"   == "UNION(A, %x. B)"
  "ALL x:A. P"  == "Ball(A, %x. P)"
  "EX x:A. P"   == "Bex(A, %x. P)"


rules
  mem_Collect_iff       "(a : {x.P(x)}) <-> P(a)"
  set_extension         "A=B <-> (ALL x.x:A <-> x:B)"

  Ball_def      "Ball(A, P)  == ALL x. x:A --> P(x)"
  Bex_def       "Bex(A, P)   == EX x. x:A & P(x)"
  mono_def      "mono(f)     == (ALL A B. A <= B --> f(A) <= f(B))"
  subset_def    "A <= B      == ALL x:A. x:B"
  singleton_def "{a}         == {x.x=a}"
  empty_def     "{}          == {x.False}"
  Un_def        "A Un B      == {x.x:A | x:B}"
  Int_def       "A Int B     == {x.x:A & x:B}"
  Compl_def     "Compl(A)    == {x. ~x:A}"
  INTER_def     "INTER(A, B) == {y. ALL x:A. y: B(x)}"
  UNION_def     "UNION(A, B) == {y. EX x:A. y: B(x)}"
  Inter_def     "Inter(S)    == (INT x:S. x)"
  Union_def     "Union(S)    == (UN x:S. x)"

end

