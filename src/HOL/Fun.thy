(*  Title:      HOL/Fun.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Notions about functions.
*)

Fun = Typedef +

instance set :: (type) order
                       (subset_refl,subset_trans,subset_antisym,psubset_eq)
consts
  fun_upd  :: "('a => 'b) => 'a => 'b => ('a => 'b)"

nonterminals
  updbinds updbind
syntax
  "_updbind"       :: ['a, 'a] => updbind             ("(2_ :=/ _)")
  ""               :: updbind => updbinds             ("_")
  "_updbinds"      :: [updbind, updbinds] => updbinds ("_,/ _")
  "_Update"        :: ['a, updbinds] => 'a            ("_/'((_)')" [1000,0] 900)

translations
  "_Update f (_updbinds b bs)"  == "_Update (_Update f b) bs"
  "f(x:=y)"                     == "fun_upd f x y"

defs
  fun_upd_def "f(a:=b) == % x. if x=a then b else f x"

(* Hint: to define the sum of two functions (or maps), use sum_case.
         A nice infix syntax could be defined (in Datatype.thy or below) by
consts
  fun_sum :: "('a => 'c) => ('b => 'c) => (('a+'b) => 'c)" (infixr "'(+')"80)
translations
 "fun_sum" == "sum_case"
*)

constdefs
  id ::  'a => 'a
    "id == %x. x"

  o  :: ['b => 'c, 'a => 'b, 'a] => 'c   (infixl 55)
    "f o g == %x. f(g(x))"

  inj_on :: ['a => 'b, 'a set] => bool
    "inj_on f A == ! x:A. ! y:A. f(x)=f(y) --> x=y"

syntax (xsymbols)
  "op o"        :: "['b => 'c, 'a => 'b, 'a] => 'c"      (infixl "\\<circ>" 55)

syntax
  inj   :: ('a => 'b) => bool                   (*injective*)

translations
  "inj f" == "inj_on f UNIV"

constdefs
  surj :: ('a => 'b) => bool                   (*surjective*)
    "surj f == ! y. ? x. y=f(x)"

  bij :: ('a => 'b) => bool                    (*bijective*)
    "bij f == inj f & surj f"


(*The Pi-operator, by Florian Kammueller*)

constdefs
  Pi      :: "['a set, 'a => 'b set] => ('a => 'b) set"
    "Pi A B == {f. ! x. if x:A then f(x) : B(x) else f(x) = arbitrary}"

  restrict :: "['a => 'b, 'a set] => ('a => 'b)"
    "restrict f A == (%x. if x : A then f x else arbitrary)"

syntax
  "@Pi"  :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3PI _:_./ _)" 10)
  funcset :: "['a set, 'b set] => ('a => 'b) set"      (infixr 60)
  "@lam" :: "[pttrn, 'a set, 'a => 'b] => ('a => 'b)"  ("(3%_:_./ _)" [0, 0, 3] 3)
syntax (xsymbols)
  "@lam" :: "[pttrn, 'a set, 'a => 'b] => ('a => 'b)"  ("(3\\<lambda>_\\<in>_./ _)" [0, 0, 3] 3)

  (*Giving funcset an arrow syntax (-> or =>) clashes with many existing theories*)

syntax (xsymbols)
  "@Pi" :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3\\<Pi> _\\<in>_./ _)"   10)

translations
  "PI x:A. B" => "Pi A (%x. B)"
  "A funcset B"    => "Pi A (_K B)"
  "%x:A. f"  == "restrict (%x. f) A"

constdefs
  compose :: "['a set, 'b => 'c, 'a => 'b] => ('a => 'c)"
  "compose A g f == %x:A. g (f x)"

end

ML
val print_translation = [("Pi", dependent_tr' ("@Pi", "op funcset"))];
