(*  Title:      HOL/Fun.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Notions about functions.
*)

Fun = Vimage + equalities + 

instance set :: (term) order
                       (subset_refl,subset_trans,subset_antisym,psubset_eq)
nonterminals
  updbinds  updbind

consts
  fun_upd  :: "('a => 'b) => 'a => 'b => ('a => 'b)"

syntax

  (* Let expressions *)

  "_updbind"       :: ['a, 'a] => updbind             ("(2_ :=/ _)")
  ""               :: updbind => updbinds             ("_")
  "_updbinds"      :: [updbind, updbinds] => updbinds ("_,/ _")
  "_Update"        :: ['a, updbinds] => 'a            ("_/'((_)')" [900,0] 900)

translations
  "_Update f (_updbinds b bs)"  == "_Update (_Update f b) bs"
  "f(x:=y)"                     == "fun_upd f x y"

defs
  fun_upd_def "f(a:=b) == % x. if x=a then b else f x"

  
constdefs
  id ::  'a => 'a
    "id == %x. x"

  o  :: ['b => 'c, 'a => 'b, 'a] => 'c   (infixl 55)
    "f o g == %x. f(g(x))"

  inj_on :: ['a => 'b, 'a set] => bool
    "inj_on f A == ! x:A. ! y:A. f(x)=f(y) --> x=y"

  surj :: ('a => 'b) => bool                   (*surjective*)
    "surj f == ! y. ? x. y=f(x)"
  
  inv :: ('a => 'b) => ('b => 'a)
    "inv(f::'a=>'b) == % y. @x. f(x)=y"
  


syntax
  inj   :: ('a => 'b) => bool                   (*injective*)

translations
  "inj f" == "inj_on f UNIV"

(*The Pi-operator, by Florian Kammueller*)
  
constdefs
  Pi      :: "['a set, 'a => 'b set] => ('a => 'b) set"
    "Pi A B == {f. ! x. if x:A then f(x) : B(x) else f(x) = (@ y. True)}"

  restrict :: "['a => 'b, 'a set] => ('a => 'b)"
    "restrict f A == (%x. if x : A then f x else (@ y. True))"

syntax
  "@Pi"  :: "[idt, 'a set, 'b set] => ('a => 'b) set"  ("(3PI _:_./ _)" 10)
  funcset :: "['a set, 'b set] => ('a => 'b) set"      (infixr 60) 
  "@lam" :: "[pttrn, 'a set, 'a => 'b] => ('a => 'b)"  ("(3lam _:_./ _)" 10)

  (*Giving funcset the nice arrow syntax -> clashes with existing theories*)

translations
  "PI x:A. B" => "Pi A (%x. B)"
  "A funcset B"    => "Pi A (_K B)"
  "lam x:A. f"  == "restrict (%x. f) A"

constdefs
  Applyall :: "[('a => 'b) set, 'a]=> 'b set"
    "Applyall F a == (%f. f a) `` F"

  compose :: "['a set, 'a => 'b, 'b => 'c] => ('a => 'c)"
    "compose A g f == lam x : A. g(f x)"

  Inv    :: "['a set, 'a => 'b] => ('b => 'a)"
    "Inv A f == (% x. (@ y. y : A & f y = x))"

  
end

ML
val print_translation = [("Pi", dependent_tr' ("@Pi", "op funcset"))];
