(*  Title:      HOL/ex/PiSets.thy
    ID:         $Id$
    Author:     Florian Kammueller, University of Cambridge

Theory for Pi type in terms of sets.
*)

PiSets = Univ + Finite +



constdefs
  Pi      :: "['a set, 'a => 'b set] => ('a => 'b) set"
    "Pi A B == {f. ! x. if x:A then f(x) : B(x) else f(x) = (@ y. True)}"

  restrict :: "['a => 'b, 'a set] => ('a => 'b)"
    "restrict f A == (%x. if x : A then f x else (@ y. True))"

syntax
  "@Pi"  :: "[idt, 'a set, 'b set] => ('a => 'b) set"  ("(3PI _:_./ _)" 10)
  "@->"  :: "['a set, 'b set] => ('a => 'b) set"       ("_ -> _" [91,90]90) 
(* or "->" ... (infixr 60) and at the end print_translation (... op ->) *)
  "@lam" :: "[pttrn, 'a set, 'a => 'b] => ('a => 'b)"    ("(3lam _:_./ _)" 10)

translations
  "PI x:A. B" => "Pi A (%x. B)"
  "A -> B"    => "Pi A (_K B)"
  "lam x:A. f"  == "restrict (%x. f) A"

constdefs
  Fset_apply :: "[('a => 'b) set, 'a]=> 'b set"   ("_ @@ _" [90,91]90)
    "F @@ a == (%f. f a) `` F"

  compose :: "['a set, 'a => 'b, 'b => 'c] => ('a => 'c)"
    "compose A g f == lam x : A. g(f x)"

  Inv    :: "['a set, 'a => 'b] => ('b => 'a)"
    "Inv A f == (% x. (@ y. y : A & f y = x))"

(* bijection between Pi_sig and Pi_=> *)
  PiBij :: "['a set, 'a => 'b set, 'a => 'b] => ('a * 'b) set"
    "PiBij A B == lam f: Pi A B. {(x, y). x: A & y = f x}"

  Graph ::  "['a set, 'a => 'b set] => ('a * 'b) set set"
   "Graph A B == {f. f: Pow(Sigma A B) & (! x: A. (?! y. (x, y): f))}"

end

ML
val print_translation = [("Pi", dependent_tr' ("@Pi", "@->"))];
