(*  Title:      HOL/ex/PiSets.thy
    ID:         $Id$
    Author:     Florian Kammueller, University of Cambridge

Theory for Pi type in terms of sets.
*)

PiSets = Univ + Finite +

consts 
  Pi      :: "['a set, 'a => 'b set] => ('a => 'b) set"

consts
  restrict :: "['a => 'b, 'a set] => ('a => 'b)"

defs
  restrict_def "restrict f A == (%x. if x : A then f x else (@ y. True))"

syntax
  "@Pi"      :: "[idt, 'a set, 'b set] => ('a => 'b) set"     ("(3PI _:_./ _)" 10)
  "@->"      :: "['a set, 'b set] => ('a => 'b) set"      ("_ -> _" [91,90]90) 
(* or "->" ... (infixr 60) and at the end print_translation (... op ->) *)
  "@lam"     :: "[idt, 'a set, 'a => 'b] => ('a => 'b)"       ("(3lam _:_./ _)" 10)
(* Could as well take pttrn *)

translations
  "PI x:A. B" => "Pi A (%x. B)"
  "A -> B"   => "Pi A (_K B)"
  "lam x:A. f"  == "restrict (%x. f) A"
(*   Larry fragen: "lam (x,y): A. f" == "restrict (%(x,y). f) A" *)
defs 
  Pi_def      "Pi A B == {f. ! x. if x:A then f(x) : B(x) else f(x) = (@ y. True)}"

consts
  Fset_apply :: "[('a => 'b) set, 'a]=> 'b set"   ("_ @@ _" [90,91]90)

defs
  Fset_apply_def "F @@ a == (%f. f a) `` F"

consts 
  compose :: "['a set, 'a => 'b, 'b => 'c] => ('a => 'c)"

defs
  compose_def "compose A g f == lam x : A. g(f x)"

consts 
  Inv    :: "['a set, 'a => 'b] => ('b => 'a)"

defs
  Inv_def "Inv A f == (% x. (@ y. y : A & f y = x))"

(* new: bijection between Pi_sig and Pi_=> *)
consts
  PiBij :: "['a set, 'a => 'b set, 'a => 'b] => ('a * 'b) set"

defs
  PiBij_def "PiBij A B == lam f: Pi A B. {(x, y). x: A & y = f x}"

consts
  Graph ::  "['a set, 'a => 'b set] => ('a * 'b) set set"

defs
  Graph_def "Graph A B == {f. f: Pow(Sigma A B) & (! x: A. (?! y. (x, y): f))}"

end

ML
val print_translation = [("Pi", dependent_tr' ("@Pi", "@->"))];
