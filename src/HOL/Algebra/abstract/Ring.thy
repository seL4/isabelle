(*
    Abstract class ring (commutative, with 1)
    $Id$
    Author: Clemens Ballarin, started 9 December 1996
*)

Ring = Main +

(* Syntactic class ring *)

axclass
  ringS < zero, plus, minus, times, power, inverse

consts
  (* Basic rings *)
  "<1>"		:: 'a::ringS				("<1>")
  "--"		:: ['a, 'a] => 'a::ringS		(infixl 65)

  (* Divisibility *)
  assoc		:: ['a::times, 'a] => bool		(infixl 50)
  irred		:: 'a::ringS => bool
  prime		:: 'a::ringS => bool

translations
  "a -- b" 	== "a + (-b)"

(* Class ring and ring axioms *)

axclass
  ring < ringS, plus_ac0

(*a_assoc	"(a + b) + c = a + (b + c)"*)
(*l_zero	"0 + a = a"*)
  l_neg		"(-a) + a = 0"
(*a_comm	"a + b = b + a"*)

  m_assoc	"(a * b) * c = a * (b * c)"
  l_one		"<1> * a = a"

  l_distr	"(a + b) * c = a * c + b * c"

  m_comm	"a * b = b * a"

  (* Definition of derived operations *)

  inverse_ax    "inverse a = (if a dvd <1> then @x. a*x = <1> else 0)"
  divide_ax     "a / b = a * inverse b"
  power_ax	"a ^ n = nat_rec <1> (%u b. b * a) n"

defs
  assoc_def	"a assoc b == a dvd b & b dvd a"
  irred_def	"irred a == a ~= 0 & ~ a dvd <1>
                          & (ALL d. d dvd a --> d dvd <1> | a dvd d)"
  prime_def	"prime p == p ~= 0 & ~ p dvd <1>
                          & (ALL a b. p dvd (a*b) --> p dvd a | p dvd b)"

(* Integral domains *)

axclass
  domain < ring

  one_not_zero	"<1> ~= 0"
  integral	"a * b = 0 ==> a = 0 | b = 0"

(* Factorial domains *)

axclass
  factorial < domain

(*
  Proper definition using divisor chain condition currently not supported.
  factorial_divisor	"wf {(a, b). a dvd b & ~ (b dvd a)}"
*)
  factorial_divisor	"True"
  factorial_prime	"irred a ==> prime a"

(* Euclidean domains *)

(*
axclass
  euclidean < domain

  euclidean_ax	"b ~= 0 ==> Ex (% (q, r, e_size::('a::ringS)=>nat).
                   a = b * q + r & e_size r < e_size b)"

  Nothing has been proved about euclidean domains, yet.
  Design question:
    Fix quo, rem and e_size as constants that are axiomatised with
    euclidean_ax?
    - advantage: more pragmatic and easier to use
    - disadvantage: for every type, one definition of quo and rem will
        be fixed, users may want to use differing ones;
        also, it seems not possible to prove that fields are euclidean
        domains, because that would require generic (type-independent)
        definitions of quo and rem.
*)

(* Fields *)

axclass
  field < ring

  field_one_not_zero	"<1> ~= 0"
		(* Avoid a common superclass as the first thing we will
		   prove about fields is that they are domains. *)
  field_ax	"a ~= 0 ==> a dvd <1>"

end
