(*
  Title:     Term order, needed for normal forms in rings
  Id:        $Id$
  Author:    Clemens Ballarin and Roland Zumkeller
  Copyright: TU Muenchen
*)

local

(* 
An order is a value of type
  ('a -> bool, 'a * 'a -> bool).

The two parts are:
 1) a unary predicate denoting the order's domain
 2) a binary predicate with the semanitcs "greater than"

If (d, ord) is an order then ord (a,b) is defined if both d a and d b.
*)

(*
Combines two orders with disjoint domains and returns
another one. 
When the compared values are from the same domain, the corresponding
order is used. If not the ones from the first domain are considerer
greater. (If a value is in neither of the two domains, exception
"Domain" is raised.)
*)

fun combineOrd ((d1, ord1), (d2, ord2)) = 
  (fn x => d1 x orelse d2 x, 
   fn (a, b) =>
     if d1 a andalso d1 b then ord1 (a, b) else
     if d1 a andalso d2 b then true else
     if d2 a andalso d2 b then ord2 (a, b) else
     if d2 a andalso d1 b then false else raise Domain)


(* Counts the number of function applications + 1. *)
(* ### is there a standard Isabelle function for this? *)

fun tsize (a $ b) = tsize a + tsize b
  | tsize _ = 1;

(* foldl on non-empty lists *)

fun foldl2 f (x::xs) = foldl f (x,xs)


(* Compares two terms, ignoring type information. *)
infix e;
fun (Const (s1, _))   e (Const (s2, _))   = s1 = s2
  | (Free (s1, _))    e (Free (s2, _))    = s1 = s2
  | (Var (ix1, _))    e (Var (ix2, _))    = ix1 = ix2
  | (Bound i1)        e (Bound i2)        = i1 = i2
  | (Abs (s1, _, t1)) e (Abs (s2, _, t2)) = s1 = s2 andalso t1 = t2
  | (s1 $ s2)         e (t1 $ t2)         = s1 = t1 andalso s2 = t2
  | _ e _ = false



(* Curried lexicographich path order induced by an order on function symbols.
Its feature include:
- compatibility with Epsilon-operations 
- closure under substitutions
- well-foundedness
- subterm-property
- termination
- defined on all terms (not only on ground terms)
- linearity

The order ignores types.
*)

infix g;
fun clpo (d, ord) (s,t) = 
  let val (op g) = clpo (d, ord) in
     (s <> t) andalso
     if tsize s < tsize t then not (t g s) else
       (* improves performance. allowed because clpo is total. *)
     #2 (foldl2 combineOrd [
        (fn _ $ _ => true | Abs _ => true | _ => false, 
  	 fn (Abs (_, _, s'), t) => s' e t orelse s' g t orelse 
 				   (case t of
 					Abs (_, _, t') => s' g t'
 				      | t1 $ t2 => s g t1 andalso s g t2
 			           )
           | (s1 $ s2, t) => s1 e t orelse s2 e t orelse 
                             s1 g t orelse s2 g t orelse
 			    (case t of
 				 t1 $ t2 => (s1 e t1 andalso s2 g t2) orelse
 					    (s1 g t1 andalso s g t2)
 			       | _ => false
                             )
        ),
        (fn Free _       => true      | _ => false,   fn (Free (a,_), Free (b,_))     => a > b),
        (fn Bound _      => true      | _ => false,   fn (Bound a, Bound b)           => a > b),
        (fn Const (c, _) => not (d c) | _ => false,   fn (Const (a, _), Const (b, _)) => a > b),
        (fn Const (c, _) => d c       | _ => false,   fn (Const (a, _), Const (b, _)) => ord (a,b))
    ]) (s,t)
  end;

(*
Open Issues: 
- scheme variables have to be ordered (should be simple)
*)

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

(* Returns the position of an element in a list. If the
element doesn't occur in the list, a MatchException is raised. *)
fun pos (x::xs) i = if x = i then 0 else 1 + pos xs i;

(* Generates a finite linear order from a list. 
[a, b, c] results in the order "a > b > c". *)
fun linOrd l = fn (a,b) => pos l a < pos l b;

(* Determines whether an element is contained in a list. *)
fun contains (x::xs) i = (x = i) orelse (contains xs i) |
    contains [] i = false;

in

(* Term order for commutative rings *)

fun termless_ring (a, b) =
  let
    val S = ["op *", "op -", "uminus", "op +", "0"];
    (* Order (decending from left to right) on the constant symbols *)
    val baseOrd = (contains S, linOrd S);
  in clpo baseOrd (b, a)
  end;

(*** Rewrite rules ***)

val a_assoc = thm "ring.a_assoc";
val l_zero = thm "ring.l_zero";
val l_neg = thm "ring.l_neg";
val a_comm = thm "ring.a_comm";
val m_assoc = thm "ring.m_assoc";
val l_one = thm "ring.l_one";
val l_distr = thm "ring.l_distr";
val m_comm = thm "ring.m_comm";
val minus_def = thm "ring.minus_def";
val inverse_def = thm "ring.inverse_def";
val divide_def = thm "ring.divide_def";
val power_def = thm "ring.power_def";

(* These are the following axioms:

  a_assoc:      "(a + b) + c = a + (b + c)"
  l_zero:       "0 + a = a"
  l_neg:        "(-a) + a = 0"
  a_comm:       "a + b = b + a"

  m_assoc:      "(a * b) * c = a * (b * c)"
  l_one:        "1 * a = a"

  l_distr:      "(a + b) * c = a * c + b * c"

  m_comm:       "a * b = b * a"

  -- {* Definition of derived operations *}

  minus_def:    "a - b = a + (-b)"
  inverse_def:  "inverse a = (if a dvd 1 then THE x. a*x = 1 else 0)"
  divide_def:   "a / b = a * inverse b"
  power_def:    "a ^ n = nat_rec 1 (%u b. b * a) n"
*)

(* These lemmas are needed in the proofs *)
val trans = thm "trans";
val sym = thm "sym";
val subst = thm "subst";
val box_equals = thm "box_equals";
val arg_cong = thm "arg_cong";
(* current theory *)
val thy = the_context ();

(* derived rewrite rules *)
val a_lcomm = prove_goal thy "(a::'a::ring)+(b+c) = b+(a+c)"
  (fn _ => [rtac (a_comm RS trans) 1, rtac (a_assoc RS trans) 1,
     rtac (a_comm RS arg_cong) 1]);
val r_zero = prove_goal thy "(a::'a::ring) + 0 = a"
  (fn _ => [rtac (a_comm RS trans) 1, rtac l_zero 1]);
val r_neg = prove_goal thy "(a::'a::ring) + (-a) = 0"
  (fn _ => [rtac (a_comm RS trans) 1, rtac l_neg 1]);
val r_neg2 = prove_goal thy "(a::'a::ring) + (-a + b) = b"
  (fn _ => [rtac (a_assoc RS sym RS trans) 1,
     simp_tac (simpset() addsimps [r_neg, l_zero]) 1]);
val r_neg1 = prove_goal thy "-(a::'a::ring) + (a + b) = b"
  (fn _ => [rtac (a_assoc RS sym RS trans) 1,
     simp_tac (simpset() addsimps [l_neg, l_zero]) 1]);
(* auxiliary *)
val a_lcancel = prove_goal thy "!! a::'a::ring. a + b = a + c ==> b = c"
  (fn _ => [rtac box_equals 1, rtac l_zero 2, rtac l_zero 2,
     res_inst_tac [("a1", "a")] (l_neg RS subst) 1,
     asm_simp_tac (simpset() addsimps [a_assoc]) 1]);
val minus_add = prove_goal thy "-((a::'a::ring) + b) = (-a) + (-b)"
  (fn _ => [res_inst_tac [("a", "a+b")] a_lcancel 1,
     simp_tac (simpset() addsimps [r_neg, l_neg, l_zero, 
                                   a_assoc, a_comm, a_lcomm]) 1]);
val minus_minus = prove_goal thy "-(-(a::'a::ring)) = a"
  (fn _ => [rtac a_lcancel 1, rtac (r_neg RS trans) 1, rtac (l_neg RS sym) 1]);
val minus0 = prove_goal thy "- 0 = (0::'a::ring)"
  (fn _ => [rtac a_lcancel 1, rtac (r_neg RS trans) 1,
     rtac (l_zero RS sym) 1]);

(* derived rules for multiplication *)
val m_lcomm = prove_goal thy "(a::'a::ring)*(b*c) = b*(a*c)"
  (fn _ => [rtac (m_comm RS trans) 1, rtac (m_assoc RS trans) 1,
     rtac (m_comm RS arg_cong) 1]);
val r_one = prove_goal thy "(a::'a::ring) * 1 = a"
  (fn _ => [rtac (m_comm RS trans) 1, rtac l_one 1]);
val r_distr = prove_goal thy "(a::'a::ring) * (b + c) = a * b + a * c"
  (fn _ => [rtac (m_comm RS trans) 1, rtac (l_distr RS trans) 1,
     simp_tac (simpset() addsimps [m_comm]) 1]);
(* the following proof is from Jacobson, Basic Algebra I, pp. 88-89 *)
val l_null = prove_goal thy "0 * (a::'a::ring) = 0"
  (fn _ => [rtac a_lcancel 1, rtac (l_distr RS sym RS trans) 1,
     simp_tac (simpset() addsimps [r_zero]) 1]);
val r_null = prove_goal thy "(a::'a::ring) * 0 = 0"
  (fn _ => [rtac (m_comm RS trans) 1, rtac l_null 1]);
val l_minus = prove_goal thy "(-(a::'a::ring)) * b = - (a * b)"
  (fn _ => [rtac a_lcancel 1, rtac (r_neg RS sym RSN (2, trans)) 1,
     rtac (l_distr RS sym RS trans) 1,
     simp_tac (simpset() addsimps [l_null, r_neg]) 1]);
val r_minus = prove_goal thy "(a::'a::ring) * (-b) = - (a * b)"
  (fn _ => [rtac a_lcancel 1, rtac (r_neg RS sym RSN (2, trans)) 1,
     rtac (r_distr RS sym RS trans) 1,
     simp_tac (simpset() addsimps [r_null, r_neg]) 1]);

val ring_ss = HOL_basic_ss settermless termless_ring addsimps
  [a_assoc, l_zero, l_neg, a_comm, m_assoc, l_one, l_distr, m_comm, minus_def,
   r_zero, r_neg, r_neg2, r_neg1, minus_add, minus_minus, minus0,
   a_lcomm, m_lcomm, r_distr, l_null, r_null, l_minus, r_minus];

val x = bind_thms ("ring_simps", [l_zero, r_zero, l_neg, r_neg,
  minus_minus, minus0, 
  l_one, r_one, l_null, r_null, l_minus, r_minus]);

(* note: r_one added to ring_simp but not ring_ss *)

(* note: not added (and not proved):
  a_lcancel_eq, a_rcancel_eq, power_one, power_Suc, power_zero, power_one,
  m_lcancel_eq, m_rcancel_eq,
  thms involving dvd, integral domains, fields
*)

end;