(*
  Title:     Term order, needed for normal forms in rings
  Id:        $Id$
  Author:    Clemens Ballarin
  Copyright: TU Muenchen
*)

local

(*** Lexicographic path order on terms.

  See Baader & Nipkow, Term rewriting, CUP 1998.
  Without variables.  Const, Var, Bound, Free and Abs are treated all as
  constants.

  f_ord maps strings to integers and serves two purposes:
  - Predicate on constant symbols.  Those that are not recognised by f_ord
    must be mapped to ~1.
  - Order on the recognised symbols.  These must be mapped to distinct
    integers >= 0.

***)

fun dest_hd f_ord (Const (a, T)) = 
      let val ord = f_ord a in
        if ord = ~1 then ((1, ((a, 0), T)), 0) else ((0, (("", ord), T)), 0)
      end
  | dest_hd _ (Free (a, T)) = ((1, ((a, 0), T)), 0)
  | dest_hd _ (Var v) = ((1, v), 1)
  | dest_hd _ (Bound i) = ((1, (("", i), Term.dummyT)), 2)
  | dest_hd _ (Abs (_, T, _)) = ((1, (("", 0), T)), 3);

fun term_lpo f_ord (s, t) =
  let val (f, ss) = strip_comb s and (g, ts) = strip_comb t in
    if forall (fn si => term_lpo f_ord (si, t) = LESS) ss
    then case hd_ord f_ord (f, g) of
	GREATER =>
	  if forall (fn ti => term_lpo f_ord (s, ti) = GREATER) ts
	  then GREATER else LESS
      | EQUAL =>
	  if forall (fn ti => term_lpo f_ord (s, ti) = GREATER) ts
	  then list_ord (term_lpo f_ord) (ss, ts)
	  else LESS
      | LESS => LESS
    else GREATER
  end
and hd_ord f_ord (f, g) = case (f, g) of
    (Abs (_, T, t), Abs (_, U, u)) =>
      (case term_lpo f_ord (t, u) of EQUAL => Term.typ_ord (T, U) | ord => ord)
  | (_, _) => prod_ord (prod_ord int_ord
                  (prod_ord Term.indexname_ord Term.typ_ord)) int_ord
                (dest_hd f_ord f, dest_hd f_ord g)

in

(*** Term order for commutative rings ***)

fun ring_ord a =
  find_index_eq a ["0", "op +", "uminus", "op -", "1", "op *"];

fun termless_ring (a, b) = (term_lpo ring_ord (a, b) = LESS);

(* Some code useful for debugging

val intT = HOLogic.intT;
val a = Free ("a", intT);
val b = Free ("b", intT);
val c = Free ("c", intT);
val plus = Const ("op +", [intT, intT]--->intT);
val mult = Const ("op *", [intT, intT]--->intT);
val uminus = Const ("uminus", intT-->intT);
val one = Const ("1", intT);
val f = Const("f", intT-->intT);

*)

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
   a_lcomm, m_lcomm, (*r_one,*) r_distr, l_null, r_null, l_minus, r_minus];

(* Note: r_one is not necessary in ring_ss *)

val x = bind_thms ("ring_simps", 
  [l_zero, r_zero, l_neg, r_neg, minus_minus, minus0, 
  l_one, r_one, l_null, r_null, l_minus, r_minus]);

(* note: not added (and not proved):
  a_lcancel_eq, a_rcancel_eq, power_one, power_Suc, power_zero, power_one,
  m_lcancel_eq, m_rcancel_eq,
  thms involving dvd, integral domains, fields
*)

end;