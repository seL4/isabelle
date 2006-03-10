(*
  Title:     Term order, needed for normal forms in rings
  Id:        $Id$
  Author:    Clemens Ballarin
  Copyright: TU Muenchen
*)

(*** Term order for commutative rings ***)

fun ring_ord a =
  find_index (fn a' => a = a') ["0", "HOL.plus", "HOL.uminus", "HOL.minus", "1", "HOL.times"];

fun termless_ring (a, b) = (Term.term_lpo ring_ord (a, b) = LESS);

(* Some code useful for debugging

val intT = HOLogic.intT;
val a = Free ("a", intT);
val b = Free ("b", intT);
val c = Free ("c", intT);
val plus = Const ("HOL.plus", [intT, intT]--->intT);
val mult = Const ("HOL.times", [intT, intT]--->intT);
val uminus = Const ("HOL.uminus", intT-->intT);
val one = Const ("1", intT);
val f = Const("f", intT-->intT);

*)

(*** Rewrite rules ***)

val a_assoc = thm "ring_class.a_assoc";
val l_zero = thm "ring_class.l_zero";
val l_neg = thm "ring_class.l_neg";
val a_comm = thm "ring_class.a_comm";
val m_assoc = thm "ring_class.m_assoc";
val l_one = thm "ring_class.l_one";
val l_distr = thm "ring_class.l_distr";
val m_comm = thm "ring_class.m_comm";
val minus_def = thm "ring_class.minus_def";
val inverse_def = thm "ring_class.inverse_def";
val divide_def = thm "ring_class.divide_def";
val power_def = thm "ring_class.power_def";

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

(* derived rewrite rules *)
val a_lcomm = prove_goal (the_context ()) "(a::'a::ring)+(b+c) = b+(a+c)"
  (fn _ => [rtac (a_comm RS trans) 1, rtac (a_assoc RS trans) 1,
     rtac (a_comm RS arg_cong) 1]);
val r_zero = prove_goal (the_context ()) "(a::'a::ring) + 0 = a"
  (fn _ => [rtac (a_comm RS trans) 1, rtac l_zero 1]);
val r_neg = prove_goal (the_context ()) "(a::'a::ring) + (-a) = 0"
  (fn _ => [rtac (a_comm RS trans) 1, rtac l_neg 1]);
val r_neg2 = prove_goal (the_context ()) "(a::'a::ring) + (-a + b) = b"
  (fn _ => [rtac (a_assoc RS sym RS trans) 1,
     simp_tac (simpset() addsimps [r_neg, l_zero]) 1]);
val r_neg1 = prove_goal (the_context ()) "-(a::'a::ring) + (a + b) = b"
  (fn _ => [rtac (a_assoc RS sym RS trans) 1,
     simp_tac (simpset() addsimps [l_neg, l_zero]) 1]);
(* auxiliary *)
val a_lcancel = prove_goal (the_context ()) "!! a::'a::ring. a + b = a + c ==> b = c"
  (fn _ => [rtac box_equals 1, rtac l_zero 2, rtac l_zero 2,
     res_inst_tac [("a1", "a")] (l_neg RS subst) 1,
     asm_simp_tac (simpset() addsimps [a_assoc]) 1]);
val minus_add = prove_goal (the_context ()) "-((a::'a::ring) + b) = (-a) + (-b)"
  (fn _ => [res_inst_tac [("a", "a+b")] a_lcancel 1,
     simp_tac (simpset() addsimps [r_neg, l_neg, l_zero, 
                                   a_assoc, a_comm, a_lcomm]) 1]);
val minus_minus = prove_goal (the_context ()) "-(-(a::'a::ring)) = a"
  (fn _ => [rtac a_lcancel 1, rtac (r_neg RS trans) 1, rtac (l_neg RS sym) 1]);
val minus0 = prove_goal (the_context ()) "- 0 = (0::'a::ring)"
  (fn _ => [rtac a_lcancel 1, rtac (r_neg RS trans) 1,
     rtac (l_zero RS sym) 1]);

(* derived rules for multiplication *)
val m_lcomm = prove_goal (the_context ()) "(a::'a::ring)*(b*c) = b*(a*c)"
  (fn _ => [rtac (m_comm RS trans) 1, rtac (m_assoc RS trans) 1,
     rtac (m_comm RS arg_cong) 1]);
val r_one = prove_goal (the_context ()) "(a::'a::ring) * 1 = a"
  (fn _ => [rtac (m_comm RS trans) 1, rtac l_one 1]);
val r_distr = prove_goal (the_context ()) "(a::'a::ring) * (b + c) = a * b + a * c"
  (fn _ => [rtac (m_comm RS trans) 1, rtac (l_distr RS trans) 1,
     simp_tac (simpset() addsimps [m_comm]) 1]);
(* the following proof is from Jacobson, Basic Algebra I, pp. 88-89 *)
val l_null = prove_goal (the_context ()) "0 * (a::'a::ring) = 0"
  (fn _ => [rtac a_lcancel 1, rtac (l_distr RS sym RS trans) 1,
     simp_tac (simpset() addsimps [r_zero]) 1]);
val r_null = prove_goal (the_context ()) "(a::'a::ring) * 0 = 0"
  (fn _ => [rtac (m_comm RS trans) 1, rtac l_null 1]);
val l_minus = prove_goal (the_context ()) "(-(a::'a::ring)) * b = - (a * b)"
  (fn _ => [rtac a_lcancel 1, rtac (r_neg RS sym RSN (2, trans)) 1,
     rtac (l_distr RS sym RS trans) 1,
     simp_tac (simpset() addsimps [l_null, r_neg]) 1]);
val r_minus = prove_goal (the_context ()) "(a::'a::ring) * (-b) = - (a * b)"
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
