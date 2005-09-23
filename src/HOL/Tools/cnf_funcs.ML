(*  Title:      HOL/Tools/cnf_funcs.ML
    ID:         $Id$
    Author:     Alwen Tiu, QSL Team, LORIA (http://qsl.loria.fr)
    Copyright   2005

  Description:
  This file contains functions and tactics to transform a formula into 
  Conjunctive Normal Forms (CNF). 
  A formula in CNF is of the following form:

      (x11 | x12 | .. x1m) & ... & (xm1 | xm2 | ... | xmn)

  where each xij is a literal (i.e., positive or negative propositional
  variables).
  This kind of formula will simply be referred to as CNF.
  A disjunction of literals is referred to as "clause".

  For the purpose of SAT proof reconstruction, we also make use of another
  representation of clauses, which we call the "raw clauses".
  Raw clauses are of the form

      (x1 ==> x2 ==> .. ==> xn ==> False)

  where each xi is a literal. Note that the above raw clause corresponds
  to the clause (x1' | ... | xn'), where each xi' is the negation normal
  form of ~xi.

  Notes for current revision:
  - the "definitional CNF transformation" (anything with prefix cnfx_ )
    introduces new literals of the form (lit_i) where i is an integer.
    For these functions to work, it is necessary that no free variables
    which names are of the form lit_i appears in the formula being
    transformed.
*)


(***************************************************************************)

signature CNF =
sig
  val cnf_tac : Tactical.tactic
  val cnf_thin_tac : Tactical.tactic
  val cnfx_thin_tac : Tactical.tactic
  val cnf_concl_tac : Tactical.tactic
  val weakening_tac : int -> Tactical.tactic
  val mk_cnf_thm : Sign.sg -> Term.term -> Thm.thm
  val mk_cnfx_thm : Sign.sg -> Term.term ->  Thm.thm
  val is_atm : Term.term -> bool
  val is_lit : Term.term -> bool
  val is_clause : Term.term -> bool
  val is_raw_clause : Term.term -> bool
  val cnf2raw_thm : Thm.thm -> Thm.thm
  val cnf2raw_thms : Thm.thm list -> Thm.thm list
  val cnf2prop : Thm.thm list -> (PropLogic.prop_formula * ((Term.term * int) list))
end


(***************************************************************************)

structure cnf : CNF =
struct

val cur_thy = the_context();
val mk_disj = HOLogic.mk_disj;
val mk_conj = HOLogic.mk_conj;
val mk_imp  = HOLogic.mk_imp;
val Not = HOLogic.Not;
val false_const = HOLogic.false_const;
val true_const = HOLogic.true_const;


(* Index for new literals *)
val lit_id = ref 0;

fun thm_by_auto G =
    prove_goal cur_thy G (fn prems => [cut_facts_tac prems 1, Auto_tac]);

(***************************************************************************)


val cnf_eq_id = thm_by_auto "(P :: bool) = P";

val cnf_eq_sym = thm_by_auto "(P :: bool) = Q ==> Q = P";

val cnf_not_true_false = thm_by_auto "~True = False";

val cnf_not_false_true = thm_by_auto "~False = True";

val cnf_imp2disj = thm_by_auto "(P --> Q) = (~P | Q)";

val cnf_neg_conj = thm_by_auto "(~(P & Q)) = (~P | ~Q)";

val cnf_neg_disj = thm_by_auto "(~(P | Q)) = (~P & ~Q)";

val cnf_neg_imp = thm_by_auto "(~(P --> Q)) = (P & ~Q)";

val cnf_double_neg = thm_by_auto "(~~P) = P";
 
val cnf_disj_conj = thm_by_auto "((P & Q) | R) = ((P | R) & (Q | R))";

val cnf_disj_imp = thm_by_auto "((P --> Q) | R) = (~P | (Q | R))";

val cnf_disj_disj = thm_by_auto "((P | Q) | R) = (P | (Q | R))";

val cnf_disj_false = thm_by_auto "(False | P) = P";

val cnf_disj_true = thm_by_auto "(True | P) = True";

val cnf_disj_not_false = thm_by_auto "(~False | P) = True";

val cnf_disj_not_true = thm_by_auto "(~True | P) = P";

val cnf_eq_trans = thm_by_auto "[| ( (P::bool) = Q) ; Q = R |] ==> (P = R)";

val cnf_comb2eq = thm_by_auto "[| P = Q ; R = T |] ==> (P & R) = (Q & T)";

val cnf_disj_sym = thm_by_auto "(P | Q) = (Q | P)";

val cnf_cong_disj = thm_by_auto "(P = Q) ==> (P | R) = (Q | R)";

val icnf_elim_disj1 = thm_by_auto "Q = R  ==> (~P | Q) = (P --> R)";

val icnf_elim_disj2 = thm_by_auto "Q = R ==> (P | Q) = (~P --> R)";

val icnf_neg_false1 = thm_by_auto "(~P) = (P --> False)";

val icnf_neg_false2 = thm_by_auto "P = (~P --> False)";

val weakening_thm = thm_by_auto "[| P ; Q |] ==> Q";

val cnf_newlit = thm_by_auto 
    "((P & Q) | R) = (EX (x :: bool). (~x | P) & (~x | Q) & (x | ~P | ~ Q) & (x | R))";

val cnf_all_ex = thm_by_auto 
    "(ALL (x :: bool). (P x = Q x)) ==> (EX x. P x) = (EX x. Q x)";

(* [| P ; ~P |] ==> False *)
val cnf_notE = read_instantiate [("R", "False")] (rotate_prems 1 notE);

val cnf_dneg = thm_by_auto "P ==> ~~P";

val cnf_neg_disjI = thm_by_auto "[| ~P ; ~Q |] ==> ~(P | Q)";

val cnf_eq_imp = thm_by_auto "[|((P::bool) = Q) ; P |] ==> Q";

(***************************************************************************)

fun is_atm (Const("Trueprop",_) $ x) = is_atm x
  | is_atm (Const("==>",_) $ x $ y) = false
  | is_atm (Const("False",_)) = false
  | is_atm (Const("True", _)) = false
  | is_atm (Const("op &",_) $ x $ y) = false
  | is_atm (Const("op |",_) $ x $ y) = false
  | is_atm (Const("op -->",_) $ x $ y) = false
  | is_atm (Const("Not",_) $ x) = false
  | is_atm t = true


fun is_lit (Const("Trueprop",_) $ x) = is_lit x
  | is_lit (Const("Not", _) $ x) = is_atm x
  | is_lit t = is_atm t

fun is_clause (Const("Trueprop",_) $ x) = is_clause x
  | is_clause (Const("op |", _) $ x $ y) = 
          (is_clause x) andalso (is_clause y)
  | is_clause t = is_lit t

fun is_cnf (Const("Trueprop", _) $ x) = is_cnf x
  | is_cnf (Const("op &",_) $ x $ y) = (is_cnf x) andalso (is_cnf y)
  | is_cnf t = is_clause t


(* Checking for raw clauses *)
fun is_raw_clause (Const("Trueprop",_) $ x) = is_raw_clause x
  | is_raw_clause (Const("==>",_) $ x $ 
                   (Const("Trueprop",_) $ Const("False",_))) = is_lit x
  | is_raw_clause (Const("==>",_) $ x $ y) = 
        (is_lit x) andalso (is_raw_clause y)
  | is_raw_clause t = false



(* Translate a CNF clause into a raw clause *)
fun cnf2raw_thm c =
let val nc = c RS cnf_notE
in
rule_by_tactic (REPEAT_SOME (fn i => 
               rtac cnf_dneg i 
               ORELSE rtac cnf_neg_disjI i)) nc
handle THM _ => nc
end

fun cnf2raw_thms nil = nil
  | cnf2raw_thms (c::l) =
    let val t = term_of (cprop_of c)
    in
       if (is_clause t) then (cnf2raw_thm c) :: cnf2raw_thms l
       else cnf2raw_thms l
    end


(* Translating HOL formula (in CNF) to PropLogic formula. Returns also an
   association list, relating literals to their indices *)

local
  (* maps atomic formulas to variable numbers *)
  val dictionary : ((Term.term * int) list) ref = ref nil;
  val var_count = ref 0;
  val pAnd = PropLogic.And;
  val pOr = PropLogic.Or;
  val pNot = PropLogic.Not;
  val pFalse = PropLogic.False;
  val pTrue = PropLogic.True;
  val pVar = PropLogic.BoolVar;

  fun mk_clause (Const("Trueprop",_) $ x) = mk_clause x
    | mk_clause (Const("op |",_) $ x $ y) = pOr(mk_clause x, mk_clause y)
    | mk_clause (Const("Not", _) $ x) = pNot (mk_clause x)
    | mk_clause (Const("True",_)) = pTrue
    | mk_clause (Const("False",_)) = pFalse
    | mk_clause t =
      let
         val idx = AList.lookup op= (!dictionary) t
      in
         case idx of
            (SOME x) => pVar x
           | NONE =>
             let
                val new_var = inc var_count
             in
                dictionary := (t, new_var) :: (!dictionary);
                pVar new_var
             end
      end

   fun mk_clauses nil = pTrue
     | mk_clauses (x::nil) = mk_clause x
     | mk_clauses (x::l) = pAnd(mk_clause x, mk_clauses l)

in
   fun cnf2prop thms =
   (
     var_count := 0;
     dictionary := nil;
     (mk_clauses (map (fn x => term_of (cprop_of x)) thms), !dictionary)
   )
end



(* Instantiate a theorem with a list of terms *)
fun inst_thm sign l thm = 
  instantiate' [] (map (fn x => SOME (cterm_of sign x)) l) thm

(* Tactic to remove the first hypothesis of the first subgoal. *) 
fun weakening_tac i = (dtac weakening_thm i) THEN (atac (i+1));

(* Tactic for removing the n first hypotheses of the first subgoal. *)
fun weakenings_tac 0 state = all_tac state
  | weakenings_tac n state = ((weakening_tac  1) THEN (weakenings_tac (n-1))) state


(* 
  Transform a formula into a "head" negation normal form, that is, 
  the top level connective is not a negation, with the exception
  of negative literals. Returns the pair of the head normal term with
  the theorem corresponding to the transformation.
*)
fun head_nnf sign (Const("Not",_)  $ (Const("op &",_) $ x $ y)) =
    let val t = mk_disj(Not $ x, Not $ y)
        val neg_thm = inst_thm sign [x, y] cnf_neg_conj 
    in
        (t, neg_thm)
    end

  | head_nnf sign (Const("Not", _) $ (Const("op |",_) $ x $ y)) =
    let val t = mk_conj(Not $ x, Not $ y)
        val neg_thm =  inst_thm sign [x, y] cnf_neg_disj; 
    in
        (t, neg_thm)
    end

  | head_nnf sign (Const("Not", _) $ (Const("op -->",_) $ x $ y)) = 
    let val t = mk_conj(x, Not $ y)
        val neg_thm = inst_thm sign [x, y] cnf_neg_imp
    in
        (t, neg_thm)
    end

  | head_nnf sign (Const("Not",_) $ (Const("Not",_) $ x)) =
    (x, inst_thm sign [x] cnf_double_neg)

  | head_nnf sign (Const("Not",_) $ Const("True",_)) = 
      (false_const, cnf_not_true_false)

  | head_nnf sign (Const("Not",_) $ Const("False",_)) = 
      (true_const, cnf_not_false_true)  

  | head_nnf sign t = 
    (t, inst_thm sign [t] cnf_eq_id)


(***************************************************************************)
(*                  Tactics for simple CNF transformation                  *)

(* A naive procedure for CNF transformation:
   Given any t, produce a theorem t = t', where t' is in
   conjunction normal form 
*)
fun mk_cnf_thm sign (Const("Trueprop",_) $ x) = mk_cnf_thm sign x
  | mk_cnf_thm sign (t as (Const(_,_))) = inst_thm sign [t] cnf_eq_id
  | mk_cnf_thm sign (t as (Free(_,_))) =  inst_thm sign [t] cnf_eq_id
 
  | mk_cnf_thm sign (Const("op -->", _) $ x $ y) =
       let val thm1 = inst_thm sign [x, y] cnf_imp2disj;
           val thm2 = mk_cnf_thm sign (mk_disj(Not $ x, y));
       in
           cnf_eq_trans OF [thm1, thm2]
       end

  | mk_cnf_thm sign (Const("op &", _) $ x $ y) = 
       let val cnf1 = mk_cnf_thm sign x;
           val cnf2 = mk_cnf_thm sign y;
       in
           cnf_comb2eq OF [cnf1, cnf2]
       end

  | mk_cnf_thm sign (Const("Not",_) $ Const("True",_)) = 
        cnf_not_true_false

  | mk_cnf_thm sign (Const("Not",_) $ Const("False",_)) = 
        cnf_not_false_true

  | mk_cnf_thm sign (t as (Const("Not", _) $ x)) =
      ( 
       if (is_atm x) then inst_thm sign [t] cnf_eq_id
       else
         let val (t1, hn_thm) = head_nnf sign t
             val cnf_thm = mk_cnf_thm sign t1
         in
             cnf_eq_trans OF [hn_thm, cnf_thm]
         end
       ) 

  | mk_cnf_thm sign (Const("op |",_) $ (Const("op &", _) $ p $ q) $ r) =
       let val thm1 = inst_thm sign [p, q, r] cnf_disj_conj;
           val thm2 = mk_cnf_thm sign (mk_conj(mk_disj(p, r), mk_disj(q,r)));
       in
          cnf_eq_trans OF [thm1, thm2]
       end

  | mk_cnf_thm sign (Const("op |",_) $ (Const("op |", _) $ p $ q) $ r) =
       let val thm1 = inst_thm sign [p,q,r] cnf_disj_disj;
           val thm2 = mk_cnf_thm sign (mk_disj(p, mk_disj(q,r)));
       in
          cnf_eq_trans OF [thm1, thm2]
       end

  | mk_cnf_thm sign (Const("op |",_) $ (Const("op -->", _) $ p $ q) $ r) =                       
       let val thm1 = inst_thm sign [p,q,r] cnf_disj_imp;
           val thm2 = mk_cnf_thm sign (mk_disj(Not $ p, mk_disj(q, r)));
       in
           cnf_eq_trans OF [thm1, thm2]
       end

  | mk_cnf_thm sign (Const("op |",_) $ Const("False",_) $ p) =
       let val thm1 = inst_thm sign [p] cnf_disj_false;
           val thm2 = mk_cnf_thm sign p
       in
           cnf_eq_trans OF [thm1, thm2]
       end

  | mk_cnf_thm sign (Const("op |",_) $ Const("True",_) $ p) =
       inst_thm sign [p] cnf_disj_true

  | mk_cnf_thm sign (Const("op |",_) $ (Const("Not",_) $ Const("True",_)) $ p) =
       let val thm1 = inst_thm sign [p] cnf_disj_not_true;
           val thm2 = mk_cnf_thm sign p
       in
           cnf_eq_trans OF [thm1, thm2]
       end

  | mk_cnf_thm sign (Const("op |",_) $ (Const("Not",_) $ Const("False",_)) $ p) =
       inst_thm sign [p] cnf_disj_not_false

  | mk_cnf_thm sign (t as (Const("op |",_) $ p $ q)) = 
       if (is_lit p) then
          (
            if (is_clause t) then inst_thm sign [t] cnf_eq_id
            else 
             let val thm1 = inst_thm sign [p, q] cnf_disj_sym;
                 val thm2 = mk_cnf_thm sign (mk_disj(q, p))
             in
                cnf_eq_trans OF [thm1, thm2]
             end
          )
       else 
            let val (u, thm1) = head_nnf sign p;
                val thm2 = inst_thm sign [p,u,q] cnf_cong_disj;
                val thm3 = mk_cnf_thm sign (mk_disj(u, q))
            in
                cnf_eq_trans OF [(thm1 RS thm2), thm3]
            end

 | mk_cnf_thm sign t = inst_thm sign [t] cnf_eq_id
    (* error ("I don't know how to handle the formula " ^ 
                          (Sign.string_of_term sign t))
    *)

fun term_of_thm c = term_of (cprop_of c)


(* Transform a given list of theorems (thms) into CNF *)

fun mk_cnf_thms sg nil = nil
  | mk_cnf_thms sg (x::l) = 
    let val t = term_of_thm x
    in
      if (is_clause t) then x :: mk_cnf_thms sg l
      else 
       let val thm1 = mk_cnf_thm sg t
           val thm2 = cnf_eq_imp OF [thm1, x]
       in 
           thm2 :: mk_cnf_thms sg l
       end
    end


(* Count the number of hypotheses in a formula *)
fun num_of_hyps (Const("Trueprop", _) $ x) = num_of_hyps x
  | num_of_hyps (Const("==>",_) $ x $ y) = 1 + (num_of_hyps y)
  | num_of_hyps t = 0

(* Tactic for converting to CNF (in primitive form): 
   it takes the first subgoal of the proof state, transform all its
   hypotheses into CNF (in primivite form) and remove the original 
   hypotheses.
*)
fun cnf_thin_tac state =
let val sg = Thm.sign_of_thm state
in
case (prems_of state) of 
  [] => Seq.empty
| (subgoal::_) => 
  let 
    val n = num_of_hyps (strip_all_body subgoal);
    val tac1 = METAHYPS (fn l => cut_facts_tac (mk_cnf_thms sg l) 1) 1
  in
    (tac1 THEN weakenings_tac n THEN (REPEAT (etac conjE 1)) ) state
  end
end

(* Tactic for converting to CNF (in primitive form), keeping 
   the original hypotheses. *)

fun cnf_tac state =
let val sg = Thm.sign_of_thm state
in
case (prems_of state) of 
  [] => Seq.empty
| (subgoal::_) => 
   METAHYPS (fn l => cut_facts_tac (mk_cnf_thms sg l) 1 
                    THEN (REPEAT (etac conjE 1)) ) 1 state
end


(***************************************************************************)
(*            CNF transformation by introducing new literals               *)

(*** IMPORTANT: 
  This transformation uses variables of the form "lit_i", where i is a natural
  number. For the transformation to work, these variables must not already
  occur freely in the formula being transformed.
***)

fun ext_conj x p q r =
   mk_conj(
    mk_disj(Not $ x, p),
    mk_conj(
      mk_disj(Not $ x, q),
      mk_conj(
        mk_disj(x, mk_disj(Not $ p, Not $ q)),
        mk_disj(x, r)
      )
    )
   )


(* Transform to CNF in primitive forms, possibly introduce extra variables *)
fun mk_cnfx_thm sign (Const("Trueprop",_) $ x) = mk_cnfx_thm sign x 
  | mk_cnfx_thm sign (t as (Const(_,_)))  = inst_thm sign [t] cnf_eq_id
  | mk_cnfx_thm sign (t as (Free(_,_)))  = inst_thm sign [t] cnf_eq_id
  | mk_cnfx_thm sign (Const("op -->", _) $ x $ y)  =
       let val thm1 = inst_thm sign [x, y] cnf_imp2disj;
           val thm2 = mk_cnfx_thm sign (mk_disj(Not $ x, y)) 
       in
           cnf_eq_trans OF [thm1, thm2]
       end

  | mk_cnfx_thm sign (Const("op &", _) $ x $ y)  = 
       let val cnf1 = mk_cnfx_thm sign x
           val cnf2 = mk_cnfx_thm sign y
       in
           cnf_comb2eq OF [cnf1, cnf2]
       end

  | mk_cnfx_thm sign (Const("Not",_) $ Const("True",_)) = 
        cnf_not_true_false

  | mk_cnfx_thm sign (Const("Not",_) $ Const("False",_))  = 
        cnf_not_false_true

  | mk_cnfx_thm sign (t as (Const("Not", _) $ x))  =
      ( 
       if (is_atm x) then inst_thm sign [t] cnf_eq_id
       else
         let val (t1, hn_thm) = head_nnf sign t
             val cnf_thm = mk_cnfx_thm sign t1 
         in
             cnf_eq_trans OF [hn_thm, cnf_thm]
         end
       ) 

  | mk_cnfx_thm sign (Const("op |",_) $ (Const("op &", _) $ p $ q) $ r)  =
      if (is_lit r) then
        let val thm1 = inst_thm sign [p, q, r] cnf_disj_conj
            val thm2 = mk_cnfx_thm sign (mk_conj(mk_disj(p, r), mk_disj(q,r)))
        in
           cnf_eq_trans OF [thm1, thm2]
        end
      else cnfx_newlit sign p q r 

  | mk_cnfx_thm sign (Const("op |",_) $ (Const("op |", _) $ p $ q) $ r)  =
       let val thm1 = inst_thm sign [p,q,r] cnf_disj_disj
           val thm2 = mk_cnfx_thm sign (mk_disj(p, mk_disj(q,r))) 
       in
          cnf_eq_trans OF [thm1, thm2]
       end

  | mk_cnfx_thm sign (Const("op |",_) $ (Const("op -->", _) $ p $ q) $ r) =                       
       let val thm1 = inst_thm sign [p,q,r] cnf_disj_imp
           val thm2 = mk_cnfx_thm sign (mk_disj(Not $ p, mk_disj(q, r))) 
       in
           cnf_eq_trans OF [thm1, thm2]
       end

  | mk_cnfx_thm sign (Const("op |",_) $ Const("False",_) $ p)  =
       let val thm1 = inst_thm sign [p] cnf_disj_false;
           val thm2 = mk_cnfx_thm sign p 
       in
           cnf_eq_trans OF [thm1, thm2]
       end

  | mk_cnfx_thm sign (Const("op |",_) $ Const("True",_) $ p)  =
       inst_thm sign [p] cnf_disj_true

  | mk_cnfx_thm sign (Const("op |",_) $ (Const("Not",_) $ Const("True",_)) $ p)  =
       let val thm1 = inst_thm sign [p] cnf_disj_not_true;
           val thm2 = mk_cnfx_thm sign p 
       in
           cnf_eq_trans OF [thm1, thm2]
       end

  | mk_cnfx_thm sign (Const("op |",_) $ (Const("Not",_) $ Const("False",_)) $ p)  =
       inst_thm sign [p] cnf_disj_not_false

  | mk_cnfx_thm sign (t as (Const("op |",_) $ p $ q))  = 
       if (is_lit p) then
          (
            if (is_clause t) then inst_thm sign [t] cnf_eq_id
            else 
             let val thm1 = inst_thm sign [p, q] cnf_disj_sym
                 val thm2 = mk_cnfx_thm sign (mk_disj(q, p)) 
             in
                cnf_eq_trans OF [thm1, thm2]
             end
          )
       else 
            let val (u, thm1) = head_nnf sign p
                val thm2 = inst_thm sign [p,u,q] cnf_cong_disj
                val thm3 = mk_cnfx_thm sign (mk_disj(u, q)) 
            in
                cnf_eq_trans OF [(thm1 RS thm2), thm3]
            end

 | mk_cnfx_thm sign t  = error ("I don't know how to handle the formula " ^ 
                          (Sign.string_of_term sign t))

and cnfx_newlit sign p q r  = 
   let val lit = read ("lit_" ^ (Int.toString (!lit_id)) ^ " :: bool")
       val _ = (lit_id := !lit_id + 1)
       val ct_lit = cterm_of sign lit
       val x_conj = ext_conj lit p q r
       val thm1 = inst_thm sign [p,q,r] cnf_newlit
       val thm2 = mk_cnfx_thm sign x_conj 
       val thm3 = forall_intr ct_lit thm2
       val thm4 = strip_shyps (thm3 COMP allI)
       val thm5 = strip_shyps (thm4 RS cnf_all_ex)
   in
       cnf_eq_trans OF [thm1, thm5]
   end


(* Theorems for converting formula into CNF (in primitive form), with 
   new extra variables *)


fun mk_cnfx_thms sg nil = nil
  | mk_cnfx_thms sg (x::l) = 
    let val t = term_of_thm x
    in
      if (is_clause t) then x :: mk_cnfx_thms sg l
      else 
       let val thm1 = mk_cnfx_thm sg t
           val thm2 = cnf_eq_imp OF [thm1,x]
       in 
           thm2 :: mk_cnfx_thms sg l
       end
    end


(* Tactic for converting hypotheses into CNF, possibly
   introducing new variables *)

fun cnfx_thin_tac state =
let val sg = Thm.sign_of_thm state
in
case (prems_of state) of 
  [] => Seq.empty
| (subgoal::_) => 
   let val n = num_of_hyps (strip_all_body subgoal);
       val tac1 =  METAHYPS (fn l => cut_facts_tac (mk_cnfx_thms sg l) 1) 1
   in
      EVERY [tac1, weakenings_tac n, 
             REPEAT (etac conjE 1 ORELSE etac exE 1)] state
   end
end

(* Tactic for converting the conclusion of a goal into CNF *)

fun get_concl (Const("Trueprop", _) $ x) = get_concl x
  | get_concl (Const("==>",_) $ x $ y) = get_concl y
  | get_concl t = t

fun cnf_concl_tac' state =
case (prems_of state) of 
  [] => Seq.empty
| (subgoal::_) =>
  let val sg = Thm.sign_of_thm state
      val c = get_concl subgoal
      val thm1 = (mk_cnf_thm sg c) RS cnf_eq_sym
      val thm2 = thm1 RS subst
  in
    rtac thm2 1 state
  end

val cnf_concl_tac  = METAHYPS (fn l => cnf_concl_tac') 1 


end (*of structure*)
