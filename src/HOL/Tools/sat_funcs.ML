(*  Title:      HOL/Tools/sat_funcs.ML
    ID:         $Id$
    Author:     Stephan Merz and Alwen Tiu, QSL Team, LORIA (http://qsl.loria.fr)
    Copyright   2005


Proof reconstruction from SAT solvers.

  Description:
    This file defines several tactics to invoke a proof-producing
    SAT solver on a propositional goal in clausal form.

    We use a sequent presentation of clauses to speed up resolution
    proof reconstruction. 
    We call such clauses as "raw clauses", which are of the form
          [| c1; c2; ...; ck |] ==> False
    where each clause ci is of the form
          [|l1,  l2,  ..., lm |] ==> False,
    where li is a literal  (see also comments in cnf_funcs.ML).

    -- observe that this is the "dualized" version of the standard
       clausal form
           l1' \/ l2' \/ ... \/ lm', where li is the negation normal
       form of ~li'.
       The tactic produces a clause representation of the given goal
       in DIMACS format and invokes a SAT solver, which should return
       a proof consisting of a sequence of resolution steps, indicating
       the two input clauses and the variable resolved upon, and resulting
       in new clauses, leading to the empty clause (i.e., False).
       The tactic replays this proof in Isabelle and thus solves the
       overall goal.

   There are two SAT tactics available. They differ in the CNF transformation
   used. The "sat_tac" uses naive CNF transformation to transform the theorem
   to be proved before giving it to SAT solver. The naive transformation in 
   some worst case can lead to explonential blow up in formula size.
   The other tactic, the "satx_tac" uses the "definitional CNF transformation"
   which produces formula of linear size increase compared to the input formula.
   This transformation introduces new variables. See also cnf_funcs.ML for
   more comments.


 Notes for the current revision:
   - The current version supports only zChaff prover.
   - The environment variable ZCHAFF_HOME must be set to point to
     the directory where zChaff executable resides
   - The environment variable ZCHAFF_VERSION must be set according to
     the version of zChaff used. Current supported version of zChaff:
     zChaff version 2004.11.15

*)

(***************************************************************************)
(** Array of clauses **)

signature CLAUSEARR =
sig
   val init : int -> unit 
   val register_at : int -> Thm.thm -> unit
   val register_list : Thm.thm list -> unit
   val getClause : int -> Thm.thm option
end

structure ClauseArr : CLAUSEARR =
struct

val clauses : ((Thm.thm option) array) ref = ref (Array.array(1, NONE));

fun init size = (clauses := Array.array(size, NONE))

fun register_at i c =  Array.update (!clauses, i, (SOME c))

fun reg_list n nil = ()
  | reg_list n (x::l) = 
     (register_at n x; reg_list (n+1) l)

fun register_list l = reg_list 0 l

fun getClause i = Array.sub (!clauses, i)

end


(***************************************************************************)

signature SAT =
sig
  val trace_sat : bool ref      (* trace tactic *)
  val sat_tac : Tactical.tactic
  val satx_tac : Tactical.tactic
end

functor SATFunc (structure cnf_struct : CNF) : SAT =
struct

structure cnf = cnf_struct

val trace_sat = ref false;	(* debugging flag *)


(* Look up the Isabelle atom corresponding to a DIMACS index in the
   reverse dictionary. This entry should exist, otherwise an error
   is raised.
*)
fun rev_lookup idx dictionary = 
let
   fun rev_assoc [] = NONE
     | rev_assoc ((key, entry)::list) =
       if entry = idx then SOME key else rev_assoc list
in
   the (rev_assoc dictionary)
end;


(* Convert rules of the form
   l1 ==> l2 ==> .. ==> li ==> .. ==> False
    to
   l1 ==> l2 ==> .... ==> ~li
*)
fun swap_prem rslv c = 
let 
    val thm1 = rule_by_tactic (metacut_tac c 1  THEN 
                  (atac 1) THEN (REPEAT_SOME atac)) rslv
in
    rule_by_tactic (ALLGOALS (cnf.weakening_tac)) thm1
end

(*** Proof reconstruction: given two clauses
   [| x1 ; .. ; a ; .. ; xn |] ==> False
   and 
   [| y1 ; .. ; ~a ; .. ; ym |] ==> False , 

   we firt convert the first clause into

   [| x1 ; ... ; xn |] ==> ~a     (using swap_prem)

   and do a resolution with the second clause to produce
   [| y1 ; ... ; x1 ; ... ; xn ; ... ; yn |] ==> False

***)

fun dual (Const("Trueprop",_) $ x) (Const("Trueprop",_) $ y) = dual x y
  | dual (Const("Not",_) $ x) y = (x = y)
  | dual x (Const("Not",_) $ y) = (x = y)
  | dual x y = false

(* Check if an atom has a dual in a list of atoms *)

fun dual_mem x nil = false
  | dual_mem x (y::l) = if (dual x y) then true else dual_mem x l


fun replay_chain sg idx (c::cs) =
let
   val (SOME fc) = ClauseArr.getClause c;

   fun strip_neg (Const("Trueprop", _) $ x) = strip_neg x
     | strip_neg (Const("Not",_) $ x) = x
     | strip_neg x = x

   (* Find out which atom (literal) is used in the resolution *)
   fun res_atom nil l = raise THM ("Proof reconstruction failed!", 0, [])
     | res_atom (x::l1) l2 = 
        if (dual_mem x l2) then strip_neg x
        else res_atom l1 l2

   fun replay old [] = old
     | replay old (cls :: clss) =
       let
          val (SOME icls) = ClauseArr.getClause cls;
          val var = res_atom (prems_of old) (prems_of icls);
          val atom = cterm_of sg var;
          val rslv = instantiate' [] [SOME atom] notI;

          val _ = if (!trace_sat) then
            (
              writeln "-- resolving clause:";
              print_thm old;
              writeln "-- with clause: ";
              print_thm icls;
              writeln "-- using ";
              writeln (string_of_cterm atom)
            ) else ();

          val thm1 = (
              rule_by_tactic (REPEAT_SOME (rtac (swap_prem rslv old))) icls
              handle THM _ =>
              rule_by_tactic (REPEAT_SOME (rtac (swap_prem rslv icls))) old );

          val new = rule_by_tactic distinct_subgoals_tac thm1;
          val _ = if (!trace_sat) then (writeln "-- resulting clause:"; print_thm new)
                  else ()
       in
          replay new clss 
       end
in
   ClauseArr.register_at idx (replay fc cs);
   if (!trace_sat) then (
      writeln ("-- Replay chain successful. " ^ 
               "The resulting clause stored at #" ^ (Int.toString idx))
   ) else ()
end


(* Replay the resolution proof from file prf_file with hypotheses hyps.
   Returns the theorem established by the proof (which is just False).
*)
fun replay_prf sg tab size =
  let
     val prf = Inttab.dest tab;

     fun complete nil = true
       | complete (x::l) = (
           case ClauseArr.getClause x of 
             NONE => false
           | (SOME _) => complete l)

     fun do_chains [] = ()
       | do_chains (pr :: rs) = 
         let val (idx, cls) = pr
         in
            if (complete cls) then  
               (replay_chain sg idx cls; do_chains rs)
            else do_chains (rs @ [pr])
         end
  in
    if (!trace_sat) then (
        writeln "Proof trace from SAT solver: ";
        print prf ; ()
     ) else () ;
     do_chains prf;
     ClauseArr.getClause size
  end;


(***************************************************************************)
(***                  Functions to build the sat tactic                  ***)

(* A trivial tactic, used in preprocessing before calling the main 
   tactic *)

val pre_sat_tac  = (REPEAT (etac conjE 1)) THEN 
                   (REPEAT ((atac 1) ORELSE (etac FalseE 1)))

fun collect_atoms (Const("Trueprop",_) $ x) l = collect_atoms x l
  | collect_atoms (Const("op |", _) $ x $ y) l = 
        collect_atoms x (collect_atoms y l) 
  | collect_atoms x l = if (x mem l) then l else (x::l) 

fun has_duals nil = false
  | has_duals (x::l) = if (dual_mem x l) then true else has_duals l

fun trivial_clause (Const("True",_)) = true
  | trivial_clause c = has_duals (collect_atoms c nil)

(* Remove trivial clauses *)
fun filter_clauses nil = nil
  | filter_clauses (x::l) =
    if (trivial_clause (term_of (cprop_of x))) then filter_clauses l
    else (x:: filter_clauses l)

fun is_true assignment x =
    case (assignment x) of 
      NONE => false
    | SOME b => b

fun get_model dict assignment = 
    map (fn (x,y) => x) (List.filter (fn (x,y) => is_true assignment y) dict)

fun string_of_model sg nil = ""
  | string_of_model sg [x] = Sign.string_of_term sg x
  | string_of_model sg (x::l) = (Sign.string_of_term sg x) ^ ", " ^ (string_of_model sg l)

(* Run external SAT solver with the given clauses. Reconstruct a proof from
   the resulting proof trace of the SAT solver. 
*)

fun rawsat_thm sg prems =
let val thms = filter_clauses prems 
    val (fm, dict) = cnf.cnf2prop thms
    val raw_thms = cnf.cnf2raw_thms thms
in
   let
       val result = SatSolver.invoke_solver "zchaff_with_proofs" fm;
   in
     case result of
       (SatSolver.UNSATISFIABLE (SOME (table, size))) => 
          let val _ = ClauseArr.init (size + 1);
              val _ = ClauseArr.register_list 
                      (map (fn x => (rule_by_tactic distinct_subgoals_tac x)) raw_thms);
              val (SOME thm1) = replay_prf sg table size
          in 
              thm1
          end
      | (SatSolver.SATISFIABLE model) => 
          let val msg = "\nSAT solver found a countermodel:\n{ " ^ 
                        (string_of_model sg (get_model dict model)) ^ " }\n"
          in
                raise THM (msg, 0, [])
          end    
      | _ => raise THM ("SAT solver failed!\n", 0, [])

  end
end

fun cnfsat_basic_tac state = 
let val sg = Thm.sign_of_thm state
in 
  METAHYPS (fn prems => rtac (rawsat_thm sg prems) 1) 1 state
end

(* Tactic for calling external SAT solver, taking as input CNF clauses *)
val cnfsat_tac = pre_sat_tac THEN (IF_UNSOLVED cnfsat_basic_tac)


(* 
   Tactic for calling external SAT solver, taking as input arbitrary formula. 
*)
val sat_tac = cnf.cnf_thin_tac THEN cnfsat_tac;

(* 
  Tactic for calling external SAT solver, taking as input arbitratry formula.
  The input is translated to CNF (in primitive form), possibly introducing
  new literals. 
*)
val satx_tac = cnf.cnfx_thin_tac THEN cnfsat_tac;

end (*of structure*)
