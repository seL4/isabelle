(*  Title:      HOL/Tools/sat_funcs.ML
    ID:         $Id$
    Author:     Stephan Merz and Alwen Tiu, QSL Team, LORIA (http://qsl.loria.fr)
    Author:     Tjark Weber
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

signature SAT =
sig
	val trace_sat : bool ref  (* print trace messages *)
	val sat_tac   : Tactical.tactic
	val satx_tac  : Tactical.tactic
end

functor SATFunc (structure cnf : CNF) : SAT =
struct

val trace_sat = ref false;

val counter = ref 0;

(* ------------------------------------------------------------------------- *)
(* rev_lookup: look up the Isabelle/HOL atom corresponding to a DIMACS       *)
(*      variable index in the dictionary.  This index should exist in the    *)
(*      dictionary, otherwise exception Option is raised.                    *)
(* ------------------------------------------------------------------------- *)

(* 'b -> ('a * 'b) list -> 'a *)

fun rev_lookup idx []                   = raise Option
  | rev_lookup idx ((key, entry)::dict) = if entry=idx then key else rev_lookup idx dict;

(* ------------------------------------------------------------------------- *)
(* swap_prem: convert rules of the form                                      *)
(*       l1 ==> l2 ==> .. ==> li ==> .. ==> False                            *)
(*     to                                                                    *)
(*       l1 ==> l2 ==> .... ==> ~li                                          *)
(* ------------------------------------------------------------------------- *)

fun swap_prem rslv c =
let
	val thm1 = rule_by_tactic (metacut_tac c 1 THEN (atac 1) THEN (REPEAT_SOME atac)) rslv
in
	rule_by_tactic (ALLGOALS (cnf.weakening_tac)) thm1
end;

(* ------------------------------------------------------------------------- *)
(* is_dual: check if two atoms are dual to each other                        *)
(* ------------------------------------------------------------------------- *)

(* Term.term -> Term.term -> bool *)

fun is_dual (Const ("Trueprop", _) $ x) y = is_dual x y
  | is_dual x (Const ("Trueprop", _) $ y) = is_dual x y
  | is_dual (Const ("Not", _) $ x) y      = (x = y)
  | is_dual x (Const ("Not", _) $ y)      = (x = y)
  | is_dual x y                           = false;

(* ------------------------------------------------------------------------- *)
(* dual_mem: check if an atom has a dual in a list of atoms                  *)
(* ------------------------------------------------------------------------- *)

(* Term.term -> Term.term list -> bool *)

fun dual_mem x []      = false
  | dual_mem x (y::ys) = is_dual x y orelse dual_mem x ys;

(* ------------------------------------------------------------------------- *)
(* replay_chain: proof reconstruction: given two clauses                     *)
(*        [| x1 ; .. ; a ; .. ; xn |] ==> False                              *)
(*      and                                                                  *)
(*        [| y1 ; .. ; ~a ; .. ; ym |] ==> False ,                           *)
(*      we first convert the first clause into                               *)
(*        [| x1 ; ... ; xn |] ==> ~a     (using swap_prem)                   *)
(*      and do a resolution with the second clause to produce                *)
(*        [| y1 ; ... ; x1 ; ... ; xn ; ... ; yn |] ==> False                *)
(* ------------------------------------------------------------------------- *)

(* Theory.theory -> Thm.thm option Array.array -> int -> int list -> unit *)

fun replay_chain sg clauses idx (c::cs) =
let
	val fc = (valOf o Array.sub) (clauses, c)

	fun strip_neg (Const ("Trueprop", _) $ x) = strip_neg x
	  | strip_neg (Const ("Not", _) $ x)      = x
	  | strip_neg x                           = x

	(* find out which atom (literal) is used in the resolution *)
	fun res_atom []      _  = raise THM ("Proof reconstruction failed!", 0, [])
	  | res_atom (x::xs) ys = if dual_mem x ys then strip_neg x else res_atom xs ys

	fun replay old []        =
		old
	  | replay old (cl::cls) =
		let
			val icl  = (valOf o Array.sub) (clauses, cl)
			val var  = res_atom (prems_of old) (prems_of icl)
			val atom = cterm_of sg var
			val rslv = instantiate' [] [SOME atom] notI
			val _ = if !trace_sat then
					tracing ("Resolving clause: " ^ string_of_thm old ^
						"\nwith clause: " ^ string_of_thm icl ^
						"\nusing literal " ^ string_of_cterm atom ^ ".")
				else ()
			val thm1 = (rule_by_tactic (REPEAT_SOME (rtac (swap_prem rslv old))) icl
				handle THM _ => rule_by_tactic (REPEAT_SOME (rtac (swap_prem rslv icl))) old)
			val new  = rule_by_tactic distinct_subgoals_tac thm1
			val _    = if !trace_sat then tracing ("Resulting clause: " ^ string_of_thm new) else ()
			val _    = inc counter
		in
			replay new cls
		end

	val _ = Array.update (clauses, idx, SOME (replay fc cs))

	val _ = if !trace_sat then
			tracing ("Replay chain successful; clause stored at #" ^ string_of_int idx)
		else ()
in
	()
end;

(* ------------------------------------------------------------------------- *)
(* replay_proof: replay the resolution proof returned by the SAT solver; cf. *)
(*      SatSolver.proof for details of the proof format.  Returns the        *)
(*      theorem established by the proof (which is just False).              *)
(* ------------------------------------------------------------------------- *)

(* Theory.theory -> Thm.thm option Array.array -> SatSolver.proof -> Thm.thm *)

fun replay_proof sg clauses (clause_table, empty_id) =
let
	(* int -> unit *)
	fun prove_clause id =
		case Array.sub (clauses, id) of
		  SOME _ =>
			()
		| NONE   =>
			let
				val ids = valOf (Inttab.lookup clause_table id)
				val _   = map prove_clause ids
			in
				replay_chain sg clauses id ids
			end

	val _ = counter := 0

	val _ = prove_clause empty_id

	val _ = if !trace_sat then
			tracing (string_of_int (!counter) ^ " resolution steps total.")
		else ()
in
	(valOf o Array.sub) (clauses, empty_id)
end;

(* ------------------------------------------------------------------------- *)
(* Functions to build the sat tactic                                         *)
(* ------------------------------------------------------------------------- *)

(* A trivial tactic, used in preprocessing before calling the main tactic *)
val pre_sat_tac = (REPEAT (etac conjE 1)) THEN (REPEAT ((atac 1) ORELSE (etac FalseE 1)));

fun collect_atoms (Const ("Trueprop", _) $ x) ls = collect_atoms x ls
  | collect_atoms (Const ("op |", _) $ x $ y) ls = collect_atoms x (collect_atoms y ls)
  | collect_atoms x                           ls = x ins ls;

fun has_duals []      = false
  | has_duals (x::xs) = dual_mem x xs orelse has_duals xs;

fun is_trivial_clause (Const ("True", _)) = true
  | is_trivial_clause c                   = has_duals (collect_atoms c []);

(* ------------------------------------------------------------------------- *)
(* rawsat_thm: run external SAT solver with the given clauses.  Reconstructs *)
(*      a proof from the resulting proof trace of the SAT solver.            *)
(* ------------------------------------------------------------------------- *)

fun rawsat_thm sg prems =
let
	val thms       = filter (not o is_trivial_clause o term_of o cprop_of) prems  (* remove trivial clauses *)
	val (fm, dict) = cnf.cnf2prop thms
	val _          = if !trace_sat then tracing "Invoking SAT solver ..." else ()
in
	case SatSolver.invoke_solver "zchaff_with_proofs" fm of
	  SatSolver.UNSATISFIABLE (SOME (clause_table, empty_id)) =>
		let
			val _         = if !trace_sat then
					tracing ("Proof trace from SAT solver:\n" ^
						"clauses: [" ^ commas (map (fn (c, cs) =>
							"(" ^ string_of_int c ^ ", [" ^ commas (map string_of_int cs) ^ "])") (Inttab.dest clause_table)) ^ "]\n" ^
						"empty clause: " ^ string_of_int empty_id)
				else ()
			val raw_thms  = cnf.cnf2raw_thms thms
			val raw_thms' = map (rule_by_tactic distinct_subgoals_tac) raw_thms
			(* initialize the clause array with the original clauses *)
			val max_idx   = valOf (Inttab.max_key clause_table)
			val clauses   = Array.array (max_idx + 1, NONE)
			val _         = fold (fn thm => fn idx => (Array.update (clauses, idx, SOME thm); idx+1)) raw_thms' 0
		in
			replay_proof sg clauses (clause_table, empty_id)
		end
	| SatSolver.UNSATISFIABLE NONE =>
		raise THM ("SAT solver claims the formula to be unsatisfiable, but did not provide a proof", 0, [])
	| SatSolver.SATISFIABLE assignment =>
		let
			val msg = "SAT solver found a countermodel:\n"
				^ (enclose "{" "}"
					o commas
					o map (Sign.string_of_term sg o fst)
					o filter (fn (_, idx) => getOpt (assignment idx, false))) dict
		in
			raise THM (msg, 0, [])
		end
	| SatSolver.UNKNOWN =>
		raise THM ("SAT solver failed to decide the formula", 0, [])
end;

(* ------------------------------------------------------------------------- *)
(* Tactics                                                                   *)
(* ------------------------------------------------------------------------- *)

fun cnfsat_basic_tac state =
let
	val sg = Thm.sign_of_thm state
in
	METAHYPS (fn prems => rtac (rawsat_thm sg prems) 1) 1 state
end;

(* Tactic for calling external SAT solver, taking as input CNF clauses *)
val cnfsat_tac = pre_sat_tac THEN (IF_UNSOLVED cnfsat_basic_tac);

(* Tactic for calling external SAT solver, taking as input arbitrary formula *)
val sat_tac = cnf.cnf_thin_tac THEN cnfsat_tac;

(*
  Tactic for calling external SAT solver, taking as input arbitrary formula.
  The input is translated to CNF (in primitive form), possibly introducing
  new literals.
*)
val satx_tac = cnf.cnfx_thin_tac THEN cnfsat_tac;

end;  (* of structure *)
