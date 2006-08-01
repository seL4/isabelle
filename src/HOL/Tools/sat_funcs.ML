(*  Title:      HOL/Tools/sat_funcs.ML
    ID:         $Id$
    Author:     Stephan Merz and Alwen Tiu, QSL Team, LORIA (http://qsl.loria.fr)
    Author:     Tjark Weber
    Copyright   2005-2006


Proof reconstruction from SAT solvers.

  Description:
    This file defines several tactics to invoke a proof-producing
    SAT solver on a propositional goal in clausal form.

    We use a sequent presentation of clauses to speed up resolution
    proof reconstruction.
    We call such clauses "raw clauses", which are of the form
          x1; ...; xn; c1; c2; ...; ck |- False
    (note the use of |- instead of ==>, i.e. of Isabelle's (meta-)hyps here),
    where each clause ci is of the form
          ~ (l1 | l2 | ... | lm) ==> False,
    where each xi and each li is a literal (see also comments in cnf_funcs.ML).

    This does not work for goals containing schematic variables!

      The tactic produces a clause representation of the given goal
      in DIMACS format and invokes a SAT solver, which should return
      a proof consisting of a sequence of resolution steps, indicating
      the two input clauses, and resulting in new clauses, leading to
      the empty clause (i.e. "False").  The tactic replays this proof
      in Isabelle and thus solves the overall goal.

  There are two SAT tactics available.  They differ in the CNF transformation
  used. "sat_tac" uses naive CNF transformation to transform the theorem to be
  proved before giving it to the SAT solver.  The naive transformation in the
  worst case can lead to an exponential blow up in formula size.  The other
  tactic, "satx_tac", uses "definitional CNF transformation" which attempts to
  produce a formula of linear size increase compared to the input formula, at
  the cost of possibly introducing new variables.  See cnf_funcs.ML for more
  comments on the CNF transformation.

  The SAT solver to be used can be set via the "solver" reference.  See
  sat_solvers.ML for possible values, and etc/settings for required (solver-
  dependent) configuration settings.  To replay SAT proofs in Isabelle, you
  must of course use a proof-producing SAT solver in the first place.

  Proofs are replayed only if "!quick_and_dirty" is false.  If
  "!quick_and_dirty" is true, the theorem (in case the SAT solver claims its
  negation to be unsatisfiable) is proved via an oracle.
*)

signature SAT =
sig
	val trace_sat : bool ref    (* print trace messages *)
	val solver    : string ref  (* name of SAT solver to be used *)
	val counter   : int ref     (* number of resolution steps during last proof replay *)
	val sat_tac   : int -> Tactical.tactic
	val satx_tac  : int -> Tactical.tactic
end

functor SATFunc (structure cnf : CNF) : SAT =
struct

val trace_sat = ref false;

val solver = ref "zchaff_with_proofs";  (* see HOL/Tools/sat_solver.ML for possible values *)

val counter = ref 0;

(* Thm.thm *)
val resolution_thm =  (* "[| P ==> False; ~P ==> False |] ==> False" *)
	let
		val cterm = cterm_of (the_context ())
		val Q     = Var (("Q", 0), HOLogic.boolT)
		val False = HOLogic.false_const
	in
		Thm.instantiate ([], [(cterm Q, cterm False)]) case_split_thm
	end;

(* Thm.cterm *)
val cP = cterm_of (theory_of_thm resolution_thm) (Var (("P", 0), HOLogic.boolT));

(* ------------------------------------------------------------------------- *)
(* CLAUSE: during proof reconstruction, three kinds of clauses are           *)
(*      distinguished:                                                       *)
(*      1. NO_CLAUSE: clause not proved (yet)                                *)
(*      2. ORIG_CLAUSE: a clause as it occurs in the original problem        *)
(*      3. RAW_CLAUSE: a raw clause, with additional precomputed information *)
(*         (a mapping from int's to its literals) for faster proof           *)
(*         reconstruction                                                    *)
(* ------------------------------------------------------------------------- *)

datatype CLAUSE = NO_CLAUSE
                | ORIG_CLAUSE of Thm.thm
                | RAW_CLAUSE of Thm.thm * Thm.cterm Inttab.table;

(* ------------------------------------------------------------------------- *)
(* resolve_raw_clauses: given a non-empty list of raw clauses, we fold       *)
(*      resolution over the list (starting with its head), i.e. with two raw *)
(*      clauses                                                              *)
(*         x1; ... ; a; ...; xn |- False                                     *)
(*      and                                                                  *)
(*        y1; ... ; a'; ...; ym |- False                                     *)
(*      (where a and a' are dual to each other), we convert the first clause *)
(*      to                                                                   *)
(*        x1; ...; xn |- a ==> False ,                                       *)
(*      the second clause to                                                 *)
(*        y1; ...; ym |- a' ==> False                                        *)
(*      and then perform resolution with                                     *)
(*        [| ?P ==> False; ~?P ==> False |] ==> False                        *)
(*      to produce                                                           *)
(*        x1; ...; xn; y1; ...; ym |- False                                  *)
(*      Each clause is accompanied with a table mapping integers (positive   *)
(*      for positive literals, negative for negative literals, and the same  *)
(*      absolute value for dual literals) to the actual literals as cterms.  *)
(* ------------------------------------------------------------------------- *)

(* (Thm.thm * Thm.cterm Inttab.table) list -> Thm.thm * Thm.cterm Inttab.table *)

fun resolve_raw_clauses [] =
	raise THM ("Proof reconstruction failed (empty list of resolvents)!", 0, [])
  | resolve_raw_clauses (c::cs) =
	let
		(* find out which two hyps are used in the resolution *)
		local exception RESULT of int * Thm.cterm * Thm.cterm in
			(* Thm.cterm Inttab.table -> Thm.cterm Inttab.table -> int * Thm.cterm * Thm.cterm *)
			fun find_res_hyps hyp1_table hyp2_table = (
				Inttab.fold (fn (i, hyp1) => fn () =>
					case Inttab.lookup hyp2_table (~i) of
					  SOME hyp2 => raise RESULT (i, hyp1, hyp2)
					| NONE      => ()) hyp1_table ();
				raise THM ("Proof reconstruction failed (no literal for resolution)!", 0, [])
			) handle RESULT x => x
		end

		(* Thm.thm * Thm.cterm Inttab.table -> Thm.thm * Thm.cterm Inttab.table -> Thm.thm * Thm.cterm Inttab.table *)
		fun resolution (c1, hyp1_table) (c2, hyp2_table) =
		let
			val _ = if !trace_sat then
					tracing ("Resolving clause: " ^ string_of_thm c1 ^ " (hyps: " ^ space_implode ", " (map (Sign.string_of_term (theory_of_thm c1)) (#hyps (rep_thm c1)))
						^ ")\nwith clause: " ^ string_of_thm c2 ^ " (hyps: " ^ space_implode ", " (map (Sign.string_of_term (theory_of_thm c2)) (#hyps (rep_thm c2))) ^ ")")
				else ()

			(* the two literals used for resolution *)
			val (i1, hyp1, hyp2) = find_res_hyps hyp1_table hyp2_table
			val hyp1_is_neg      = i1 < 0

			val c1' = Thm.implies_intr hyp1 c1  (* Gamma1 |- hyp1 ==> False *)
			val c2' = Thm.implies_intr hyp2 c2  (* Gamma2 |- hyp2 ==> False *)

			val res_thm =  (* |- (lit ==> False) ==> (~lit ==> False) ==> False *)
				let
					val cLit = snd (Thm.dest_comb (if hyp1_is_neg then hyp2 else hyp1))  (* strip Trueprop *)
				in
					Thm.instantiate ([], [(cP, cLit)]) resolution_thm
				end

			val _ = if !trace_sat then
					tracing ("Resolution theorem: " ^ string_of_thm res_thm)
				else ()

			val c_new = Thm.implies_elim (Thm.implies_elim res_thm (if hyp1_is_neg then c2' else c1')) (if hyp1_is_neg then c1' else c2')  (* Gamma1, Gamma2 |- False *)

			(* since the mapping from integers to literals should be injective *)
			(* (over different clauses), 'K true' here should be equivalent to *)
			(* 'op=' (but faster)                                              *)
			val hypnew_table = Inttab.merge (K true) (Inttab.delete i1 hyp1_table, Inttab.delete (~i1) hyp2_table)

			val _ = if !trace_sat then
					tracing ("Resulting clause: " ^ string_of_thm c_new ^ " (hyps: " ^ space_implode ", " (map (Sign.string_of_term (theory_of_thm c_new)) (#hyps (rep_thm c_new))) ^ ")")
				else ()
			val _ = inc counter
		in
			(c_new, hypnew_table)
		end
	in
		fold resolution cs c
	end;

(* ------------------------------------------------------------------------- *)
(* replay_proof: replays the resolution proof returned by the SAT solver;    *)
(*      cf. SatSolver.proof for details of the proof format.  Updates the    *)
(*      'clauses' array with derived clauses, and returns the derived clause *)
(*      at index 'empty_id' (which should just be "False" if proof           *)
(*      reconstruction was successful, with the used clauses as hyps).       *)
(*      'atom_table' must contain an injective mapping from all atoms that   *)
(*      occur (as part of a literal) in 'clauses' to positive integers.      *)
(* ------------------------------------------------------------------------- *)

(* int Termtab.table -> CLAUSE Array.array -> SatSolver.proof -> Thm.thm *)

fun replay_proof atom_table clauses (clause_table, empty_id) =
let
	(* Thm.cterm -> int option *)
	fun index_of_literal chyp = (
		case (HOLogic.dest_Trueprop o term_of) chyp of
		  (Const ("Not", _) $ atom) =>
			SOME (~(valOf (Termtab.lookup atom_table atom)))
		| atom =>
			SOME (valOf (Termtab.lookup atom_table atom))
	) handle TERM _ => NONE;  (* 'chyp' is not a literal *)

	(* int -> Thm.thm * Thm.cterm Inttab.table *)
	fun prove_clause id =
		case Array.sub (clauses, id) of
		  RAW_CLAUSE clause =>
			clause
		| ORIG_CLAUSE thm =>
			(* convert the original clause *)
			let
				val _         = if !trace_sat then tracing ("Using original clause #" ^ string_of_int id) else ()
				val raw       = cnf.clause2raw_thm thm
				val lit_table = fold (fn chyp => fn lit_table => (case index_of_literal chyp of
					  SOME i => Inttab.update_new (i, chyp) lit_table
					| NONE   => lit_table)) (#hyps (Thm.crep_thm raw)) Inttab.empty
				val clause    = (raw, lit_table)
				val _         = Array.update (clauses, id, RAW_CLAUSE clause)
			in
				clause
			end
		| NO_CLAUSE =>
			(* prove the clause, using information from 'clause_table' *)
			let
				val _      = if !trace_sat then tracing ("Proving clause #" ^ string_of_int id ^ " ...") else ()
				val ids    = valOf (Inttab.lookup clause_table id)
				val clause = resolve_raw_clauses (map prove_clause ids)
				val _      = Array.update (clauses, id, RAW_CLAUSE clause)
				val _      = if !trace_sat then tracing ("Replay chain successful; clause stored at #" ^ string_of_int id) else ()
			in
				clause
			end

	val _            = counter := 0
	val empty_clause = fst (prove_clause empty_id)
	val _            = if !trace_sat then tracing ("Proof reconstruction successful; " ^ string_of_int (!counter) ^ " resolution step(s) total.") else ()
in
	empty_clause
end;

(* ------------------------------------------------------------------------- *)
(* string_of_prop_formula: return a human-readable string representation of  *)
(*      a 'prop_formula' (just for tracing)                                  *)
(* ------------------------------------------------------------------------- *)

(* PropLogic.prop_formula -> string *)

fun string_of_prop_formula PropLogic.True             = "True"
  | string_of_prop_formula PropLogic.False            = "False"
  | string_of_prop_formula (PropLogic.BoolVar i)      = "x" ^ string_of_int i
  | string_of_prop_formula (PropLogic.Not fm)         = "~" ^ string_of_prop_formula fm
  | string_of_prop_formula (PropLogic.Or (fm1, fm2))  = "(" ^ string_of_prop_formula fm1 ^ " v " ^ string_of_prop_formula fm2 ^ ")"
  | string_of_prop_formula (PropLogic.And (fm1, fm2)) = "(" ^ string_of_prop_formula fm1 ^ " & " ^ string_of_prop_formula fm2 ^ ")";

(* ------------------------------------------------------------------------- *)
(* rawsat_thm: run external SAT solver with the given clauses.  Reconstructs *)
(*      a proof from the resulting proof trace of the SAT solver.  Each      *)
(*      premise in 'prems' that is not a clause is ignored, and the theorem  *)
(*      returned is just "False" (with some clauses as hyps).                *)
(* ------------------------------------------------------------------------- *)

(* Thm.thm list -> Thm.thm *)

fun rawsat_thm prems =
let
	(* remove premises that equal "True" *)
	val non_triv_prems    = filter (fn thm =>
		(not_equal HOLogic.true_const o HOLogic.dest_Trueprop o prop_of) thm
			handle TERM ("dest_Trueprop", _) => true) prems
	(* remove non-clausal premises -- of course this shouldn't actually   *)
	(* remove anything as long as 'rawsat_thm' is only called after the   *)
	(* premises have been converted to clauses                            *)
	val clauses           = filter (fn thm =>
		((cnf.is_clause o HOLogic.dest_Trueprop o prop_of) thm handle TERM ("dest_Trueprop", _) => false)
		orelse (warning ("Ignoring non-clausal premise " ^ (string_of_cterm o cprop_of) thm); false)) non_triv_prems
	(* remove trivial clauses -- this is necessary because zChaff removes *)
	(* trivial clauses during preprocessing, and otherwise our clause     *)
	(* numbering would be off                                             *)
	val non_triv_clauses  = filter (not o cnf.clause_is_trivial o HOLogic.dest_Trueprop o prop_of) clauses
	val _                 = if !trace_sat then
			tracing ("Non-trivial clauses:\n" ^ space_implode "\n" (map (string_of_cterm o cprop_of) non_triv_clauses))
		else ()
	(* translate clauses from HOL terms to PropLogic.prop_formula *)
	val (fms, atom_table) = fold_map (PropLogic.prop_formula_of_term o HOLogic.dest_Trueprop o prop_of) non_triv_clauses Termtab.empty
	val _                 = if !trace_sat then
			tracing ("Invoking SAT solver on clauses:\n" ^ space_implode "\n" (map string_of_prop_formula fms))
		else ()
	val fm                = PropLogic.all fms
	(* unit -> Thm.thm *)
	fun make_quick_and_dirty_thm () = (
		if !trace_sat then
			tracing "'quick_and_dirty' is set: proof reconstruction skipped, using oracle instead."
		else ();
		(* of course just returning "False" is unsound; what we should return *)
		(* instead is "False" with all 'non_triv_clauses' as hyps -- but this *)
		(* might be rather slow, and it makes no real difference as long as   *)
		(* 'rawsat_thm' is only called from 'rawsat_tac'                      *)
		SkipProof.make_thm (the_context ()) (HOLogic.Trueprop $ HOLogic.false_const)
	)
in
	case SatSolver.invoke_solver (!solver) fm of
	  SatSolver.UNSATISFIABLE (SOME (clause_table, empty_id)) => (
		if !trace_sat then
			tracing ("Proof trace from SAT solver:\n" ^
				"clauses: [" ^ commas (map (fn (c, cs) =>
					"(" ^ string_of_int c ^ ", [" ^ commas (map string_of_int cs) ^ "])") (Inttab.dest clause_table)) ^ "]\n" ^
				"empty clause: " ^ string_of_int empty_id)
		else ();
		if !quick_and_dirty then
			make_quick_and_dirty_thm ()
		else
			let
				(* initialize the clause array with the given clauses *)
				val max_idx     = valOf (Inttab.max_key clause_table)
				val clause_arr  = Array.array (max_idx + 1, NO_CLAUSE)
				val _           = fold (fn thm => fn idx => (Array.update (clause_arr, idx, ORIG_CLAUSE thm); idx+1)) non_triv_clauses 0
				(* replay the proof to derive the empty clause *)
				val FalseThm    = replay_proof atom_table clause_arr (clause_table, empty_id)
			in
				(* convert the hyps back to the original format *)
				cnf.rawhyps2clausehyps_thm FalseThm
			end)
	| SatSolver.UNSATISFIABLE NONE =>
		if !quick_and_dirty then (
			warning "SAT solver claims the formula to be unsatisfiable, but did not provide a proof";
			make_quick_and_dirty_thm ()
		) else
			raise THM ("SAT solver claims the formula to be unsatisfiable, but did not provide a proof", 0, [])
	| SatSolver.SATISFIABLE assignment =>
		let
			val msg = "SAT solver found a countermodel:\n"
				^ (commas
					o map (fn (term, idx) =>
						Sign.string_of_term (the_context ()) term ^ ": "
							^ (case assignment idx of NONE => "arbitrary" | SOME true => "true" | SOME false => "false")))
					(Termtab.dest atom_table)
		in
			raise THM (msg, 0, [])
		end
	| SatSolver.UNKNOWN =>
		raise THM ("SAT solver failed to decide the formula", 0, [])
end;

(* ------------------------------------------------------------------------- *)
(* Tactics                                                                   *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* rawsat_tac: solves the i-th subgoal of the proof state; this subgoal      *)
(*      should be of the form                                                *)
(*        [| c1; c2; ...; ck |] ==> False                                    *)
(*      where each cj is a non-empty clause (i.e. a disjunction of literals) *)
(*      or "True"                                                            *)
(* ------------------------------------------------------------------------- *)

(* int -> Tactical.tactic *)

fun rawsat_tac i = METAHYPS (fn prems => rtac (rawsat_thm prems) 1) i;

(* ------------------------------------------------------------------------- *)
(* pre_cnf_tac: converts the i-th subgoal                                    *)
(*        [| A1 ; ... ; An |] ==> B                                          *)
(*      to                                                                   *)
(*        [| A1; ... ; An ; ~B |] ==> False                                  *)
(*      (handling meta-logical connectives in B properly before negating),   *)
(*      then replaces meta-logical connectives in the premises (i.e. "==>",  *)
(*      "!!" and "==") by connectives of the HOL object-logic (i.e. by       *)
(*      "-->", "!", and "="), then performs beta-eta-normalization on the    *)
(*      subgoal                                                              *)
(* ------------------------------------------------------------------------- *)

(* int -> Tactical.tactic *)

fun pre_cnf_tac i =
	rtac ccontr i THEN ObjectLogic.atomize_tac i THEN
		PRIMITIVE (Drule.fconv_rule (Drule.goals_conv (equal i) (Drule.beta_eta_conversion)));

(* ------------------------------------------------------------------------- *)
(* cnfsat_tac: checks if the empty clause "False" occurs among the premises; *)
(*      if not, eliminates conjunctions (i.e. each clause of the CNF formula *)
(*      becomes a separate premise), then applies 'rawsat_tac' to solve the  *)
(*      subgoal                                                              *)
(* ------------------------------------------------------------------------- *)

(* int -> Tactical.tactic *)

fun cnfsat_tac i =
	(etac FalseE i) ORELSE (REPEAT_DETERM (etac conjE i) THEN rawsat_tac i);

(* ------------------------------------------------------------------------- *)
(* cnfxsat_tac: checks if the empty clause "False" occurs among the          *)
(*      premises; if not, eliminates conjunctions (i.e. each clause of the   *)
(*      CNF formula becomes a separate premise) and existential quantifiers, *)
(*      then applies 'rawsat_tac' to solve the subgoal                       *)
(* ------------------------------------------------------------------------- *)

(* int -> Tactical.tactic *)

fun cnfxsat_tac i =
	(etac FalseE i) ORELSE
		(REPEAT_DETERM (etac conjE i ORELSE etac exE i) THEN rawsat_tac i);

(* ------------------------------------------------------------------------- *)
(* sat_tac: tactic for calling an external SAT solver, taking as input an    *)
(*      arbitrary formula.  The input is translated to CNF, possibly causing *)
(*      an exponential blowup.                                               *)
(* ------------------------------------------------------------------------- *)

(* int -> Tactical.tactic *)

fun sat_tac i =
	pre_cnf_tac i THEN cnf.cnf_rewrite_tac i THEN cnfsat_tac i;

(* ------------------------------------------------------------------------- *)
(* satx_tac: tactic for calling an external SAT solver, taking as input an   *)
(*      arbitrary formula.  The input is translated to CNF, possibly         *)
(*      introducing new literals.                                            *)
(* ------------------------------------------------------------------------- *)

(* int -> Tactical.tactic *)

fun satx_tac i =
	pre_cnf_tac i THEN cnf.cnfx_rewrite_tac i THEN cnfxsat_tac i;

end;  (* of structure SATFunc *)
