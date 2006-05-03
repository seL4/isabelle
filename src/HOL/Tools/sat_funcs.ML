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
       the empty clause (i.e., False).  The tactic replays this proof
       in Isabelle and thus solves the overall goal.

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
   - zChaff must have been compiled with proof generation enabled
     (#define VERIFY_ON).
*)

signature SAT =
sig
	val trace_sat : bool ref  (* print trace messages *)
	val sat_tac   : int -> Tactical.tactic
	val satx_tac  : int -> Tactical.tactic
	val counter   : int ref  (* number of resolution steps during last proof replay *)
end

functor SATFunc (structure cnf : CNF) : SAT =
struct

val trace_sat = ref false;

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

(* ------------------------------------------------------------------------- *)
(* resolve_raw_clauses: given a non-empty list of raw clauses, we fold       *)
(*      resolution over the list (starting with its head), i.e. with two raw *)
(*      clauses                                                              *)
(*        [| x1; ... ; a; ...; xn |] ==> False                               *)
(*      and                                                                  *)
(*        [| y1; ... ; a'; ...; ym |] ==> False                              *)
(*      (where a and a' are dual to each other), we first convert the first  *)
(*      clause to                                                            *)
(*        [| x1; ...; xn |] ==> a'                                           *)
(*      (using swap_prem and perhaps notnotD), and then do a resolution with *)
(*      the second clause to produce                                         *)
(*        [| y1; ...; x1; ...; xn; ...; yn |] ==> False                      *)
(*      amd finally remove duplicate literals.                               *)
(* ------------------------------------------------------------------------- *)

(* Thm.thm list -> Thm.thm *)

fun resolve_raw_clauses [] =
	raise THM ("Proof reconstruction failed (empty list of resolvents)!", 0, [])
  | resolve_raw_clauses (c::cs) =
	let
		fun dual (Const ("Not", _) $ x) = x
		  | dual x                      = HOLogic.Not $ x

		fun is_neg (Const ("Not", _) $ _) = true
		  | is_neg _                      = false

		(* find out which two hyps are used in the resolution *)
		(* Term.term list -> Term.term list -> Term.term * Term.term *)
		fun res_hyps [] _ =
			raise THM ("Proof reconstruction failed (no literal for resolution)!", 0, [])
		  | res_hyps _ [] =
			raise THM ("Proof reconstruction failed (no literal for resolution)!", 0, [])
		  | res_hyps ((Const ("Trueprop", _) $ x) :: xs) ys =
			let val dx = dual x in
				(* hyps are implemented as ordered list in the kernel, and *)
				(* stripping 'Trueprop' should not change the order        *)
				if OrdList.member Term.fast_term_ord ys dx then
					(x, dx)
				else
					res_hyps xs ys
			end
		  | res_hyps (_ :: xs) ys =
			(* hyps are implemented as ordered list in the kernel, all hyps are of *)
			(* the form 'Trueprop $ lit' or 'implies $ (negated clause) $ False',  *)
			(* and the former are LESS than the latter according to the order --   *)
			(* therefore there is no need to continue the search via               *)
			(* 'res_hyps xs ys' here                                               *)
			raise THM ("Proof reconstruction failed (no literal for resolution)!", 0, [])

		(* Thm.thm -> Thm.thm -> Thm.thm *)
		fun resolution c1 c2 =
		let
			val _ = if !trace_sat then
					tracing ("Resolving clause: " ^ string_of_thm c1 ^ " (hyps: " ^ space_implode ", " (map (Sign.string_of_term (theory_of_thm c1)) (#hyps (rep_thm c1)))
						^ ")\nwith clause: " ^ string_of_thm c2 ^ " (hyps: " ^ space_implode ", " (map (Sign.string_of_term (theory_of_thm c2)) (#hyps (rep_thm c2))) ^ ")")
				else ()

			(* Term.term list -> Term.term list *)
			fun dest_filter_Trueprop []                                  = []
			  | dest_filter_Trueprop ((Const ("Trueprop", _) $ x) :: xs) = x :: dest_filter_Trueprop xs
			  | dest_filter_Trueprop (_ :: xs)                           =      dest_filter_Trueprop xs

			val hyps1    =                        (#hyps o rep_thm) c1
			(* minor optimization: dest/filter over the second list outside 'res_hyps' to do it only once *)
			val hyps2    = (dest_filter_Trueprop o #hyps o rep_thm) c2

			val (l1, l2) = res_hyps hyps1 hyps2  (* the two literals used for resolution, with 'Trueprop' stripped *)
			val is_neg   = is_neg l1

			val c1'      = Thm.implies_intr (cterm_of (theory_of_thm c1) (HOLogic.mk_Trueprop l1)) c1  (* Gamma1 |- l1 ==> False *)
			val c2'      = Thm.implies_intr (cterm_of (theory_of_thm c2) (HOLogic.mk_Trueprop l2)) c2  (* Gamma2 |- l2 ==> False *)

			val res_thm  =  (* |- (lit ==> False) ==> (~lit ==> False) ==> False *)
				let
					val P          = Var (("P", 0), HOLogic.boolT)
					val (lit, thy) = if is_neg then (l2, theory_of_thm c2') else (l1, theory_of_thm c1')
					val cterm      = cterm_of thy
				in
					Thm.instantiate ([], [(cterm P, cterm lit)]) resolution_thm
				end

			val _ = if !trace_sat then
					tracing ("Resolution theorem: " ^ string_of_thm res_thm)
				else ()

			val c_new    = Thm.implies_elim (Thm.implies_elim res_thm (if is_neg then c2' else c1')) (if is_neg then c1' else c2')  (* Gamma1, Gamma2 |- False *)

			val _ = if !trace_sat then
					tracing ("Resulting clause: " ^ string_of_thm c_new ^ " (hyps: " ^ space_implode ", " (map (Sign.string_of_term (theory_of_thm c_new)) (#hyps (rep_thm c_new))) ^ ")")
				else ()
			val _ = inc counter
		in
			c_new
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
(* ------------------------------------------------------------------------- *)

(* Thm.thm option Array.array -> SatSolver.proof -> Thm.thm *)

fun replay_proof clauses (clause_table, empty_id) =
let
	(* int -> Thm.thm *)
	fun prove_clause id =
		case Array.sub (clauses, id) of
		  SOME thm =>
			thm
		| NONE     =>
			let
				val _   = if !trace_sat then tracing ("Proving clause #" ^ string_of_int id ^ " ...") else ()
				val ids = valOf (Inttab.lookup clause_table id)
				val thm = resolve_raw_clauses (map prove_clause ids)
				val _   = Array.update (clauses, id, SOME thm)
				val _   = if !trace_sat then tracing ("Replay chain successful; clause stored at #" ^ string_of_int id) else ()
			in
				thm
			end

	val _            = counter := 0
	val empty_clause = prove_clause empty_id
	val _            = if !trace_sat then tracing ("Proof reconstruction successful; " ^ string_of_int (!counter) ^ " resolution step(s) total.") else ()
in
	empty_clause
end;

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
	case SatSolver.invoke_solver "zchaff_with_proofs" fm of
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
				(* initialize the clause array with the given clauses, *)
				(* but converted to raw clause format                  *)
				val max_idx     = valOf (Inttab.max_key clause_table)
				val clause_arr  = Array.array (max_idx + 1, NONE)
				val raw_clauses = map cnf.clause2raw_thm non_triv_clauses
				(* Every raw clause has only its literals and itself as hyp, and hyps are *)
				(* accumulated during resolution steps.  Experimental results indicate    *)
				(* that it is NOT faster to weaken all raw_clauses to contain every       *)
				(* clause in the hyps beforehand.                                         *)
				val _           = fold (fn thm => fn idx => (Array.update (clause_arr, idx, SOME thm); idx+1)) raw_clauses 0
				(* replay the proof to derive the empty clause *)
				val FalseThm    = replay_proof clause_arr (clause_table, empty_id)
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

fun pre_cnf_tac i = rtac ccontr i THEN ObjectLogic.atomize_tac i THEN
                      PRIMITIVE (Drule.fconv_rule (Drule.goals_conv (equal i) (Drule.beta_eta_conversion)));

(* ------------------------------------------------------------------------- *)
(* cnfsat_tac: checks if the empty clause "False" occurs among the premises; *)
(*      if not, eliminates conjunctions (i.e. each clause of the CNF formula *)
(*      becomes a separate premise), then applies 'rawsat_tac' to solve the  *)
(*      subgoal                                                              *)
(* ------------------------------------------------------------------------- *)

(* int -> Tactical.tactic *)

fun cnfsat_tac i = (etac FalseE i) ORELSE (REPEAT_DETERM (etac conjE i) THEN rawsat_tac i);

(* ------------------------------------------------------------------------- *)
(* cnfxsat_tac: checks if the empty clause "False" occurs among the          *)
(*      premises; if not, eliminates conjunctions (i.e. each clause of the   *)
(*      CNF formula becomes a separate premise) and existential quantifiers, *)
(*      then applies 'rawsat_tac' to solve the subgoal                       *)
(* ------------------------------------------------------------------------- *)

(* int -> Tactical.tactic *)

fun cnfxsat_tac i = (etac FalseE i) ORELSE (REPEAT_DETERM (etac conjE i ORELSE etac exE i) THEN rawsat_tac i);

(* ------------------------------------------------------------------------- *)
(* sat_tac: tactic for calling an external SAT solver, taking as input an    *)
(*      arbitrary formula.  The input is translated to CNF, possibly causing *)
(*      an exponential blowup.                                               *)
(* ------------------------------------------------------------------------- *)

(* int -> Tactical.tactic *)

fun sat_tac i = pre_cnf_tac i THEN cnf.cnf_rewrite_tac i THEN cnfsat_tac i;

(* ------------------------------------------------------------------------- *)
(* satx_tac: tactic for calling an external SAT solver, taking as input an   *)
(*      arbitrary formula.  The input is translated to CNF, possibly         *)
(*      introducing new literals.                                            *)
(* ------------------------------------------------------------------------- *)

(* int -> Tactical.tactic *)

fun satx_tac i = pre_cnf_tac i THEN cnf.cnfx_rewrite_tac i THEN cnfxsat_tac i;

end;  (* of structure *)
