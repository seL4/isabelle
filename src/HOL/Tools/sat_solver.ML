(*  Title:      HOL/Tools/sat_solver.ML
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2004-2005

Interface to external SAT solvers, and (simple) built-in SAT solvers.
*)

signature SAT_SOLVER =
sig
	exception NOT_CONFIGURED

	type assignment = int -> bool option
	type proof      = int list Inttab.table * int
	datatype result = SATISFIABLE of assignment
	                | UNSATISFIABLE of proof option
	                | UNKNOWN
	type solver     = PropLogic.prop_formula -> result

	(* auxiliary functions to create external SAT solvers *)
	val write_dimacs_cnf_file : Path.T -> PropLogic.prop_formula -> unit
	val write_dimacs_sat_file : Path.T -> PropLogic.prop_formula -> unit
	val read_std_result_file  : Path.T -> string * string * string -> result
	val make_external_solver  : string -> (PropLogic.prop_formula -> unit) -> (unit -> result) -> solver

	val read_dimacs_cnf_file : Path.T -> PropLogic.prop_formula

	(* generic solver interface *)
	val solvers       : (string * solver) list ref
	val add_solver    : string * solver -> unit
	val invoke_solver : string -> solver  (* exception Option *)
end;

structure SatSolver : SAT_SOLVER =
struct

	open PropLogic;

(* ------------------------------------------------------------------------- *)
(* should be raised by an external SAT solver to indicate that the solver is *)
(* not configured properly                                                   *)
(* ------------------------------------------------------------------------- *)

	exception NOT_CONFIGURED;

(* ------------------------------------------------------------------------- *)
(* type of partial (satisfying) assignments: 'a i = NONE' means that 'a' is  *)
(*      a satisfying assigment regardless of the value of variable 'i'       *)
(* ------------------------------------------------------------------------- *)

	type assignment = int -> bool option;

(* ------------------------------------------------------------------------- *)
(* a proof of unsatisfiability, to be interpreted as follows: each integer   *)
(*      is a clause ID, each list 'xs' stored under the key 'x' in the table *)
(*      contains the IDs of clauses that must be resolved (in the given      *)
(*      order) to obtain the new clause 'x'.  Each list 'xs' must be         *)
(*      non-empty, and the literal to be resolved upon must always be unique *)
(*      (e.g. "A | ~B" must not be resolved with "~A | B").  Circular        *)
(*      dependencies of clauses are not allowed.  (At least) one of the      *)
(*      clauses in the table must be the empty clause (i.e. contain no       *)
(*      literals); its ID is given by the second component of the proof.     *)
(*      The clauses of the original problem passed to the SAT solver have    *)
(*      consecutive IDs starting with 0.  Clause IDs must be non-negative,   *)
(*      but do not need to be consecutive.                                   *)
(* ------------------------------------------------------------------------- *)

	type proof = int list Inttab.table * int;

(* ------------------------------------------------------------------------- *)
(* return type of SAT solvers: if the result is 'SATISFIABLE', a satisfying  *)
(*      assignment must be returned as well; if the result is                *)
(*      'UNSATISFIABLE', a proof of unsatisfiability may be returned         *)
(* ------------------------------------------------------------------------- *)

	datatype result = SATISFIABLE of assignment
	                | UNSATISFIABLE of proof option
	                | UNKNOWN;

(* ------------------------------------------------------------------------- *)
(* type of SAT solvers: given a propositional formula, a satisfying          *)
(*      assignment may be returned                                           *)
(* ------------------------------------------------------------------------- *)

	type solver = prop_formula -> result;

(* ------------------------------------------------------------------------- *)
(* write_dimacs_cnf_file: serializes a formula 'fm' of propositional logic   *)
(*      to a file in DIMACS CNF format (see "Satisfiability Suggested        *)
(*      Format", May 8 1993, Section 2.1)                                    *)
(* Note: 'fm' must not contain a variable index less than 1.                 *)
(* Note: 'fm' must be given in CNF.                                          *)
(* ------------------------------------------------------------------------- *)

	(* Path.T -> prop_formula -> unit *)

	fun write_dimacs_cnf_file path fm =
	let
		(* prop_formula -> prop_formula *)
		fun cnf_True_False_elim True =
			Or (BoolVar 1, Not (BoolVar 1))
		  | cnf_True_False_elim False =
			And (BoolVar 1, Not (BoolVar 1))
		  | cnf_True_False_elim fm =
			fm  (* since 'fm' is in CNF, either 'fm'='True'/'False', or 'fm' does not contain 'True'/'False' at all *)
		(* prop_formula -> int *)
		fun cnf_number_of_clauses (And (fm1,fm2)) =
			(cnf_number_of_clauses fm1) + (cnf_number_of_clauses fm2)
		  | cnf_number_of_clauses _ =
			1
		(* prop_formula -> string list *)
		fun cnf_string fm =
		let
			(* prop_formula -> string list -> string list *)
			fun cnf_string_acc True acc =
				error "formula is not in CNF"
			  | cnf_string_acc False acc =
				error "formula is not in CNF"
			  | cnf_string_acc (BoolVar i) acc =
				(assert (i>=1) "formula contains a variable index less than 1";
				string_of_int i :: acc)
			  | cnf_string_acc (Not (BoolVar i)) acc =
				"-" :: cnf_string_acc (BoolVar i) acc
			  | cnf_string_acc (Not _) acc =
				error "formula is not in CNF"
			  | cnf_string_acc (Or (fm1,fm2)) acc =
				cnf_string_acc fm1 (" " :: cnf_string_acc fm2 acc)
			  | cnf_string_acc (And (fm1,fm2)) acc =
				cnf_string_acc fm1 (" 0\n" :: cnf_string_acc fm2 acc)
		in
			cnf_string_acc fm []
		end
		val fm'               = cnf_True_False_elim fm
		val number_of_vars    = maxidx fm'
		val number_of_clauses = cnf_number_of_clauses fm'
	in
		File.write path
			("c This file was generated by SatSolver.write_dimacs_cnf_file\n" ^
			 "p cnf " ^ string_of_int number_of_vars ^ " " ^ string_of_int number_of_clauses ^ "\n");
		File.append_list path
			(cnf_string fm');
		File.append path
			" 0\n"
	end;

(* ------------------------------------------------------------------------- *)
(* write_dimacs_sat_file: serializes a formula 'fm' of propositional logic   *)
(*      to a file in DIMACS SAT format (see "Satisfiability Suggested        *)
(*      Format", May 8 1993, Section 2.2)                                    *)
(* Note: 'fm' must not contain a variable index less than 1.                 *)
(* ------------------------------------------------------------------------- *)

	(* Path.T -> prop_formula -> unit *)

	fun write_dimacs_sat_file path fm =
	let
		(* prop_formula -> string list *)
		fun sat_string fm =
		let
			(* prop_formula -> string list -> string list *)
			fun sat_string_acc True acc =
				"*()" :: acc
			  | sat_string_acc False acc =
				"+()" :: acc
			  | sat_string_acc (BoolVar i) acc =
				(assert (i>=1) "formula contains a variable index less than 1";
				string_of_int i :: acc)
			  | sat_string_acc (Not (BoolVar i)) acc =
				"-" :: sat_string_acc (BoolVar i) acc
			  | sat_string_acc (Not fm) acc =
				"-(" :: sat_string_acc fm (")" :: acc)
			  | sat_string_acc (Or (fm1,fm2)) acc =
				"+(" :: sat_string_acc_or fm1 (" " :: sat_string_acc_or fm2 (")" :: acc))
			  | sat_string_acc (And (fm1,fm2)) acc =
				"*(" :: sat_string_acc_and fm1 (" " :: sat_string_acc_and fm2 (")" :: acc))
			(* optimization to make use of n-ary disjunction/conjunction *)
			(* prop_formula -> string list -> string list *)
			and sat_string_acc_or (Or (fm1,fm2)) acc =
				sat_string_acc_or fm1 (" " :: sat_string_acc_or fm2 acc)
			  | sat_string_acc_or fm acc =
				sat_string_acc fm acc
			(* prop_formula -> string list -> string list *)
			and sat_string_acc_and (And (fm1,fm2)) acc =
				sat_string_acc_and fm1 (" " :: sat_string_acc_and fm2 acc)
			  | sat_string_acc_and fm acc =
				sat_string_acc fm acc
		in
			sat_string_acc fm []
		end
		val number_of_vars = Int.max (maxidx fm, 1)
	in
		File.write path
			("c This file was generated by SatSolver.write_dimacs_sat_file\n" ^
			 "p sat " ^ string_of_int number_of_vars ^ "\n" ^
			 "(");
		File.append_list path
			(sat_string fm);
		File.append path
			")\n"
	end;

(* ------------------------------------------------------------------------- *)
(* read_std_result_file: scans a SAT solver's output file for a satisfying   *)
(*      variable assignment.  Returns the assignment, or 'UNSATISFIABLE' if  *)
(*      the file contains 'unsatisfiable', or 'UNKNOWN' if the file contains *)
(*      neither 'satisfiable' nor 'unsatisfiable'.  Empty lines are ignored. *)
(*      The assignment must be given in one or more lines immediately after  *)
(*      the line that contains 'satisfiable'.  These lines must begin with   *)
(*      'assignment_prefix'.  Variables must be separated by " ".  Non-      *)
(*      integer strings are ignored.  If variable i is contained in the      *)
(*      assignment, then i is interpreted as 'true'.  If ~i is contained in  *)
(*      the assignment, then i is interpreted as 'false'.  Otherwise the     *)
(*      value of i is taken to be unspecified.                               *)
(* ------------------------------------------------------------------------- *)

	(* Path.T -> string * string * string -> result *)

	fun read_std_result_file path (satisfiable, assignment_prefix, unsatisfiable) =
	let
		(* string -> int list *)
		fun int_list_from_string s =
			List.mapPartial Int.fromString (space_explode " " s)
		(* int list -> assignment *)
		fun assignment_from_list [] i =
			NONE  (* the SAT solver didn't provide a value for this variable *)
		  | assignment_from_list (x::xs) i =
			if x=i then (SOME true)
			else if x=(~i) then (SOME false)
			else assignment_from_list xs i
		(* int list -> string list -> assignment *)
		fun parse_assignment xs [] =
			assignment_from_list xs
		  | parse_assignment xs (line::lines) =
			if String.isPrefix assignment_prefix line then
				parse_assignment (xs @ int_list_from_string line) lines
			else
				assignment_from_list xs
		(* string -> string -> bool *)
		fun is_substring needle haystack =
		let
			val length1 = String.size needle
			val length2 = String.size haystack
		in
			if length2 < length1 then
				false
			else if needle = String.substring (haystack, 0, length1) then
				true
			else is_substring needle (String.substring (haystack, 1, length2-1))
		end
		(* string list -> result *)
		fun parse_lines [] =
			UNKNOWN
		  | parse_lines (line::lines) =
			if is_substring satisfiable line then
				SATISFIABLE (parse_assignment [] lines)
			else if is_substring unsatisfiable line then
				UNSATISFIABLE NONE
			else
				parse_lines lines
	in
		(parse_lines o (List.filter (fn l => l <> "")) o split_lines o File.read) path
	end;

(* ------------------------------------------------------------------------- *)
(* make_external_solver: call 'writefn', execute 'cmd', call 'readfn'        *)
(* ------------------------------------------------------------------------- *)

	(* string -> (PropLogic.prop_formula -> unit) -> (unit -> result) -> solver *)

	fun make_external_solver cmd writefn readfn fm =
		(writefn fm; system cmd; readfn ());

(* ------------------------------------------------------------------------- *)
(* read_dimacs_cnf_file: returns a propositional formula that corresponds to *)
(*      a SAT problem given in DIMACS CNF format                             *)
(* ------------------------------------------------------------------------- *)

	(* Path.T -> PropLogic.prop_formula *)

	fun read_dimacs_cnf_file path =
	let
		(* string list -> string list *)
		fun filter_preamble [] =
			error "problem line not found in DIMACS CNF file"
		  | filter_preamble (line::lines) =
			if String.isPrefix "c " line then
				(* ignore comments *)
				filter_preamble lines
			else if String.isPrefix "p " line then
				(* ignore the problem line (which must be the last line of the preamble) *)
				(* Ignoring the problem line implies that if the file contains more clauses *)
				(* or variables than specified in its preamble, we will accept it anyway.   *)
				lines
			else
				error "preamble in DIMACS CNF file contains a line that does not begin with \"c \" or \"p \""
		(* string -> int *)
		fun int_from_string s =
			case Int.fromString s of
			  SOME i => i
			| NONE   => error ("token " ^ quote s ^ "in DIMACS CNF file is not a number")
		(* int list -> int list list *)
		fun clauses xs =
			let
				val (xs1, xs2) = take_prefix (fn i => i <> 0) xs
			in
				case xs2 of
				  []      => [xs1]
				| (0::[]) => [xs1]
				| (0::tl) => xs1 :: clauses tl
				| _       => sys_error "this cannot happen"
			end
		(* int -> PropLogic.prop_formula *)
		fun literal_from_int i =
			(assert (i<>0) "variable index in DIMACS CNF file is 0";
			if i>0 then
				PropLogic.BoolVar i
			else
				PropLogic.Not (PropLogic.BoolVar (~i)))
		(* PropLogic.prop_formula list -> PropLogic.prop_formula *)
		fun disjunction [] =
			error "empty clause in DIMACS CNF file"
		  | disjunction (x::xs) =
			(case xs of
			  [] => x
			| _  => PropLogic.Or (x, disjunction xs))
		(* PropLogic.prop_formula list -> PropLogic.prop_formula *)
		fun conjunction [] =
			error "no clause in DIMACS CNF file"
		  | conjunction (x::xs) =
			(case xs of
			  [] => x
			| _  => PropLogic.And (x, conjunction xs))
	in
		(conjunction
		o (map disjunction)
		o (map (map literal_from_int))
		o clauses
		o (map int_from_string)
		o List.concat
		o (map (String.fields (fn c => c mem [#" ", #"\t", #"\n"])))
		o filter_preamble
		o (List.filter (fn l => l <> ""))
		o split_lines
		o File.read)
			path
	end;

(* ------------------------------------------------------------------------- *)
(* solvers: a (reference to a) table of all registered SAT solvers           *)
(* ------------------------------------------------------------------------- *)

	val solvers = ref ([] : (string * solver) list);

(* ------------------------------------------------------------------------- *)
(* add_solver: updates 'solvers' by adding a new solver                      *)
(* ------------------------------------------------------------------------- *)

	(* string * solver -> unit *)

	fun add_solver (name, new_solver) =
		(solvers := update_warn (op =) ("SAT solver " ^ quote name ^ " was defined before") (name, new_solver) (!solvers));

(* ------------------------------------------------------------------------- *)
(* invoke_solver: returns the solver associated with the given 'name'        *)
(* Note: If no solver is associated with 'name', exception 'Option' will be  *)
(*       raised.                                                             *)
(* ------------------------------------------------------------------------- *)

	(* string -> solver *)

	fun invoke_solver name =
		(the o AList.lookup (op =) (!solvers)) name;

end;  (* SatSolver *)


(* ------------------------------------------------------------------------- *)
(* Predefined SAT solvers                                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Internal SAT solver, available as 'SatSolver.invoke_solver "enumerate"'   *)
(* -- simply enumerates assignments until a satisfying assignment is found   *)
(* ------------------------------------------------------------------------- *)

let
	fun enum_solver fm =
	let
		(* int list *)
		val indices = PropLogic.indices fm
		(* int list -> int list -> int list option *)
		(* binary increment: list 'xs' of current bits, list 'ys' of all bits (lower bits first) *)
		fun next_list _ ([]:int list) =
			NONE
		  | next_list [] (y::ys) =
			SOME [y]
		  | next_list (x::xs) (y::ys) =
			if x=y then
				(* reset the bit, continue *)
				next_list xs ys
			else
				(* set the lowest bit that wasn't set before, keep the higher bits *)
				SOME (y::x::xs)
		(* int list -> int -> bool *)
		fun assignment_from_list xs i =
			i mem xs
		(* int list -> SatSolver.result *)
		fun solver_loop xs =
			if PropLogic.eval (assignment_from_list xs) fm then
				SatSolver.SATISFIABLE (SOME o (assignment_from_list xs))
			else
				(case next_list xs indices of
				  SOME xs' => solver_loop xs'
				| NONE     => SatSolver.UNSATISFIABLE NONE)
	in
		(* start with the "first" assignment (all variables are interpreted as 'false') *)
		solver_loop []
	end
in
	SatSolver.add_solver ("enumerate", enum_solver)
end;

(* ------------------------------------------------------------------------- *)
(* Internal SAT solver, available as 'SatSolver.invoke_solver "dpll"' -- a   *)
(* simple implementation of the DPLL algorithm (cf. L. Zhang, S. Malik: "The *)
(* Quest for Efficient Boolean Satisfiability Solvers", July 2002, Fig. 1).  *)
(* ------------------------------------------------------------------------- *)

let
	local
		open PropLogic
	in
		fun dpll_solver fm =
		let
			(* We could use 'PropLogic.defcnf fm' instead of 'PropLogic.nnf fm' *)
			(* but that sometimes leads to worse performance due to the         *)
			(* introduction of additional variables.                            *)
			val fm' = PropLogic.nnf fm
			(* int list *)
			val indices = PropLogic.indices fm'
			(* int list -> int -> prop_formula *)
			fun partial_var_eval []      i = BoolVar i
			  | partial_var_eval (x::xs) i = if x=i then True else if x=(~i) then False else partial_var_eval xs i
			(* int list -> prop_formula -> prop_formula *)
			fun partial_eval xs True             = True
			  | partial_eval xs False            = False
			  | partial_eval xs (BoolVar i)      = partial_var_eval xs i
			  | partial_eval xs (Not fm)         = SNot (partial_eval xs fm)
			  | partial_eval xs (Or (fm1, fm2))  = SOr (partial_eval xs fm1, partial_eval xs fm2)
			  | partial_eval xs (And (fm1, fm2)) = SAnd (partial_eval xs fm1, partial_eval xs fm2)
			(* prop_formula -> int list *)
			fun forced_vars True              = []
			  | forced_vars False             = []
			  | forced_vars (BoolVar i)       = [i]
			  | forced_vars (Not (BoolVar i)) = [~i]
			  | forced_vars (Or (fm1, fm2))   = (forced_vars fm1) inter_int (forced_vars fm2)
			  | forced_vars (And (fm1, fm2))  = (forced_vars fm1) union_int (forced_vars fm2)
			  (* Above, i *and* ~i may be forced.  In this case the first occurrence takes   *)
			  (* precedence, and the next partial evaluation of the formula returns 'False'. *)
			  | forced_vars _                 = error "formula is not in negation normal form"
			(* int list -> prop_formula -> (int list * prop_formula) *)
			fun eval_and_force xs fm =
			let
				val fm' = partial_eval xs fm
				val xs' = forced_vars fm'
			in
				if null xs' then
					(xs, fm')
				else
					eval_and_force (xs@xs') fm'  (* xs and xs' should be distinct, so '@' here should have *)
					                             (* the same effect as 'union_int'                         *)
			end
			(* int list -> int option *)
			fun fresh_var xs =
				Library.find_first (fn i => not (i mem_int xs) andalso not ((~i) mem_int xs)) indices
			(* int list -> prop_formula -> int list option *)
			(* partial assignment 'xs' *)
			fun dpll xs fm =
			let
				val (xs', fm') = eval_and_force xs fm
			in
				case fm' of
				  True  => SOME xs'
				| False => NONE
				| _     =>
					let
						val x = valOf (fresh_var xs')  (* a fresh variable must exist since 'fm' did not evaluate to 'True'/'False' *)
					in
						case dpll (x::xs') fm' of  (* passing fm' rather than fm should save some simplification work *)
						  SOME xs'' => SOME xs''
						| NONE      => dpll ((~x)::xs') fm'  (* now try interpreting 'x' as 'False' *)
					end
			end
			(* int list -> assignment *)
			fun assignment_from_list [] i =
				NONE  (* the DPLL procedure didn't provide a value for this variable *)
			  | assignment_from_list (x::xs) i =
				if x=i then (SOME true)
				else if x=(~i) then (SOME false)
				else assignment_from_list xs i
		in
			(* initially, no variable is interpreted yet *)
			case dpll [] fm' of
			  SOME assignment => SatSolver.SATISFIABLE (assignment_from_list assignment)
			| NONE            => SatSolver.UNSATISFIABLE NONE
		end
	end  (* local *)
in
	SatSolver.add_solver ("dpll", dpll_solver)
end;

(* ------------------------------------------------------------------------- *)
(* Internal SAT solver, available as 'SatSolver.invoke_solver "auto"': uses  *)
(* the last installed solver (other than "auto" itself) that does not raise  *)
(* 'NOT_CONFIGURED'.  (However, the solver may return 'UNKNOWN'.)            *)
(* ------------------------------------------------------------------------- *)

let
	fun auto_solver fm =
	let
		fun loop [] =
			SatSolver.UNKNOWN
		  | loop ((name, solver)::solvers) =
			if name="auto" then
				(* do not call solver "auto" from within "auto" *)
				loop solvers
			else (
				(if name="dpll" orelse name="enumerate" then
					warning ("Using SAT solver " ^ quote name ^ "; for better performance, consider using an external solver.")
				else
					Output.debug ("Using SAT solver " ^ quote name ^ "."));
				(* apply 'solver' to 'fm' *)
				solver fm
					handle SatSolver.NOT_CONFIGURED => loop solvers
			)
	in
		loop (!SatSolver.solvers)
	end
in
	SatSolver.add_solver ("auto", auto_solver)
end;

(* ------------------------------------------------------------------------- *)
(* zChaff (http://www.princeton.edu/~chaff/zchaff.html)                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* 'zchaff_with_proofs' applies the "zchaff" prover to a formula, and if     *)
(* zChaff finds that the formula is unsatisfiable, a proof of this is read   *)
(* from a file "resolve_trace" that was generated by zChaff.  See the code   *)
(* below for the expected format of the "resolve_trace" file.  Aside from    *)
(* some basic syntactic checks, no verification of the proof is performed.   *)
(* ------------------------------------------------------------------------- *)

(* add "zchaff_with_proofs" _before_ "zchaff" to the available solvers, so   *)
(* that the latter is preferred by the "auto" solver                         *)

let
	exception INVALID_PROOF of string
	fun zchaff_with_proofs fm =
	case SatSolver.invoke_solver "zchaff" fm of
	  SatSolver.UNSATISFIABLE NONE =>
		(let
			(* string list *)
			val proof_lines = ((split_lines o File.read) (Path.unpack "resolve_trace"))
				handle _ => raise INVALID_PROOF "Could not read file \"resolve_trace\""
			(* PropLogic.prop_formula -> int *)
			fun cnf_number_of_clauses (PropLogic.And (fm1, fm2)) = cnf_number_of_clauses fm1 + cnf_number_of_clauses fm2
			  | cnf_number_of_clauses _                          = 1
			(* string -> int *)
			fun int_from_string s = (
				case Int.fromString s of
				  SOME i => i
				| NONE   => raise INVALID_PROOF ("File format error: number expected (" ^ quote s ^ " encountered).")
			)
			(* parse the "resolve_trace" file *)
			(* int ref *)
			val clause_offset = ref ~1
			(* string list -> proof -> proof *)
			fun process_tokens [] proof =
				proof
			  | process_tokens (tok::toks) (clause_table, empty_id) =
				if tok="CL:" then (
					case toks of
					  id::sep::ids =>
						let
							val _   = if !clause_offset = ~1 then () else raise INVALID_PROOF ("File format error: \"CL:\" disallowed after \"VAR:\".")
							val _   = if empty_id = ~1 then () else raise INVALID_PROOF ("File format error: \"CL:\" disallowed after \"CONF:\".")
							val cid = int_from_string id
							val _   = if sep = "<=" then () else raise INVALID_PROOF ("File format error: \"<=\" expected (" ^ quote sep ^ " encountered).")
							val rs  = map int_from_string ids
						in
							(* update clause table *)
							(Inttab.update_new (cid, rs) clause_table, empty_id)
								handle Inttab.DUP _ => raise INVALID_PROOF ("File format error: clause " ^ id ^ " defined more than once.")
						end
					| _ =>
						raise INVALID_PROOF "File format error: \"CL:\" followed by an insufficient number of tokens."
				) else if tok="VAR:" then (
					case toks of
					  id::levsep::levid::valsep::valid::antesep::anteid::litsep::lits =>
						let
							val _   = if empty_id = ~1 then () else raise INVALID_PROOF ("File format error: \"VAR:\" disallowed after \"CONF:\".")
							(* set 'clause_offset' to the largest used clause ID *)
							val _   = if !clause_offset = ~1 then clause_offset :=
								(case Inttab.max_key clause_table of
								  SOME id => id
								| NONE    => cnf_number_of_clauses (PropLogic.defcnf fm) - 1  (* the first clause ID is 0, not 1 *))
								else
									()
							val vid = int_from_string id
							val _   = if levsep = "L:" then () else raise INVALID_PROOF ("File format error: \"L:\" expected (" ^ quote levsep ^ " encountered).")
							val _   = int_from_string levid
							val _   = if valsep = "V:" then () else raise INVALID_PROOF ("File format error: \"V:\" expected (" ^ quote valsep ^ " encountered).")
							val _   = int_from_string valid
							val _   = if antesep = "A:" then () else raise INVALID_PROOF ("File format error: \"A:\" expected (" ^ quote antesep ^ " encountered).")
							val aid = int_from_string anteid
							val _   = if litsep = "Lits:" then () else raise INVALID_PROOF ("File format error: \"Lits:\" expected (" ^ quote litsep ^ " encountered).")
							val ls  = map int_from_string lits
							(* convert the data provided by zChaff to our resolution-style proof format *)
							(* each "VAR:" line defines a unit clause, the resolvents are implicitly    *)
							(* given by the literals in the antecedent clause                           *)
							(* we use the sum of '!clause_offset' and the variable ID as clause ID for the unit clause *)
							val cid = !clause_offset + vid
							(* the low bit of each literal gives its sign (positive/negative), therefore  *)
							(* we have to divide each literal by 2 to obtain the proper variable ID; then *)
							(* we add '!clause_offset' to obtain the ID of the corresponding unit clause  *)
							val vids = filter (not_equal vid) (map (fn l => l div 2) ls)
							val rs   = aid :: map (fn v => !clause_offset + v) vids
						in
							(* update clause table *)
							(Inttab.update_new (cid, rs) clause_table, empty_id)
								handle Inttab.DUP _ => raise INVALID_PROOF ("File format error: clause " ^ string_of_int cid ^ " (derived from antecedent for variable " ^ id ^ ") already defined.")
						end
					| _ =>
						raise INVALID_PROOF "File format error: \"VAR:\" followed by an insufficient number of tokens."
				) else if tok="CONF:" then (
					case toks of
					  id::sep::ids =>
						let
							val _   = if empty_id = ~1 then () else raise INVALID_PROOF "File format error: more than one conflicting clause specified."
							val cid = int_from_string id
							val _   = if sep = "==" then () else raise INVALID_PROOF ("File format error: \"==\" expected (" ^ quote sep ^ " encountered).")
							val ls  = map int_from_string ids
							(* the conflict clause must be resolved with the unit clauses *)
							(* for its literals to obtain the empty clause                *)
							val vids         = map (fn l => l div 2) ls
							val rs           = cid :: map (fn v => !clause_offset + v) vids
							val new_empty_id = getOpt (Inttab.max_key clause_table, !clause_offset) + 1
						in
							(* update clause table and conflict id *)
							(Inttab.update_new (new_empty_id, rs) clause_table, new_empty_id)
								handle Inttab.DUP _ => raise INVALID_PROOF ("File format error: clause " ^ string_of_int new_empty_id ^ " (empty clause derived from clause " ^ id ^ ") already defined.")
						end
					| _ =>
						raise INVALID_PROOF "File format error: \"CONF:\" followed by an insufficient number of tokens."
				) else
					raise INVALID_PROOF ("File format error: unknown token " ^ quote tok ^ " encountered.")
			(* string list -> proof -> proof *)
			fun process_lines [] proof =
				proof
			  | process_lines (l::ls) proof =
				process_lines ls (process_tokens (String.tokens (fn c => c = #" " orelse c = #"\t") l) proof)
			(* proof *)
			val (clause_table, empty_id) = process_lines proof_lines (Inttab.empty, ~1)
			val _                        = if empty_id <> ~1 then () else raise INVALID_PROOF "File format error: no conflicting clause specified."
		in
			SatSolver.UNSATISFIABLE (SOME (clause_table, empty_id))
		end handle INVALID_PROOF reason => (warning reason; SatSolver.UNSATISFIABLE NONE))
	| result =>
		result
in
	SatSolver.add_solver ("zchaff_with_proofs", zchaff_with_proofs)
end;

let
	fun zchaff fm =
	let
		val _          = if (getenv "ZCHAFF_HOME") = "" then raise SatSolver.NOT_CONFIGURED else ()
		val _          = if (getenv "ZCHAFF_VERSION") <> "2004.5.13" andalso
		                    (getenv "ZCHAFF_VERSION") <> "2004.11.15" then raise SatSolver.NOT_CONFIGURED else ()
			(* both versions of zChaff appear to have the same interface, so we do *)
			(* not actually need to distinguish between them in the following code *)
		val inpath     = File.tmp_path (Path.unpack "isabelle.cnf")
		val outpath    = File.tmp_path (Path.unpack "result")
		val cmd        = (getenv "ZCHAFF_HOME") ^ "/zchaff " ^ (Path.pack inpath) ^ " > " ^ (Path.pack outpath)
		fun writefn fm = SatSolver.write_dimacs_cnf_file inpath (PropLogic.defcnf fm)
		fun readfn ()  = SatSolver.read_std_result_file outpath ("Instance Satisfiable", "", "Instance Unsatisfiable")
		val _          = if File.exists inpath then warning ("overwriting existing file " ^ quote (Path.pack inpath)) else ()
		val _          = if File.exists outpath then warning ("overwriting existing file " ^ quote (Path.pack outpath)) else ()
		val result     = SatSolver.make_external_solver cmd writefn readfn fm
		val _          = try File.rm inpath
		val _          = try File.rm outpath
	in
		result
	end
in
	SatSolver.add_solver ("zchaff", zchaff)
end;

(* ------------------------------------------------------------------------- *)
(* BerkMin 561 (http://eigold.tripod.com/BerkMin.html)                       *)
(* ------------------------------------------------------------------------- *)

let
	fun berkmin fm =
	let
		val _          = if (getenv "BERKMIN_HOME") = "" orelse (getenv "BERKMIN_EXE") = "" then raise SatSolver.NOT_CONFIGURED else ()
		val inpath     = File.tmp_path (Path.unpack "isabelle.cnf")
		val outpath    = File.tmp_path (Path.unpack "result")
		val cmd        = (getenv "BERKMIN_HOME") ^ "/" ^ (getenv "BERKMIN_EXE") ^ " " ^ (Path.pack inpath) ^ " > " ^ (Path.pack outpath)
		fun writefn fm = SatSolver.write_dimacs_cnf_file inpath (PropLogic.defcnf fm)
		fun readfn ()  = SatSolver.read_std_result_file outpath ("Satisfiable          !!", "solution =", "UNSATISFIABLE          !!")
		val _          = if File.exists inpath then warning ("overwriting existing file " ^ quote (Path.pack inpath)) else ()
		val _          = if File.exists outpath then warning ("overwriting existing file " ^ quote (Path.pack outpath)) else ()
		val result     = SatSolver.make_external_solver cmd writefn readfn fm
		val _          = try File.rm inpath
		val _          = try File.rm outpath
	in
		result
	end
in
	SatSolver.add_solver ("berkmin", berkmin)
end;

(* ------------------------------------------------------------------------- *)
(* Jerusat 1.3 (http://www.cs.tau.ac.il/~ale1/)                              *)
(* ------------------------------------------------------------------------- *)

let
	fun jerusat fm =
	let
		val _          = if (getenv "JERUSAT_HOME") = "" then raise SatSolver.NOT_CONFIGURED else ()
		val inpath     = File.tmp_path (Path.unpack "isabelle.cnf")
		val outpath    = File.tmp_path (Path.unpack "result")
		val cmd        = (getenv "JERUSAT_HOME") ^ "/Jerusat1.3 " ^ (Path.pack inpath) ^ " > " ^ (Path.pack outpath)
		fun writefn fm = SatSolver.write_dimacs_cnf_file inpath (PropLogic.defcnf fm)
		fun readfn ()  = SatSolver.read_std_result_file outpath ("s SATISFIABLE", "v ", "s UNSATISFIABLE")
		val _          = if File.exists inpath then warning ("overwriting existing file " ^ quote (Path.pack inpath)) else ()
		val _          = if File.exists outpath then warning ("overwriting existing file " ^ quote (Path.pack outpath)) else ()
		val result     = SatSolver.make_external_solver cmd writefn readfn fm
		val _          = try File.rm inpath
		val _          = try File.rm outpath
	in
		result
	end
in
	SatSolver.add_solver ("jerusat", jerusat)
end;

(* ------------------------------------------------------------------------- *)
(* Add code for other SAT solvers below.                                     *)
(* ------------------------------------------------------------------------- *)

(*
let
	fun mysolver fm = ...
in
	SatSolver.add_solver ("myname", (fn fm => if mysolver_is_configured then mysolver fm else raise SatSolver.NOT_CONFIGURED));  -- register the solver
end;

-- the solver is now available as SatSolver.invoke_solver "myname"
*)
