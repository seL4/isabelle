(*  Title:      HOL/Tools/sat_solver.ML
    Author:     Tjark Weber
    Copyright   2004-2009

Interface to external SAT solvers, and (simple) built-in SAT solvers.

Relevant Isabelle environment settings:

  # MiniSat 1.14
  #MINISAT_HOME=/usr/local/bin

  # zChaff
  #ZCHAFF_HOME=/usr/local/bin

  # BerkMin561
  #BERKMIN_HOME=/usr/local/bin
  #BERKMIN_EXE=BerkMin561-linux
  #BERKMIN_EXE=BerkMin561-solaris

  # Jerusat 1.3
  #JERUSAT_HOME=/usr/local/bin
*)

signature SAT_SOLVER =
sig
  exception NOT_CONFIGURED

  type assignment = int -> bool option
  type proof      = int list Inttab.table * int
  datatype result = SATISFIABLE of assignment
                  | UNSATISFIABLE of proof option
                  | UNKNOWN
  type solver     = Prop_Logic.prop_formula -> result

  (* auxiliary functions to create external SAT solvers *)
  val write_dimacs_cnf_file : Path.T -> Prop_Logic.prop_formula -> unit
  val write_dimacs_sat_file : Path.T -> Prop_Logic.prop_formula -> unit
  val read_std_result_file : Path.T -> string * string * string -> result
  val make_external_solver : string -> (Prop_Logic.prop_formula -> unit) ->
    (unit -> result) -> solver

  val read_dimacs_cnf_file : Path.T -> Prop_Logic.prop_formula

  (* generic solver interface *)
  val get_solvers   : unit -> (string * solver) list
  val add_solver    : string * solver -> unit
  val invoke_solver : string -> solver  (* exception Option *)
end;

structure SatSolver : SAT_SOLVER =
struct

  open Prop_Logic;

(* ------------------------------------------------------------------------- *)
(* should be raised by an external SAT solver to indicate that the solver is *)
(* not configured properly                                                   *)
(* ------------------------------------------------------------------------- *)

  exception NOT_CONFIGURED;

(* ------------------------------------------------------------------------- *)
(* type of partial (satisfying) assignments: 'a i = NONE' means that 'a' is  *)
(*      a satisfying assignment regardless of the value of variable 'i'      *)
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

  fun write_dimacs_cnf_file path fm =
  let
    fun cnf_True_False_elim True =
      Or (BoolVar 1, Not (BoolVar 1))
      | cnf_True_False_elim False =
      And (BoolVar 1, Not (BoolVar 1))
      | cnf_True_False_elim fm =
      fm  (* since 'fm' is in CNF, either 'fm'='True'/'False',
             or 'fm' does not contain 'True'/'False' at all *)
    fun cnf_number_of_clauses (And (fm1, fm2)) =
      (cnf_number_of_clauses fm1) + (cnf_number_of_clauses fm2)
      | cnf_number_of_clauses _ =
      1
    fun write_cnf_file out =
    let
      fun write_formula True =
          error "formula is not in CNF"
        | write_formula False =
          error "formula is not in CNF"
        | write_formula (BoolVar i) =
          (i>=1 orelse error "formula contains a variable index less than 1";
           TextIO.output (out, string_of_int i))
        | write_formula (Not (BoolVar i)) =
          (TextIO.output (out, "-");
           write_formula (BoolVar i))
        | write_formula (Not _) =
          error "formula is not in CNF"
        | write_formula (Or (fm1, fm2)) =
          (write_formula fm1;
           TextIO.output (out, " ");
           write_formula fm2)
        | write_formula (And (fm1, fm2)) =
          (write_formula fm1;
           TextIO.output (out, " 0\n");
           write_formula fm2)
      val fm'               = cnf_True_False_elim fm
      val number_of_vars    = maxidx fm'
      val number_of_clauses = cnf_number_of_clauses fm'
    in
      TextIO.output (out, "c This file was generated by SatSolver.write_dimacs_cnf_file\n");
      TextIO.output (out, "p cnf " ^ string_of_int number_of_vars ^ " " ^
                            string_of_int number_of_clauses ^ "\n");
      write_formula fm';
      TextIO.output (out, " 0\n")
    end
  in
    File.open_output write_cnf_file path
  end;

(* ------------------------------------------------------------------------- *)
(* write_dimacs_sat_file: serializes a formula 'fm' of propositional logic   *)
(*      to a file in DIMACS SAT format (see "Satisfiability Suggested        *)
(*      Format", May 8 1993, Section 2.2)                                    *)
(* Note: 'fm' must not contain a variable index less than 1.                 *)
(* ------------------------------------------------------------------------- *)

  fun write_dimacs_sat_file path fm =
  let
    fun write_sat_file out =
    let
      fun write_formula True =
          TextIO.output (out, "*()")
        | write_formula False =
          TextIO.output (out, "+()")
        | write_formula (BoolVar i) =
          (i>=1 orelse error "formula contains a variable index less than 1";
           TextIO.output (out, string_of_int i))
        | write_formula (Not (BoolVar i)) =
          (TextIO.output (out, "-");
           write_formula (BoolVar i))
        | write_formula (Not fm) =
          (TextIO.output (out, "-(");
           write_formula fm;
           TextIO.output (out, ")"))
        | write_formula (Or (fm1, fm2)) =
          (TextIO.output (out, "+(");
           write_formula_or fm1;
           TextIO.output (out, " ");
           write_formula_or fm2;
           TextIO.output (out, ")"))
        | write_formula (And (fm1, fm2)) =
          (TextIO.output (out, "*(");
           write_formula_and fm1;
           TextIO.output (out, " ");
           write_formula_and fm2;
           TextIO.output (out, ")"))
      (* optimization to make use of n-ary disjunction/conjunction *)
      and write_formula_or (Or (fm1, fm2)) =
          (write_formula_or fm1;
           TextIO.output (out, " ");
           write_formula_or fm2)
        | write_formula_or fm =
          write_formula fm
      and write_formula_and (And (fm1, fm2)) =
          (write_formula_and fm1;
           TextIO.output (out, " ");
           write_formula_and fm2)
        | write_formula_and fm =
          write_formula fm
      val number_of_vars = Int.max (maxidx fm, 1)
    in
      TextIO.output (out, "c This file was generated by SatSolver.write_dimacs_sat_file\n");
      TextIO.output (out, "p sat " ^ string_of_int number_of_vars ^ "\n");
      TextIO.output (out, "(");
      write_formula fm;
      TextIO.output (out, ")\n")
    end
  in
    File.open_output write_sat_file path
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

  fun read_std_result_file path (satisfiable, assignment_prefix, unsatisfiable) =
  let
    fun int_list_from_string s =
      map_filter Int.fromString (space_explode " " s)
    fun assignment_from_list [] i =
      NONE  (* the SAT solver didn't provide a value for this variable *)
      | assignment_from_list (x::xs) i =
      if x=i then (SOME true)
      else if x=(~i) then (SOME false)
      else assignment_from_list xs i
    fun parse_assignment xs [] =
      assignment_from_list xs
      | parse_assignment xs (line::lines) =
      if String.isPrefix assignment_prefix line then
        parse_assignment (xs @ int_list_from_string line) lines
      else
        assignment_from_list xs
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
    fun parse_lines [] =
      UNKNOWN
      | parse_lines (line::lines) =
      if is_substring unsatisfiable line then
        UNSATISFIABLE NONE
      else if is_substring satisfiable line then
        SATISFIABLE (parse_assignment [] lines)
      else
        parse_lines lines
  in
    (parse_lines o filter (fn l => l <> "") o split_lines o File.read) path
  end;

(* ------------------------------------------------------------------------- *)
(* make_external_solver: call 'writefn', execute 'cmd', call 'readfn'        *)
(* ------------------------------------------------------------------------- *)

  fun make_external_solver cmd writefn readfn fm =
    (writefn fm; Isabelle_System.bash cmd; readfn ());

(* ------------------------------------------------------------------------- *)
(* read_dimacs_cnf_file: returns a propositional formula that corresponds to *)
(*      a SAT problem given in DIMACS CNF format                             *)
(* ------------------------------------------------------------------------- *)

  fun read_dimacs_cnf_file path =
  let
    fun filter_preamble [] =
      error "problem line not found in DIMACS CNF file"
      | filter_preamble (line::lines) =
      if String.isPrefix "c " line orelse line = "c" then
        (* ignore comments *)
        filter_preamble lines
      else if String.isPrefix "p " line then
        (* ignore the problem line (which must be the last line of the preamble) *)
        (* Ignoring the problem line implies that if the file contains more clauses *)
        (* or variables than specified in its preamble, we will accept it anyway.   *)
        lines
      else
        error "preamble in DIMACS CNF file contains a line that does not begin with \"c \" or \"p \""
    fun int_from_string s =
      case Int.fromString s of
        SOME i => i
      | NONE   => error ("token " ^ quote s ^ " in DIMACS CNF file is not a number")
    fun clauses xs =
      let
        val (xs1, xs2) = take_prefix (fn i => i <> 0) xs
      in
        case xs2 of
          []      => [xs1]
        | (0::[]) => [xs1]
        | (0::tl) => xs1 :: clauses tl
        | _       => raise Fail "SatSolver.clauses"
      end
    fun literal_from_int i =
      (i<>0 orelse error "variable index in DIMACS CNF file is 0";
      if i>0 then
        Prop_Logic.BoolVar i
      else
        Prop_Logic.Not (Prop_Logic.BoolVar (~i)))
    fun disjunction [] =
      error "empty clause in DIMACS CNF file"
      | disjunction (x::xs) =
      (case xs of
        [] => x
      | _  => Prop_Logic.Or (x, disjunction xs))
    fun conjunction [] =
      error "no clause in DIMACS CNF file"
      | conjunction (x::xs) =
      (case xs of
        [] => x
      | _  => Prop_Logic.And (x, conjunction xs))
  in
    (conjunction
    o (map disjunction)
    o (map (map literal_from_int))
    o clauses
    o (map int_from_string)
    o (maps (String.tokens (member (op =) [#" ", #"\t", #"\n"])))
    o filter_preamble
    o filter (fn l => l <> "")
    o split_lines
    o File.read)
      path
  end;

(* ------------------------------------------------------------------------- *)
(* solvers: a table of all registered SAT solvers                            *)
(* ------------------------------------------------------------------------- *)

  val solvers = Synchronized.var "solvers" ([] : (string * solver) list);

  fun get_solvers () = Synchronized.value solvers;

(* ------------------------------------------------------------------------- *)
(* add_solver: updates 'solvers' by adding a new solver                      *)
(* ------------------------------------------------------------------------- *)

  fun add_solver (name, new_solver) =
    Synchronized.change solvers (fn the_solvers =>
      let
        val _ = if AList.defined (op =) the_solvers name
          then warning ("SAT solver " ^ quote name ^ " was defined before")
          else ();
      in AList.update (op =) (name, new_solver) the_solvers end);

(* ------------------------------------------------------------------------- *)
(* invoke_solver: returns the solver associated with the given 'name'        *)
(* Note: If no solver is associated with 'name', exception 'Option' will be  *)
(*       raised.                                                             *)
(* ------------------------------------------------------------------------- *)

  fun invoke_solver name =
    the (AList.lookup (op =) (get_solvers ()) name);

end;  (* SatSolver *)


(* ------------------------------------------------------------------------- *)
(* Predefined SAT solvers                                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Internal SAT solver, available as 'SatSolver.invoke_solver "cdclite"' --  *)
(* a simplified implementation of the conflict-driven clause-learning        *)
(* algorithm (cf. L. Zhang, S. Malik: "The Quest for Efficient Boolean       *)
(* Satisfiability Solvers", July 2002, Fig. 2). This solver produces models  *)
(* and proof traces.                                                         *)
(* ------------------------------------------------------------------------- *)

let
  type clause = int list * int
  type value = bool option
  datatype reason = Decided | Implied of clause | Level0 of int
  type variable = bool option * reason * int * int
  type proofs = int * int list Inttab.table
  type state =
    int * int list * variable Inttab.table * clause list Inttab.table * proofs
  exception CONFLICT of clause * state
  exception UNSAT of clause * state

  fun neg i = ~i

  fun lit_value lit value = if lit > 0 then value else Option.map not value

  fun var_of vars lit: variable = the (Inttab.lookup vars (abs lit))
  fun value_of vars lit = lit_value lit (#1 (var_of vars lit))
  fun reason_of vars lit = #2 (var_of vars lit)
  fun level_of vars lit = #3 (var_of vars lit)

  fun is_true vars lit = (value_of vars lit = SOME true)
  fun is_false vars lit = (value_of vars lit = SOME false)
  fun is_unassigned vars lit = (value_of vars lit = NONE)
  fun assignment_of vars lit = the_default NONE (try (value_of vars) lit)

  fun put_var value reason level (_, _, _, rank) = (value, reason, level, rank)
  fun incr_rank (value, reason, level, rank) = (value, reason, level, rank + 1)
  fun update_var lit f = Inttab.map_entry (abs lit) f
  fun add_var lit = Inttab.update (abs lit, (NONE, Decided, ~1, 0))

  fun assign lit r l = update_var lit (put_var (SOME (lit > 0)) r l)
  fun unassign lit = update_var lit (put_var NONE Decided ~1)

  fun add_proof [] (idx, ptab) = (idx, (idx + 1, ptab))
    | add_proof ps (idx, ptab) = (idx, (idx + 1, Inttab.update (idx, ps) ptab))

  fun level0_proof_of (Level0 idx) = SOME idx
    | level0_proof_of _ = NONE

  fun level0_proofs_of vars = map_filter (level0_proof_of o reason_of vars)
  fun prems_of vars (lits, p) = p :: level0_proofs_of vars lits
  fun mk_proof vars cls proofs = add_proof (prems_of vars cls) proofs

  fun push lit cls (level, trail, vars, clss, proofs) =
    let
      val (reason, proofs) =
        if level = 0 then apfst Level0 (mk_proof vars cls proofs)
        else (Implied cls, proofs)
    in (level, lit :: trail, assign lit reason level vars, clss, proofs) end

  fun push_decided lit (level, trail, vars, clss, proofs) =
    let val vars' = assign lit Decided (level + 1) vars
    in (level + 1, lit :: 0 :: trail, vars', clss, proofs) end

  fun prop (cls as (lits, _)) (cx as (units, state as (level, _, vars, _, _))) =
    if exists (is_true vars) lits then cx
    else if forall (is_false vars) lits then
      if level = 0 then raise UNSAT (cls, state)
      else raise CONFLICT (cls, state)
    else
      (case filter (is_unassigned vars) lits of
        [lit] => (lit :: units, push lit cls state)
      | _ => cx)

  fun propagate units (state as (_, _, _, clss, _)) =
    (case fold (fold prop o Inttab.lookup_list clss) units ([], state) of
      ([], state') => (NONE, state')
    | (units', state') => propagate units' state')
    handle CONFLICT (cls, state') => (SOME cls, state')

  fun max_unassigned (v, (NONE, _, _, rank)) (x as (_, r)) =
        if rank > r then (SOME v, rank) else x
    | max_unassigned _  x = x

  fun decide (state as (_, _, vars, _, _)) =
    (case Inttab.fold max_unassigned vars (NONE, 0) of
      (SOME lit, _) => SOME (lit, push_decided lit state)
    | (NONE, _) => NONE)

  fun mark lit = Inttab.update (abs lit, true)
  fun marked ms lit = the_default false (Inttab.lookup ms (abs lit))
  fun ignore l ms lit = ((lit = l) orelse marked ms lit)

  fun first_lit _ [] = raise Empty
    | first_lit _ (0 :: _) = raise Empty
    | first_lit pred (lit :: lits) =
        if pred lit then (lit, lits) else first_lit pred lits

  fun reason_cls_of vars lit =
    (case reason_of vars lit of
      Implied cls => cls
    | _ => raise Option)

  fun analyze conflicting_cls (level, trail, vars, _, _) =
    let
      fun back i lit (lits, p) trail ms ls ps =
        let
          val (lits0, lits') = List.partition (equal 0 o level_of vars) lits
          val lits1 = filter_out (ignore lit ms) lits'
          val lits2 = filter_out (equal level o level_of vars) lits1
          val i' = length lits1 - length lits2 + i
          val ms' = fold mark lits1 ms
          val ls' = lits2 @ ls
          val ps' = level0_proofs_of vars lits0 @ (p :: ps)
          val (lit', trail') = first_lit (marked ms') trail
        in 
          if i' = 1 then (neg lit', ls', rev ps')
          else back (i' - 1) lit' (reason_cls_of vars lit') trail' ms' ls' ps'
        end
    in back 0 0 conflicting_cls trail Inttab.empty [] [] end

  fun keep_clause (cls as (lits, _)) (level, trail, vars, clss, proofs) =
    let
      val vars' = fold (fn lit => update_var lit incr_rank) lits vars
      val clss' = fold (fn lit => Inttab.cons_list (neg lit, cls)) lits clss
    in (level, trail, vars', clss', proofs) end

  fun learn (cls as (lits, _)) = (length lits <= 2) ? keep_clause cls

  fun backjump _ (state as (_, [], _, _, _)) = state 
    | backjump i (level, 0 :: trail, vars, clss, proofs) =
        (level - 1, trail, vars, clss, proofs) |> (i > 1) ? backjump (i - 1)
    | backjump i (level, lit :: trail, vars, clss, proofs) =
        backjump i (level, trail, unassign lit vars, clss, proofs)

  fun search units state =
    (case propagate units state of
      (NONE, state' as (_, _, vars, _, _)) =>
        (case decide state' of
          NONE => SatSolver.SATISFIABLE (assignment_of vars)
        | SOME (lit, state'') => search [lit] state'')
    | (SOME conflicting_cls, state' as (level, trail, vars, clss, proofs)) =>
        let 
          val (lit, lits, ps) = analyze conflicting_cls state'
          val (idx, proofs') = add_proof ps proofs
          val cls = (lit :: lits, idx)
        in
          (level, trail, vars, clss, proofs')
          |> backjump (level - fold (Integer.max o level_of vars) lits 0)
          |> learn cls
          |> push lit cls
          |> search [lit]
        end)

  fun has_opposing_lits [] = false
    | has_opposing_lits (lit :: lits) =
        member (op =) lits (neg lit) orelse has_opposing_lits lits

  fun add_clause (cls as ([_], _)) (units, state) =
        let val (units', state') = prop cls (units, state)
        in (units', state') end
    | add_clause (cls as (lits, _)) (cx as (units, state)) =
        if has_opposing_lits lits then cx
        else (units, keep_clause cls state)

  fun mk_clause lits proofs =
    apfst (pair (distinct (op =) lits)) (add_proof [] proofs)

  fun solve litss =
    let
      val (clss, proofs) = fold_map mk_clause litss (0, Inttab.empty)
      val vars = fold (fold add_var) litss Inttab.empty
      val state = (0, [], vars, Inttab.empty, proofs)
    in uncurry search (fold add_clause clss ([], state)) end
    handle UNSAT (conflicting_cls, (_, _, vars, _, proofs)) =>
      let val (idx, (_, ptab)) = mk_proof vars conflicting_cls proofs
      in SatSolver.UNSATISFIABLE (SOME (ptab, idx)) end

  fun variable_of (Prop_Logic.BoolVar 0) = error "bad propositional variable"
    | variable_of (Prop_Logic.BoolVar i) = i
    | variable_of _ = error "expected formula in CNF"
  fun literal_of (Prop_Logic.Not fm) = neg (variable_of fm)
    | literal_of fm = variable_of fm
  fun clause_of (Prop_Logic.Or (fm1, fm2)) = clause_of fm1 @ clause_of fm2
    | clause_of fm = [literal_of fm]
  fun clauses_of (Prop_Logic.And (fm1, fm2)) = clauses_of fm1 @ clauses_of fm2
    | clauses_of Prop_Logic.True = [[1, ~1]]
    | clauses_of Prop_Logic.False = [[1], [~1]]
    | clauses_of fm = [clause_of fm]

  fun dpll_solver fm =
    let val fm' = if Prop_Logic.is_cnf fm then fm else Prop_Logic.defcnf fm
    in solve (clauses_of fm') end
in
  SatSolver.add_solver ("cdclite", dpll_solver)
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
        (* apply 'solver' to 'fm' *)
        solver fm
          handle SatSolver.NOT_CONFIGURED => loop solvers
      )
  in
    loop (SatSolver.get_solvers ())
  end
in
  SatSolver.add_solver ("auto", auto_solver)
end;

(* ------------------------------------------------------------------------- *)
(* MiniSat 1.14                                                              *)
(* (http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/)            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* "minisat_with_proofs" requires a modified version of MiniSat 1.14 by John *)
(* Matthews, which can output ASCII proof traces.  Replaying binary proof    *)
(* traces generated by MiniSat-p_v1.14 has _not_ been implemented.           *)
(* ------------------------------------------------------------------------- *)

(* add "minisat_with_proofs" _before_ "minisat" to the available solvers, so *)
(* that the latter is preferred by the "auto" solver                         *)

(* There is a complication that is dealt with in the code below: MiniSat     *)
(* introduces IDs for original clauses in the proof trace.  It does not (in  *)
(* general) follow the convention that the original clauses are numbered     *)
(* from 0 to n-1 (where n is the number of clauses in the formula).          *)

let
  exception INVALID_PROOF of string
  fun minisat_with_proofs fm =
  let
    val _          = if (getenv "MINISAT_HOME") = "" then raise SatSolver.NOT_CONFIGURED else ()
    val serial_str = serial_string ()
    val inpath     = File.tmp_path (Path.explode ("isabelle" ^ serial_str ^ ".cnf"))
    val outpath    = File.tmp_path (Path.explode ("result" ^ serial_str))
    val proofpath  = File.tmp_path (Path.explode ("result" ^ serial_str ^ ".prf"))
    val cmd        = getenv "MINISAT_HOME" ^ "/minisat " ^ File.shell_path inpath ^ " -r " ^ File.shell_path outpath ^ " -t " ^ File.shell_path proofpath ^ "> /dev/null"
    fun writefn fm = SatSolver.write_dimacs_cnf_file inpath fm
    fun readfn ()  = SatSolver.read_std_result_file outpath ("SAT", "", "UNSAT")
    val _ = if File.exists inpath then warning ("overwriting existing file " ^ Path.print inpath) else ()
    val _ = if File.exists outpath then warning ("overwriting existing file " ^ Path.print outpath) else ()
    val cnf        = Prop_Logic.defcnf fm
    val result     = SatSolver.make_external_solver cmd writefn readfn cnf
    val _          = try File.rm inpath
    val _          = try File.rm outpath
  in  case result of
    SatSolver.UNSATISFIABLE NONE =>
    (let
      val proof_lines = (split_lines o File.read) proofpath
        handle IO.Io _ => raise INVALID_PROOF "Could not read file \"result.prf\""
      (* representation of clauses as ordered lists of literals (with duplicates removed) *)
      fun clause_to_lit_list (Prop_Logic.Or (fm1, fm2)) =
        Ord_List.union int_ord (clause_to_lit_list fm1) (clause_to_lit_list fm2)
        | clause_to_lit_list (Prop_Logic.BoolVar i) =
        [i]
        | clause_to_lit_list (Prop_Logic.Not (Prop_Logic.BoolVar i)) =
        [~i]
        | clause_to_lit_list _ =
        raise INVALID_PROOF "Error: invalid clause in CNF formula."
      fun cnf_number_of_clauses (Prop_Logic.And (fm1, fm2)) =
        cnf_number_of_clauses fm1 + cnf_number_of_clauses fm2
        | cnf_number_of_clauses _ =
        1
      val number_of_clauses = cnf_number_of_clauses cnf
      (* int list array *)
      val clauses = Array.array (number_of_clauses, [])
      (* initialize the 'clauses' array *)
      fun init_array (Prop_Logic.And (fm1, fm2), n) =
        init_array (fm2, init_array (fm1, n))
        | init_array (fm, n) =
        (Array.update (clauses, n, clause_to_lit_list fm); n+1)
      val _ = init_array (cnf, 0)
      (* optimization for the common case where MiniSat "R"s clauses in their *)
      (* original order:                                                      *)
      val last_ref_clause = Unsynchronized.ref (number_of_clauses - 1)
      (* search the 'clauses' array for the given list of literals 'lits', *)
      (* starting at index '!last_ref_clause + 1'                          *)
      fun original_clause_id lits =
      let
        fun original_clause_id_from index =
          if index = number_of_clauses then
            (* search from beginning again *)
            original_clause_id_from 0
          (* both 'lits' and the list of literals used in 'clauses' are sorted, so *)
          (* testing for equality should suffice -- barring duplicate literals     *)
          else if Array.sub (clauses, index) = lits then (
            (* success *)
            last_ref_clause := index;
            SOME index
          ) else if index = !last_ref_clause then
            (* failure *)
            NONE
          else
            (* continue search *)
            original_clause_id_from (index + 1)
      in
        original_clause_id_from (!last_ref_clause + 1)
      end
      fun int_from_string s =
        (case Int.fromString s of
          SOME i => i
        | NONE   => raise INVALID_PROOF ("File format error: number expected (" ^ quote s ^ " encountered)."))
      (* parse the proof file *)
      val clause_table  = Unsynchronized.ref (Inttab.empty : int list Inttab.table)
      val empty_id      = Unsynchronized.ref ~1
      (* contains a mapping from clause IDs as used by MiniSat to clause IDs in *)
      (* our proof format, where original clauses are numbered starting from 0  *)
      val clause_id_map = Unsynchronized.ref (Inttab.empty : int Inttab.table)
      fun sat_to_proof id = (
        case Inttab.lookup (!clause_id_map) id of
          SOME id' => id'
        | NONE     => raise INVALID_PROOF ("Clause ID " ^ string_of_int id ^ " used, but not defined.")
      )
      val next_id = Unsynchronized.ref (number_of_clauses - 1)
      fun process_tokens [] =
        ()
        | process_tokens (tok::toks) =
        if tok="R" then (
          case toks of
            id::sep::lits =>
            let
              val _        = if !empty_id = ~1 then () else raise INVALID_PROOF "File format error: \"R\" disallowed after \"X\"."
              val cid      = int_from_string id
              val _        = if sep = "<=" then () else raise INVALID_PROOF ("File format error: \"<=\" expected (" ^ quote sep ^ " encountered).")
              val ls       = sort int_ord (map int_from_string lits)
              val proof_id = case original_clause_id ls of
                               SOME orig_id => orig_id
                             | NONE         => raise INVALID_PROOF ("Original clause (new ID is " ^ id ^ ") not found.")
            in
              (* extend the mapping of clause IDs with this newly defined ID *)
              clause_id_map := Inttab.update_new (cid, proof_id) (!clause_id_map)
                handle Inttab.DUP _ => raise INVALID_PROOF ("File format error: clause " ^ id ^ " defined more than once (in \"R\").")
              (* the proof itself doesn't change *)
            end
          | _ =>
            raise INVALID_PROOF "File format error: \"R\" followed by an insufficient number of tokens."
        ) else if tok="C" then (
          case toks of
            id::sep::ids =>
            let
              val _        = if !empty_id = ~1 then () else raise INVALID_PROOF "File format error: \"C\" disallowed after \"X\"."
              val cid      = int_from_string id
              val _        = if sep = "<=" then () else raise INVALID_PROOF ("File format error: \"<=\" expected (" ^ quote sep ^ " encountered).")
              (* ignore the pivot literals in MiniSat's trace *)
              fun unevens []             = raise INVALID_PROOF "File format error: \"C\" followed by an even number of IDs."
                | unevens (x :: [])      = x :: []
                | unevens (x :: _ :: xs) = x :: unevens xs
              val rs       = (map sat_to_proof o unevens o map int_from_string) ids
              (* extend the mapping of clause IDs with this newly defined ID *)
              val proof_id = Unsynchronized.inc next_id
              val _        = clause_id_map := Inttab.update_new (cid, proof_id) (!clause_id_map)
                               handle Inttab.DUP _ => raise INVALID_PROOF ("File format error: clause " ^ id ^ " defined more than once (in \"C\").")
            in
              (* update clause table *)
              clause_table := Inttab.update_new (proof_id, rs) (!clause_table)
                handle Inttab.DUP _ => raise INVALID_PROOF ("Error: internal ID for clause " ^ id ^ " already used.")
            end
          | _ =>
            raise INVALID_PROOF "File format error: \"C\" followed by an insufficient number of tokens."
        ) else if tok="D" then (
          case toks of
            [id] =>
            let
              val _ = if !empty_id = ~1 then () else raise INVALID_PROOF "File format error: \"D\" disallowed after \"X\"."
              val _ = sat_to_proof (int_from_string id)
            in
              (* simply ignore "D" *)
              ()
            end
          | _ =>
            raise INVALID_PROOF "File format error: \"D\" followed by an illegal number of tokens."
        ) else if tok="X" then (
          case toks of
            [id1, id2] =>
            let
              val _            = if !empty_id = ~1 then () else raise INVALID_PROOF "File format error: more than one end-of-proof statement."
              val _            = sat_to_proof (int_from_string id1)
              val new_empty_id = sat_to_proof (int_from_string id2)
            in
              (* update conflict id *)
              empty_id := new_empty_id
            end
          | _ =>
            raise INVALID_PROOF "File format error: \"X\" followed by an illegal number of tokens."
        ) else
          raise INVALID_PROOF ("File format error: unknown token " ^ quote tok ^ " encountered.")
      fun process_lines [] =
        ()
        | process_lines (l::ls) = (
          process_tokens (String.tokens (fn c => c = #" " orelse c = #"\t") l);
          process_lines ls
        )
      (* proof *)
      val _ = process_lines proof_lines
      val _ = if !empty_id <> ~1 then () else raise INVALID_PROOF "File format error: no conflicting clause specified."
    in
      SatSolver.UNSATISFIABLE (SOME (!clause_table, !empty_id))
    end handle INVALID_PROOF reason => (warning reason; SatSolver.UNSATISFIABLE NONE))
  | result =>
    result
  end
in
  SatSolver.add_solver ("minisat_with_proofs", minisat_with_proofs)
end;

let
  fun minisat fm =
  let
    val _          = if getenv "MINISAT_HOME" = "" then raise SatSolver.NOT_CONFIGURED else ()
    val serial_str = serial_string ()
    val inpath     = File.tmp_path (Path.explode ("isabelle" ^ serial_str ^ ".cnf"))
    val outpath    = File.tmp_path (Path.explode ("result" ^ serial_str))
    val cmd        = getenv "MINISAT_HOME" ^ "/minisat " ^ File.shell_path inpath ^ " -r " ^ File.shell_path outpath ^ " > /dev/null"
    fun writefn fm = SatSolver.write_dimacs_cnf_file inpath (Prop_Logic.defcnf fm)
    fun readfn ()  = SatSolver.read_std_result_file outpath ("SAT", "", "UNSAT")
    val _ = if File.exists inpath then warning ("overwriting existing file " ^ Path.print inpath) else ()
    val _ = if File.exists outpath then warning ("overwriting existing file " ^ Path.print outpath) else ()
    val result     = SatSolver.make_external_solver cmd writefn readfn fm
    val _          = try File.rm inpath
    val _          = try File.rm outpath
  in
    result
  end
in
  SatSolver.add_solver ("minisat", minisat)
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
      (* FIXME File.tmp_path (!?) *)
      val proof_lines = ((split_lines o File.read) (Path.explode "resolve_trace"))
        handle IO.Io _ => raise INVALID_PROOF "Could not read file \"resolve_trace\""
      fun cnf_number_of_clauses (Prop_Logic.And (fm1, fm2)) =
            cnf_number_of_clauses fm1 + cnf_number_of_clauses fm2
        | cnf_number_of_clauses _ = 1
      fun int_from_string s = (
        case Int.fromString s of
          SOME i => i
        | NONE   => raise INVALID_PROOF ("File format error: number expected (" ^ quote s ^ " encountered).")
      )
      (* parse the "resolve_trace" file *)
      val clause_offset = Unsynchronized.ref ~1
      val clause_table  = Unsynchronized.ref (Inttab.empty : int list Inttab.table)
      val empty_id      = Unsynchronized.ref ~1
      fun process_tokens [] =
        ()
        | process_tokens (tok::toks) =
        if tok="CL:" then (
          case toks of
            id::sep::ids =>
            let
              val _   = if !clause_offset = ~1 then () else raise INVALID_PROOF ("File format error: \"CL:\" disallowed after \"VAR:\".")
              val _   = if !empty_id = ~1 then () else raise INVALID_PROOF ("File format error: \"CL:\" disallowed after \"CONF:\".")
              val cid = int_from_string id
              val _   = if sep = "<=" then () else raise INVALID_PROOF ("File format error: \"<=\" expected (" ^ quote sep ^ " encountered).")
              val rs  = map int_from_string ids
            in
              (* update clause table *)
              clause_table := Inttab.update_new (cid, rs) (!clause_table)
                handle Inttab.DUP _ => raise INVALID_PROOF ("File format error: clause " ^ id ^ " defined more than once.")
            end
          | _ =>
            raise INVALID_PROOF "File format error: \"CL:\" followed by an insufficient number of tokens."
        ) else if tok="VAR:" then (
          case toks of
            id::levsep::levid::valsep::valid::antesep::anteid::litsep::lits =>
            let
              val _   = if !empty_id = ~1 then () else raise INVALID_PROOF ("File format error: \"VAR:\" disallowed after \"CONF:\".")
              (* set 'clause_offset' to the largest used clause ID *)
              val _   = if !clause_offset = ~1 then clause_offset :=
                (case Inttab.max (!clause_table) of
                  SOME (id, _) => id
                | NONE => cnf_number_of_clauses (Prop_Logic.defcnf fm) - 1  (* the first clause ID is 0, not 1 *))
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
              clause_table := Inttab.update_new (cid, rs) (!clause_table)
                handle Inttab.DUP _ => raise INVALID_PROOF ("File format error: clause " ^ string_of_int cid ^ " (derived from antecedent for variable " ^ id ^ ") already defined.")
            end
          | _ =>
            raise INVALID_PROOF "File format error: \"VAR:\" followed by an insufficient number of tokens."
        ) else if tok="CONF:" then (
          case toks of
            id::sep::ids =>
            let
              val _   = if !empty_id = ~1 then () else raise INVALID_PROOF "File format error: more than one conflicting clause specified."
              val cid = int_from_string id
              val _   = if sep = "==" then () else raise INVALID_PROOF ("File format error: \"==\" expected (" ^ quote sep ^ " encountered).")
              val ls  = map int_from_string ids
              (* the conflict clause must be resolved with the unit clauses *)
              (* for its literals to obtain the empty clause                *)
              val vids         = map (fn l => l div 2) ls
              val rs           = cid :: map (fn v => !clause_offset + v) vids
              val new_empty_id = the_default (!clause_offset) (Option.map fst (Inttab.max (!clause_table))) + 1
            in
              (* update clause table and conflict id *)
              clause_table := Inttab.update_new (new_empty_id, rs) (!clause_table)
                handle Inttab.DUP _ => raise INVALID_PROOF ("File format error: clause " ^ string_of_int new_empty_id ^ " (empty clause derived from clause " ^ id ^ ") already defined.");
              empty_id     := new_empty_id
            end
          | _ =>
            raise INVALID_PROOF "File format error: \"CONF:\" followed by an insufficient number of tokens."
        ) else
          raise INVALID_PROOF ("File format error: unknown token " ^ quote tok ^ " encountered.")
      fun process_lines [] =
        ()
        | process_lines (l::ls) = (
          process_tokens (String.tokens (fn c => c = #" " orelse c = #"\t") l);
          process_lines ls
        )
      (* proof *)
      val _ = process_lines proof_lines
      val _ = if !empty_id <> ~1 then () else raise INVALID_PROOF "File format error: no conflicting clause specified."
    in
      SatSolver.UNSATISFIABLE (SOME (!clause_table, !empty_id))
    end handle INVALID_PROOF reason => (warning reason; SatSolver.UNSATISFIABLE NONE))
  | result =>
    result
in
  SatSolver.add_solver ("zchaff_with_proofs", zchaff_with_proofs)
end;

let
  fun zchaff fm =
  let
    val _          = if getenv "ZCHAFF_HOME" = "" then raise SatSolver.NOT_CONFIGURED else ()
    val serial_str = serial_string ()
    val inpath     = File.tmp_path (Path.explode ("isabelle" ^ serial_str ^ ".cnf"))
    val outpath    = File.tmp_path (Path.explode ("result" ^ serial_str))
    val cmd        = getenv "ZCHAFF_HOME" ^ "/zchaff " ^ File.shell_path inpath ^ " > " ^ File.shell_path outpath
    fun writefn fm = SatSolver.write_dimacs_cnf_file inpath (Prop_Logic.defcnf fm)
    fun readfn ()  = SatSolver.read_std_result_file outpath ("Instance Satisfiable", "", "Instance Unsatisfiable")
    val _ = if File.exists inpath then warning ("overwriting existing file " ^ Path.print inpath) else ()
    val _ = if File.exists outpath then warning ("overwriting existing file " ^ Path.print outpath) else ()
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
    val _          = if (getenv "BERKMIN_HOME") = "" then raise SatSolver.NOT_CONFIGURED else ()
    val serial_str = serial_string ()
    val inpath     = File.tmp_path (Path.explode ("isabelle" ^ serial_str ^ ".cnf"))
    val outpath    = File.tmp_path (Path.explode ("result" ^ serial_str))
    val exec       = getenv "BERKMIN_EXE"
    val cmd        = getenv "BERKMIN_HOME" ^ "/" ^ (if exec = "" then "BerkMin561" else exec) ^ " " ^ File.shell_path inpath ^ " > " ^ File.shell_path outpath
    fun writefn fm = SatSolver.write_dimacs_cnf_file inpath (Prop_Logic.defcnf fm)
    fun readfn ()  = SatSolver.read_std_result_file outpath ("Satisfiable          !!", "solution =", "UNSATISFIABLE          !!")
    val _ = if File.exists inpath then warning ("overwriting existing file " ^ Path.print inpath) else ()
    val _ = if File.exists outpath then warning ("overwriting existing file " ^ Path.print outpath) else ()
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
    val serial_str = serial_string ()
    val inpath     = File.tmp_path (Path.explode ("isabelle" ^ serial_str ^ ".cnf"))
    val outpath    = File.tmp_path (Path.explode ("result" ^ serial_str))
    val cmd        = getenv "JERUSAT_HOME" ^ "/Jerusat1.3 " ^ File.shell_path inpath ^ " > " ^ File.shell_path outpath
    fun writefn fm = SatSolver.write_dimacs_cnf_file inpath (Prop_Logic.defcnf fm)
    fun readfn ()  = SatSolver.read_std_result_file outpath ("s SATISFIABLE", "v ", "s UNSATISFIABLE")
    val _ = if File.exists inpath then warning ("overwriting existing file " ^ Path.print inpath) else ()
    val _ = if File.exists outpath then warning ("overwriting existing file " ^ Path.print outpath) else ()
    val result     = SatSolver.make_external_solver cmd writefn readfn fm
    val _          = try File.rm inpath
    val _          = try File.rm outpath
  in
    result
  end
in
  SatSolver.add_solver ("jerusat", jerusat)
end;
