(*  Title:      HOL/Tools/refute.ML
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2003-2004

Finite model generation for HOL formulae, using an external SAT solver.
*)

(* ------------------------------------------------------------------------- *)
(* Declares the 'REFUTE' signature as well as a structure 'Refute'.  See     *)
(* 'find_model' below for a description of the implemented algorithm, and    *)
(* the Isabelle/Isar theories 'HOL/Refute.thy' and 'HOL/Main.thy' on how to  *)
(* set things up.                                                            *)
(* ------------------------------------------------------------------------- *)

signature REFUTE =
sig

	(* We use 'REFUTE' only for internal error conditions that should    *)
	(* never occur in the first place (i.e. errors caused by bugs in our *)
	(* code).  Otherwise (e.g. to indicate invalid input data) we use    *)
	(* 'error'.                                                          *)

	exception REFUTE of string * string;	(* ("in function", "cause") *)

	val setup : (theory -> theory) list

	val set_default_param : (string * string) -> theory -> theory
	val get_default_param : theory -> string -> string option
	val get_default_params : theory -> (string * string) list

	val find_model : theory -> (string * string) list -> Term.term -> unit

	val refute_term : theory -> (string * string) list -> Term.term -> unit
	val refute_subgoal : theory -> (string * string) list -> Thm.thm -> int -> unit
end;


structure Refute : REFUTE =
struct
	exception REFUTE of string * string;

	exception EMPTY_DATATYPE;

	structure RefuteDataArgs =
	struct
		val name = "Refute/refute";
		type T = string Symtab.table;
		val empty = Symtab.empty;
		val copy = I;
		val prep_ext = I;
		val merge =
			fn (symTable1, symTable2) =>
				(Symtab.merge (op=) (symTable1, symTable2));
		fun print sg symTable =
			writeln
				("'refute', default parameters:\n" ^
				(space_implode "\n" (map (fn (name,value) => name ^ " = " ^ value) (Symtab.dest symTable))))
	end;

	structure RefuteData = TheoryDataFun(RefuteDataArgs);


(* ------------------------------------------------------------------------- *)
(* INTERFACE, PART 1: INITIALIZATION, PARAMETER MANAGEMENT                   *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* use 'setup Refute.setup' in an Isabelle theory to initialize the 'Refute' *)
(* structure                                                                 *)
(* ------------------------------------------------------------------------- *)

	val setup = [RefuteData.init];

(* ------------------------------------------------------------------------- *)
(* set_default_param: stores the '(name, value)' pair in RefuteData's symbol *)
(*                    table                                                  *)
(* ------------------------------------------------------------------------- *)

	fun set_default_param (name, value) thy =
	let
		val symTable = RefuteData.get thy
	in
		case Symtab.lookup (symTable, name) of
			None   => RefuteData.put (Symtab.extend (symTable, [(name, value)])) thy
		|	Some _ => RefuteData.put (Symtab.update ((name, value), symTable)) thy
	end;

(* ------------------------------------------------------------------------- *)
(* get_default_param: retrieves the value associated with 'name' from        *)
(*                    RefuteData's symbol table                              *)
(* ------------------------------------------------------------------------- *)

	fun get_default_param thy name = Symtab.lookup (RefuteData.get thy, name);

(* ------------------------------------------------------------------------- *)
(* get_default_params: returns a list of all '(name, value)' pairs that are  *)
(*                     stored in RefuteData's symbol table                   *)
(* ------------------------------------------------------------------------- *)

	fun get_default_params thy = Symtab.dest (RefuteData.get thy);


(* ------------------------------------------------------------------------- *)
(* PROPOSITIONAL FORMULAS                                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* prop_formula: formulas of propositional logic, built from boolean         *)
(*               variables (referred to by index) and True/False using       *)
(*               not/or/and                                                  *)
(* ------------------------------------------------------------------------- *)

	datatype prop_formula =
		  True
		| False
		| BoolVar of int
		| Not of prop_formula
		| Or of prop_formula * prop_formula
		| And of prop_formula * prop_formula;

	(* the following constructor functions make sure that True and False do *)
	(* not occur within any of the other connectives (i.e. Not, Or, And)    *)

	(* prop_formula -> prop_formula *)

	fun SNot True  = False
	  | SNot False = True
	  | SNot fm    = Not fm;

	(* prop_formula * prop_formula -> prop_formula *)

	fun SOr (True, _)   = True
	  | SOr (_, True)   = True
	  | SOr (False, fm) = fm
	  | SOr (fm, False) = fm
	  | SOr (fm1, fm2)  = Or (fm1, fm2);

	(* prop_formula * prop_formula -> prop_formula *)

	fun SAnd (True, fm) = fm
	  | SAnd (fm, True) = fm
	  | SAnd (False, _) = False
	  | SAnd (_, False) = False
	  | SAnd (fm1, fm2) = And (fm1, fm2);

(* ------------------------------------------------------------------------- *)
(* list_disjunction: computes the disjunction of a list of propositional     *)
(*                   formulas                                                *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula list -> prop_formula *)

	fun list_disjunction []      = False
	  | list_disjunction (x::xs) = SOr (x, list_disjunction xs);

(* ------------------------------------------------------------------------- *)
(* list_conjunction: computes the conjunction of a list of propositional     *)
(*                   formulas                                                *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula list -> prop_formula *)

	fun list_conjunction []      = True
	  | list_conjunction (x::xs) = SAnd (x, list_conjunction xs);

(* ------------------------------------------------------------------------- *)
(* prop_formula_dot_product: [x1,...,xn] * [y1,...,yn] -> x1*y1+...+xn*yn    *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula list * prop_formula list -> prop_formula *)

	fun prop_formula_dot_product ([],[])       = False
	  | prop_formula_dot_product (x::xs,y::ys) = SOr (SAnd (x,y), prop_formula_dot_product (xs,ys))
	  | prop_formula_dot_product (_,_)         = raise REFUTE ("prop_formula_dot_product", "lists are of different length");

(* ------------------------------------------------------------------------- *)
(* prop_formula_to_nnf: computes the negation normal form of a formula 'fm'  *)
(*                      of propositional logic (i.e. only variables may be   *)
(*                      negated, but not subformulas)                        *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> prop_formula *)

	fun prop_formula_to_nnf fm =
		case fm of
		(* constants *)
		  True                => True
		| False               => False
		(* literals *)
		| BoolVar i           => BoolVar i
		| Not (BoolVar i)     => Not (BoolVar i)
		(* double-negation elimination *)
		| Not (Not fm)        => prop_formula_to_nnf fm
		(* pushing 'not' inside of 'or'/'and' using de Morgan's laws *)
		| Not (Or  (fm1,fm2)) => SAnd (prop_formula_to_nnf (SNot fm1),prop_formula_to_nnf (SNot fm2))
		| Not (And (fm1,fm2)) => SOr  (prop_formula_to_nnf (SNot fm1),prop_formula_to_nnf (SNot fm2))
		(* 'or' and 'and' as outermost connectives are left untouched *)
		| Or  (fm1,fm2)       => SOr  (prop_formula_to_nnf fm1,prop_formula_to_nnf fm2)
		| And (fm1,fm2)       => SAnd (prop_formula_to_nnf fm1,prop_formula_to_nnf fm2)
		(* 'not' + constant *)
		| Not _               => raise REFUTE ("prop_formula_to_nnf", "'True'/'False' not allowed inside of 'Not'");

(* ------------------------------------------------------------------------- *)
(* prop_formula_nnf_to_cnf: computes the conjunctive normal form of a        *)
(*      formula 'fm' of propositional logic that is given in negation normal *)
(*      form.  Note that there may occur an exponential blowup of the        *)
(*      formula.                                                             *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> prop_formula *)

	fun prop_formula_nnf_to_cnf fm =
		case fm of
		(* constants *)
		  True            => True
		| False           => False
		(* literals *)
		| BoolVar i       => BoolVar i
		| Not (BoolVar i) => Not (BoolVar i)
		(* pushing 'or' inside of 'and' using distributive laws *)
		| Or (fm1,fm2)    =>
			let
				val fm1' = prop_formula_nnf_to_cnf fm1
				val fm2' = prop_formula_nnf_to_cnf fm2
			in
				case fm1' of
				  And (fm11,fm12) => prop_formula_nnf_to_cnf (SAnd (SOr(fm11,fm2'),SOr(fm12,fm2')))
				| _               =>
					(case fm2' of
					  And (fm21,fm22) => prop_formula_nnf_to_cnf (SAnd (SOr(fm1',fm21),SOr(fm1',fm22)))
					(* neither subformula contains 'and' *)
					| _               => fm)
			end
		(* 'and' as outermost connective is left untouched *)
		| And (fm1,fm2)   => SAnd (prop_formula_nnf_to_cnf fm1, prop_formula_nnf_to_cnf fm2)
		(* error *)
		| _               => raise REFUTE ("prop_formula_nnf_to_cnf", "formula is not in negation normal form");

(* ------------------------------------------------------------------------- *)
(* max: computes the maximum of two integer values 'i' and 'j'               *)
(* ------------------------------------------------------------------------- *)

	(* int * int -> int *)

	fun max (i,j) =
		if (i>j) then i else j;

(* ------------------------------------------------------------------------- *)
(* max_var_index: computes the maximal variable index occuring in 'fm',      *)
(*      where 'fm' is a formula of propositional logic                       *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> int *)

	fun max_var_index fm =
		case fm of
		  True          => 0
		| False         => 0
		| BoolVar i     => i
		| Not fm1       => max_var_index fm1
		| And (fm1,fm2) => max (max_var_index fm1, max_var_index fm2)
		| Or (fm1,fm2)  => max (max_var_index fm1, max_var_index fm2);

(* ------------------------------------------------------------------------- *)
(* prop_formula_nnf_to_def_cnf: computes the definitional conjunctive normal *)
(*      form of a formula 'fm' of propositional logic that is given in       *)
(*      negation normal form.  To avoid an exponential blowup of the         *)
(*      formula, auxiliary variables may be introduced.  The result formula  *)
(*      is SAT-equivalent to 'fm' (i.e. it is satisfiable if and only if     *)
(*      'fm' is satisfiable).                                                *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> prop_formula *)

	fun prop_formula_nnf_to_def_cnf fm =
	let
		(* prop_formula * int -> prop_formula * int *)
		fun prop_formula_nnf_to_def_cnf_new (fm,new) =
		(* 'new' specifies the next index that is available to introduce an auxiliary variable *)
			case fm of
			(* constants *)
			  True            => (True, new)
			| False           => (False, new)
			(* literals *)
			| BoolVar i       => (BoolVar i, new)
			| Not (BoolVar i) => (Not (BoolVar i), new)
			(* pushing 'or' inside of 'and' using distributive laws *)
			| Or (fm1,fm2)    =>
				let
					val fm1' = prop_formula_nnf_to_def_cnf_new (fm1, new)
					val fm2' = prop_formula_nnf_to_def_cnf_new (fm2, snd fm1')
				in
					case fst fm1' of
					  And (fm11,fm12) =>
						let
							val aux = BoolVar (snd fm2')
						in
							(* '(fm11 AND fm12) OR fm2' is SAT-equivalent to '(fm11 OR aux) AND (fm12 OR aux) AND (fm2 OR NOT aux)' *)
							prop_formula_nnf_to_def_cnf_new (SAnd (SAnd (SOr (fm11,aux), SOr (fm12,aux)), SOr(fst fm2', Not aux)), (snd fm2')+1)
						end
					| _               =>
						(case fst fm2' of
						  And (fm21,fm22) =>
							let
								val aux = BoolVar (snd fm2')
							in
								(* 'fm1 OR (fm21 AND fm22)' is SAT-equivalent to '(fm1 OR NOT aux) AND (fm21 OR aux) AND (fm22 OR NOT aux)' *)
								prop_formula_nnf_to_def_cnf_new (SAnd (SOr (fst fm1', Not aux), SAnd (SOr (fm21,aux), SOr (fm22,aux))), (snd fm2')+1)
							end
						(* neither subformula contains 'and' *)
						| _               => (fm, new))
				end
			(* 'and' as outermost connective is left untouched *)
			| And (fm1,fm2)   =>
				let
					val fm1' = prop_formula_nnf_to_def_cnf_new (fm1, new)
					val fm2' = prop_formula_nnf_to_def_cnf_new (fm2, snd fm1')
				in
					(SAnd (fst fm1', fst fm2'), snd fm2')
				end
			(* error *)
			| _               => raise REFUTE ("prop_formula_nnf_to_def_cnf", "formula is not in negation normal form")
	in
		fst (prop_formula_nnf_to_def_cnf_new (fm, (max_var_index fm)+1))
	end;

(* ------------------------------------------------------------------------- *)
(* prop_formula_to_cnf: computes the conjunctive normal form of a formula    *)
(*                      'fm' of propositional logic                          *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> prop_formula *)

	fun prop_formula_to_cnf fm =
		prop_formula_nnf_to_cnf (prop_formula_to_nnf fm);

(* ------------------------------------------------------------------------- *)
(* prop_formula_to_def_cnf: computes the definitional conjunctive normal     *)
(*      form of a formula 'fm' of propositional logic, introducing auxiliary *)
(*      variables if necessary to avoid an exponential blowup of the formula *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> prop_formula *)

	fun prop_formula_to_def_cnf fm =
		prop_formula_nnf_to_def_cnf (prop_formula_to_nnf fm);

(* ------------------------------------------------------------------------- *)
(* prop_formula_to_dimacs_cnf_format: serializes a formula of propositional  *)
(*      logic to a file in DIMACS CNF format (see "Satisfiability Suggested  *)
(*      Format", May 8 1993, Section 2.1)                                    *)
(* fm  : formula to be serialized.  Note: 'fm' must not contain a variable   *)
(*       index less than 1.                                                  *)
(* def : If true, translate 'fm' into definitional CNF.  Otherwise translate *)
(*       'fm' into CNF.                                                      *)
(* path: path of the file to be created                                      *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> bool -> Path.T -> unit *)

	fun prop_formula_to_dimacs_cnf_format fm def path =
	let
		(* prop_formula *)
		val cnf =
			if def then
				prop_formula_to_def_cnf fm
			else
				prop_formula_to_cnf fm
		val fm' =
			case cnf of
			  True  => Or (BoolVar 1, Not (BoolVar 1))
			| False => And (BoolVar 1, Not (BoolVar 1))
			| _     => cnf (* either 'cnf'=True/False, or 'cnf' does not contain True/False at all *)
		(* prop_formula -> int *)
		fun cnf_number_of_clauses (And (fm1,fm2)) =
			(cnf_number_of_clauses fm1) + (cnf_number_of_clauses fm2)
		  | cnf_number_of_clauses _ =
			1
		(* prop_formula -> string *)
		fun cnf_prop_formula_to_string (BoolVar i) =
			if (i<1) then
				raise REFUTE ("prop_formula_to_dimacs_cnf_format", "formula contains a variable index less than 1")
			else
				(string_of_int i)
		  | cnf_prop_formula_to_string (Not fm1) =
			"-" ^ (cnf_prop_formula_to_string fm1)
		  | cnf_prop_formula_to_string (Or (fm1,fm2)) =
			(cnf_prop_formula_to_string fm1) ^ " " ^ (cnf_prop_formula_to_string fm2)
		  | cnf_prop_formula_to_string (And (fm1,fm2)) =
			(cnf_prop_formula_to_string fm1) ^ " 0\n" ^ (cnf_prop_formula_to_string fm2)
		  | cnf_prop_formula_to_string _ =
			raise REFUTE ("prop_formula_to_dimacs_cnf_format", "formula contains True/False")
	in
		File.write path ("c This file was generated by prop_formula_to_dimacs_cnf_format\n"
			^ "c (c) Tjark Weber\n"
			^ "p cnf " ^ (string_of_int (max_var_index fm')) ^ " " ^ (string_of_int (cnf_number_of_clauses fm')) ^ "\n"
			^ (cnf_prop_formula_to_string fm') ^ "\n")
	end;

(* ------------------------------------------------------------------------- *)
(* prop_formula_to_dimacs_sat_format: serializes a formula of propositional  *)
(*      logic to a file in DIMACS SAT format (see "Satisfiability Suggested  *)
(*      Format", May 8 1993, Section 2.2)                                    *)
(* fm  : formula to be serialized.  Note: 'fm' must not contain a variable   *)
(*       index less than 1.                                                  *)
(* path: path of the file to be created                                      *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> Path.T -> unit *)

	fun prop_formula_to_dimacs_sat_format fm path =
	let
		fun prop_formula_to_string True =
			"*()"
		  | prop_formula_to_string False =
			"+()"
		  | prop_formula_to_string (BoolVar i) =
			if (i<1) then
				raise REFUTE ("prop_formula_to_dimacs_sat_format", "formula contains a variable index less than 1")
			else
				(string_of_int i)
		  | prop_formula_to_string (Not fm1) =
			"-(" ^ (prop_formula_to_string fm1) ^ ")"
		  | prop_formula_to_string (Or (fm1,fm2)) =
			"+(" ^ (prop_formula_to_string fm1) ^ " " ^ (prop_formula_to_string fm2) ^ ")"
		  | prop_formula_to_string (And (fm1,fm2)) =
			"*(" ^ (prop_formula_to_string fm1) ^ " " ^ (prop_formula_to_string fm2) ^ ")"
	in
		File.write path ("c This file was generated by prop_formula_to_dimacs_sat_format\n"
			^ "c (c) Tjark Weber\n"
			^ "p sat " ^ (string_of_int (max (max_var_index fm, 1))) ^ "\n"
			^ "(" ^ (prop_formula_to_string fm) ^ ")\n")
	end;

(* ------------------------------------------------------------------------- *)
(* prop_formula_sat_solver: try to find a satisfying assignment for the      *)
(*      boolean variables in a propositional formula, using an external SAT  *)
(*      solver.  If the SAT solver did not find an assignment, 'None' is     *)
(*      returned.  Otherwise 'Some (list of integers)' is returned, where    *)
(*      i>0 means that the boolean variable i is set to TRUE, and i<0 means  *)
(*      that the boolean variable i is set to FALSE.  Note that if           *)
(*      'satformat' is 'defcnf', then the assignment returned may contain    *)
(*      auxiliary variables that were not present in the original formula    *)
(*      'fm'.                                                                *)
(* fm        : formula that is passed to the SAT solver                      *) 
(* satpath   : path of the file used to store the propositional formula,     *)
(*             i.e. the input to the SAT solver                              *)
(* satformat : format of the SAT solver's input file.  Must be either "cnf", *)
(*             "defcnf", or "sat".                                           *)
(* resultpath: path of the file containing the SAT solver's output           *)
(* success   : part of the line in the SAT solver's output that is followed  *)
(*             by a line consisting of a list of integers representing the   *)
(*             satisfying assignment                                         *)
(* command   : system command used to execute the SAT solver                 *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> Path.T -> string -> Path.T -> string -> string -> int list option *)

	fun prop_formula_sat_solver fm satpath satformat resultpath success command =
		if File.exists satpath then
			error ("file '" ^ (Path.pack satpath) ^ "' exists, please delete (will not overwrite)")
		else if File.exists resultpath then
			error ("file '" ^ (Path.pack resultpath) ^ "' exists, please delete (will not overwrite)")
		else
		(
			(* serialize the formula 'fm' to a file *)
			if satformat="cnf" then
				prop_formula_to_dimacs_cnf_format fm false satpath
			else if satformat="defcnf" then
				prop_formula_to_dimacs_cnf_format fm true satpath
			else if satformat="sat" then
				prop_formula_to_dimacs_sat_format fm satpath
			else
				error ("invalid argument: satformat='" ^ satformat ^ "' (must be either 'cnf', 'defcnf', or 'sat')");
			(* execute SAT solver *)
			if (system command)<>0 then
			(
				(* error executing SAT solver *)
				File.rm satpath;
				File.rm resultpath;
				error ("system command '" ^ command ^ "' failed (make sure a SAT solver is installed)")
			)
			else
			(
				(* read assignment from the result file *)
				File.rm satpath;
				let
					(* 'a option -> 'a Library.option *)
					fun option (SOME a) =
						Some a
					  | option NONE =
						None
					(* string -> int list *)
					fun string_to_int_list s =
						mapfilter (option o Int.fromString) (space_explode " " s)
					(* string -> string -> bool *)
					fun is_substring s1 s2 =
					let
						val length1 = String.size s1
						val length2 = String.size s2
					in
						if length2 < length1 then
							false
						else if s1 = String.substring (s2, 0, length1) then
							true
						else is_substring s1 (String.substring (s2, 1, length2-1))
					end
					(* string list -> int list option *)
					fun extract_solution [] =
						None
					  | extract_solution (line::lines) =
						if is_substring success line then
							(* the next line must be a list of integers *)
							Some (string_to_int_list (hd lines))
						else
							extract_solution lines
					val sat_result = File.read resultpath
				in
					File.rm resultpath;
					extract_solution (split_lines sat_result)
				end
			)
		);


(* ------------------------------------------------------------------------- *)
(* TREES                                                                     *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* tree: implements an arbitrarily (but finitely) branching tree as a list   *)
(*       of (lists of ...) elements                                          *)
(* ------------------------------------------------------------------------- *)

	datatype 'a tree =
		  Leaf of 'a
		| Node of ('a tree) list;

	type prop_tree =
		prop_formula list tree;

	(* ('a -> 'b) -> 'a tree -> 'b tree *)

	fun tree_map f tr =
		case tr of
		  Leaf x  => Leaf (f x)
		| Node xs => Node (map (tree_map f) xs);

	(* ('a * 'b -> 'a) -> 'a * ('b tree) -> 'a *)

	fun tree_foldl f =
	let
		fun itl (e, Leaf x)  = f(e,x)
		  | itl (e, Node xs) = foldl (tree_foldl f) (e,xs)
	in
		itl
	end;

	(* 'a tree * 'b tree -> ('a * 'b) tree *)

	fun tree_pair (t1,t2) =
		case t1 of
		  Leaf x =>
			(case t2 of
				  Leaf y => Leaf (x,y)
				| Node _ => raise REFUTE ("tree_pair", "trees are of different height (second tree is higher)"))
		| Node xs =>
			(case t2 of
				  (* '~~' will raise an exception if the number of branches in both trees is different at the current node *)
				  Node ys => Node (map tree_pair (xs ~~ ys))
				| Leaf _  => raise REFUTE ("tree_pair", "trees are of different height (first tree is higher)"));

(* ------------------------------------------------------------------------- *)
(* prop_tree_to_true: returns a propositional formula that is true iff the   *)
(*      tree denotes the boolean value TRUE                                  *)
(* ------------------------------------------------------------------------- *)

	(* prop_tree -> prop_formula *)

	(* a term of type 'bool' is represented as a 2-element leaf, where *)
	(* the term is true iff the leaf's first element is true           *)

	fun prop_tree_to_true (Leaf [fm,_]) =
		fm
	  | prop_tree_to_true _ =
		raise REFUTE ("prop_tree_to_true", "tree is not a 2-element leaf");

(* ------------------------------------------------------------------------- *)
(* prop_tree_to_false: returns a propositional formula that is true iff the  *)
(*      tree denotes the boolean value FALSE                                 *)
(* ------------------------------------------------------------------------- *)

	(* prop_tree -> prop_formula *)

	(* a term of type 'bool' is represented as a 2-element leaf, where *)
	(* the term is false iff the leaf's second element is true         *)

	fun prop_tree_to_false (Leaf [_,fm]) =
		fm
	  | prop_tree_to_false _ =
		raise REFUTE ("prop_tree_to_false", "tree is not a 2-element leaf");

(* ------------------------------------------------------------------------- *)
(* restrict_to_single_element: returns a propositional formula which is true *)
(*      iff the tree 'tr' describes a single element of its corresponding    *)
(*      type, i.e. iff at each leaf, one and only one formula is true        *)
(* ------------------------------------------------------------------------- *)

	(* prop_tree -> prop_formula *)

	fun restrict_to_single_element tr =
	let
		(* prop_formula list -> prop_formula *)
		fun allfalse []      = True
		  | allfalse (x::xs) = SAnd (SNot x, allfalse xs)
		(* prop_formula list -> prop_formula *)
		fun exactly1true []      = False
		  | exactly1true (x::xs) = SOr (SAnd (x, allfalse xs), SAnd (SNot x, exactly1true xs))
	in
		case tr of
		  Leaf [BoolVar _, Not (BoolVar _)] => True (* optimization for boolean variables *)
		| Leaf xs                           => exactly1true xs
		| Node trees                        => list_conjunction (map restrict_to_single_element trees)
	end;

(* ------------------------------------------------------------------------- *)
(* HOL FORMULAS                                                              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* absvar: form an abstraction over a schematic variable                     *)
(* ------------------------------------------------------------------------- *)

	(* Term.indexname * Term.typ * Term.term -> Term.term *)

	(* this function is similar to Term.absfree, but for schematic       *)
	(* variables (rather than free variables)                            *)
	fun absvar ((x,i),T,body) =
		Abs(x, T, abstract_over (Var((x,i),T), body));

(* ------------------------------------------------------------------------- *)
(* list_all_var: quantification over a list of schematic variables           *)
(* ------------------------------------------------------------------------- *)

	(* (Term.indexname * Term.typ) list * Term.term -> Term.term *)

	(* this function is similar to Term.list_all_free, but for schematic *)
	(* variables (rather than free variables)                            *)
	fun list_all_var ([], t) =
		t
	  | list_all_var ((idx,T)::vars, t) =
		(all T) $ (absvar(idx, T, list_all_var(vars,t)));

(* ------------------------------------------------------------------------- *)
(* close_vars: close up a formula over all schematic variables by            *)
(*             quantification (note that the result term may still contain   *)
(*             (non-schematic) free variables)                               *)
(* ------------------------------------------------------------------------- *)

	(* Term.term -> Term.term *)

	(* this function is similar to Logic.close_form, but for schematic   *)
	(* variables (rather than free variables)                            *)
	fun close_vars A =
		list_all_var (sort_wrt (fst o fst) (map dest_Var (term_vars A)), A);

(* ------------------------------------------------------------------------- *)
(* make_universes: given a list 'xs' of "types" and a universe size 'size',  *)
(*      this function returns all possible partitions of the universe into   *)
(*      the "types" in 'xs' such that no "type" is empty.  If 'size' is less *)
(*      than 'length xs', the returned list of partitions is empty.          *)
(*      Otherwise, if the list 'xs' is empty, then the returned list of      *)
(*      partitions contains only the empty list, regardless of 'size'.       *)
(* ------------------------------------------------------------------------- *)

	(* 'a list -> int -> ('a * int) list list *)

	fun make_universes xs size =
	let
		(* 'a list -> int -> int -> ('a * int) list list *)
		fun make_partitions_loop (x::xs) 0 total =
			map (fn us => ((x,0)::us)) (make_partitions xs total)
		  | make_partitions_loop (x::xs) first total =
			(map (fn us => ((x,first)::us)) (make_partitions xs (total-first))) @ (make_partitions_loop (x::xs) (first-1) total)
		  | make_partitions_loop _ _ _ =
			raise REFUTE ("make_universes::make_partitions_loop", "empty list")
		and
		(* 'a list -> int -> ('a * int) list list *)
		make_partitions [x] size =
			(* we must use all remaining elements on the type 'x', so there is only one partition *)
			[[(x,size)]]
		  | make_partitions (x::xs) 0 =
			(* there are no elements left in the universe, so there is only one partition *)
			[map (fn t => (t,0)) (x::xs)]
		  | make_partitions (x::xs) size =
			(* we assign either size, size-1, ..., 1 or 0 elements to 'x'; the remaining elements are partitioned recursively *)
			make_partitions_loop (x::xs) size size
		  | make_partitions _ _ =
			raise REFUTE ("make_universes::make_partitions", "empty list")
		val len = length xs
	in
		if size<len then
			(* the universe isn't big enough to make every type non-empty *)
			[]
		else if xs=[] then
			(* no types: return one universe, regardless of the size *)
			[[]]
		else
			(* partition into possibly empty types, then add 1 element to each type *)
			map (fn us => map (fn (x,i) => (x,i+1)) us) (make_partitions xs (size-len))
	end;

(* ------------------------------------------------------------------------- *)
(* sum: computes the sum of a list of integers; sum [] = 0                   *)
(* ------------------------------------------------------------------------- *)

	(* int list -> int *)

	fun sum xs = foldl op+ (0, xs);

(* ------------------------------------------------------------------------- *)
(* product: computes the product of a list of integers; product [] = 1       *)
(* ------------------------------------------------------------------------- *)

	(* int list -> int *)

	fun product xs = foldl op* (1, xs);

(* ------------------------------------------------------------------------- *)
(* power: power(a,b) computes a^b, for a>=0, b>=0                            *)
(* ------------------------------------------------------------------------- *)

	(* int * int -> int *)

	fun power (a,0) = 1
	  | power (a,1) = a
	  | power (a,b) = let val ab = power(a,b div 2) in ab * ab * power(a,b mod 2) end;

(* ------------------------------------------------------------------------- *)
(* size_of_type: returns the size of a type, where 'us' specifies the size   *)
(*      of each basic type (i.e. each type variable), and 'cdepth' specifies *)
(*      the maximal constructor depth for inductive datatypes                *)
(* ------------------------------------------------------------------------- *)

	(* Term.typ -> (Term.typ * int) list -> theory -> int -> int *)

	fun size_of_type T us thy cdepth =
	let
		(* Term.typ -> (Term.typ * int) -> int *)
		fun lookup_size T [] =
			raise REFUTE ("size_of_type", "no size specified for type variable '" ^ (Sign.string_of_typ (sign_of thy) T) ^ "'")
		  | lookup_size T ((typ,size)::pairs) =
			if T=typ then size else lookup_size T pairs
	in
		case T of
		  Type ("prop", [])     => 2
		| Type ("bool", [])     => 2
		| Type ("Product_Type.unit", []) => 1
		| Type ("+", [T1,T2])   => (size_of_type T1 us thy cdepth) + (size_of_type T2 us thy cdepth)
		| Type ("*", [T1,T2])   => (size_of_type T1 us thy cdepth) * (size_of_type T2 us thy cdepth)
		| Type ("fun", [T1,T2]) => power (size_of_type T2 us thy cdepth, size_of_type T1 us thy cdepth)
		| Type ("set", [T1])    => size_of_type (Type ("fun", [T1, HOLogic.boolT])) us thy cdepth
		| Type (s, Ts)          =>
			(case DatatypePackage.datatype_info thy s of
			  Some info => (* inductive datatype *)
				if cdepth>0 then
					let
						val index               = #index info
						val descr               = #descr info
						val (_, dtyps, constrs) = the (assoc (descr, index))
						val Typs                = dtyps ~~ Ts
						(* DatatypeAux.dtyp -> Term.typ *)
						fun typ_of_dtyp (DatatypeAux.DtTFree a) =
							the (assoc (Typs, DatatypeAux.DtTFree a))
						  | typ_of_dtyp (DatatypeAux.DtRec i) =
							let
								val (s, ds, _) = the (assoc (descr, i))
							in
								Type (s, map typ_of_dtyp ds)
							end
						  | typ_of_dtyp (DatatypeAux.DtType (s, ds)) =
							Type (s, map typ_of_dtyp ds)
					in
						sum (map (fn (_,ds) => product (map (fn d => size_of_type (typ_of_dtyp d) us thy (cdepth-1)) ds)) constrs)
					end
				else 0
			| None      => error ("size_of_type: type contains an unknown type constructor: '" ^ s ^ "'"))
		| TFree _               => lookup_size T us
		| TVar _                => lookup_size T us
	end;

(* ------------------------------------------------------------------------- *)
(* type_to_prop_tree: creates a tree of boolean variables that denotes an    *)
(*      element of the type 'T'.  The height and branching factor of the     *)
(*      tree depend on the size and "structure" of 'T'.                      *)
(* 'us' : a "universe" specifying the number of elements for each basic type *)
(*        (i.e. each type variable) in 'T'                                   *)
(* 'cdepth': maximum constructor depth to be used for inductive datatypes    *)
(* 'idx': the next index to be used for a boolean variable                   *)
(* ------------------------------------------------------------------------- *)

	(* Term.typ -> (Term.typ * int) list -> theory -> int -> int -> prop_tree * int *)

	fun type_to_prop_tree T us thy cdepth idx =
	let
		(* int -> Term.typ -> int -> prop_tree list * int *)
		fun type_to_prop_tree_list 1 T' idx' =
			let val (tr, newidx) = type_to_prop_tree T' us thy cdepth idx' in
				([tr], newidx)
			end
		  | type_to_prop_tree_list n T' idx' =
			let val (tr, newidx) = type_to_prop_tree T' us thy cdepth idx' in
				let val (trees, lastidx) = type_to_prop_tree_list (n-1) T' newidx in
					(tr::trees, lastidx)
				end
			end
	in
		case T of
		  Type ("prop", []) =>
			(Leaf [BoolVar idx, Not (BoolVar idx)], idx+1)
		| Type ("bool", []) =>
			(Leaf [BoolVar idx, Not (BoolVar idx)], idx+1)
		| Type ("Product_Type.unit", []) =>
			(Leaf [True], idx)
		| Type ("+", [T1,T2]) =>
			let
				val s1 = size_of_type T1 us thy cdepth
				val s2 = size_of_type T2 us thy cdepth
				val s  = s1 + s2
			in
				if s1=0 orelse s2=0 then (* could use 'andalso' instead? *)
					raise EMPTY_DATATYPE
				else
					error "sum types (+) not implemented yet (TODO)"
			end
		| Type ("*", [T1,T2]) =>
			let
				val s1 = size_of_type T1 us thy cdepth
				val s2 = size_of_type T2 us thy cdepth
				val s  = s1 * s2
			in
				if s1=0 orelse s2=0 then
					raise EMPTY_DATATYPE
				else
					error "product types (*) not implemented yet (TODO)"
			end
		| Type ("fun", [T1,T2]) =>
			(* we create 'size_of_type T1' different copies of the tree for 'T2', *)
			(* which are then combined into a single new tree                     *)
			let
				val s = size_of_type T1 us thy cdepth
			in
				if s=0 then
					raise EMPTY_DATATYPE
				else
					let val (trees, newidx) = type_to_prop_tree_list s T2 idx in
						(Node trees, newidx)
					end
			end
		| Type ("set", [T1]) =>
			type_to_prop_tree (Type ("fun", [T1, HOLogic.boolT])) us thy cdepth idx
		| Type (s, _) =>
			(case DatatypePackage.constrs_of thy s of
			   Some _ => (* inductive datatype *)
					let
						val s = size_of_type T us thy cdepth
					in
						if s=0 then
							raise EMPTY_DATATYPE
						else
							(Leaf (map (fn i => BoolVar i) (idx upto (idx+s-1))), idx+s)
					end
			 | None   => error ("type_to_prop_tree: type contains an unknown type constructor: '" ^ s ^ "'"))
		| TFree _ =>
			let val s = size_of_type T us thy cdepth in
				(Leaf (map (fn i => BoolVar i) (idx upto (idx+s-1))), idx+s)
			end
		| TVar _  =>
			let val s = size_of_type T us thy cdepth in
				(Leaf (map (fn i => BoolVar i) (idx upto (idx+s-1))), idx+s)
			end
	end;

(* ------------------------------------------------------------------------- *)
(* type_to_constants: creates a list of prop_trees with constants (True,     *)
(*      False) rather than boolean variables, one for every element in the   *)
(*      type 'T'; c.f. type_to_prop_tree                                     *)
(* ------------------------------------------------------------------------- *)

	(* Term.typ -> (Term.typ * int) list -> theory -> int -> prop_tree list *)

	fun type_to_constants T us thy cdepth =
	let
		(* returns a list with all unit vectors of length n *)
		(* int -> prop_tree list *)
		fun unit_vectors n =
		let
			(* returns the k-th unit vector of length n *)
			(* int * int -> prop_tree *)
			fun unit_vector (k,n) =
				Leaf ((replicate (k-1) False) @ (True :: (replicate (n-k) False)))
			(* int -> prop_tree list -> prop_tree list *)
			fun unit_vectors_acc k vs =
				if k>n then [] else (unit_vector (k,n))::(unit_vectors_acc (k+1) vs)
		in
			unit_vectors_acc 1 []
		end
		(* concatenates 'x' with every list in 'xss', returning a new list of lists *)
		(* 'a -> 'a list list -> 'a list list *)
		fun cons_list x xss =
			map (fn xs => x::xs) xss
		(* returns a list of lists, each one consisting of n (possibly identical) elements from 'xs' *)
		(* int -> 'a list -> 'a list list *)
		fun pick_all 1 xs =
			map (fn x => [x]) xs
		  | pick_all n xs =
			let val rec_pick = pick_all (n-1) xs in
				foldl (fn (acc,x) => (cons_list x rec_pick) @ acc) ([],xs)
			end
	in
		case T of
		  Type ("prop", [])     => unit_vectors 2
		| Type ("bool", [])     => unit_vectors 2
		| Type ("Product_Type.unit", []) => unit_vectors 1
                | Type ("+", [T1,T2])   =>
			let
				val s1 = size_of_type T1 us thy cdepth
				val s2 = size_of_type T2 us thy cdepth
			in
				if s1=0 orelse s2=0 then (* could use 'andalso' instead? *)
					raise EMPTY_DATATYPE
				else
					error "sum types (+) not implemented yet (TODO)"
			end
                | Type ("*", [T1,T2])   =>
			let
				val s1 = size_of_type T1 us thy cdepth
				val s2 = size_of_type T2 us thy cdepth
			in
				if s1=0 orelse s2=0 then
					raise EMPTY_DATATYPE
				else
					error "product types (*) not implemented yet (TODO)"
			end
		| Type ("fun", [T1,T2]) =>
			let
				val s = size_of_type T1 us thy cdepth
			in
				if s=0 then
					raise EMPTY_DATATYPE
				else
					map (fn xs => Node xs) (pick_all s (type_to_constants T2 us thy cdepth))
			end
		| Type ("set", [T1])    => type_to_constants (Type ("fun", [T1, HOLogic.boolT])) us thy cdepth
		| Type (s, _)           =>
			(case DatatypePackage.constrs_of thy s of
			   Some _ => (* inductive datatype *)
					let
						val s = size_of_type T us thy cdepth
					in
						if s=0 then
							raise EMPTY_DATATYPE
						else
							unit_vectors s
					end
			 | None   => error ("type_to_constants: type contains an unknown type constructor: '" ^ s ^ "'"))
		| TFree _               => unit_vectors (size_of_type T us thy cdepth)
		| TVar _                => unit_vectors (size_of_type T us thy cdepth)
	end;

(* ------------------------------------------------------------------------- *)
(* prop_tree_equal: returns a propositional formula that is true iff 'tr1'   *)
(*      and 'tr2' both denote the same element                               *)
(* ------------------------------------------------------------------------- *)

	(* prop_tree * prop_tree -> prop_formula *)

	fun prop_tree_equal (tr1,tr2) =
		case tr1 of
		  Leaf x =>
			(case tr2 of
			  Leaf y => prop_formula_dot_product (x,y)
			| _      => raise REFUTE ("prop_tree_equal", "second tree is higher"))
		| Node xs =>
			(case tr2 of
			  Leaf _  => raise REFUTE ("prop_tree_equal", "first tree is higher")
			(* extensionality: two functions are equal iff they are equal for every element *)
			| Node ys => list_conjunction (map prop_tree_equal (xs ~~ ys)));

(* ------------------------------------------------------------------------- *)
(* prop_tree_apply: returns a tree that denotes the element obtained by      *)
(*      applying the function which is denoted by the tree 't1' to the       *)
(*      element which is denoted by the tree 't2'                            *)
(* ------------------------------------------------------------------------- *)

	(* prop_tree * prop_tree -> prop_tree *)

	fun prop_tree_apply (tr1,tr2) =
	let
		(* prop_tree * prop_tree -> prop_tree *)
		fun prop_tree_disjunction (tr1,tr2) =
			tree_map (fn (xs,ys) => map (fn (x,y) => SOr(x,y)) (xs ~~ ys)) (tree_pair (tr1,tr2))
		(* prop_formula * prop_tree -> prop_tree *)
		fun prop_formula_times_prop_tree (fm,tr) =
			tree_map (map (fn x => SAnd (fm,x))) tr
		(* prop_formula list * prop_tree list -> prop_tree *)
		fun prop_formula_list_dot_product_prop_tree_list ([fm],[tr]) =
			prop_formula_times_prop_tree (fm,tr)
		  | prop_formula_list_dot_product_prop_tree_list (fm::fms,tr::trees) =
			prop_tree_disjunction (prop_formula_times_prop_tree (fm,tr), prop_formula_list_dot_product_prop_tree_list (fms,trees))
		  | prop_formula_list_dot_product_prop_tree_list (_,_) =
			raise REFUTE ("prop_tree_apply::prop_formula_list_dot_product_prop_tree_list", "empty list")
		(* concatenates 'x' with every list in 'xss', returning a new list of lists *)
		(* 'a -> 'a list list -> 'a list list *)
		fun cons_list x xss =
			map (fn xs => x::xs) xss
		(* returns a list of lists, each one consisting of one element from each element of 'xss' *)
		(* 'a list list -> 'a list list *)
		fun pick_all [xs] =
			map (fn x => [x]) xs
		  | pick_all (xs::xss) =
			let val rec_pick = pick_all xss in
				foldl (fn (acc,x) => (cons_list x rec_pick) @ acc) ([],xs)
			end
		  | pick_all _ =
			raise REFUTE ("prop_tree_apply::pick_all", "empty list")
		(* prop_tree -> prop_formula list *)
		fun prop_tree_to_prop_formula_list (Leaf xs) =
			xs
		  | prop_tree_to_prop_formula_list (Node trees) =
			map list_conjunction (pick_all (map prop_tree_to_prop_formula_list trees))
	in
		case tr1 of
		  Leaf _ =>
			raise REFUTE ("prop_tree_apply", "first tree is a leaf")
		| Node xs =>
			prop_formula_list_dot_product_prop_tree_list (prop_tree_to_prop_formula_list tr2, xs)
	end

(* ------------------------------------------------------------------------- *)
(* term_to_prop_tree: translates a HOL term 't' into a tree of propositional *)
(*      formulas; 'us' specifies the number of elements for each type        *)
(*      variable in 't'; 'cdepth' specifies the maximal constructor depth    *)
(*      for inductive datatypes.  Also returns the lowest index that was not *)
(*      used for a boolean variable, and a substitution of terms (free/      *)
(*      schematic variables) by prop_trees.                                  *)
(* ------------------------------------------------------------------------- *)

	(* Term.term -> (Term.typ * int) list -> theory -> int -> prop_tree * (int * (Term.term * prop_tree) list) *)

	fun term_to_prop_tree t us thy cdepth =
	let
		(* Term.term -> int * (Term.term * prop_tree) list -> prop_tree * (int * (Term.term * prop_tree) list) *)
		fun variable_to_prop_tree_subst t' (idx,subs) =
			case assoc (subs,t') of
			  Some tr =>
				(* return the previously associated tree; the substitution remains unchanged *)
				(tr, (idx,subs))
			| None =>
				(* generate a new tree; update the index; extend the substitution *)
				let
					val T = case t' of
						  Free (_,T) => T
						| Var (_,T)  => T
						| _          => raise REFUTE ("variable_to_prop_tree_subst", "term is not a (free or schematic) variable")
					val (tr,newidx) = type_to_prop_tree T us thy cdepth idx
				in
					(tr, (newidx, (t',tr)::subs))
				end
		(* Term.term -> int * (Term.term * prop_tree) list -> prop_tree list -> prop_tree * (int * (Term.term * prop_tree) list) *)
		fun term_to_prop_tree_subst t' (idx,subs) bsubs =
			case t' of
			(* meta-logical constants *)
			  Const ("Goal", _) $ t1 =>
				term_to_prop_tree_subst t1 (idx,subs) bsubs
			| Const ("all", _) $ t1 =>
				let
					val (tree1,(i1,s1)) = term_to_prop_tree_subst t1 (idx,subs) bsubs
				in
					case tree1 of
					  Node xs =>
						let
							val fmTrue  = list_conjunction (map prop_tree_to_true xs)
							val fmFalse = list_disjunction (map prop_tree_to_false xs)
						in
							(Leaf [fmTrue, fmFalse], (i1,s1))
						end
					| _ =>
						raise REFUTE ("term_to_prop_tree_subst", "'all' is not followed by a function")
				end
			| Const ("==", _) $ t1 $ t2 =>
				let
					val (tree1,(i1,s1)) = term_to_prop_tree_subst t1 (idx,subs) bsubs
					val (tree2,(i2,s2)) = term_to_prop_tree_subst t2 (i1,s1) bsubs
					val fmTrue          = prop_tree_equal (tree1,tree2)
					val fmFalse         = SNot fmTrue
				in
					(Leaf [fmTrue, fmFalse], (i2,s2))
				end
			| Const ("==>", _) $ t1 $ t2 =>
				let
					val (tree1,(i1,s1)) = term_to_prop_tree_subst t1 (idx,subs) bsubs
					val (tree2,(i2,s2)) = term_to_prop_tree_subst t2 (i1,s1) bsubs
					val fmTrue          = SOr (prop_tree_to_false tree1, prop_tree_to_true tree2)
					val fmFalse         = SAnd (prop_tree_to_true tree1, prop_tree_to_false tree2)
				in
					(Leaf [fmTrue, fmFalse], (i2,s2))
				end
			(* HOL constants *)
			| Const ("Trueprop", _) $ t1 =>
				term_to_prop_tree_subst t1 (idx,subs) bsubs
			| Const ("Not", _) $ t1 =>
				let
					val (tree1,(i1,s1)) = term_to_prop_tree_subst t1 (idx,subs) bsubs
					val fmTrue          = prop_tree_to_false tree1
					val fmFalse         = prop_tree_to_true tree1
				in
					(Leaf [fmTrue, fmFalse], (i1,s1))
				end
			| Const ("True", _) =>
				(Leaf [True, False], (idx,subs))
			| Const ("False", _) =>
				(Leaf [False, True], (idx,subs))
			| Const ("All", _) $ t1 =>
				let
					val (tree1,(i1,s1)) = term_to_prop_tree_subst t1 (idx,subs) bsubs
				in
					case tree1 of
					  Node xs =>
						let
							val fmTrue  = list_conjunction (map prop_tree_to_true xs)
							val fmFalse = list_disjunction (map prop_tree_to_false xs)
						in
							(Leaf [fmTrue, fmFalse], (i1,s1))
						end
					| _ =>
						raise REFUTE ("term_to_prop_tree_subst", "'All' is not followed by a function")
				end
			| Const ("Ex", _) $ t1 =>
				let
					val (tree1,(i1,s1)) = term_to_prop_tree_subst t1 (idx,subs) bsubs
				in
					case tree1 of
					  Node xs =>
						let
							val fmTrue  = list_disjunction (map prop_tree_to_true xs)
							val fmFalse = list_conjunction (map prop_tree_to_false xs)
						in
							(Leaf [fmTrue, fmFalse], (i1,s1))
						end
					| _ =>
						raise REFUTE ("term_to_prop_tree_subst", "'Ex' is not followed by a function")
				end
			| Const ("Ex1", Type ("fun", [Type ("fun", [T, Type ("bool",[])]), Type ("bool",[])])) $ t1 =>
				(* 'Ex1 t1' is equivalent to 'Ex Abs(x,T,t1' x & All Abs(y,T,t1'' y --> x=y))' *)
				let
					val t1'      = Term.incr_bv (1, 0, t1)
					val t1''     = Term.incr_bv (2, 0, t1)
					val t_equal  = (HOLogic.eq_const T) $ (Bound 1) $ (Bound 0)
					val t_unique = (HOLogic.all_const T) $ Abs("y",T,HOLogic.mk_imp (t1'' $ (Bound 0),t_equal))
					val t_ex1    = (HOLogic.exists_const T) $ Abs("x",T,HOLogic.mk_conj (t1' $ (Bound 0),t_unique))
				in
					term_to_prop_tree_subst t_ex1 (idx,subs) bsubs
				end
			| Const ("op =", _) $ t1 $ t2 =>
				let
					val (tree1,(i1,s1)) = term_to_prop_tree_subst t1 (idx,subs) bsubs
					val (tree2,(i2,s2)) = term_to_prop_tree_subst t2 (i1,s1) bsubs
					val fmTrue          = prop_tree_equal (tree1,tree2)
					val fmFalse         = SNot fmTrue
				in
					(Leaf [fmTrue, fmFalse], (i2,s2))
				end
			| Const ("op &", _) $ t1 $ t2 =>
				let
					val (tree1,(i1,s1)) = term_to_prop_tree_subst t1 (idx,subs) bsubs
					val (tree2,(i2,s2)) = term_to_prop_tree_subst t2 (i1,s1) bsubs
					val fmTrue          = SAnd (prop_tree_to_true tree1, prop_tree_to_true tree2)
					val fmFalse         = SOr (prop_tree_to_false tree1, prop_tree_to_false tree2)
				in
					(Leaf [fmTrue, fmFalse], (i2,s2))
				end
			| Const ("op |", _) $ t1 $ t2 =>
				let
					val (tree1,(i1,s1)) = term_to_prop_tree_subst t1 (idx,subs) bsubs
					val (tree2,(i2,s2)) = term_to_prop_tree_subst t2 (i1,s1) bsubs
					val fmTrue          = SOr (prop_tree_to_true tree1, prop_tree_to_true tree2)
					val fmFalse         = SAnd (prop_tree_to_false tree1, prop_tree_to_false tree2)
				in
					(Leaf [fmTrue, fmFalse], (i2,s2))
				end
			| Const ("op -->", _) $ t1 $ t2 =>
				let
					val (tree1,(i1,s1)) = term_to_prop_tree_subst t1 (idx,subs) bsubs
					val (tree2,(i2,s2)) = term_to_prop_tree_subst t2 (i1,s1) bsubs
					val fmTrue          = SOr (prop_tree_to_false tree1, prop_tree_to_true tree2)
					val fmFalse         = SAnd (prop_tree_to_true tree1, prop_tree_to_false tree2)
				in
					(Leaf [fmTrue, fmFalse], (i2,s2))
				end
			(* set constants *)
			| Const ("Collect", _) $ t1 =>
				term_to_prop_tree_subst t1 (idx,subs) bsubs
			| Const ("op :", _) $ t1 $ t2 =>
				term_to_prop_tree_subst (t2 $ t1) (idx,subs) bsubs
			(* datatype constants *)
			| Const ("Product_Type.Unity", _) =>
				(Leaf [True], (idx,subs))
			(* unknown constants *)
			| Const (c, _) =>
				error ("term contains an unknown constant: '" ^ c ^ "'")
			(* abstractions *)
			| Abs (_,T,body) =>
				let
					val constants       = type_to_constants T us thy cdepth
					val (trees, substs) = split_list (map (fn c => term_to_prop_tree_subst body (idx,subs) (c::bsubs)) constants)
				in
					(* the substitutions in 'substs' are all identical *)
					(Node trees, hd substs)
				end
			(* (free/schematic) variables *)
			| Free _ =>
				variable_to_prop_tree_subst t' (idx,subs)
			| Var _ =>
				variable_to_prop_tree_subst t' (idx,subs)
			(* bound variables *)
			| Bound i =>
				if (length bsubs) <= i then
					raise REFUTE ("term_to_prop_tree_subst", "term contains a loose bound variable (with index " ^ (string_of_int i) ^ ")")
				else
					(nth_elem (i,bsubs), (idx,subs))
			(* application *)
			| t1 $ t2 =>
				let
					val (tree1,(i1,s1)) = term_to_prop_tree_subst t1 (idx,subs) bsubs
					val (tree2,(i2,s2)) = term_to_prop_tree_subst t2 (i1,s1) bsubs
				in
					(prop_tree_apply (tree1,tree2), (i2,s2))
				end
	in
		term_to_prop_tree_subst t (1,[]) []
	end;

(* ------------------------------------------------------------------------- *)
(* term_to_prop_formula: translates a HOL formula 't' into a propositional   *)
(*      formula that is satisfiable if and only if 't' has a model of "size" *)
(*      'us' (where 'us' specifies the number of elements for each free type *)
(*      variable in 't') and maximal constructor depth 'cdepth'.             *)
(* ------------------------------------------------------------------------- *)

	(* TODO: shouldn't 'us' also specify the number of elements for schematic type variables? (if so, modify the comment above) *)

	(* Term.term -> (Term.typ * int) list -> theory -> int -> prop_formula * (int * (Term.term * prop_tree) list) *)

	fun term_to_prop_formula t us thy cdepth =
	let
		val (tr, (idx,subs)) = term_to_prop_tree t us thy cdepth
		val fm               = prop_tree_to_true tr
	in
		if subs=[] then
			(fm, (idx,subs))
		else
			(* make sure every tree that is substituted for a term describes a single element *)
			(SAnd (list_conjunction (map (fn (_,tr) => restrict_to_single_element tr) subs), fm), (idx,subs))
	end;


(* ------------------------------------------------------------------------- *)
(* INTERFACE, PART 2: FINDING A MODEL                                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* string_of_universe: prints a universe, i.e. an assignment of sizes for    *)
(*                     types                                                 *)
(* thy: the current theory                                                   *)
(* us : a list containing types together with their size                     *)
(* ------------------------------------------------------------------------- *)

	(* theory -> (Term.typ * int) list -> string *)

	fun string_of_universe thy [] =
		"empty universe (no type variables in term)"
	  | string_of_universe thy us =
		space_implode ", " (map (fn (T,i) => (Sign.string_of_typ (sign_of thy) T) ^ ": " ^ (string_of_int i)) us);

(* ------------------------------------------------------------------------- *)
(* string_of_model: prints a model, given by a substitution 'subs' of trees  *)
(*      of propositional variables and an assignment 'ass' of truth values   *)
(*      for these variables.                                                 *)
(* thy   : the current theory                                                *)
(* us    : universe, specifies the "size" of each type (i.e. type variable)  *)
(* cdepth: maximal constructor depth for inductive datatypes                 *)
(* subs  : substitution of trees of propositional formulas (for variables)   *)
(* ass   : assignment of truth values for boolean variables; see function    *)
(*         'truth_value' below for its meaning                               *)
(* ------------------------------------------------------------------------- *)

	(* theory -> (Term.typ * int) list -> int -> (Term.term * prop_formula tree) list -> int list -> string *)

	fun string_of_model thy us cdepth [] ass =
		"empty interpretation (no free variables in term)"
	  | string_of_model thy us cdepth subs ass =
		let
			(* Sign.sg *)
			val sg = sign_of thy
			(* int -> bool *)
			fun truth_value i =
				if i mem ass then true
				else if ~i mem ass then false
				else error ("SAT solver assignment does not specify a value for variable " ^ (string_of_int i))
			(* string -> string *)
			fun strip_leading_quote str =
				if nth_elem_string(0,str)="'" then
					String.substring (str, 1, size str - 1)
				else
					str;
			(* prop_formula list -> int *)
			fun true_index xs =
				(* returns the (0-based) index of the first true formula in xs *)
				let fun true_index_acc [] _ =
					raise REFUTE ("string_of_model::true_index", "no variable was set to true")
				      | true_index_acc (x::xs) n =
					case x of
					  BoolVar i =>
						if truth_value i then n else true_index_acc xs (n+1)
					| True =>
						n
					| False =>
						true_index_acc xs (n+1)
					| _ =>
						raise REFUTE ("string_of_model::true_index", "formula is not a boolean variable/true/false")
				in
					true_index_acc xs 0
				end
			(* Term.typ -> int -> prop_tree -> string *)
			(* prop *)
			fun string_of_prop_tree (Type ("prop",[])) cdepth (Leaf [BoolVar i, Not (BoolVar _)]) =
				if truth_value i then "true" else "false"
			  | string_of_prop_tree (Type ("prop",[])) cdepth (Leaf [True, False]) =
				"true"
			  | string_of_prop_tree (Type ("prop",[])) cdepth (Leaf [False, True]) =
				"false"
			(* bool *)
			  | string_of_prop_tree (Type ("bool",[])) cdepth (Leaf [BoolVar i, Not (BoolVar _)]) =
				if truth_value i then "true" else "false"
			  | string_of_prop_tree (Type ("bool",[])) cdepth (Leaf [True, False]) =
				"true"
			  | string_of_prop_tree (Type ("bool",[])) cdepth (Leaf [False, True]) =
				"false"
			(* unit *)
			  | string_of_prop_tree (Type ("Product_Type.unit",[])) cdepth (Leaf [True]) =
				"()"
			  | string_of_prop_tree (Type (s,Ts)) cdepth (Leaf xs) =
				(case DatatypePackage.datatype_info thy s of
				   Some info => (* inductive datatype *)
					let
						val index               = #index info
						val descr               = #descr info
						val (_, dtyps, constrs) = the (assoc (descr, index))
						val Typs                = dtyps ~~ Ts
						(* string -> string *)
						fun unqualify s =
							implode (snd (take_suffix (fn c => c <> ".") (explode s)))
						(* DatatypeAux.dtyp -> Term.typ *)
						fun typ_of_dtyp (DatatypeAux.DtTFree a) =
							the (assoc (Typs, DatatypeAux.DtTFree a))
						  | typ_of_dtyp (DatatypeAux.DtRec i) =
							let
								val (s, ds, _) = the (assoc (descr, i))
							in
								Type (s, map typ_of_dtyp ds)
							end
						  | typ_of_dtyp (DatatypeAux.DtType (s, ds)) =
							Type (s, map typ_of_dtyp ds)
						(* DatatypeAux.dtyp list -> int -> string *)
						fun string_of_inductive_type_cargs [] n =
							if n<>0 then
								raise REFUTE ("string_of_model", "internal error computing the element index for an inductive type")
							else
								""
						  | string_of_inductive_type_cargs (d::ds) n =
							let
								val size_ds = product (map (fn d => size_of_type (typ_of_dtyp d) us thy (cdepth-1)) ds)
							in
								" " ^ (string_of_prop_tree (typ_of_dtyp d) (cdepth-1) (nth_elem (n div size_ds, type_to_constants (typ_of_dtyp d) us thy (cdepth-1)))) ^ (string_of_inductive_type_cargs ds (n mod size_ds))
							end
						(* (string * DatatypeAux.dtyp list) list -> int -> string *)
						fun string_of_inductive_type_constrs [] n =
							raise REFUTE ("string_of_model", "inductive type has fewer elements than needed")
						  | string_of_inductive_type_constrs ((s,ds)::cs) n =
							let
								val size = product (map (fn d => size_of_type (typ_of_dtyp d) us thy (cdepth-1)) ds)
							in
								if n < size then
									(unqualify s) ^ (string_of_inductive_type_cargs ds n)
								else
									string_of_inductive_type_constrs cs (n - size)
							end
					in
						string_of_inductive_type_constrs constrs (true_index xs)
					end
				 | None =>
					raise REFUTE ("string_of_model", "type contains an unknown type constructor: '" ^ s ^ "'"))
			(* type variable *)
			  | string_of_prop_tree (TFree (s,_)) cdepth (Leaf xs) =
					(strip_leading_quote s) ^ (string_of_int (true_index xs))
			  | string_of_prop_tree (TVar ((s,_),_)) cdepth (Leaf xs) =
					(strip_leading_quote s) ^ (string_of_int (true_index xs))
			(* function or set type *)
			  | string_of_prop_tree T cdepth (Node xs) =
				case T of
				  Type ("fun", [T1,T2]) =>
					let
						val strings = foldl (fn (ss,(c,x)) => ss @ [(string_of_prop_tree T1 cdepth c) ^ "\\<mapsto>" ^ (string_of_prop_tree T2 cdepth x)]) ([], (type_to_constants T1 us thy cdepth) ~~ xs)
					in
						"(" ^ (space_implode ", " strings) ^ ")"
					end
				| Type ("set", [T1]) =>
					let
						val strings = foldl (fn (ss,(c,x)) => if (string_of_prop_tree (Type ("bool",[])) cdepth x)="true" then ss @ [string_of_prop_tree T1 cdepth c] else ss) ([], (type_to_constants T1 us thy cdepth) ~~ xs)
					in
						"{" ^ (space_implode ", " strings) ^ "}"
					end
				| _ => raise REFUTE ("string_of_model::string_of_prop_tree", "not a function/set type")
			(* Term.term * prop_formula tree -> string *)
			fun string_of_term_assignment (t,tr) =
			let
				val T = case t of
					  Free (_,T) => T
					| Var (_,T)  => T
					| _          => raise REFUTE ("string_of_model::string_of_term_assignment", "term is not a (free or schematic) variable")
			in
				(Sign.string_of_term sg t) ^ " = " ^ (string_of_prop_tree T cdepth tr)
			end
		in
			space_implode "\n" (map string_of_term_assignment subs)
		end;

(* ------------------------------------------------------------------------- *)
(* find_model: repeatedly calls 'prop_formula_sat_solver' with appropriate   *)
(*             parameters, and displays the results to the user              *)
(* params    : list of '(name, value)' pairs used to override default        *)
(*             parameters                                                    *)
(*                                                                           *)
(* This is a brief description of the algorithm implemented:                 *)
(*                                                                           *)
(* 1. Let k = max ('minsize',1).                                             *)
(* 2. Let the universe have k elements.  Find all possible partitions of     *)
(*    these elements into the basic types occuring in 't' such that no basic *)
(*    type is empty.                                                         *)
(* 3. Translate 't' into a propositional formula p s.t. 't' has a model wrt. *)
(*    the partition chosen in step (2.) if (actually, if and only if) p is   *)
(*    satisfiable.  To do this, replace quantification by conjunction/       *)
(*    disjunction over all elements of the type being quantified over.  (If  *)
(*    p contains more than 'maxvars' boolean variables, terminate.)          *)
(* 4. Serialize p to a file, and try to find a satisfying assignment for p   *)
(*    by invoking an external SAT solver.                                    *)
(* 5. If the SAT solver finds a satisfying assignment for p, translate this  *)
(*    assignment back into a model for 't'.  Present this model to the user, *)
(*    then terminate.                                                        *)
(* 6. As long as there is another partition left, pick it and go back to     *)
(*    step (3.).                                                             *)
(* 7. Increase k by 1.  As long as k does not exceed 'maxsize', go back to   *)
(*    step (2.).                                                             *)
(*                                                                           *)
(* The following parameters are currently supported (and required!):         *)
(*                                                                           *)
(* Name          Type    Description                                         *)
(*                                                                           *)
(* "minsize"     int     Only search for models with size at least           *)
(*                       'minsize'.                                          *)
(* "maxsize"     int     If >0, only search for models with size at most     *)
(*                       'maxsize'.                                          *)
(* "maxvars"     int     If >0, use at most 'maxvars' boolean variables      *)
(*                       when transforming the term into a propositional     *)
(*                       formula.                                            *)
(* "satfile"     string  Name of the file used to store the propositional    *)
(*                       formula, i.e. the input to the SAT solver.          *)
(* "satformat"   string  Format of the SAT solver's input file.  Must be     *)
(*                       either "cnf", "defcnf", or "sat".  Since "sat" is   *)
(*                       not supported by most SAT solvers, and "cnf" can    *)
(*                       cause exponential blowup of the formula, "defcnf"   *)
(*                       is recommended.                                     *)
(* "resultfile"  string  Name of the file containing the SAT solver's        *)
(*                       output.                                             *)
(* "success"     string  Part of the line in the SAT solver's output that    *)
(*                       precedes a list of integers representing the        *)
(*                       satisfying assignment.                              *)
(* "command"     string  System command used to execute the SAT solver.      *)
(*                       Note that you if you change 'satfile' or            *)
(*                       'resultfile', you will also need to change          *)
(*                       'command'.                                          *)
(*                                                                           *)
(* See the Isabelle/Isar theory 'Refute.thy' for reasonable default values.  *)
(* ------------------------------------------------------------------------- *)

	(* theory -> (string * string) list -> Term.term -> unit *)

	fun find_model thy params t =
	let
		(* (string * string) list * (string * string) list -> (string * string) list *)
		fun add_params (parms, []) =
			parms
		  | add_params (parms, defparm::defparms) =
			add_params (gen_ins (fn (a, b) => (fst a) = (fst b)) (defparm, parms), defparms)
		(* (string * string) list * string -> int *)
		fun read_int (parms, name) =
			case assoc_string (parms, name) of
			  Some s => (case Int.fromString s of
				  SOME i => i
				| NONE   => error ("parameter '" ^ name ^ "' (value is '" ^ s ^ "') must be an integer value"))
			| None   => error ("parameter '" ^ name ^ "' must be assigned a value")
		(* (string * string) list * string -> string *)
		fun read_string (parms, name) =
			case assoc_string (parms, name) of
			  Some s => s
			| None   => error ("parameter '" ^ name ^ "' must be assigned a value")
		(* (string * string) list *)
		val allparams  = add_params (params, get_default_params thy)
		(* int *)
		val minsize    = read_int (allparams, "minsize")
		val maxsize    = read_int (allparams, "maxsize")
		val maxvars    = read_int (allparams, "maxvars")
		(* string *)
		val satfile    = read_string (allparams, "satfile")
		val satformat  = read_string (allparams, "satformat")
		val resultfile = read_string (allparams, "resultfile")
		val success    = read_string (allparams, "success")
		val command    = read_string (allparams, "command")
		(* misc *)
		val satpath    = Path.unpack satfile
		val resultpath = Path.unpack resultfile
		val sg         = sign_of thy
		(* Term.typ list *)
		val tvars      = map (fn (i,s) => TVar(i,s)) (term_tvars t)
		val tfrees     = map (fn (x,s) => TFree(x,s)) (term_tfrees t)
		(* universe -> int -> bool *)
		fun find_model_universe u cdepth =
			let
				(* given the universe 'u' and constructor depth 'cdepth', translate *)
        	                (* the term 't' into a propositional formula 'fm'                   *)
				val (fm,(idx,subs)) = term_to_prop_formula t u thy cdepth
				val usedvars        = idx-1
			in
				(* 'maxvars=0' means "use as many variables as necessary" *)
				if usedvars>maxvars andalso maxvars<>0 then
					(
						(* too many variables used: terminate *)
						writeln ("\nSearch terminated: " ^ (string_of_int usedvars) ^ " boolean variables used (only " ^ (string_of_int maxvars) ^ " allowed).");
						true
					)
				else
					(* pass the formula 'fm' to an external SAT solver *)
					case prop_formula_sat_solver fm satpath satformat resultpath success command of
					  None =>
						(* no model found *)
						false
					| Some assignment =>
						(* model found: terminate *)
						(
							writeln ("\nModel found:\n" ^ (string_of_universe thy u) ^ "\n" ^ (string_of_model thy u cdepth subs assignment));
							true
						)
			end
		(* universe list -> int -> bool *)
		fun find_model_universes [] cdepth =
			(
				std_output "\n";
				false
			)
		  | find_model_universes (u::us) cdepth =
			(
				std_output ".";
				((if find_model_universe u cdepth then
					(* terminate *)
					true
				else
					(* continue search with the next universe *)
					find_model_universes us cdepth)
				handle EMPTY_DATATYPE => (std_output "[empty inductive type (constructor depth too small)]\n"; false))
			)
		(* int * int -> unit *)
		fun find_model_from_to (min,max) =
			(* 'max=0' means "search for arbitrary large models" *)
			if min>max andalso max<>0 then
				writeln ("Search terminated: no model found.")
			else
			(
				std_output ("Searching for a model of size " ^ (string_of_int min));
				if find_model_universes (make_universes tfrees min) min then
					(* terminate *)
					()
				else
					(* continue search with increased size *)
					find_model_from_to (min+1, max)
			)
	in
		writeln ("Trying to find a model of: " ^ (Sign.string_of_term sg t));
		if tvars<>[] then
			(* TODO: deal with schematic type variables in a better way, if possible *)
			error "term contains schematic type variables"
		else
		(
			if minsize<1 then
				writeln ("'minsize' is less than 1; starting search with size 1.")
			else
				();
			if maxsize<max (minsize,1) andalso maxsize<>0 then
				writeln ("'maxsize' is less than 'minsize': no model found.")
			else
				find_model_from_to (max (minsize,1), maxsize)
		)
	end;

(* ------------------------------------------------------------------------- *)
(* refute_term: calls 'find_model' on the negation of a term                 *)
(* params     : list of '(name, value)' pairs used to override default       *)
(*              parameters                                                   *)
(* ------------------------------------------------------------------------- *)

	(* theory -> (string * string) list -> Term.term -> unit *)

	fun refute_term thy params t =
	let
		(* TODO: schematic type variables? *)
		val negation = close_vars (HOLogic.Not $ t)
		(* If 't' is of type 'propT' (rather than 'boolT'), applying *)
		(* 'HOLogic.Not' is not type-correct.  However, this isn't   *)
		(* really a problem as long as 'find_model' still interprets *)
		(* the resulting term correctly, without checking its type.  *)
	in
		find_model thy params negation
	end;

(* ------------------------------------------------------------------------- *)
(* refute_subgoal: calls 'refute_term' on a specific subgoal                 *)
(* params        : list of '(name, value)' pairs used to override default    *)
(*                 parameters                                                *)
(* subgoal       : 0-based index specifying the subgoal number               *)
(* ------------------------------------------------------------------------- *)

	(* theory -> (string * string) list -> Thm.thm -> int -> unit *)

	fun refute_subgoal thy params thm subgoal =
		refute_term thy params (nth_elem (subgoal, prems_of thm));

end
