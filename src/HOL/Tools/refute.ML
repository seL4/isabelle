(*  Title:      HOL/Tools/refute.ML
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2003-2004

Finite model generation for HOL formulae, using a SAT solver.
*)

(* ------------------------------------------------------------------------- *)
(* TODO: Change parameter handling so that only supported parameters can be  *)
(*       set, and specify defaults here, rather than in HOL/Main.thy.        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Declares the 'REFUTE' signature as well as a structure 'Refute'.          *)
(* Documentation is available in the Isabelle/Isar theory 'HOL/Refute.thy'.  *)
(* ------------------------------------------------------------------------- *)

signature REFUTE =
sig

	exception REFUTE of string * string

(* ------------------------------------------------------------------------- *)
(* Model/interpretation related code (translation HOL -> boolean formula)    *)
(* ------------------------------------------------------------------------- *)

	exception CANNOT_INTERPRET

	type interpretation
	type model
	type arguments

	val add_interpreter : string -> (theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option) -> theory -> theory
	val add_printer     : string -> (theory -> model -> Term.term -> interpretation -> (int -> bool) -> string option) -> theory -> theory

	val interpret           : theory -> model -> arguments -> Term.term -> interpretation * model * arguments  (* exception CANNOT_INTERPRET *)
	val is_satisfying_model : model -> interpretation -> bool -> PropLogic.prop_formula

	val print       : theory -> model -> Term.term -> interpretation -> (int -> bool) -> string
	val print_model : theory -> model -> (int -> bool) -> string

(* ------------------------------------------------------------------------- *)
(* Interface                                                                 *)
(* ------------------------------------------------------------------------- *)

	val set_default_param  : (string * string) -> theory -> theory
	val get_default_param  : theory -> string -> string option
	val get_default_params : theory -> (string * string) list
	val actual_params      : theory -> (string * string) list -> (int * int * int * string)

	val find_model : theory -> (int * int * int * string) -> Term.term -> bool -> unit

	val satisfy_term   : theory -> (string * string) list -> Term.term -> unit  (* tries to find a model for a formula *)
	val refute_term    : theory -> (string * string) list -> Term.term -> unit  (* tries to find a model that refutes a formula *)
	val refute_subgoal : theory -> (string * string) list -> Thm.thm -> int -> unit

	val setup : (theory -> theory) list
end;

structure Refute : REFUTE =
struct

	open PropLogic;

	(* We use 'REFUTE' only for internal error conditions that should    *)
	(* never occur in the first place (i.e. errors caused by bugs in our *)
	(* code).  Otherwise (e.g. to indicate invalid input data) we use    *)
	(* 'error'.                                                          *)
	exception REFUTE of string * string;  (* ("in function", "cause") *)

(* ------------------------------------------------------------------------- *)
(* TRANSLATION HOL -> PROPOSITIONAL LOGIC, BOOLEAN ASSIGNMENT -> MODEL       *)
(* ------------------------------------------------------------------------- *)

	exception CANNOT_INTERPRET;

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
(* interpretation: a term's interpretation is given by a variable of type    *)
(*                 'interpretation'                                          *)
(* ------------------------------------------------------------------------- *)

	type interpretation =
		prop_formula list tree;

(* ------------------------------------------------------------------------- *)
(* model: a model specifies the size of types and the interpretation of      *)
(*        terms                                                              *)
(* ------------------------------------------------------------------------- *)

	type model =
		(Term.typ * int) list * (Term.term * interpretation) list;

(* ------------------------------------------------------------------------- *)
(* arguments: additional arguments required during interpretation of terms   *)
(* ------------------------------------------------------------------------- *)
	
	type arguments =
		{next_idx: int, bounds: interpretation list, wellformed: prop_formula};


	structure RefuteDataArgs =
	struct
		val name = "HOL/refute";
		type T =
			{interpreters: (string * (theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option)) list,
			 printers: (string * (theory -> model -> Term.term -> interpretation -> (int -> bool) -> string option)) list,
			 parameters: string Symtab.table};
		val empty = {interpreters = [], printers = [], parameters = Symtab.empty};
		val copy = I;
		val prep_ext = I;
		fun merge
			({interpreters = in1, printers = pr1, parameters = pa1},
			 {interpreters = in2, printers = pr2, parameters = pa2}) =
			{interpreters = rev (merge_alists (rev in1) (rev in2)),
			 printers = rev (merge_alists (rev pr1) (rev pr2)),
			 parameters = Symtab.merge (op=) (pa1, pa2)};
		fun print sg {interpreters, printers, parameters} =
			Pretty.writeln (Pretty.chunks
				[Pretty.strs ("default parameters:" :: flat (map (fn (name,value) => [name, "=", value]) (Symtab.dest parameters))),
				 Pretty.strs ("interpreters:" :: map fst interpreters),
				 Pretty.strs ("printers:" :: map fst printers)]);
	end;

	structure RefuteData = TheoryDataFun(RefuteDataArgs);


(* ------------------------------------------------------------------------- *)
(* interpret: tries to interpret the term 't' using a suitable interpreter;  *)
(*            returns the interpretation and a (possibly extended) model     *)
(*            that keeps track of the interpretation of subterms             *)
(* Note: exception 'CANNOT_INTERPRETE' is raised if the term cannot be       *)
(*       interpreted by any interpreter                                      *)
(* ------------------------------------------------------------------------- *)

	(* theory -> model -> arguments -> Term.term -> interpretation * model * arguments *)

	fun interpret thy model args t =
		(case get_first (fn (_, f) => f thy model args t) (#interpreters (RefuteData.get thy)) of
		  None =>
			(std_output "\n"; warning ("Unable to interpret term:\n" ^ Sign.string_of_term (sign_of thy) t);
			raise CANNOT_INTERPRET)
		| Some x => x);

(* ------------------------------------------------------------------------- *)
(* print: tries to print the constant denoted by the term 't' using a        *)
(*        suitable printer                                                   *)
(* ------------------------------------------------------------------------- *)

	(* theory -> model -> Term.term -> interpretation -> (int -> bool) -> string *)

	fun print thy model t intr assignment =
		(case get_first (fn (_, f) => f thy model t intr assignment) (#printers (RefuteData.get thy)) of
		  None => "<<no printer available>>"
		| Some s => s);

(* ------------------------------------------------------------------------- *)
(* is_satisfying_model: returns a propositional formula that is true iff the *)
(*      given interpretation denotes 'satisfy', and the model meets certain  *)
(*      well-formedness properties                                           *)
(* ------------------------------------------------------------------------- *)

	(* model -> interpretation -> bool -> PropLogic.prop_formula *)

	fun is_satisfying_model model intr satisfy =
	let
		(* prop_formula list -> prop_formula *)
		fun oneoutoftwofalse []      = True
		  | oneoutoftwofalse (x::xs) = SAnd (PropLogic.all (map (fn x' => SOr (SNot x, SNot x')) xs), oneoutoftwofalse xs)
		(* prop_formula list -> prop_formula *)
		fun exactly1true xs = SAnd (PropLogic.exists xs, oneoutoftwofalse xs)
	(* ------------------------------------------------------------------------- *)
	(* restrict_to_single_element: returns a propositional formula that is true  *)
	(*      iff the interpretation denotes a single element of its corresponding *)
	(*      type, i.e. iff at each leaf, one and only one formula is true        *)
	(* ------------------------------------------------------------------------- *)
		(* interpretation -> prop_formula *)
		fun restrict_to_single_element (Leaf [BoolVar i, Not (BoolVar j)]) =
			if (i=j) then
				True  (* optimization for boolean variables *)
			else
				raise REFUTE ("is_satisfying_model", "boolean variables in leaf have different indices")
		  | restrict_to_single_element (Leaf xs) =
			exactly1true xs
		  | restrict_to_single_element (Node trees) =
			PropLogic.all (map restrict_to_single_element trees)
	in
		(* a term of type 'bool' is represented as a 2-element leaf, where  *)
		(* the term is true iff the leaf's first element is true, and false *)
		(* iff the leaf's second element is true                            *)
		case intr of
		  Leaf [fmT,fmF] =>
			(* well-formedness properties and formula 'fmT'/'fmF' *)
			SAnd (PropLogic.all (map (restrict_to_single_element o snd) (snd model)), if satisfy then fmT else fmF)
		| _ =>
			raise REFUTE ("is_satisfying_model", "interpretation does not denote a boolean value")
	end;

(* ------------------------------------------------------------------------- *)
(* print_model: turns the model into a string, using a fixed interpretation  *)
(*              (given by an assignment for boolean variables) and suitable  *)
(*              printers                                                     *)
(* ------------------------------------------------------------------------- *)

	fun print_model thy model assignment =
	let
		val (typs, terms) = model
	in
		(if null typs then
			"empty universe (no type variables in term)"
		else
			"Size of types: " ^ commas (map (fn (T,i) => Sign.string_of_typ (sign_of thy) T ^ ": " ^ string_of_int i) typs))
		^ "\n"
		^ (if null terms then
			"empty interpretation (no free variables in term)"
		  else
			space_implode "\n" (map
				(fn (t,intr) =>
					Sign.string_of_term (sign_of thy) t ^ ": " ^ print thy model t intr assignment)
				terms)
		  )
		^ "\n"
	end;


(* ------------------------------------------------------------------------- *)
(* PARAMETER MANAGEMENT                                                      *)
(* ------------------------------------------------------------------------- *)

	(* string -> (theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option) -> theory -> theory *)

	fun add_interpreter name f thy =
	let
		val {interpreters, printers, parameters} = RefuteData.get thy
	in
		case assoc (interpreters, name) of
		  None   => RefuteData.put {interpreters = (name, f) :: interpreters, printers = printers, parameters = parameters} thy
		| Some _ => error ("Interpreter " ^ name ^ " already declared")
	end;

	(* string -> (theory -> model -> Term.term -> interpretation -> (int -> bool) -> string option) -> theory -> theory *)

	fun add_printer name f thy =
	let
		val {interpreters, printers, parameters} = RefuteData.get thy
	in
		case assoc (printers, name) of
		  None   => RefuteData.put {interpreters = interpreters, printers = (name, f) :: printers, parameters = parameters} thy
		| Some _ => error ("Printer " ^ name ^ " already declared")
	end;

(* ------------------------------------------------------------------------- *)
(* set_default_param: stores the '(name, value)' pair in RefuteData's        *)
(*                    parameter table                                        *)
(* ------------------------------------------------------------------------- *)

	(* (string * string) -> theory -> theory *)

	fun set_default_param (name, value) thy =
	let
		val {interpreters, printers, parameters} = RefuteData.get thy
	in
		case Symtab.lookup (parameters, name) of
		  None   => RefuteData.put
			{interpreters = interpreters, printers = printers, parameters = Symtab.extend (parameters, [(name, value)])} thy
		| Some _ => RefuteData.put
			{interpreters = interpreters, printers = printers, parameters = Symtab.update ((name, value), parameters)} thy
	end;

(* ------------------------------------------------------------------------- *)
(* get_default_param: retrieves the value associated with 'name' from        *)
(*                    RefuteData's parameter table                           *)
(* ------------------------------------------------------------------------- *)

	(* theory -> string -> string option *)

	fun get_default_param thy name = Symtab.lookup ((#parameters o RefuteData.get) thy, name);

(* ------------------------------------------------------------------------- *)
(* get_default_params: returns a list of all '(name, value)' pairs that are  *)
(*                     stored in RefuteData's parameter table                *)
(* ------------------------------------------------------------------------- *)

	(* theory -> (string * string) list *)

	fun get_default_params thy = (Symtab.dest o #parameters o RefuteData.get) thy;

(* ------------------------------------------------------------------------- *)
(* actual_params: takes a (possibly empty) list 'params' of parameters that  *)
(*      override the default parameters currently specified in 'thy', and    *)
(*      returns a tuple that can be passed to 'find_model'.                  *)
(*                                                                           *)
(* The following parameters are supported (and required!):                   *)
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
(* "satsolver"   string  SAT solver to be used.                              *)
(* ------------------------------------------------------------------------- *)

	(* theory -> (string * string) list -> (int * int * int * string) *)

	fun actual_params thy params =
	let
		(* (string * string) list * string -> int *)
		fun read_int (parms, name) =
			case assoc_string (parms, name) of
			  Some s => (case Int.fromString s of
				  SOME i => i
				| NONE   => error ("parameter " ^ quote name ^ " (value is " ^ quote s ^ ") must be an integer value"))
			| None   => error ("parameter " ^ quote name ^ " must be assigned a value")
		(* (string * string) list * string -> string *)
		fun read_string (parms, name) =
			case assoc_string (parms, name) of
			  Some s => s
			| None   => error ("parameter " ^ quote name ^ " must be assigned a value")
		(* (string * string) list *)
		val allparams = params @ (get_default_params thy)  (* 'params' first, defaults last (to override) *)
		(* int *)
		val minsize   = read_int (allparams, "minsize")
		val maxsize   = read_int (allparams, "maxsize")
		val maxvars   = read_int (allparams, "maxvars")
		(* string *)
		val satsolver = read_string (allparams, "satsolver")
	in
		(minsize, maxsize, maxvars, satsolver)
	end;

(* ------------------------------------------------------------------------- *)
(* find_model: repeatedly calls 'invoke_propgen' with appropriate            *)
(*             parameters, applies the SAT solver, and (in case a model is   *)
(*             found) displays the model to the user                         *)
(* thy      : the current theory                                             *)
(* minsize  : the minimal size of the model                                  *)
(* maxsize  : the maximal size of the model                                  *)
(* maxvars  : the maximal number of boolean variables to be used             *)
(* satsolver: the name of the SAT solver to be used                          *)
(* satisfy  : if 'True', search for a model that makes 't' true; otherwise   *)
(*            search for a model that makes 't' false                        *)
(* ------------------------------------------------------------------------- *)

	(* theory ->  (int * int * int * string) -> Term.term -> bool -> unit *)

	fun find_model thy (minsize, maxsize, maxvars, satsolver) t satisfy =
	let
		(* Term.typ list *)
		val tvars  = map (fn (i,s) => TVar(i,s)) (term_tvars t)
		val tfrees = map (fn (x,s) => TFree(x,s)) (term_tfrees t)
		(* int -> unit *)
		fun find_model_loop size =
			(* 'maxsize=0' means "search for arbitrary large models" *)
			if size>maxsize andalso maxsize<>0 then
				writeln ("Search terminated: maxsize=" ^ string_of_int maxsize ^ " exceeded.")
			else
			let
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
						raise REFUTE ("find_model", "empty list (in make_partitions_loop)")
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
						raise REFUTE ("find_model", "empty list (in make_partitions)")
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
				end
				(* ('a * int) list -> bool *)
				fun find_interpretation xs =
				let
					val init_model          = (xs, [])
					val init_args           = {next_idx = 1, bounds = [], wellformed = True}
					val (intr, model, args) = interpret thy init_model init_args t
					val fm                  = SAnd (#wellformed args, is_satisfying_model model intr satisfy)
					val usedvars            = maxidx fm
				in
					(* 'maxvars=0' means "use as many variables as necessary" *)
					if usedvars>maxvars andalso maxvars<>0 then
						(writeln ("\nSearch terminated: " ^ string_of_int usedvars ^ " boolean variables used (only " ^ string_of_int maxvars ^ " allowed).");
						true)
					else
					(
						std_output " invoking SAT solver...";
						case SatSolver.invoke_solver satsolver fm of
						  None =>
							(std_output (" error: SAT solver " ^ quote satsolver ^ " not configured.\n");
							true)
						| Some None =>
							(std_output " no model found.\n";
							false)
						| Some (Some assignment) =>
							(writeln ("\nModel found:\n" ^ print_model thy model assignment);
							true)
					)
				end handle CANNOT_INTERPRET => true
					(* TODO: change this to false once the ability to interpret terms depends on the universe *)
			in
				case make_universes (tvars@tfrees) size of
				  [] =>
					(writeln ("Searching for a model of size " ^ string_of_int size ^ ": cannot make every type non-empty (model is too small).");
					find_model_loop (size+1))
				| [[]] =>
					(std_output ("Searching for a model of size " ^ string_of_int size ^ ", translating term...");
					if find_interpretation [] then
						()
					else
						writeln ("Search terminated: no type variables in term."))
				| us =>
					let
						fun loop []      =
							find_model_loop (size+1)
						  | loop (u::us) =
							(std_output ("Searching for a model of size " ^ string_of_int size ^ ", translating term...");
							if find_interpretation u then () else loop us)
					in
						loop us
					end
			end
	in
		writeln ("Trying to find a model that "
			^ (if satisfy then "satisfies" else "refutes")
			^ ": " ^ (Sign.string_of_term (sign_of thy) t));
		if minsize<1 then
			writeln "\"minsize\" is less than 1; starting search with size 1."
		else ();
		find_model_loop (Int.max (minsize,1))
	end;


(* ------------------------------------------------------------------------- *)
(* INTERFACE, PART 2: FINDING A MODEL                                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* satisfy_term: calls 'find_model' to find a model that satisfies 't'       *)
(* params      : list of '(name, value)' pairs used to override default      *)
(*               parameters                                                  *)
(* ------------------------------------------------------------------------- *)

	(* theory -> (string * string) list -> Term.term -> unit *)

	fun satisfy_term thy params t =
		find_model thy (actual_params thy params) t true;

(* ------------------------------------------------------------------------- *)
(* refute_term: calls 'find_model' to find a model that refutes 't'          *)
(* params     : list of '(name, value)' pairs used to override default       *)
(*              parameters                                                   *)
(* ------------------------------------------------------------------------- *)

	(* theory -> (string * string) list -> Term.term -> unit *)

	fun refute_term thy params t =
	let
		(* disallow schematic type variables, since we cannot properly negate terms containing them *)
		val _ = assert (null (term_tvars t)) "Term to be refuted contains schematic type variables"
		(* existential closure over schematic variables *)
		(* (Term.indexname * Term.typ) list *)
		val vars = sort_wrt (fst o fst) (map dest_Var (term_vars t))
		(* Term.term *)
		val ex_closure = foldl
			(fn (t', ((x,i),T)) => (HOLogic.exists_const T) $ Abs (x, T, abstract_over (Var((x,i),T), t')))
			(t, vars)
		(* If 't' is of type 'propT' (rather than 'boolT'), applying  *)
		(* 'HOLogic.exists_const' is not type-correct.  However, this *)
		(* isn't really a problem as long as 'find_model' still       *)
		(* interprets the resulting term correctly, without checking  *)
		(* its type.                                                  *)
	in
		find_model thy (actual_params thy params) ex_closure false
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


(* ------------------------------------------------------------------------- *)
(* INTERPRETERS                                                              *)
(* ------------------------------------------------------------------------- *)

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun var_typevar_interpreter thy model args t =
	let
		fun is_var (Free _) = true
		  | is_var (Var _)  = true
		  | is_var _        = false
		fun typeof (Free (_,T)) = T
		  | typeof (Var (_,T))  = T
		  | typeof _            = raise REFUTE ("var_typevar_interpreter", "term is not a variable")
		fun is_typevar (TFree _) = true
		  | is_typevar (TVar _)  = true
		  | is_typevar _         = false
		val (sizes, intrs) = model
	in
		if is_var t andalso is_typevar (typeof t) then
			(case assoc (intrs, t) of
			  Some intr => Some (intr, model, args)
			| None      =>
				let
					val size = (the o assoc) (sizes, typeof t)  (* the model MUST specify a size for type variables *)
					val idx  = #next_idx args
					val intr = (if size=2 then Leaf [BoolVar idx, Not (BoolVar idx)] else Leaf (map BoolVar (idx upto (idx+size-1))))
					val next = (if size=2 then idx+1 else idx+size)
				in
					(* extend the model, increase 'next_idx' *)
					Some (intr, (sizes, (t, intr)::intrs), {next_idx = next, bounds = #bounds args, wellformed = #wellformed args})
				end)
		else
			None
	end;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun var_funtype_interpreter thy model args t =
	let
		fun is_var (Free _) = true
		  | is_var (Var _)  = true
		  | is_var _        = false
		fun typeof (Free (_,T)) = T
		  | typeof (Var (_,T))  = T
		  | typeof _            = raise REFUTE ("var_funtype_interpreter", "term is not a variable")
		fun stringof (Free (x,_))     = x
		  | stringof (Var ((x,_), _)) = x
		  | stringof _                = raise REFUTE ("var_funtype_interpreter", "term is not a variable")
		fun is_funtype (Type ("fun", [_,_])) = true
		  | is_funtype _                     = false
		val (sizes, intrs) = model
	in
		if is_var t andalso is_funtype (typeof t) then
			(case assoc (intrs, t) of
			  Some intr => Some (intr, model, args)
			| None      =>
				let
					val T1 = domain_type (typeof t)
					val T2 = range_type (typeof t)
					(* we create 'size_of_interpretation (interpret (... T1))' different copies *)
					(* of the tree for 'T2', which are then combined into a single new tree     *)
					val (i1, _, _) = interpret thy (sizes, []) {next_idx=1, bounds=[], wellformed=True} (Free (stringof t, T1))
					(* power(a,b) computes a^b, for a>=0, b>=0 *)
					(* int * int -> int *)
					fun power (a,0) = 1
					  | power (a,1) = a
					  | power (a,b) = let val ab = power(a,b div 2) in ab * ab * power(a,b mod 2) end
					fun size_of_interpretation (Leaf xs) = length xs
					  | size_of_interpretation (Node xs) = power (size_of_interpretation (hd xs), length xs)
					val size = size_of_interpretation i1
					(* make fresh copies, with different variable indices *)
					(* int -> int -> (int * interpretation list *)
					fun make_copies idx 0 =
						(idx, [])
					  | make_copies idx n =
						let
							val (copy, _, args) = interpret thy (sizes, []) {next_idx = idx, bounds = [], wellformed=True} (Free (stringof t, T2))
							val (next, copies)  = make_copies (#next_idx args) (n-1)
						in
							(next, copy :: copies)
						end
					val (idx, copies) = make_copies (#next_idx args) (size_of_interpretation i1)
					(* combine copies into a single tree *)
					val intr = Node copies
				in
					(* extend the model, increase 'next_idx' *)
					Some (intr, (sizes, (t, intr)::intrs), {next_idx = idx, bounds = #bounds args, wellformed = #wellformed args})
				end)
		else
			None
	end;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun var_settype_interpreter thy model args t =
		let
			val (sizes, intrs) = model
		in
			case t of
			  Free (x, Type ("set", [T])) =>
				(case assoc (intrs, t) of
				  Some intr => Some (intr, model, args)
				| None      =>
					let
						val (intr, _, args') = interpret thy model args (Free (x, Type ("fun", [T, Type ("bool", [])])))
					in
						Some (intr, (sizes, (t, intr)::intrs), args')
					end)
			| Var ((x,i), Type ("set", [T])) =>
				(case assoc (intrs, t) of
				  Some intr => Some (intr, model, args)
				| None      =>
					let
						val (intr, _, args') = interpret thy model args (Var ((x,i), Type ("fun", [T, Type ("bool", [])])))
					in
						Some (intr, (sizes, (t, intr)::intrs), args')
					end)
			| _ => None
		end;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun boundvar_interpreter thy model args (Bound i) = Some (nth_elem (i, #bounds (args:arguments)), model, args)
	  | boundvar_interpreter thy model args _         = None;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun abstraction_interpreter thy model args (Abs (x, T, t)) =
		let
			val (sizes, intrs) = model
			(* create all constants of type T *)
			val (i, _, _) = interpret thy (sizes, []) {next_idx=1, bounds=[], wellformed=True} (Free (x, T))
			(* returns a list with all unit vectors of length n *)
			(* int -> interpretation list *)
			fun unit_vectors n =
			let
				(* returns the k-th unit vector of length n *)
				(* int * int -> interpretation *)
				fun unit_vector (k,n) =
					Leaf ((replicate (k-1) False) @ (True :: (replicate (n-k) False)))
				(* int -> interpretation list -> interpretation list *)
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
			(* interpretation -> interpretation list *)
			fun make_constants (Leaf xs) =
				unit_vectors (length xs)
			  | make_constants (Node xs) =
				map (fn xs' => Node xs') (pick_all (length xs) (make_constants (hd xs)))
			(* interpret the body 't' separately for each constant *)
			val ((model', args'), bodies) = foldl_map
				(fn ((m,a), c) =>
					let
						(* add 'c' to 'bounds' *)
						val (i',m',a') = interpret thy m {next_idx = #next_idx a, bounds = c::(#bounds a), wellformed = #wellformed a} t
					in
						(* keep the new model m' and 'next_idx', but use old 'bounds' *)
						((m',{next_idx = #next_idx a', bounds = #bounds a, wellformed = #wellformed a'}), i')
					end)
				((model,args), make_constants i)
		in
			Some (Node bodies, model', args')
		end
	  | abstraction_interpreter thy model args _               = None;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun apply_interpreter thy model args (t1 $ t2) =
		let
			(* auxiliary functions *)
			(* interpretation * interpretation -> interpretation *)
			fun interpretation_disjunction (tr1,tr2) =
				tree_map (fn (xs,ys) => map (fn (x,y) => SOr(x,y)) (xs ~~ ys)) (tree_pair (tr1,tr2))
			(* prop_formula * interpretation -> interpretation *)
			fun prop_formula_times_interpretation (fm,tr) =
				tree_map (map (fn x => SAnd (fm,x))) tr
			(* prop_formula list * interpretation list -> interpretation *)
			fun prop_formula_list_dot_product_interpretation_list ([fm],[tr]) =
				prop_formula_times_interpretation (fm,tr)
			  | prop_formula_list_dot_product_interpretation_list (fm::fms,tr::trees) =
				interpretation_disjunction (prop_formula_times_interpretation (fm,tr), prop_formula_list_dot_product_interpretation_list (fms,trees))
			  | prop_formula_list_dot_product_interpretation_list (_,_) =
				raise REFUTE ("apply_interpreter", "empty list (in dot product)")
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
				raise REFUTE ("apply_interpreter", "empty list (in pick_all)")
			(* interpretation -> prop_formula list *)
			fun interpretation_to_prop_formula_list (Leaf xs) =
				xs
			  | interpretation_to_prop_formula_list (Node trees) =
				map PropLogic.all (pick_all (map interpretation_to_prop_formula_list trees))
			(* interpretation * interpretation -> interpretation *)
			fun interpretation_apply (tr1,tr2) =
				(case tr1 of
				  Leaf _ =>
					raise REFUTE ("apply_interpreter", "first interpretation is a leaf")
				| Node xs =>
					prop_formula_list_dot_product_interpretation_list (interpretation_to_prop_formula_list tr2, xs))
			(* interpret 't1' and 't2' *)
			val (intr1, model1, args1) = interpret thy model args t1
			val (intr2, model2, args2) = interpret thy model1 args1 t2
		in
			Some (interpretation_apply (intr1,intr2), model2, args2)
		end
	  | apply_interpreter thy model args _         = None;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun const_unfold_interpreter thy model args t =
		(* ------------------------------------------------------------------------- *)
		(* We unfold constants for which a defining equation is given as an axiom.   *)
		(* A polymorphic axiom's type variables are instantiated.  Eta-expansion is  *)
		(* performed only if necessary; arguments in the axiom that are present as   *)
		(* actual arguments in 't' are simply substituted.  If more actual than      *)
		(* formal arguments are present, the constant is *not* unfolded, so that     *)
		(* other interpreters (that may just not have looked into the term far       *)
		(* enough yet) may be applied first (after 'apply_interpreter' gets rid of   *)
		(* one argument).                                                            *)
		(* ------------------------------------------------------------------------- *)
		let
			val (head, actuals) = strip_comb t
			val actuals_count   = length actuals
		in
			case head of
			  Const (s,T) =>
				let
					(* (string * Term.term) list *)
					val axioms = flat (map (Symtab.dest o #axioms o Theory.rep_theory) (thy :: Theory.ancestors_of thy))
					(* Term.term * Term.term list * Term.term list -> Term.term *)
					(* term, formal arguments, actual arguments *)
					fun normalize (t, [],    [])    = t
					  | normalize (t, [],    y::ys) = raise REFUTE ("const_unfold_interpreter", "more actual than formal parameters")
					  | normalize (t, x::xs, [])    = normalize (lambda x t, xs, [])                (* eta-expansion *)
					  | normalize (t, x::xs, y::ys) = normalize (betapply (lambda x t, y), xs, ys)  (* substitution *)
					(* string -> Term.typ -> (string * Term.term) list -> Term.term option *)
					fun get_defn s T [] =
						None
					  | get_defn s T ((_,ax)::axms) =
						(let
							val (lhs, rhs)   = Logic.dest_equals ax  (* equations only *)
							val (c, formals) = strip_comb lhs
							val (s', T')     = dest_Const c
						in
							if (s=s') andalso (actuals_count <= length formals) then
								let
									val varT'      = Type.varifyT T'  (* for polymorphic definitions *)
									val typeSubs   = Type.typ_match (Sign.tsig_of (sign_of thy)) (Vartab.empty, (varT', T))
									val varRhs     = map_term_types Type.varifyT rhs
									val varFormals = map (map_term_types Type.varifyT) formals
									val rhs'       = normalize (varRhs, varFormals, actuals)
									val unvarRhs   = map_term_types
										(map_type_tvar
											(fn (v,_) =>
												case Vartab.lookup (typeSubs, v) of
												  None =>
													raise REFUTE ("const_unfold_interpreter", "schematic type variable " ^ (fst v) ^ "not instantiated (in definition of " ^ quote s ^ ")")
												| Some typ =>
													typ))
										rhs'
								in
									Some unvarRhs
								end
							else
								get_defn s T axms
						end
						handle TERM _          => get_defn s T axms
						     | Type.TYPE_MATCH => get_defn s T axms)
				in
					case get_defn s T axioms of
					  Some t' => Some (interpret thy model args t')
					| None    => None
				end
			| _ => None
		end;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun Pure_interpreter thy model args t =
		let
			fun toTrue (Leaf [fm,_]) = fm
			  | toTrue _             = raise REFUTE ("Pure_interpreter", "interpretation does not denote a boolean value")
			fun toFalse (Leaf [_,fm]) = fm
			  | toFalse _             = raise REFUTE ("Pure_interpreter", "interpretation does not denote a boolean value")
		in
			case t of
			  (*Const ("Goal", _) $ t1 =>
				Some (interpret thy model args t1) |*)
			  Const ("all", _) $ t1 =>
				let
					val (i,m,a) = (interpret thy model args t1)
				in
					case i of
					  Node xs =>
						let
							val fmTrue  = PropLogic.all (map toTrue xs)
							val fmFalse = PropLogic.exists (map toFalse xs)
						in
							Some (Leaf [fmTrue, fmFalse], m, a)
						end
					| _ =>
						raise REFUTE ("Pure_interpreter", "\"all\" is not followed by a function")
				end
			| Const ("==", _) $ t1 $ t2 =>
				let
					val (i1,m1,a1) = interpret thy model args t1
					val (i2,m2,a2) = interpret thy m1 a1 t2
					(* interpretation * interpretation -> prop_formula *)
					fun interpret_equal (tr1,tr2) =
						(case tr1 of
						  Leaf x =>
							(case tr2 of
							  Leaf y => PropLogic.dot_product (x,y)
							| _      => raise REFUTE ("Pure_interpreter", "\"==\": second tree is higher"))
						| Node xs =>
							(case tr2 of
							  Leaf _  => raise REFUTE ("Pure_interpreter", "\"==\": first tree is higher")
							(* extensionality: two functions are equal iff they are equal for every element *)
							| Node ys => PropLogic.all (map interpret_equal (xs ~~ ys))))
					(* interpretation * interpretation -> prop_formula *)
					fun interpret_unequal (tr1,tr2) =
						(case tr1 of
						  Leaf x =>
							(case tr2 of
							  Leaf y =>
								let
									fun unequal [] ([],_) =
										False
									  | unequal (x::xs) (y::ys1, ys2) =
										SOr (SAnd (x, PropLogic.exists (ys1@ys2)), unequal xs (ys1, y::ys2))
									  | unequal _ _ =
										raise REFUTE ("Pure_interpreter", "\"==\": leafs have different width")
								in
									unequal x (y,[])
								end
							| _      => raise REFUTE ("Pure_interpreter", "\"==\": second tree is higher"))
						| Node xs =>
							(case tr2 of
							  Leaf _  => raise REFUTE ("Pure_interpreter", "\"==\": first tree is higher")
							(* extensionality: two functions are unequal iff there exist unequal elements *)
							| Node ys => PropLogic.exists (map interpret_unequal (xs ~~ ys))))
					val fmTrue  = interpret_equal (i1,i2)
					val fmFalse = interpret_unequal (i1,i2)
				in
					Some (Leaf [fmTrue, fmFalse], m2, a2)
				end
			| Const ("==>", _) $ t1 $ t2 =>
				let
					val (i1,m1,a1) = interpret thy model args t1
					val (i2,m2,a2) = interpret thy m1 a1 t2
					val fmTrue     = SOr (toFalse i1, toTrue i2)
					val fmFalse    = SAnd (toTrue i1, toFalse i2)
				in
					Some (Leaf [fmTrue, fmFalse], m2, a2)
				end
			| _ => None
		end;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun HOLogic_interpreter thy model args t =
	(* ------------------------------------------------------------------------- *)
	(* Providing interpretations directly is more efficient than unfolding the   *)
	(* logical constants; however, we need versions for constants with arguments *)
	(* (to avoid unfolding) as well as versions for constants without arguments  *)
	(* (since in HOL, logical constants can themselves be arguments)             *)
	(* ------------------------------------------------------------------------- *)
	let
		fun eta_expand t i =
			let
				val Ts = binder_types (fastype_of t)
			in
				foldr (fn (T, t) => Abs ("<eta_expand>", T, t))
					(take (i, Ts), list_comb (t, map Bound (i-1 downto 0)))
			end
		val TT = Leaf [True, False]
		val FF = Leaf [False, True]
		fun toTrue (Leaf [fm,_]) = fm
		  | toTrue _             = raise REFUTE ("HOLogic_interpreter", "interpretation does not denote a boolean value")
		fun toFalse (Leaf [_,fm]) = fm
		  | toFalse _             = raise REFUTE ("HOLogic_interpreter", "interpretation does not denote a boolean value")
	in
		case t of
		  Const ("Trueprop", _) $ t1 =>
			Some (interpret thy model args t1)
		| Const ("Trueprop", _) =>
			Some (Node [TT, FF], model, args)
		| Const ("Not", _) $ t1 =>
			apply_interpreter thy model args t
		| Const ("Not", _) =>
			Some (Node [FF, TT], model, args)
		| Const ("True", _) =>
			Some (TT, model, args)
		| Const ("False", _) =>
			Some (FF, model, args)
		| Const ("arbitrary", T) =>
			(* treat 'arbitrary' just like a free variable of the same type *)
			(case assoc (snd model, t) of
			  Some intr =>
				Some (intr, model, args)
			| None =>
				let
					val (sizes, intrs) = model
					val (intr, _, a)   = interpret thy (sizes, []) args (Free ("<arbitrary>", T))
				in
					Some (intr, (sizes, (t,intr)::intrs), a)
				end)
		| Const ("The", _) $ t1 =>
			apply_interpreter thy model args t
		| Const ("The", T as Type ("fun", [_, T'])) =>
			(* treat 'The' like a free variable, but with a fixed interpretation for boolean *)
			(* functions that map exactly one constant of type T' to True                    *)
			(case assoc (snd model, t) of
				Some intr =>
					Some (intr, model, args)
			| None =>
				let
					val (sizes, intrs) = model
					val (intr, _, a)   = interpret thy (sizes, []) args (Free ("<The>", T))
					(* create all constants of type T' => bool, ... *)
					val (intrFun, _, _) = interpret thy (sizes, []) {next_idx=1, bounds=[], wellformed=True} (Free ("<The>", Type ("fun", [T', Type ("bool",[])])))
					(* ... and all constants of type T' *)
					val (intrT', _, _) = interpret thy (sizes, []) {next_idx=1, bounds=[], wellformed=True} (Free ("<The>", T'))
					(* returns a list with all unit vectors of length n *)
					(* int -> interpretation list *)
					fun unit_vectors n =
					let
						(* returns the k-th unit vector of length n *)
						(* int * int -> interpretation *)
						fun unit_vector (k,n) =
							Leaf ((replicate (k-1) False) @ (True :: (replicate (n-k) False)))
						(* int -> interpretation list -> interpretation list *)
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
					(* interpretation -> interpretation list *)
					fun make_constants (Leaf xs) =
						unit_vectors (length xs)
					  | make_constants (Node xs) =
						map (fn xs' => Node xs') (pick_all (length xs) (make_constants (hd xs)))
					val constantsFun = make_constants intrFun
					val constantsT'  = make_constants intrT'
					(* interpretation -> interpretation list -> interpretation option *)
					fun the_val (Node xs) cs =
						let
							val TrueCount = foldl (fn (n,x) => if toTrue x = True then n+1 else n) (0,xs)
							fun findThe (x::xs) (c::cs) =
								if toTrue x = True then
									c
								else
									findThe xs cs
							  | findThe _ _ =
								raise REFUTE ("HOLogic_interpreter", "\"The\": not found")
						in
							if TrueCount=1 then
								Some (findThe xs cs)
							else
								None
						end
					  | the_val _ _ =
						raise REFUTE ("HOLogic_interpreter", "\"The\": function interpreted as a leaf")
				in
					case intr of
					  Node xs =>
						let
							(* replace interpretation 'x' by the interpretation determined by 'f' *)
							val intrThe = Node (map (fn (x,f) => if_none (the_val f constantsT') x) (xs ~~ constantsFun))
						in
							Some (intrThe, (sizes, (t,intrThe)::intrs), a)
						end
					| _ =>
						raise REFUTE ("HOLogic_interpreter", "\"The\": interpretation is a leaf")
				end)
		| Const ("Hilbert_Choice.Eps", _) $ t1 =>
			apply_interpreter thy model args t
		| Const ("Hilbert_Choice.Eps", T as Type ("fun", [_, T'])) =>
			(* treat 'The' like a free variable, but with a fixed interpretation for boolean *)
			(* functions that map exactly one constant of type T' to True                    *)
			(case assoc (snd model, t) of
				Some intr =>
					Some (intr, model, args)
			| None =>
				let
					val (sizes, intrs) = model
					val (intr, _, a)   = interpret thy (sizes, []) args (Free ("<Eps>", T))
					(* create all constants of type T' => bool, ... *)
					val (intrFun, _, _) = interpret thy (sizes, []) {next_idx=1, bounds=[], wellformed=True} (Free ("<Eps>", Type ("fun", [T', Type ("bool",[])])))
					(* ... and all constants of type T' *)
					val (intrT', _, _) = interpret thy (sizes, []) {next_idx=1, bounds=[], wellformed=True} (Free ("<Eps>", T'))
					(* returns a list with all unit vectors of length n *)
					(* int -> interpretation list *)
					fun unit_vectors n =
					let
						(* returns the k-th unit vector of length n *)
						(* int * int -> interpretation *)
						fun unit_vector (k,n) =
							Leaf ((replicate (k-1) False) @ (True :: (replicate (n-k) False)))
						(* int -> interpretation list -> interpretation list *)
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
					(* interpretation -> interpretation list *)
					fun make_constants (Leaf xs) =
						unit_vectors (length xs)
					  | make_constants (Node xs) =
						map (fn xs' => Node xs') (pick_all (length xs) (make_constants (hd xs)))
					val constantsFun = make_constants intrFun
					val constantsT'  = make_constants intrT'
					(* interpretation -> interpretation list -> interpretation list *)
					fun true_values (Node xs) cs =
						mapfilter (fn (x,c) => if toTrue x = True then Some c else None) (xs~~cs)
					  | true_values _ _ =
						raise REFUTE ("HOLogic_interpreter", "\"Eps\": function interpreted as a leaf")
				in
					case intr of
					  Node xs =>
						let
							val (wf, intrsEps) = foldl_map (fn (w,(x,f)) =>
								case true_values f constantsT' of
								  []  => (w, x)  (* no value mapped to true -> no restriction *)
								| [c] => (w, c)  (* one value mapped to true -> that's the one *)
								| cs  =>
									let
										(* interpretation * interpretation -> prop_formula *)
										fun interpret_equal (tr1,tr2) =
											(case tr1 of
											  Leaf x =>
												(case tr2 of
												  Leaf y => PropLogic.dot_product (x,y)
												| _      => raise REFUTE ("HOLogic_interpreter", "\"Eps\": second tree is higher"))
												| Node xs =>
												(case tr2 of
												  Leaf _  => raise REFUTE ("HOLogic_interpreter", "\"Eps\": first tree is higher")
												(* extensionality: two functions are equal iff they are equal for every element *)
												| Node ys => PropLogic.all (map interpret_equal (xs ~~ ys))))
									in
										(SAnd (w, PropLogic.exists (map (fn c => interpret_equal (x,c)) cs)), x)  (* impose restrictions on x *)
									end
								)
								(#wellformed a, xs ~~ constantsFun)
							val intrEps = Node intrsEps
						in
							Some (intrEps, (sizes, (t,intrEps)::intrs), {next_idx = #next_idx a, bounds = #bounds a, wellformed = wf})
						end
					| _ =>
						raise REFUTE ("HOLogic_interpreter", "\"Eps\": interpretation is a leaf")
				end)
		| Const ("All", _) $ t1 =>
			let
				val (i,m,a) = interpret thy model args t1
			in
				case i of
				  Node xs =>
					let
						val fmTrue  = PropLogic.all (map toTrue xs)
						val fmFalse = PropLogic.exists (map toFalse xs)
					in
						Some (Leaf [fmTrue, fmFalse], m, a)
					end
				| _ =>
					raise REFUTE ("HOLogic_interpreter", "\"All\" is not followed by a function")
			end
		| Const ("All", _) =>
			Some (interpret thy model args (eta_expand t 1))
		| Const ("Ex", _) $ t1 =>
			let
				val (i,m,a) = interpret thy model args t1
			in
				case i of
				  Node xs =>
					let
						val fmTrue  = PropLogic.exists (map toTrue xs)
						val fmFalse = PropLogic.all (map toFalse xs)
					in
						Some (Leaf [fmTrue, fmFalse], m, a)
					end
				| _ =>
					raise REFUTE ("HOLogic_interpreter", "\"Ex\" is not followed by a function")
			end
		| Const ("Ex", _) =>
			Some (interpret thy model args (eta_expand t 1))
		| Const ("Ex1", _) $ t1 =>
			let
				val (i,m,a) = interpret thy model args t1
			in
				case i of
				  Node xs =>
					let
						(* interpretation list -> prop_formula *)
						fun allfalse []      = True
						  | allfalse (x::xs) = SAnd (toFalse x, allfalse xs)
						(* interpretation list -> prop_formula *)
						fun exactly1true []      = False
						  | exactly1true (x::xs) = SOr (SAnd (toTrue x, allfalse xs), SAnd (toFalse x, exactly1true xs))
						(* interpretation list -> prop_formula *)
						fun atleast2true []      = False
						  | atleast2true (x::xs) = SOr (SAnd (toTrue x, PropLogic.exists (map toTrue xs)), atleast2true xs)
						val fmTrue  = exactly1true xs
						val fmFalse = SOr (allfalse xs, atleast2true xs)
					in
						Some (Leaf [fmTrue, fmFalse], m, a)
					end
				| _ =>
					raise REFUTE ("HOLogic_interpreter", "\"Ex1\" is not followed by a function")
			end
		| Const ("Ex1", _) =>
			Some (interpret thy model args (eta_expand t 1))
		| Const ("op =", _) $ t1 $ t2 =>
				let
					val (i1,m1,a1) = interpret thy model args t1
					val (i2,m2,a2) = interpret thy m1 a1 t2
					(* interpretation * interpretation -> prop_formula *)
					fun interpret_equal (tr1,tr2) =
						(case tr1 of
						  Leaf x =>
							(case tr2 of
							  Leaf y => PropLogic.dot_product (x,y)
							| _      => raise REFUTE ("HOLogic_interpreter", "\"==\": second tree is higher"))
						| Node xs =>
							(case tr2 of
							  Leaf _  => raise REFUTE ("HOLogic_interpreter", "\"==\": first tree is higher")
							(* extensionality: two functions are equal iff they are equal for every element *)
							| Node ys => PropLogic.all (map interpret_equal (xs ~~ ys))))
					(* interpretation * interpretation -> prop_formula *)
					fun interpret_unequal (tr1,tr2) =
						(case tr1 of
						  Leaf x =>
							(case tr2 of
							  Leaf y =>
								let
									fun unequal [] ([],_) =
										False
									  | unequal (x::xs) (y::ys1, ys2) =
										SOr (SAnd (x, PropLogic.exists (ys1@ys2)), unequal xs (ys1, y::ys2))
									  | unequal _ _ =
										raise REFUTE ("HOLogic_interpreter", "\"==\": leafs have different width")
								in
									unequal x (y,[])
								end
							| _      => raise REFUTE ("HOLogic_interpreter", "\"==\": second tree is higher"))
						| Node xs =>
							(case tr2 of
							  Leaf _  => raise REFUTE ("HOLogic_interpreter", "\"==\": first tree is higher")
							(* extensionality: two functions are unequal iff there exist unequal elements *)
							| Node ys => PropLogic.exists (map interpret_unequal (xs ~~ ys))))
					val fmTrue  = interpret_equal (i1,i2)
					val fmFalse = interpret_unequal (i1,i2)
				in
					Some (Leaf [fmTrue, fmFalse], m2, a2)
				end
		| Const ("op =", _) $ t1 =>
			Some (interpret thy model args (eta_expand t 1))
		| Const ("op =", _) =>
			Some (interpret thy model args (eta_expand t 2))
		| Const ("op &", _) $ t1 $ t2 =>
			apply_interpreter thy model args t
		| Const ("op &", _) $ t1 =>
			apply_interpreter thy model args t
		| Const ("op &", _) =>
			Some (Node [Node [TT, FF], Node [FF, FF]], model, args)
		| Const ("op |", _) $ t1 $ t2 =>
			apply_interpreter thy model args t
		| Const ("op |", _) $ t1 =>
			apply_interpreter thy model args t
		| Const ("op |", _) =>
			Some (Node [Node [TT, TT], Node [TT, FF]], model, args)
		| Const ("op -->", _) $ t1 $ t2 =>
			apply_interpreter thy model args t
		| Const ("op -->", _) $ t1 =>
			apply_interpreter thy model args t
		| Const ("op -->", _) =>
			Some (Node [Node [TT, FF], Node [TT, TT]], model, args)
		| Const ("Collect", _) $ t1 =>
			(* Collect == identity *)
			Some (interpret thy model args t1)
		| Const ("Collect", _) =>
			Some (interpret thy model args (eta_expand t 1))
		| Const ("op :", _) $ t1 $ t2 =>
			(* op: == application *)
			Some (interpret thy model args (t2 $ t1))
		| Const ("op :", _) $ t1 =>
			Some (interpret thy model args (eta_expand t 1))
		| Const ("op :", _) =>
			Some (interpret thy model args (eta_expand t 2))
		| _ => None
	end;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun IDT_interpreter thy model args t =
	let
		fun is_var (Free _) = true
		  | is_var (Var _)  = true
		  | is_var _        = false
		fun typeof (Free (_,T)) = T
		  | typeof (Var (_,T))  = T
		  | typeof _            = raise REFUTE ("var_IDT_interpreter", "term is not a variable")
		val (sizes, intrs) = model
		(* power(a,b) computes a^b, for a>=0, b>=0 *)
		(* int * int -> int *)
		fun power (a,0) = 1
		  | power (a,1) = a
		  | power (a,b) = let val ab = power(a,b div 2) in ab * ab * power(a,b mod 2) end
		(* interpretation -> int *)
		fun size_of_interpretation (Leaf xs) = length xs
		  | size_of_interpretation (Node xs) = power (size_of_interpretation (hd xs), length xs)
		(* Term.typ -> int *)
		fun size_of_type T =
			let
				val (i,_,_) = interpret thy model args (Free ("<IDT>", T))
			in
				size_of_interpretation i
			end
		(* int list -> int *)
		fun sum xs = foldl op+ (0, xs)
		(* int list -> int *)
		fun product xs = foldl op* (1, xs)
		(* DatatypeAux.dtyp * Term.typ -> DatatypeAux.dtyp -> Term.typ *)
		fun typ_of_dtyp typ_assoc (DatatypeAux.DtTFree a) =
			the (assoc (typ_assoc, DatatypeAux.DtTFree a))
		  | typ_of_dtyp typ_assoc (DatatypeAux.DtRec i) =
			raise REFUTE ("var_IDT_interpreter", "recursive datatype")
		  | typ_of_dtyp typ_assoc (DatatypeAux.DtType (s, ds)) =
			Type (s, map (typ_of_dtyp typ_assoc) ds)
	in
		if is_var t then
			(case typeof t of
			  Type (s, Ts) =>
				(case DatatypePackage.datatype_info thy s of
				  Some info =>  (* inductive datatype *)
					let
						val index               = #index info
						val descr               = #descr info
						val (_, dtyps, constrs) = the (assoc (descr, index))
					in
						if Library.exists (fn d => case d of DatatypeAux.DtTFree _ => false | _ => true) dtyps then
							raise REFUTE ("var_IDT_interpreter", "recursive datatype argument")
						else if Library.exists (fn (_,ds) => Library.exists DatatypeAux.is_rec_type ds) constrs then
							None  (* recursive datatype (requires an infinite model) *)
						else
							case assoc (intrs, t) of
							  Some intr => Some (intr, model, args)
							| None      =>
								let
									val typ_assoc = dtyps ~~ Ts
									val size = sum (map (fn (_,ds) =>
										product (map (fn d => size_of_type (typ_of_dtyp typ_assoc d)) ds)) constrs)
									val idx  = #next_idx args
									(* for us, an IDT has no "internal structure" -- its interpretation is just a leaf *)
									val intr = (if size=2 then Leaf [BoolVar idx, Not (BoolVar idx)] else Leaf (map BoolVar (idx upto (idx+size-1))))
									val next = (if size=2 then idx+1 else idx+size)
								in
									(* extend the model, increase 'next_idx' *)
									Some (intr, (sizes, (t, intr)::intrs), {next_idx = next, bounds = #bounds args, wellformed = #wellformed args})
								end
					end
				| None => None)
			| _ => None)
		else
		let
			val (head, params) = strip_comb t  (* look into applications to avoid unfolding *)
		in
			(case head of
			  Const (c, T) =>
				(case body_type T of
				  Type (s, Ts) =>
					(case DatatypePackage.datatype_info thy s of
					  Some info =>  (* inductive datatype *)
						let
							val index               = #index info
							val descr               = #descr info
							val (_, dtyps, constrs) = the (assoc (descr, index))
						in
							if Library.exists (fn d => case d of DatatypeAux.DtTFree _ => false | _ => true) dtyps then
								raise REFUTE ("var_IDT_interpreter", "recursive datatype argument")
							else if Library.exists (fn (_,ds) => Library.exists DatatypeAux.is_rec_type ds) constrs then
								None  (* recursive datatype (requires an infinite model) *)
							else
								(case take_prefix (fn (c',_) => c' <> c) constrs of
								  (_, []) =>
									None (* unknown constructor *)
								| (prevs, _) =>
									if null params then
									let
										val typ_assoc = dtyps ~~ Ts
										val offset = sum (map (fn (_,ds) =>
											product (map (fn d => size_of_type (typ_of_dtyp typ_assoc d)) ds)) prevs)
										val (i,_,_) = interpret thy model args (Free ("<IDT>", T))
										(* int * interpretation  -> int * interpretation *)
										fun replace (offset, Leaf xs) =
											(* replace the offset-th element by True, all others by False, inc. offset by 1 *)
											(offset+1, Leaf (snd (foldl_map (fn (n,_) => (n+1, if n=offset then True else False)) (0, xs))))
										  | replace (offset, Node xs) =
											let
												val (offset', xs') = foldl_map replace (offset, xs)
											in
												(offset', Node xs')
											end
										val (_,intr) = replace (offset, i)
									in
										Some (intr, model, args)
									end
									else
										apply_interpreter thy model args t)  (* avoid unfolding by calling 'apply_interpreter' directly *)
						end
					| None => None)
				| _ => None)
			| _ => None)
		end
	end;


(* ------------------------------------------------------------------------- *)
(* PRINTERS                                                                  *)
(* ------------------------------------------------------------------------- *)

	(* theory -> model -> Term.term -> interpretation -> (int -> bool) -> string option *)

	fun var_typevar_printer thy model t intr assignment =
	let
		fun is_var (Free _) = true
		  | is_var (Var _)  = true
		  | is_var _        = false
		fun typeof (Free (_,T)) = T
		  | typeof (Var (_,T))  = T
		  | typeof _            = raise REFUTE ("var_typevar_printer", "term is not a variable")
		fun is_typevar (TFree _) = true
		  | is_typevar (TVar _)  = true
		  | is_typevar _         = false
	in
		if is_var t andalso is_typevar (typeof t) then
			let
				(* interpretation -> int *)
				fun index_from_interpretation (Leaf xs) =
					let
						val idx = find_index (PropLogic.eval assignment) xs
					in
						if idx<0 then
							raise REFUTE ("var_typevar_printer", "illegal interpretation: no value assigned")
						else
							idx
					end
				  | index_from_interpretation _ =
					raise REFUTE ("var_typevar_printer", "interpretation is not a leaf")
				(* string -> string *)
				fun strip_leading_quote s =
					(implode o (fn (x::xs) => if x="'" then xs else (x::xs)) o explode) s
				(* Term.typ -> string *)
				fun string_of_typ (TFree (x,_))    = strip_leading_quote x
				  | string_of_typ (TVar ((x,i),_)) = strip_leading_quote x ^ string_of_int i
				  | string_of_typ _                = raise REFUTE ("var_typevar_printer", "type is not a type variable")
			in
				Some (string_of_typ (typeof t) ^ string_of_int (index_from_interpretation intr))
			end
		else
			None
	end;

	(* theory -> model -> Term.term -> interpretation -> (int -> bool) -> string option *)

	fun var_funtype_printer thy model t intr assignment =
	let
		fun is_var (Free _) = true
		  | is_var (Var _)  = true
		  | is_var _        = false
		fun typeof (Free (_,T)) = T
		  | typeof (Var (_,T))  = T
		  | typeof _            = raise REFUTE ("var_funtype_printer", "term is not a variable")
		fun is_funtype (Type ("fun", [_,_])) = true
		  | is_funtype _                     = false
	in
		if is_var t andalso is_funtype (typeof t) then
			let
				val T1         = domain_type (typeof t)
				val T2         = range_type (typeof t)
				val (sizes, _) = model
				(* create all constants of type T1 *)
				val (i, _, _) = interpret thy (sizes, []) {next_idx=1, bounds=[], wellformed=True} (Free ("var_funtype_printer", T1))
				(* returns a list with all unit vectors of length n *)
				(* int -> interpretation list *)
				fun unit_vectors n =
				let
					(* returns the k-th unit vector of length n *)
					(* int * int -> interpretation *)
					fun unit_vector (k,n) =
						Leaf ((replicate (k-1) False) @ (True :: (replicate (n-k) False)))
					(* int -> interpretation list -> interpretation list *)
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
				(* interpretation -> interpretation list *)
				fun make_constants (Leaf xs) =
					unit_vectors (length xs)
				  | make_constants (Node xs) =
					map (fn xs' => Node xs') (pick_all (length xs) (make_constants (hd xs)))
				(* interpretation list *)
				val results = (case intr of
					  Node xs => xs
					| _       => raise REFUTE ("var_funtype_printer", "interpretation is a leaf"))
				(* string list *)
				val strings = map
					(fn (argi,resulti) => print thy model (Free ("var_funtype_printer", T1)) argi assignment
						^ "\\<mapsto>"
						^ print thy model (Free ("var_funtype_printer", T2)) resulti assignment)
					((make_constants i) ~~ results)
			in
				Some (enclose "(" ")" (commas strings))
			end
		else
			None
	end;

	(* theory -> model -> Term.term -> interpretation -> (int -> bool) -> string option *)

	fun var_settype_printer thy model t intr assignment =
	let
		val (sizes, _) = model
		(* returns a list with all unit vectors of length n *)
		(* int -> interpretation list *)
		fun unit_vectors n =
		let
			(* returns the k-th unit vector of length n *)
			(* int * int -> interpretation *)
			fun unit_vector (k,n) =
				Leaf ((replicate (k-1) False) @ (True :: (replicate (n-k) False)))
			(* int -> interpretation list -> interpretation list *)
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
		(* interpretation -> interpretation list *)
		fun make_constants (Leaf xs) =
			unit_vectors (length xs)
		  | make_constants (Node xs) =
			map (fn xs' => Node xs') (pick_all (length xs) (make_constants (hd xs)))
	in
		case t of
		  Free (x, Type ("set", [T])) =>
			let
				(* interpretation list *)
				val results = (case intr of
				  Node xs => xs
					| _       => raise REFUTE ("var_settype_printer", "interpretation is a leaf"))
				(* create all constants of type T *)
				val (i, _, _) = interpret thy (sizes, []) {next_idx=1, bounds=[], wellformed=True} (Free ("var_settype_printer", T))
				(* string list *)
				val strings = mapfilter
					(fn (argi,Leaf [fmTrue,fmFalse]) =>
						if PropLogic.eval assignment fmTrue then
							Some (print thy model (Free ("x", T)) argi assignment)
						else if PropLogic.eval assignment fmFalse then
							None
						else
							raise REFUTE ("var_settype_printer", "illegal interpretation: no value assigned"))
					((make_constants i) ~~ results)
			in
				Some (enclose "{" "}" (commas strings))
			end
		| Var ((x,i), Type ("set", [T])) =>
			let
				(* interpretation list *)
				val results = (case intr of
				  Node xs => xs
					| _       => raise REFUTE ("var_settype_printer", "interpretation is a leaf"))
				(* create all constants of type T *)
				val (i, _, _) = interpret thy (sizes, []) {next_idx=1, bounds=[], wellformed=True} (Free ("var_settype_printer", T))
				(* string list *)
				val strings = mapfilter
					(fn (argi,Leaf [fmTrue,fmFalse]) =>
						if PropLogic.eval assignment fmTrue then
							Some (print thy model (Free ("var_settype_printer", T)) argi assignment)
						else if PropLogic.eval assignment fmTrue then
							None
						else
							raise REFUTE ("var_settype_printer", "illegal interpretation: no value assigned"))
					((make_constants i) ~~ results)
			in
				Some (enclose "{" "}" (commas strings))
			end
		| _ => None
	end;

	(* theory -> model -> Term.term -> interpretation -> (int -> bool) -> string option *)

	fun HOLogic_printer thy model t intr assignment =
		case t of
		(* 'arbitrary', 'The', 'Hilbert_Choice.Eps' are printed like free variables of the same type *)
		  Const ("arbitrary", T) =>
			Some (print thy model (Free ("<arbitrary>", T)) intr assignment)
		| Const ("The", T) =>
			Some (print thy model (Free ("<The>", T)) intr assignment)
		| Const ("Hilbert_Choice.Eps", T) =>
			Some (print thy model (Free ("<Eps>", T)) intr assignment)
		| _ =>
			None;

	(* theory -> model -> Term.term -> interpretation -> (int -> bool) -> string option *)

	fun var_IDT_printer thy model t intr assignment =
	let
		fun is_var (Free _) = true
		  | is_var (Var _)  = true
		  | is_var _        = false
		fun typeof (Free (_,T)) = T
		  | typeof (Var (_,T))  = T
		  | typeof _            = raise REFUTE ("var_IDT_printer", "term is not a variable")
	in
		if is_var t then
			(case typeof t of
			  Type (s, Ts) =>
				(case DatatypePackage.datatype_info thy s of
				  Some info =>  (* inductive datatype *)
					let
						val index               = #index info
						val descr               = #descr info
						val (_, dtyps, constrs) = the (assoc (descr, index))
					in
						if Library.exists (fn d => case d of DatatypeAux.DtTFree _ => false | _ => true) dtyps then
							raise REFUTE ("var_IDT_printer", "recursive datatype argument")
						else if Library.exists (fn (_,ds) => Library.exists DatatypeAux.is_rec_type ds) constrs then
							None  (* recursive datatype (requires an infinite model) *)
						else
						let
							val (sizes, _) = model
							val typ_assoc  = dtyps ~~ Ts
							(* interpretation -> int *)
							fun index_from_interpretation (Leaf xs) =
								let
									val idx = find_index (PropLogic.eval assignment) xs
								in
									if idx<0 then
										raise REFUTE ("var_IDT_printer", "illegal interpretation: no value assigned")
									else
										idx
								end
							  | index_from_interpretation _ =
								raise REFUTE ("var_IDT_printer", "interpretation is not a leaf")
							(* string -> string *)
							fun unqualify s =
								implode (snd (take_suffix (fn c => c <> ".") (explode s)))
							(* DatatypeAux.dtyp -> Term.typ *)
							fun typ_of_dtyp (DatatypeAux.DtTFree a) =
								the (assoc (typ_assoc, DatatypeAux.DtTFree a))
							  | typ_of_dtyp (DatatypeAux.DtRec i) =
								raise REFUTE ("var_IDT_printer", "recursive datatype")
							  | typ_of_dtyp (DatatypeAux.DtType (s, ds)) =
								Type (s, map typ_of_dtyp ds)
							fun sum xs     = foldl op+ (0, xs)
							fun product xs = foldl op* (1, xs)
							(* power(a,b) computes a^b, for a>=0, b>=0 *)
							(* int * int -> int *)
							fun power (a,0) = 1
							  | power (a,1) = a
							  | power (a,b) = let val ab = power(a,b div 2) in ab * ab * power(a,b mod 2) end
							fun size_of_interpretation (Leaf xs) = length xs
							  | size_of_interpretation (Node xs) = power (size_of_interpretation (hd xs), length xs)
							fun size_of_type T =
								let
									val (i,_,_) = interpret thy (sizes, []) {next_idx=1, bounds=[], wellformed=True} (Free ("<IDT>", T))
								in
									size_of_interpretation i
								end
							(* returns a list with all unit vectors of length n *)
							(* int -> interpretation list *)
							fun unit_vectors n =
							let
								(* returns the k-th unit vector of length n *)
								(* int * int -> interpretation *)
								fun unit_vector (k,n) =
									Leaf ((replicate (k-1) False) @ (True :: (replicate (n-k) False)))
								(* int -> interpretation list -> interpretation list *)
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
							(* interpretation -> interpretation list *)
							fun make_constants (Leaf xs) =
								unit_vectors (length xs)
							  | make_constants (Node xs) =
								map (fn xs' => Node xs') (pick_all (length xs) (make_constants (hd xs)))
							(* DatatypeAux.dtyp list -> int -> string *)
							fun string_of_inductive_type_cargs [] n =
								if n<>0 then
									raise REFUTE ("var_IDT_printer", "internal error computing the element index for an inductive type")
								else
									""
							  | string_of_inductive_type_cargs (d::ds) n =
								let
									val size_ds   = product (map (fn d => size_of_type (typ_of_dtyp d)) ds)
									val T         = typ_of_dtyp d
									val (i,_,_)   = interpret thy (sizes, []) {next_idx=1, bounds=[], wellformed=True} (Free ("<IDT>", T))
									val constants = make_constants i
								in
									" "
									^ (print thy model (Free ("<IDT>", T)) (nth_elem (n div size_ds, constants)) assignment)
									^ (string_of_inductive_type_cargs ds (n mod size_ds))
								end
							(* (string * DatatypeAux.dtyp list) list -> int -> string *)
							fun string_of_inductive_type_constrs [] n =
								raise REFUTE ("var_IDT_printer", "inductive type has fewer elements than needed")
							  | string_of_inductive_type_constrs ((c,ds)::cs) n =
								let
									val size = product (map (fn d => size_of_type (typ_of_dtyp d)) ds)
								in
									if n < size then
										(unqualify c) ^ (string_of_inductive_type_cargs ds n)
									else
										string_of_inductive_type_constrs cs (n - size)
								end
						in
							Some (string_of_inductive_type_constrs constrs (index_from_interpretation intr))
						end
					end
				| None => None)
			| _ => None)
		else
			None
	end;


(* ------------------------------------------------------------------------- *)
(* use 'setup Refute.setup' in an Isabelle theory to initialize the 'Refute' *)
(* structure                                                                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Note: the interpreters and printers are used in reverse order; however,   *)
(*       an interpreter that can handle non-atomic terms ends up being       *)
(*       applied before other interpreters are applied to subterms!          *)
(* ------------------------------------------------------------------------- *)

	(* (theory -> theory) list *)

	val setup =
		[RefuteData.init,
		 add_interpreter "var_typevar"   var_typevar_interpreter,
		 add_interpreter "var_funtype"   var_funtype_interpreter,
		 add_interpreter "var_settype"   var_settype_interpreter,
		 add_interpreter "boundvar"      boundvar_interpreter,
		 add_interpreter "abstraction"   abstraction_interpreter,
		 add_interpreter "apply"         apply_interpreter,
		 add_interpreter "const_unfold"  const_unfold_interpreter,
		 add_interpreter "Pure"          Pure_interpreter,
		 add_interpreter "HOLogic"       HOLogic_interpreter,
		 add_interpreter "IDT"           IDT_interpreter,
		 add_printer "var_typevar"   var_typevar_printer,
		 add_printer "var_funtype"   var_funtype_printer,
		 add_printer "var_settype"   var_settype_printer,
		 add_printer "HOLogic"       HOLogic_printer,
		 add_printer "var_IDT"       var_IDT_printer];

end
