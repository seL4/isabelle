(*  Title:      HOL/Tools/refute.ML
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2003-2004

Finite model generation for HOL formulae, using a SAT solver.
*)

(* TODO: case, rec, size for IDTs are not supported yet      *)

(* ------------------------------------------------------------------------- *)
(* Declares the 'REFUTE' signature as well as a structure 'Refute'.          *)
(* Documentation is available in the Isabelle/Isar theory 'HOL/Refute.thy'.  *)
(* ------------------------------------------------------------------------- *)

signature REFUTE =
sig

	exception REFUTE of string * string

(* ------------------------------------------------------------------------- *)
(* Model/interpretation related code (translation HOL -> propositional logic *)
(* ------------------------------------------------------------------------- *)

	type params
	type interpretation
	type model
	type arguments

	exception CANNOT_INTERPRET of Term.term
	exception MAXVARS_EXCEEDED

	val add_interpreter : string -> (theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option) -> theory -> theory
	val add_printer     : string -> (theory -> model -> Term.term -> interpretation -> (int -> bool) -> Term.term option) -> theory -> theory

	val interpret : theory -> model -> arguments -> Term.term -> (interpretation * model * arguments)  (* exception CANNOT_INTERPRET *)

	val print       : theory -> model -> Term.term -> interpretation -> (int -> bool) -> Term.term
	val print_model : theory -> model -> (int -> bool) -> string

(* ------------------------------------------------------------------------- *)
(* Interface                                                                 *)
(* ------------------------------------------------------------------------- *)

	val set_default_param  : (string * string) -> theory -> theory
	val get_default_param  : theory -> string -> string option
	val get_default_params : theory -> (string * string) list
	val actual_params      : theory -> (string * string) list -> params

	val find_model : theory -> params -> Term.term -> bool -> unit

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

	exception CANNOT_INTERPRET of Term.term;

	(* should be raised by an interpreter when more variables would be *)
	(* required than allowed by 'maxvars'                              *)
	exception MAXVARS_EXCEEDED;

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
				  (* '~~' will raise an exception if the number of branches in   *)
				  (* both trees is different at the current node                 *)
				  Node ys => Node (map tree_pair (xs ~~ ys))
				| Leaf _  => raise REFUTE ("tree_pair", "trees are of different height (first tree is higher)"));


(* ------------------------------------------------------------------------- *)
(* params: parameters that control the translation into a propositional      *)
(*         formula/model generation                                          *)
(*                                                                           *)
(* The following parameters are supported (and required (!), except for      *)
(* "sizes"):                                                                 *)
(*                                                                           *)
(* Name          Type    Description                                         *)
(*                                                                           *)
(* "sizes"       (string * int) list                                         *)
(*                       Size of ground types (e.g. 'a=2), or depth of IDTs. *)
(* "minsize"     int     If >0, minimal size of each ground type/IDT depth.  *)
(* "maxsize"     int     If >0, maximal size of each ground type/IDT depth.  *)
(* "maxvars"     int     If >0, use at most 'maxvars' Boolean variables      *)
(*                       when transforming the term into a propositional     *)
(*                       formula.                                            *)
(* "maxtime"     int     If >0, terminate after at most 'maxtime' seconds.   *)
(* "satsolver"   string  SAT solver to be used.                              *)
(* ------------------------------------------------------------------------- *)

	type params =
		{
			sizes    : (string * int) list,
			minsize  : int,
			maxsize  : int,
			maxvars  : int,
			maxtime  : int,
			satsolver: string
		};

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
		{
			(* just passed unchanged from 'params' *)
			maxvars   : int,
			(* these may change during the translation *)
			next_idx  : int,
			bounds    : interpretation list,
			wellformed: prop_formula
		};


	structure RefuteDataArgs =
	struct
		val name = "HOL/refute";
		type T =
			{interpreters: (string * (theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option)) list,
			 printers: (string * (theory -> model -> Term.term -> interpretation -> (int -> bool) -> Term.term option)) list,
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
(* Note: exception 'CANNOT_INTERPRET t' is raised if the term cannot be      *)
(*       interpreted by any interpreter                                      *)
(* ------------------------------------------------------------------------- *)

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) *)

	fun interpret thy model args t =
		(case get_first (fn (_, f) => f thy model args t) (#interpreters (RefuteData.get thy)) of
		  None   => raise (CANNOT_INTERPRET t)
		| Some x => x);

(* ------------------------------------------------------------------------- *)
(* print: tries to convert the constant denoted by the term 't' into a term  *)
(*        using a suitable printer                                           *)
(* ------------------------------------------------------------------------- *)

	(* theory -> model -> Term.term -> interpretation -> (int -> bool) -> Term.term *)

	fun print thy model t intr assignment =
		(case get_first (fn (_, f) => f thy model t intr assignment) (#printers (RefuteData.get thy)) of
		  None   => Const ("<<no printer available>>", fastype_of t)
		| Some x => x);

(* ------------------------------------------------------------------------- *)
(* print_model: turns the model into a string, using a fixed interpretation  *)
(*              (given by an assignment for Boolean variables) and suitable  *)
(*              printers                                                     *)
(* ------------------------------------------------------------------------- *)

	(* theory -> model -> (int -> bool) -> string *)

	fun print_model thy model assignment =
	let
		val (typs, terms) = model
		val typs_msg =
			if null typs then
				"empty universe (no type variables in term)\n"
			else
				"Size of types: " ^ commas (map (fn (T,i) => Sign.string_of_typ (sign_of thy) T ^ ": " ^ string_of_int i) typs) ^ "\n"
		val show_consts_msg =
			if not (!show_consts) andalso Library.exists (is_Const o fst) terms then
				"set \"show_consts\" to show the interpretation of constants\n"
			else
				""
		val terms_msg =
			if null terms then
				"empty interpretation (no free variables in term)\n"
			else
				space_implode "\n" (mapfilter (fn (t,intr) =>
					(* print constants only if 'show_consts' is true *)
					if (!show_consts) orelse not (is_Const t) then
						Some (Sign.string_of_term (sign_of thy) t ^ ": " ^ Sign.string_of_term (sign_of thy) (print thy model t intr assignment))
					else
						None) terms) ^ "\n"
	in
		typs_msg ^ show_consts_msg ^ terms_msg
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

	(* string -> (theory -> model -> Term.term -> interpretation -> (int -> bool) -> Term.term option) -> theory -> theory *)

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
(*      returns a record that can be passed to 'find_model'.                 *)
(* ------------------------------------------------------------------------- *)

	(* theory -> (string * string) list -> params *)

	fun actual_params thy override =
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
		val allparams = override @ (get_default_params thy)  (* 'override' first, defaults last *)
		(* int *)
		val minsize   = read_int (allparams, "minsize")
		val maxsize   = read_int (allparams, "maxsize")
		val maxvars   = read_int (allparams, "maxvars")
      val maxtime   = read_int (allparams, "maxtime")
		(* string *)
		val satsolver = read_string (allparams, "satsolver")
		(* all remaining parameters of the form "string=int" are collected in  *)
		(* 'sizes'                                                             *)
		(* TODO: it is currently not possible to specify a size for a type     *)
		(*       whose name is one of the other parameters (e.g. 'maxvars')    *)
		(* (string * int) list *)
		val sizes     = mapfilter
			(fn (name,value) => (case Int.fromString value of SOME i => Some (name, i) | NONE => None))
			(filter (fn (name,_) => name<>"minsize" andalso name<>"maxsize" andalso name<>"maxvars" andalso name<>"maxtime" andalso name<>"satsolver")
				allparams)
	in
		{sizes=sizes, minsize=minsize, maxsize=maxsize, maxvars=maxvars, maxtime=maxtime, satsolver=satsolver}
	end;


(* ------------------------------------------------------------------------- *)
(* TRANSLATION HOL -> PROPOSITIONAL LOGIC, BOOLEAN ASSIGNMENT -> MODEL       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* collect_axioms: collects (monomorphic, universally quantified versions    *)
(*                 of) all HOL axioms that are relevant w.r.t 't'            *)
(* ------------------------------------------------------------------------- *)

	(* TODO: to make the collection of axioms more easily extensible, this    *)
	(*       function could be based on user-supplied "axiom collectors",     *)
	(*       similar to 'interpret'/interpreters or 'print'/printers          *)

	(* theory -> Term.term -> Term.term list *)

	(* Which axioms are "relevant" for a particular term/type goes hand in    *)
	(* hand with the interpretation of that term/type by its interpreter (see *)
	(* way below): if the interpretation respects an axiom anyway, the axiom  *)
	(* does not need to be added as a constraint here.                        *)

	(* When an axiom is added as relevant, further axioms may need to be      *)
	(* added as well (e.g. when a constant is defined in terms of other       *)
	(* constants).  To avoid infinite recursion (which should not happen for  *)
	(* constants anyway, but it could happen for "typedef"-related axioms,    *)
	(* since they contain the type again), we use an accumulator 'axs' and    *)
	(* add a relevant axiom only if it is not in 'axs' yet.                   *)

	fun collect_axioms thy t =
	let
		val _ = std_output "Adding axioms..."
		(* (string * Term.term) list *)
		val axioms = flat (map (Symtab.dest o #axioms o Theory.rep_theory) (thy :: Theory.ancestors_of thy))
		(* given a constant 's' of type 'T', which is a subterm of 't', where  *)
		(* 't' has a (possibly) more general type, the schematic type          *)
		(* variables in 't' are instantiated to match the type 'T'             *)
		(* (string * Term.typ) * Term.term -> Term.term *)
		fun specialize_type ((s, T), t) =
		let
			fun find_typeSubs (Const (s', T')) =
				(if s=s' then
					Some (Type.typ_match (Sign.tsig_of (sign_of thy)) (Vartab.empty, (T', T)))
				else
					None
				handle Type.TYPE_MATCH => None)
			  | find_typeSubs (Free _)           = None
			  | find_typeSubs (Var _)            = None
			  | find_typeSubs (Bound _)          = None
			  | find_typeSubs (Abs (_, _, body)) = find_typeSubs body
			  | find_typeSubs (t1 $ t2)          = (case find_typeSubs t1 of Some x => Some x | None => find_typeSubs t2)
			val typeSubs = (case find_typeSubs t of
				  Some x => x
				| None   => raise REFUTE ("collect_axioms", "no type instantiation found for " ^ quote s ^ " in " ^ Sign.string_of_term (sign_of thy) t))
		in
			map_term_types
				(map_type_tvar
					(fn (v,_) =>
						case Vartab.lookup (typeSubs, v) of
						  None =>
							(* schematic type variable not instantiated *)
							raise REFUTE ("collect_axioms", "term " ^ Sign.string_of_term (sign_of thy) t ^ " still has a polymorphic type (after instantiating type of " ^ quote s ^ ")")
						| Some typ =>
							typ))
					t
		end
		(* Term.term list * Term.typ -> Term.term list *)
		fun collect_type_axioms (axs, T) =
			case T of
			(* simple types *)
			  Type ("prop", [])      => axs
			| Type ("fun", [T1, T2]) => collect_type_axioms (collect_type_axioms (axs, T1), T2)
			| Type ("set", [T1])     => collect_type_axioms (axs, T1)
			| Type (s, Ts)           =>
				let
					(* look up the definition of a type, as created by "typedef" *)
					(* (string * Term.term) list -> (string * Term.term) option *)
					fun get_typedefn [] =
						None
					  | get_typedefn ((axname,ax)::axms) =
						(let
							(* Term.term -> Term.typ option *)
							fun type_of_type_definition (Const (s', T')) =
								if s'="Typedef.type_definition" then
									Some T'
								else
									None
							  | type_of_type_definition (Free _)           = None
							  | type_of_type_definition (Var _)            = None
							  | type_of_type_definition (Bound _)          = None
							  | type_of_type_definition (Abs (_, _, body)) = type_of_type_definition body
							  | type_of_type_definition (t1 $ t2)          = (case type_of_type_definition t1 of Some x => Some x | None => type_of_type_definition t2)
						in
							case type_of_type_definition ax of
							  Some T' =>
								let
									val T''      = (domain_type o domain_type) T'
									val typeSubs = Type.typ_match (Sign.tsig_of (sign_of thy)) (Vartab.empty, (T'', T))
									val unvar_ax = map_term_types
										(map_type_tvar
											(fn (v,_) =>
												case Vartab.lookup (typeSubs, v) of
												  None =>
													(* schematic type variable not instantiated *)
													raise ERROR
												| Some typ =>
													typ))
										ax
								in
									Some (axname, unvar_ax)
								end
							| None =>
								get_typedefn axms
						end
						handle ERROR           => get_typedefn axms
						     | MATCH           => get_typedefn axms
						     | Type.TYPE_MATCH => get_typedefn axms)
				in
					case DatatypePackage.datatype_info thy s of
					  Some info =>  (* inductive datatype *)
							(* only collect relevant type axioms for the argument types *)
							foldl collect_type_axioms (axs, Ts)
					| None =>
						(case get_typedefn axioms of
						  Some (axname, ax) => 
							if mem_term (ax, axs) then
								(* collect relevant type axioms for the argument types *)
								foldl collect_type_axioms (axs, Ts)
							else
								(std_output (" " ^ axname);
								collect_term_axioms (ax :: axs, ax))
						| None =>
							(* at least collect relevant type axioms for the argument types *)
							foldl collect_type_axioms (axs, Ts))
				end
			(* TODO: include sort axioms *)
			| TFree (_, sorts)       => ((*if not (null sorts) then std_output " *ignoring sorts*" else ();*) axs)
			| TVar  (_, sorts)       => ((*if not (null sorts) then std_output " *ignoring sorts*" else ();*) axs)
		(* Term.term list * Term.term -> Term.term list *)
		and collect_term_axioms (axs, t) =
			case t of
			(* Pure *)
			  Const ("all", _)                => axs
			| Const ("==", _)                 => axs
			| Const ("==>", _)                => axs
			(* HOL *)
			| Const ("Trueprop", _)           => axs
			| Const ("Not", _)                => axs
			| Const ("True", _)               => axs  (* redundant, since 'True' is also an IDT constructor *)
			| Const ("False", _)              => axs  (* redundant, since 'False' is also an IDT constructor *)
			| Const ("arbitrary", T)          => collect_type_axioms (axs, T)
			| Const ("The", T)                =>
				let
					val ax = specialize_type (("The", T), (the o assoc) (axioms, "HOL.the_eq_trivial"))
				in
					if mem_term (ax, axs) then
						collect_type_axioms (axs, T)
					else
						(std_output " HOL.the_eq_trivial";
						collect_term_axioms (ax :: axs, ax))
				end
			| Const ("Hilbert_Choice.Eps", T) =>
				let
					val ax = specialize_type (("Hilbert_Choice.Eps", T), (the o assoc) (axioms, "Hilbert_Choice.someI"))
				in
					if mem_term (ax, axs) then
						collect_type_axioms (axs, T)
					else
						(std_output " Hilbert_Choice.someI";
						collect_term_axioms (ax :: axs, ax))
				end
			| Const ("All", _) $ t1           => collect_term_axioms (axs, t1)
			| Const ("Ex", _) $ t1            => collect_term_axioms (axs, t1)
			| Const ("op =", T)               => collect_type_axioms (axs, T)
			| Const ("op &", _)               => axs
			| Const ("op |", _)               => axs
			| Const ("op -->", _)             => axs
			(* sets *)
			| Const ("Collect", T)            => collect_type_axioms (axs, T)
			| Const ("op :", T)               => collect_type_axioms (axs, T)
			(* other optimizations *)
			| Const ("Finite_Set.card", T)    => collect_type_axioms (axs, T)
			(* simply-typed lambda calculus *)
			| Const (s, T)                    =>
				let
					(* look up the definition of a constant, as created by "constdefs" *)
					(* string -> Term.typ -> (string * Term.term) list -> (string * Term.term) option *)
					fun get_defn [] =
						None
					  | get_defn ((axname,ax)::axms) =
						(let
							val (lhs, _) = Logic.dest_equals ax  (* equations only *)
							val c        = head_of lhs
							val (s', T') = dest_Const c
						in
							if s=s' then
								let
									val typeSubs = Type.typ_match (Sign.tsig_of (sign_of thy)) (Vartab.empty, (T', T))
									val unvar_ax = map_term_types
										(map_type_tvar
											(fn (v,_) =>
												case Vartab.lookup (typeSubs, v) of
												  None =>
													(* schematic type variable not instantiated *)
													raise ERROR
												| Some typ =>
													typ))
										ax
								in
									Some (axname, unvar_ax)
								end
							else
								get_defn axms
						end
						handle ERROR           => get_defn axms
						     | TERM _          => get_defn axms
						     | Type.TYPE_MATCH => get_defn axms)
						(* unit -> bool *)
						fun is_IDT_constructor () =
							(case body_type T of
							  Type (s', _) =>
								(case DatatypePackage.constrs_of thy s' of
								  Some constrs =>
									Library.exists (fn c =>
										(case c of
										  Const (cname, ctype) =>
											cname = s andalso Type.typ_instance (Sign.tsig_of (sign_of thy)) (T, ctype)
										| _ =>
											raise REFUTE ("collect_axioms", "IDT constructor is not a constant")))
										constrs
								| None =>
									false)
							| _  =>
								false)
						(* unit -> bool *)
						fun is_IDT_recursor () =
							(* the type of a recursion operator: [T1,...,Tn,IDT]--->TResult (where *)
							(* the T1,...,Tn depend on the types of the datatype's constructors)   *)
							((case last_elem (binder_types T) of
							  Type (s', _) =>
								(case DatatypePackage.datatype_info thy s' of
								  Some info =>
									(* TODO: I'm not quite sute if comparing the names is sufficient, or if *)
									(*       we should also check the type                                  *)
									s mem (#rec_names info)
								| None =>  (* not an inductive datatype *)
									false)
							| _ =>  (* a (free or schematic) type variable *)
								false)
							handle LIST "last_elem" => false)  (* not even a function type *)
				in
					if is_IDT_constructor () orelse is_IDT_recursor () then
						(* only collect relevant type axioms *)
						collect_type_axioms (axs, T)
					else
						(case get_defn axioms of
						  Some (axname, ax) => 
							if mem_term (ax, axs) then
								(* collect relevant type axioms *)
								collect_type_axioms (axs, T)
							else
								(std_output (" " ^ axname);
								collect_term_axioms (ax :: axs, ax))
						| None =>
							(* collect relevant type axioms *)
							collect_type_axioms (axs, T))
				end
			| Free (_, T)                     => collect_type_axioms (axs, T)
			| Var (_, T)                      => collect_type_axioms (axs, T)
			| Bound i                         => axs
			| Abs (_, T, body)                => collect_term_axioms (collect_type_axioms (axs, T), body)
			| t1 $ t2                         => collect_term_axioms (collect_term_axioms (axs, t1), t2)
		(* universal closure over schematic variables *)
		(* Term.term -> Term.term *)
		fun close_form t =
		let
			(* (Term.indexname * Term.typ) list *)
			val vars = sort_wrt (fst o fst) (map dest_Var (term_vars t))
		in
			foldl
				(fn (t', ((x,i),T)) => (Term.all T) $ Abs (x, T, abstract_over (Var((x,i),T), t')))
				(t, vars)
		end
		(* Term.term list *)
		val result = map close_form (collect_term_axioms ([], t))
		val _ = writeln " ...done."
	in
		result
	end;

(* ------------------------------------------------------------------------- *)
(* ground_types: collects all ground types in a term (including argument     *)
(*               types of other types), suppressing duplicates.  Does not    *)
(*               return function types, set types, non-recursive IDTs, or    *)
(*               'propT'.  For IDTs, also the argument types of constructors *)
(*               are considered.                                             *)
(* ------------------------------------------------------------------------- *)

	(* theory -> Term.term -> Term.typ list *)

	fun ground_types thy t =
	let
		(* Term.typ * Term.typ list -> Term.typ list *)
		fun collect_types (T, acc) =
			if T mem acc then
				acc  (* prevent infinite recursion (for IDTs) *)
			else
				(case T of
				  Type ("fun", [T1, T2]) => collect_types (T1, collect_types (T2, acc))
				| Type ("prop", [])      => acc
				| Type ("set", [T1])     => collect_types (T1, acc)
				| Type (s, Ts)           =>
					(case DatatypePackage.datatype_info thy s of
					  Some info =>  (* inductive datatype *)
						let
							val index               = #index info
							val descr               = #descr info
							val (_, dtyps, constrs) = (the o assoc) (descr, index)
							val typ_assoc           = dtyps ~~ Ts
							(* sanity check: every element in 'dtyps' must be a 'DtTFree' *)
							val _ = (if Library.exists (fn d =>
									case d of DatatypeAux.DtTFree _ => false | _ => true) dtyps
								then
									raise REFUTE ("ground_types", "datatype argument (for type " ^ Sign.string_of_typ (sign_of thy) (Type (s, Ts)) ^ ") is not a variable")
								else
									())
							(* DatatypeAux.descr -> (DatatypeAux.dtyp * Term.typ) list -> DatatypeAux.dtyp -> Term.typ *)
							fun typ_of_dtyp descr typ_assoc (DatatypeAux.DtTFree a) =
								(* replace a 'DtTFree' variable by the associated type *)
								(the o assoc) (typ_assoc, DatatypeAux.DtTFree a)
							  | typ_of_dtyp descr typ_assoc (DatatypeAux.DtRec i) =
								let
									val (s, ds, _) = (the o assoc) (descr, i)
								in
									Type (s, map (typ_of_dtyp descr typ_assoc) ds)
								end
							  | typ_of_dtyp descr typ_assoc (DatatypeAux.DtType (s, ds)) =
								Type (s, map (typ_of_dtyp descr typ_assoc) ds)
							(* if the current type is a recursive IDT (i.e. a depth is required), add it to 'acc' *)
							val acc' = (if Library.exists (fn (_, ds) => Library.exists DatatypeAux.is_rec_type ds) constrs then
									T ins acc
								else
									acc)
							(* collect argument types *)
							val acc_args = foldr collect_types (Ts, acc')
							(* collect constructor types *)
							val acc_constrs = foldr collect_types (flat (map (fn (_, ds) => map (typ_of_dtyp descr typ_assoc) ds) constrs), acc_args)
						in
							acc_constrs
						end
					| None =>  (* not an inductive datatype, e.g. defined via "typedef" or "typedecl" *)
						T ins (foldr collect_types (Ts, acc)))
				| TFree _                => T ins acc
				| TVar _                 => T ins acc)
	in
		it_term_types collect_types (t, [])
	end;

(* ------------------------------------------------------------------------- *)
(* string_of_typ: (rather naive) conversion from types to strings, used to   *)
(*                look up the size of a type in 'sizes'.  Parameterized      *)
(*                types with different parameters (e.g. "'a list" vs. "bool  *)
(*                list") are identified.                                     *)
(* ------------------------------------------------------------------------- *)

	(* Term.typ -> string *)

	fun string_of_typ (Type (s, _))     = s
	  | string_of_typ (TFree (s, _))    = s
	  | string_of_typ (TVar ((s,_), _)) = s;

(* ------------------------------------------------------------------------- *)
(* first_universe: returns the "first" (i.e. smallest) universe by assigning *)
(*                 'minsize' to every type for which no size is specified in *)
(*                 'sizes'                                                   *)
(* ------------------------------------------------------------------------- *)

	(* Term.typ list -> (string * int) list -> int -> (Term.typ * int) list *)

	fun first_universe xs sizes minsize =
	let
		fun size_of_typ T =
			case assoc (sizes, string_of_typ T) of
			  Some n => n
			| None   => minsize
	in
		map (fn T => (T, size_of_typ T)) xs
	end;

(* ------------------------------------------------------------------------- *)
(* next_universe: enumerates all universes (i.e. assignments of sizes to     *)
(*                types), where the minimal size of a type is given by       *)
(*                'minsize', the maximal size is given by 'maxsize', and a   *)
(*                type may have a fixed size given in 'sizes'                *)
(* ------------------------------------------------------------------------- *)

	(* (Term.typ * int) list -> (string * int) list -> int -> int -> (Term.typ * int) list option *)

	fun next_universe xs sizes minsize maxsize =
	let
		(* int -> int list -> int list option *)
		fun add1 _ [] =
			None  (* overflow *)
		  | add1 max (x::xs) =
		 	if x<max orelse max<0 then
				Some ((x+1)::xs)  (* add 1 to the head *)
			else
				apsome (fn xs' => 0 :: xs') (add1 max xs)  (* carry-over *)
		(* int -> int list * int list -> int list option *)
		fun shift _ (_, []) =
			None
		  | shift max (zeros, x::xs) =
			if x=0 then
				shift max (0::zeros, xs)
			else
				apsome (fn xs' => (x-1) :: (zeros @ xs')) (add1 max xs)
		(* creates the "first" list of length 'len', where the sum of all list *)
		(* elements is 'sum', and the length of the list is 'len'              *)
		(* int -> int -> int -> int list option *)
		fun make_first 0 sum _ =
			if sum=0 then
				Some []
			else
				None
		  | make_first len sum max =
			if sum<=max orelse max<0 then
				apsome (fn xs' => sum :: xs') (make_first (len-1) 0 max)
			else
				apsome (fn xs' => max :: xs') (make_first (len-1) (sum-max) max)
		(* enumerates all int lists with a fixed length, where 0<=x<='max' for *)
		(* all list elements x (unless 'max'<0)                                *)
		(* int -> int list -> int list option *)
		fun next max xs =
			(case shift max ([], xs) of
			  Some xs' =>
				Some xs'
			| None =>
				let
					val (len, sum) = foldl (fn ((l, s), x) => (l+1, s+x)) ((0, 0), xs)
				in
					make_first len (sum+1) max  (* increment 'sum' by 1 *)
				end)
		(* only consider those types for which the size is not fixed *)
		val mutables = filter (fn (T, _) => assoc (sizes, string_of_typ T) = None) xs
		(* subtract 'minsize' from every size (will be added again at the end) *)
		val diffs = map (fn (_, n) => n-minsize) mutables
	in
		case next (maxsize-minsize) diffs of
		  Some diffs' =>
			(* merge with those types for which the size is fixed *)
			Some (snd (foldl_map (fn (ds, (T, _)) =>
				case assoc (sizes, string_of_typ T) of
				  Some n => (ds, (T, n))                      (* return the fixed size *)
				| None   => (tl ds, (T, minsize + (hd ds))))  (* consume the head of 'ds', add 'minsize' *)
				(diffs', xs)))
		| None =>
			None
	end;

(* ------------------------------------------------------------------------- *)
(* toTrue: converts the interpretation of a Boolean value to a propositional *)
(*         formula that is true iff the interpretation denotes "true"        *)
(* ------------------------------------------------------------------------- *)

	(* interpretation -> prop_formula *)

	fun toTrue (Leaf [fm,_]) = fm
	  | toTrue _             = raise REFUTE ("toTrue", "interpretation does not denote a Boolean value");

(* ------------------------------------------------------------------------- *)
(* toFalse: converts the interpretation of a Boolean value to a              *)
(*          propositional formula that is true iff the interpretation        *)
(*          denotes "false"                                                  *)
(* ------------------------------------------------------------------------- *)

	(* interpretation -> prop_formula *)

	fun toFalse (Leaf [_,fm]) = fm
	  | toFalse _             = raise REFUTE ("toFalse", "interpretation does not denote a Boolean value");

(* ------------------------------------------------------------------------- *)
(* find_model: repeatedly calls 'interpret' with appropriate parameters,     *)
(*             applies a SAT solver, and (in case a model is found) displays *)
(*             the model to the user by calling 'print_model'                *)
(* thy       : the current theory                                            *)
(* {...}     : parameters that control the translation/model generation      *)
(* t         : term to be translated into a propositional formula            *)
(* negate    : if true, find a model that makes 't' false (rather than true) *)
(* Note: exception 'TimeOut' is raised if the algorithm does not terminate   *)
(*       within 'maxtime' seconds (if 'maxtime' >0)                          *)
(* ------------------------------------------------------------------------- *)

	(* theory -> params -> Term.term -> bool -> unit *)

	fun find_model thy {sizes, minsize, maxsize, maxvars, maxtime, satsolver} t negate =
	let
		(* unit -> unit *)
		fun wrapper () =
		let
			(* Term.term list *)
			val axioms = collect_axioms thy t
			(* Term.typ list *)
			val types  = foldl (fn (acc, t') => acc union (ground_types thy t')) ([], t :: axioms)
			val _      = writeln ("Ground types: "
				^ (if null types then "none."
				   else commas (map (Sign.string_of_typ (sign_of thy)) types)))
			(* (Term.typ * int) list -> unit *)
			fun find_model_loop universe =
			(let
				val init_model             = (universe, [])
				val init_args              = {maxvars = maxvars, next_idx = 1, bounds = [], wellformed = True}
				val _                      = std_output ("Translating term (sizes: " ^ commas (map (fn (_, n) => string_of_int n) universe) ^ ") ...")
				(* translate 't' and all axioms *)
				val ((model, args), intrs) = foldl_map (fn ((m, a), t') =>
					let
						val (i, m', a') = interpret thy m a t'
					in
						((m', a'), i)
					end) ((init_model, init_args), t :: axioms)
				(* make 't' either true or false, and make all axioms true, and *)
				(* add the well-formedness side condition                       *)
				val fm_t  = (if negate then toFalse else toTrue) (hd intrs)
				val fm_ax = PropLogic.all (map toTrue (tl intrs))
				val fm    = PropLogic.all [#wellformed args, fm_ax, fm_t]
			in
				std_output " invoking SAT solver...";
				case SatSolver.invoke_solver satsolver fm of
				  None =>
					error ("SAT solver " ^ quote satsolver ^ " not configured.")
				| Some None =>
					(std_output " no model found.\n";
					case next_universe universe sizes minsize maxsize of
					  Some universe' => find_model_loop universe'
					| None           => writeln "Search terminated, no larger universe within the given limits.")
				| Some (Some assignment) =>
					writeln ("\n*** Model found: ***\n" ^ print_model thy model assignment)
			end handle MAXVARS_EXCEEDED =>
				writeln ("\nSearch terminated, number of Boolean variables (" ^ string_of_int maxvars ^ " allowed) exceeded.")
			| CANNOT_INTERPRET t' =>
				error ("Unable to interpret term " ^ Sign.string_of_term (sign_of thy) t'))
			in
				find_model_loop (first_universe types sizes minsize)
			end
		in
			(* some parameter sanity checks *)
			assert (minsize>=1) ("\"minsize\" is " ^ string_of_int minsize ^ ", must be at least 1");
			assert (maxsize>=1) ("\"maxsize\" is " ^ string_of_int maxsize ^ ", must be at least 1");
			assert (maxsize>=minsize) ("\"maxsize\" (=" ^ string_of_int maxsize ^ ") is less than \"minsize\" (=" ^ string_of_int minsize ^ ").");
			assert (maxvars>=0) ("\"maxvars\" is " ^ string_of_int maxvars ^ ", must be at least 0");
			assert (maxtime>=0) ("\"maxtime\" is " ^ string_of_int maxtime ^ ", must be at least 0");
			(* enter loop with/without time limit *)
			writeln ("Trying to find a model that " ^ (if negate then "refutes" else "satisfies") ^ ": "
				^ Sign.string_of_term (sign_of thy) t);
			if maxtime>0 then
				(* TODO: this only works with SML/NJ *)
				((*TimeLimit.timeLimit (Time.fromSeconds (Int32.fromInt maxtime))*)
					wrapper ()
				(*handle TimeLimit.TimeOut =>
					writeln ("\nSearch terminated, time limit ("
						^ string_of_int maxtime ^ " second"
						^ (if maxtime=1 then "" else "s")
						^ ") exceeded.")*))
			else
				wrapper ()
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
		find_model thy (actual_params thy params) t false;

(* ------------------------------------------------------------------------- *)
(* refute_term: calls 'find_model' to find a model that refutes 't'          *)
(* params     : list of '(name, value)' pairs used to override default       *)
(*              parameters                                                   *)
(* ------------------------------------------------------------------------- *)

	(* theory -> (string * string) list -> Term.term -> unit *)

	fun refute_term thy params t =
	let
		(* disallow schematic type variables, since we cannot properly negate  *)
		(* terms containing them (their logical meaning is that there EXISTS a *)
		(* type s.t. ...; to refute such a formula, we would have to show that *)
		(* for ALL types, not ...)                                             *)
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
		(* is not really a problem as long as 'find_model' still      *)
		(* interprets the resulting term correctly, without checking  *)
		(* its type.                                                  *)
	in
		find_model thy (actual_params thy params) ex_closure true
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

(* ------------------------------------------------------------------------- *)
(* make_constants: returns all interpretations that have the same tree       *)
(*                 structure as 'intr', but consist of unit vectors with     *)
(*                 'True'/'False' only (no Boolean variables)                *)
(* ------------------------------------------------------------------------- *)

	(* interpretation -> interpretation list *)

	fun make_constants intr =
	let
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
	in
		case intr of
		  Leaf xs => unit_vectors (length xs)
		| Node xs => map (fn xs' => Node xs') (pick_all (length xs) (make_constants (hd xs)))
	end;

(* ------------------------------------------------------------------------- *)
(* size_of_type: returns the number of constants in a type (i.e. 'length     *)
(*               (make_constants intr)', but implemented more efficiently)   *)
(* ------------------------------------------------------------------------- *)

	(* interpretation -> int *)

	fun size_of_type intr =
	let
		(* power(a,b) computes a^b, for a>=0, b>=0 *)
		(* int * int -> int *)
		fun power (a,0) = 1
		  | power (a,1) = a
		  | power (a,b) = let val ab = power(a,b div 2) in ab * ab * power(a,b mod 2) end
	in
		case intr of
		  Leaf xs => length xs
		| Node xs => power (size_of_type (hd xs), length xs)
	end;

(* ------------------------------------------------------------------------- *)
(* TT/FF: interpretations that denote "true" or "false", respectively        *)
(* ------------------------------------------------------------------------- *)

	(* interpretation *)

	val TT = Leaf [True, False];

	val FF = Leaf [False, True];

(* ------------------------------------------------------------------------- *)
(* make_equality: returns an interpretation that denotes (extensional)       *)
(*                equality of two interpretations                            *)
(* ------------------------------------------------------------------------- *)

	(* We could in principle represent '=' on a type T by a particular        *)
	(* interpretation.  However, the size of that interpretation is quadratic *)
	(* in the size of T.  Therefore comparing the interpretations 'i1' and    *)
	(* 'i2' directly is more efficient than constructing the interpretation   *)
	(* for equality on T first, and "applying" this interpretation to 'i1'    *)
	(* and 'i2' in the usual way (cf. 'interpretation_apply') then.           *)

	(* interpretation * interpretation -> interpretation *)

	fun make_equality (i1, i2) =
	let
		(* interpretation * interpretation -> prop_formula *)
		fun equal (i1, i2) =
			(case i1 of
			  Leaf xs =>
				(case i2 of
				  Leaf ys => PropLogic.dot_product (xs, ys)
				| Node _  => raise REFUTE ("make_equality", "second interpretation is higher"))
			| Node xs =>
				(case i2 of
				  Leaf _  => raise REFUTE ("make_equality", "first interpretation is higher")
				| Node ys => PropLogic.all (map equal (xs ~~ ys))))
		(* interpretation * interpretation -> prop_formula *)
		fun not_equal (i1, i2) =
			(case i1 of
			  Leaf xs =>
				(case i2 of
				  Leaf ys => PropLogic.all ((PropLogic.exists xs) :: (PropLogic.exists ys) ::
					(map (fn (x,y) => SOr (SNot x, SNot y)) (xs ~~ ys)))  (* defined and not equal *)
				| Node _  => raise REFUTE ("make_equality", "second interpretation is higher"))
			| Node xs =>
				(case i2 of
				  Leaf _  => raise REFUTE ("make_equality", "first interpretation is higher")
				| Node ys => PropLogic.exists (map not_equal (xs ~~ ys))))
	in
		(* a value may be undefined; therefore 'not_equal' is not just the     *)
		(* negation of 'equal':                                                *)
		(* - two interpretations are 'equal' iff they are both defined and     *)
		(*   denote the same value                                             *)
		(* - two interpretations are 'not_equal' iff they are both defined at  *)
		(*   least partially, and a defined part denotes different values      *)
		(* - an undefined interpretation is neither 'equal' nor 'not_equal' to *)
		(*   another value                                                     *)
		Leaf [equal (i1, i2), not_equal (i1, i2)]
	end;


	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	(* simply typed lambda calculus: Isabelle's basic term syntax, with type  *)
	(* variables, function types, and propT                                   *)

	fun stlc_interpreter thy model args t =
	let
		val (typs, terms)                           = model
		val {maxvars, next_idx, bounds, wellformed} = args
		(* Term.typ -> (interpretation * model * arguments) option *)
		fun interpret_groundterm T =
		let
			(* unit -> (interpretation * model * arguments) option *)
			fun interpret_groundtype () =
			let
				val size = (if T = Term.propT then 2 else (the o assoc) (typs, T))  (* the model MUST specify a size for ground types *)
				val next = (if size=2 then next_idx+1 else next_idx+size)  (* optimization for types with size 2 *)
				val _    = (if next-1>maxvars andalso maxvars>0 then raise MAXVARS_EXCEEDED else ())  (* check if 'maxvars' is large enough *)
				(* prop_formula list *)
				val fms  = (if size=2 then [BoolVar next_idx, Not (BoolVar next_idx)]
					else (map BoolVar (next_idx upto (next_idx+size-1))))
				(* interpretation *)
				val intr = Leaf fms
				(* prop_formula list -> prop_formula *)
				fun one_of_two_false []      = True
				  | one_of_two_false (x::xs) = SAnd (PropLogic.all (map (fn x' => SOr (SNot x, SNot x')) xs), one_of_two_false xs)
				(* prop_formula list -> prop_formula *)
				fun exactly_one_true xs = SAnd (PropLogic.exists xs, one_of_two_false xs)
				(* prop_formula *)
				val wf   = (if size=2 then True else exactly_one_true fms)
			in
				(* extend the model, increase 'next_idx', add well-formedness condition *)
				Some (intr, (typs, (t, intr)::terms), {maxvars = maxvars, next_idx = next, bounds = bounds, wellformed = SAnd (wellformed, wf)})
			end
		in
			case T of
			  Type ("fun", [T1, T2]) =>
				let
					(* we create 'size_of_type (interpret (... T1))' different copies *)
					(* of the interpretation for 'T2', which are then combined into a *)
					(* single new interpretation                                      *)
					val (i1, _, _) =
						(interpret thy model {maxvars=0, next_idx=1, bounds=[], wellformed=True} (Free ("dummy", T1))
						handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
					(* make fresh copies, with different variable indices *)
					(* 'idx': next variable index                         *)
					(* 'n'  : number of copies                            *)
					(* int -> int -> (int * interpretation list * prop_formula *)
					fun make_copies idx 0 =
						(idx, [], True)
					  | make_copies idx n =
						let
							val (copy, _, new_args) =
								(interpret thy (typs, []) {maxvars = maxvars, next_idx = idx, bounds = [], wellformed = True} (Free ("dummy", T2))
								handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
							val (idx', copies, wf') = make_copies (#next_idx new_args) (n-1)
						in
							(idx', copy :: copies, SAnd (#wellformed new_args, wf'))
						end
					val (next, copies, wf) = make_copies next_idx (size_of_type i1)
					(* combine copies into a single interpretation *)
					val intr = Node copies
				in
					(* extend the model, increase 'next_idx', add well-formedness condition *)
					Some (intr, (typs, (t, intr)::terms), {maxvars = maxvars, next_idx = next, bounds = bounds, wellformed = SAnd (wellformed, wf)})
				end
			| Type _  => interpret_groundtype ()
			| TFree _ => interpret_groundtype ()
			| TVar  _ => interpret_groundtype ()
		end
	in
		case assoc (terms, t) of
		  Some intr =>
			(* return an existing interpretation *)
			Some (intr, model, args)
		| None =>
			(case t of
			  Const (_, T)     =>
				interpret_groundterm T
			| Free (_, T)      =>
				interpret_groundterm T
			| Var (_, T)       =>
				interpret_groundterm T
			| Bound i          =>
				Some (nth_elem (i, #bounds args), model, args)
			| Abs (x, T, body) =>
				let
					(* create all constants of type 'T' *)
					val (i, _, _) =
						(interpret thy model {maxvars=0, next_idx=1, bounds=[], wellformed=True} (Free ("dummy", T))
						handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
					val constants = make_constants i
					(* interpret the 'body' separately for each constant *)
					val ((model', args'), bodies) = foldl_map
						(fn ((m,a), c) =>
							let
								(* add 'c' to 'bounds' *)
								val (i', m', a') = interpret thy m {maxvars = #maxvars a, next_idx = #next_idx a, bounds = (c :: #bounds a), wellformed = #wellformed a} body
							in
								(* keep the new model m' and 'next_idx' and 'wellformed', but use old 'bounds' *)
								((m', {maxvars = maxvars, next_idx = #next_idx a', bounds = bounds, wellformed = #wellformed a'}), i')
							end)
						((model, args), constants)
				in
					Some (Node bodies, model', args')
				end
			| t1 $ t2          =>
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
						raise REFUTE ("stlc_interpreter", "empty list (in dot product)")
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
						raise REFUTE ("stlc_interpreter", "empty list (in pick_all)")
					(* interpretation -> prop_formula list *)
					fun interpretation_to_prop_formula_list (Leaf xs) =
						xs
					  | interpretation_to_prop_formula_list (Node trees) =
						map PropLogic.all (pick_all (map interpretation_to_prop_formula_list trees))
					(* interpretation * interpretation -> interpretation *)
					fun interpretation_apply (tr1,tr2) =
						(case tr1 of
						  Leaf _ =>
							raise REFUTE ("stlc_interpreter", "first interpretation is a leaf")
						| Node xs =>
							prop_formula_list_dot_product_interpretation_list (interpretation_to_prop_formula_list tr2, xs))
					(* interpret 't1' and 't2' separately *)
					val (intr1, model1, args1) = interpret thy model args t1
					val (intr2, model2, args2) = interpret thy model1 args1 t2
				in
					Some (interpretation_apply (intr1,intr2), model2, args2)
				end)
	end;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun Pure_interpreter thy model args t =
		case t of
		  Const ("all", _) $ t1 =>  (* in the meta-logic, 'all' MUST be followed by an argument term *)
			let
				val (i, m, a) = interpret thy model args t1
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
				val (i1, m1, a1) = interpret thy model args t1
				val (i2, m2, a2) = interpret thy m1 a1 t2
			in
				Some (make_equality (i1, i2), m2, a2)
			end
		| Const ("==>", _) =>  (* simpler than translating 'Const ("==>", _) $ t1 $ t2' *)
			Some (Node [Node [TT, FF], Node [TT, TT]], model, args)
		| _ => None;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun HOLogic_interpreter thy model args t =
	let
		(* Term.term -> int -> Term.term *)
		fun eta_expand t i =
		let
			val Ts = binder_types (fastype_of t)
		in
			foldr (fn (T, t) => Abs ("<eta_expand>", T, t))
				(take (i, Ts), list_comb (t, map Bound (i-1 downto 0)))
		end
	in
	(* ------------------------------------------------------------------------- *)
	(* Providing interpretations directly is more efficient than unfolding the   *)
	(* logical constants.  IN HOL however, logical constants can themselves be   *)
	(* arguments.  "All" and "Ex" are then translated just like any other        *)
	(* constant, with the relevant axiom being added by 'collect_axioms'.        *)
	(* ------------------------------------------------------------------------- *)
		case t of
		  Const ("Trueprop", _) =>
			Some (Node [TT, FF], model, args)
		| Const ("Not", _) =>
			Some (Node [FF, TT], model, args)
		| Const ("True", _) =>  (* redundant, since 'True' is also an IDT constructor *)
			Some (TT, model, args)
		| Const ("False", _) =>  (* redundant, since 'False' is also an IDT constructor *)
			Some (FF, model, args)
		| Const ("All", _) $ t1 =>
			let
				val (i, m, a) = interpret thy model args t1
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
		| Const ("Ex", _) $ t1 =>
			let
				val (i, m, a) = interpret thy model args t1
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
		| Const ("op =", _) $ t1 $ t2 =>
			let
				val (i1, m1, a1) = interpret thy model args t1
				val (i2, m2, a2) = interpret thy m1 a1 t2
			in
				Some (make_equality (i1, i2), m2, a2)
			end
		| Const ("op =", _) $ t1 =>
			(Some (interpret thy model args (eta_expand t 1)) handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
		| Const ("op =", _) =>
			(Some (interpret thy model args (eta_expand t 2)) handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
		| Const ("op &", _) =>
			Some (Node [Node [TT, FF], Node [FF, FF]], model, args)
		| Const ("op |", _) =>
			Some (Node [Node [TT, TT], Node [TT, FF]], model, args)
		| Const ("op -->", _) =>
			Some (Node [Node [TT, FF], Node [TT, TT]], model, args)
		| _ => None
	end;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun set_interpreter thy model args t =
	(* "T set" is isomorphic to "T --> bool" *)
	let
		val (typs, terms) = model
		(* Term.term -> int -> Term.term *)
		fun eta_expand t i =
		let
			val Ts = binder_types (fastype_of t)
		in
			foldr (fn (T, t) => Abs ("<eta_expand>", T, t))
				(take (i, Ts), list_comb (t, map Bound (i-1 downto 0)))
		end
	in
		case assoc (terms, t) of
		  Some intr =>
			(* return an existing interpretation *)
			Some (intr, model, args)
		| None =>
			(case t of
			  Free (x, Type ("set", [T])) =>
				(let
					val (intr, _, args') = interpret thy (typs, []) args (Free (x, T --> HOLogic.boolT))
				in
					Some (intr, (typs, (t, intr)::terms), args')
				end handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
			| Var ((x,i), Type ("set", [T])) =>
				(let
					val (intr, _, args') = interpret thy (typs, []) args (Var ((x,i), T --> HOLogic.boolT))
				in
					Some (intr, (typs, (t, intr)::terms), args')
				end handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
			| Const (s, Type ("set", [T])) =>
				(let
					val (intr, _, args') = interpret thy (typs, []) args (Const (s, T --> HOLogic.boolT))
				in
					Some (intr, (typs, (t, intr)::terms), args')
				end handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
			(* 'Collect' == identity *)
			| Const ("Collect", _) $ t1 =>
				Some (interpret thy model args t1)
			| Const ("Collect", _) =>
				(Some (interpret thy model args (eta_expand t 1)) handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
			(* 'op :' == application *)
			| Const ("op :", _) $ t1 $ t2 =>
				Some (interpret thy model args (t2 $ t1))
			| Const ("op :", _) $ t1 =>
				(Some (interpret thy model args (eta_expand t 1)) handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
			| Const ("op :", _) =>
				(Some (interpret thy model args (eta_expand t 2)) handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
			| _ => None)
	end;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	fun IDT_interpreter thy model args t =
	let
		val (typs, terms) = model
		(* DatatypeAux.descr -> (DatatypeAux.dtyp * Term.typ) list -> DatatypeAux.dtyp -> Term.typ *)
		fun typ_of_dtyp descr typ_assoc (DatatypeAux.DtTFree a) =
			(* replace a 'DtTFree' variable by the associated type *)
			(the o assoc) (typ_assoc, DatatypeAux.DtTFree a)
		  | typ_of_dtyp descr typ_assoc (DatatypeAux.DtRec i) =
			let
				val (s, ds, _) = (the o assoc) (descr, i)
			in
				Type (s, map (typ_of_dtyp descr typ_assoc) ds)
			end
		  | typ_of_dtyp descr typ_assoc (DatatypeAux.DtType (s, ds)) =
			Type (s, map (typ_of_dtyp descr typ_assoc) ds)
		(* int list -> int *)
		fun sum xs = foldl op+ (0, xs)
		(* int list -> int *)
		fun product xs = foldl op* (1, xs)
		(* the size of an IDT is the sum (over its constructors) of the        *)
		(* product (over their arguments) of the size of the argument type     *)
		(* (Term.typ * int) list -> DatatypeAux.descr -> (DatatypeAux.dtyp * Term.typ) list -> (string * DatatypeAux.dtyp list) list -> int *)
		fun size_of_dtyp typs descr typ_assoc constrs =
			sum (map (fn (_, ds) =>
				product (map (fn d =>
					let
						val T         = typ_of_dtyp descr typ_assoc d
						val (i, _, _) =
							(interpret thy (typs, []) {maxvars=0, next_idx=1, bounds=[], wellformed=True} (Free ("dummy", T))
							handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
					in
						size_of_type i
					end) ds)) constrs)
		(* Term.typ -> (interpretation * model * arguments) option *)
		fun interpret_variable (Type (s, Ts)) =
			(case DatatypePackage.datatype_info thy s of
			  Some info =>  (* inductive datatype *)
				let
					val (typs, terms) = model
					(* int option -- only recursive IDTs have an associated depth *)
					val depth         = assoc (typs, Type (s, Ts))
				in
					if depth = (Some 0) then  (* termination condition to avoid infinite recursion *)
						(* return a leaf of size 0 *)
						Some (Leaf [], model, args)
					else
						let
							val index               = #index info
							val descr               = #descr info
							val (_, dtyps, constrs) = (the o assoc) (descr, index)
							val typ_assoc           = dtyps ~~ Ts
							(* sanity check: every element in 'dtyps' must be a 'DtTFree' *)
							val _ = (if Library.exists (fn d =>
									case d of DatatypeAux.DtTFree _ => false | _ => true) dtyps
								then
									raise REFUTE ("IDT_interpreter", "datatype argument (for type " ^ Sign.string_of_typ (sign_of thy) (Type (s, Ts)) ^ ") is not a variable")
								else
									())
							(* if the model specifies a depth for the current type, decrement it to avoid infinite recursion *)
							val typs'    = (case depth of None => typs | Some n => overwrite (typs, (Type (s, Ts), n-1)))
							(* recursively compute the size of the datatype *)
							val size     = size_of_dtyp typs' descr typ_assoc constrs
							val next_idx = #next_idx args
							val next     = (if size=2 then next_idx+1 else next_idx+size)  (* optimization for types with size 2 *)
							val _        = (if next-1>(#maxvars args) andalso (#maxvars args)>0 then raise MAXVARS_EXCEEDED else ())  (* check if 'maxvars' is large enough *)
							(* prop_formula list *)
							val fms      = (if size=2 then [BoolVar next_idx, Not (BoolVar next_idx)]
								else (map BoolVar (next_idx upto (next_idx+size-1))))
							(* interpretation *)
							val intr     = Leaf fms
							(* prop_formula list -> prop_formula *)
							fun one_of_two_false []      = True
							  | one_of_two_false (x::xs) = SAnd (PropLogic.all (map (fn x' => SOr (SNot x, SNot x')) xs), one_of_two_false xs)
							(* prop_formula list -> prop_formula *)
							fun exactly_one_true xs = SAnd (PropLogic.exists xs, one_of_two_false xs)
							(* prop_formula *)
							val wf       = (if size=2 then True else exactly_one_true fms)
						in
							(* extend the model, increase 'next_idx', add well-formedness condition *)
							Some (intr, (typs, (t, intr)::terms), {maxvars = #maxvars args, next_idx = next, bounds = #bounds args, wellformed = SAnd (#wellformed args, wf)})
						end
				end
			| None =>  (* not an inductive datatype *)
				None)
		  | interpret_variable _ =  (* a (free or schematic) type variable *)
			None
	in
		case assoc (terms, t) of
		  Some intr =>
			(* return an existing interpretation *)
			Some (intr, model, args)
		| None =>
			(case t of
			  Free (_, T)  => interpret_variable T
			| Var (_, T)   => interpret_variable T
			| Const (s, T) =>
				(* TODO: case, recursion, size *)
				let
					(* unit -> (interpretation * model * arguments) option *)
					fun interpret_constructor () =
						(case body_type T of
						  Type (s', Ts') =>
							(case DatatypePackage.datatype_info thy s' of
							  Some info =>  (* body type is an inductive datatype *)
								let
									val index               = #index info
									val descr               = #descr info
									val (_, dtyps, constrs) = (the o assoc) (descr, index)
									val typ_assoc           = dtyps ~~ Ts'
									(* sanity check: every element in 'dtyps' must be a 'DtTFree' *)
									val _ = (if Library.exists (fn d =>
											case d of DatatypeAux.DtTFree _ => false | _ => true) dtyps
										then
											raise REFUTE ("IDT_interpreter", "datatype argument (for type " ^ Sign.string_of_typ (sign_of thy) (Type (s', Ts')) ^ ") is not a variable")
										else
											())
									(* split the constructors into those occuring before/after 'Const (s, T)' *)
									val (constrs1, constrs2) = take_prefix (fn (cname, ctypes) =>
										not (cname = s andalso Type.typ_instance (Sign.tsig_of (sign_of thy)) (T,
											map (typ_of_dtyp descr typ_assoc) ctypes ---> Type (s', Ts')))) constrs
								in
									case constrs2 of
									  [] =>
										(* 'Const (s, T)' is not a constructor of this datatype *)
										None
									| c::cs =>
										let
											(* int option -- only recursive IDTs have an associated depth *)
											val depth = assoc (typs, Type (s', Ts'))
											val typs' = (case depth of None => typs | Some n => overwrite (typs, (Type (s', Ts'), n-1)))
											(* constructors before 'Const (s, T)' generate elements of the datatype *)
											val offset  = size_of_dtyp typs' descr typ_assoc constrs1
											(* 'Const (s, T)' and constructors after it generate elements of the datatype *)
											val total   = offset + (size_of_dtyp typs' descr typ_assoc constrs2)
											(* create an interpretation that corresponds to the constructor 'Const (s, T)' *)
											(* by recursion over its argument types                                        *)
											(* DatatypeAux.dtyp list -> interpretation *)
											fun make_partial [] =
												(* all entries of the leaf are 'False' *)
												Leaf (replicate total False)
											  | make_partial (d::ds) =
												let
													(* compute the "new" size of the type 'd' *)
													val T         = typ_of_dtyp descr typ_assoc d
													val (i, _, _) =
														(interpret thy (typs, []) {maxvars=0, next_idx=1, bounds=[], wellformed=True} (Free ("dummy", T))
														handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
												in
													(* all entries of the whole subtree are 'False' *)
													Node (replicate (size_of_type i) (make_partial ds))
												end
											(* int * DatatypeAux.dtyp list -> int * interpretation *)
											fun make_constr (offset, []) =
												if offset<total then
													(offset+1, Leaf ((replicate offset False) @ True :: (replicate (total-offset-1) False)))
												else
													raise REFUTE ("IDT_interpreter", "internal error: offset >= total")
											  | make_constr (offset, d::ds) =
												let
													(* compute the "new" and "old" size of the type 'd' *)
													val T         = typ_of_dtyp descr typ_assoc d
													val (i, _, _) =
														(interpret thy (typs, []) {maxvars=0, next_idx=1, bounds=[], wellformed=True} (Free ("dummy", T))
														handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
													val (i', _, _) =
														(interpret thy (typs', []) {maxvars=0, next_idx=1, bounds=[], wellformed=True} (Free ("dummy", T))
														handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
													val size  = size_of_type i
													val size' = size_of_type i'
													val _ = if size<size' then
															raise REFUTE ("IDT_interpreter", "internal error: new size < old size")
														else
															()
													val (new_offset, intrs) = foldl_map make_constr (offset, replicate size' ds)
												in
													(* the first size' elements of the type actually yield a result *)
													(* element, while the remaining size-size' elements don't       *)
													(new_offset, Node (intrs @ (replicate (size-size') (make_partial ds))))
												end
										in
											Some ((snd o make_constr) (offset, snd c), model, args)
										end
								end
							| None =>  (* body type is not an inductive datatype *)
								None)
						| _ =>  (* body type is a (free or schematic) type variable *)
							None)
				in
					case interpret_constructor () of
					  Some x => Some x
					| None   => interpret_variable T
				end
			| _ => None)
	end;

	(* theory -> model -> arguments -> Term.term -> (interpretation * model * arguments) option *)

	(* only an optimization: 'card' could in principle be interpreted with    *)
	(* interpreters available already (using its definition), but the code    *)
	(* below is much more efficient                                           *)

	fun Finite_Set_card_interpreter thy model args t =
		case t of
		  Const ("Finite_Set.card", Type ("fun", [Type ("set", [T]), Type ("nat", [])])) =>
			let
				val (i_nat, _, _) =
					(interpret thy model {maxvars=0, next_idx=1, bounds=[], wellformed=True} (Free ("dummy", Type ("nat", [])))
						handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
				val size_nat      = size_of_type i_nat
				val (i_set, _, _) =
					(interpret thy model {maxvars=0, next_idx=1, bounds=[], wellformed=True} (Free ("dummy", Type ("set", [T])))
						handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
				val constants     = make_constants i_set
				(* interpretation -> int *)
				fun number_of_elements (Node xs) =
					foldl (fn (n, x) =>
						if x=TT then n+1 else if x=FF then n else raise REFUTE ("Finite_Set_card_interpreter", "interpretation for set type does not yield a Boolean")) (0, xs)
				  | number_of_elements (Leaf _) =
					raise REFUTE ("Finite_Set_card_interpreter", "interpretation for set type is a leaf")
				(* takes an interpretation for a set and returns an interpretation for a 'nat' *)
				(* interpretation -> interpretation *)
				fun card i =
					let
						val n = number_of_elements i
					in
						if n<size_nat then
							Leaf ((replicate n False) @ True :: (replicate (size_nat-n-1) False))
						else
							Leaf (replicate size_nat False)
					end
			in
				Some (Node (map card constants), model, args)
			end
		| _ =>
			None;


(* ------------------------------------------------------------------------- *)
(* PRINTERS                                                                  *)
(* ------------------------------------------------------------------------- *)

	(* theory -> model -> Term.term -> interpretation -> (int -> bool) -> Term.term option *)

	fun stlc_printer thy model t intr assignment =
	let
		(* Term.term -> Term.typ option *)
		fun typeof (Free (_, T))  = Some T
		  | typeof (Var (_, T))   = Some T
		  | typeof (Const (_, T)) = Some T
		  | typeof _              = None
		(* string -> string *)
		fun strip_leading_quote s =
			(implode o (fn ss => case ss of [] => [] | x::xs => if x="'" then xs else ss) o explode) s
		(* Term.typ -> string *)
		fun string_of_typ (Type (s, _))     = s
		  | string_of_typ (TFree (x, _))    = strip_leading_quote x
		  | string_of_typ (TVar ((x,i), _)) = strip_leading_quote x ^ string_of_int i
		(* interpretation -> int *)
		fun index_from_interpretation (Leaf xs) =
			let
				val idx = find_index (PropLogic.eval assignment) xs
			in
				if idx<0 then
					raise REFUTE ("stlc_printer", "illegal interpretation: no value assigned (SAT solver unsound?)")
				else
					idx
			end
		  | index_from_interpretation _ =
			raise REFUTE ("stlc_printer", "interpretation for ground type is not a leaf")
	in
		case typeof t of
		  Some T =>
			(case T of
			  Type ("fun", [T1, T2]) =>
				(let
					(* create all constants of type 'T1' *)
					val (i, _, _) = interpret thy model {maxvars=0, next_idx=1, bounds=[], wellformed=True} (Free ("dummy", T1))
					val constants = make_constants i
					(* interpretation list *)
					val results = (case intr of
						  Node xs => xs
						| _       => raise REFUTE ("stlc_printer", "interpretation for function type is a leaf"))
					(* Term.term list *)
					val pairs = map (fn (arg, result) =>
						HOLogic.mk_prod
							(print thy model (Free ("dummy", T1)) arg assignment,
							 print thy model (Free ("dummy", T2)) result assignment))
						(constants ~~ results)
					(* Term.typ *)
					val HOLogic_prodT = HOLogic.mk_prodT (T1, T2)
					val HOLogic_setT  = HOLogic.mk_setT HOLogic_prodT
					(* Term.term *)
					val HOLogic_empty_set = Const ("{}", HOLogic_setT)
					val HOLogic_insert    = Const ("insert", HOLogic_prodT --> HOLogic_setT --> HOLogic_setT)
				in
					Some (foldr (fn (pair, acc) => HOLogic_insert $ pair $ acc) (pairs, HOLogic_empty_set))
				end handle CANNOT_INTERPRET _ => None)
			| Type ("prop", [])      =>
				(case index_from_interpretation intr of
				  0 => Some (HOLogic.mk_Trueprop HOLogic.true_const)
				| 1 => Some (HOLogic.mk_Trueprop HOLogic.false_const)
				| _ => raise REFUTE ("stlc_interpreter", "illegal interpretation for a propositional value"))
			| Type _  => Some (Const (string_of_typ T ^ string_of_int (index_from_interpretation intr), T))
			| TFree _ => Some (Const (string_of_typ T ^ string_of_int (index_from_interpretation intr), T))
			| TVar _  => Some (Const (string_of_typ T ^ string_of_int (index_from_interpretation intr), T)))
		| None =>
			None
	end;

	(* theory -> model -> Term.term -> interpretation -> (int -> bool) -> string option *)

	fun set_printer thy model t intr assignment =
	let
		(* Term.term -> Term.typ option *)
		fun typeof (Free (_, T))  = Some T
		  | typeof (Var (_, T))   = Some T
		  | typeof (Const (_, T)) = Some T
		  | typeof _              = None
	in
		case typeof t of
		  Some (Type ("set", [T])) =>
			(let
				(* create all constants of type 'T' *)
				val (i, _, _) = interpret thy model {maxvars=0, next_idx=1, bounds=[], wellformed=True} (Free ("dummy", T))
				val constants = make_constants i
				(* interpretation list *)
				val results = (case intr of
					  Node xs => xs
					| _       => raise REFUTE ("set_printer", "interpretation for set type is a leaf"))
				(* Term.term list *)
				val elements = mapfilter (fn (arg, result) =>
					case result of
					  Leaf [fmTrue, fmFalse] =>
						if PropLogic.eval assignment fmTrue then
							Some (print thy model (Free ("dummy", T)) arg assignment)
						else if PropLogic.eval assignment fmFalse then
							None
						else
							raise REFUTE ("set_printer", "illegal interpretation: no value assigned (SAT solver unsound?)")
					| _ =>
						raise REFUTE ("set_printer", "illegal interpretation for a Boolean value"))
					(constants ~~ results)
				(* Term.typ *)
				val HOLogic_setT  = HOLogic.mk_setT T
				(* Term.term *)
				val HOLogic_empty_set = Const ("{}", HOLogic_setT)
				val HOLogic_insert    = Const ("insert", T --> HOLogic_setT --> HOLogic_setT)
			in
				Some (foldl (fn (acc, elem) => HOLogic_insert $ elem $ acc) (HOLogic_empty_set, elements))
			end handle CANNOT_INTERPRET _ => None)
		| _ =>
			None
	end;

	(* theory -> model -> Term.term -> interpretation -> (int -> bool) -> Term.term option *)

	fun IDT_printer thy model t intr assignment =
	let
		(* Term.term -> Term.typ option *)
		fun typeof (Free (_, T))  = Some T
		  | typeof (Var (_, T))   = Some T
		  | typeof (Const (_, T)) = Some T
		  | typeof _              = None
	in
		case typeof t of
		  Some (Type (s, Ts)) =>
			(case DatatypePackage.datatype_info thy s of
			  Some info =>  (* inductive datatype *)
				let
					val (typs, _)           = model
					val index               = #index info
					val descr               = #descr info
					val (_, dtyps, constrs) = (the o assoc) (descr, index)
					val typ_assoc           = dtyps ~~ Ts
					(* sanity check: every element in 'dtyps' must be a 'DtTFree' *)
					val _ = (if Library.exists (fn d =>
							case d of DatatypeAux.DtTFree _ => false | _ => true) dtyps
						then
							raise REFUTE ("IDT_printer", "datatype argument (for type " ^ Sign.string_of_typ (sign_of thy) (Type (s, Ts)) ^ ") is not a variable")
						else
							())
					(* the index of the element in the datatype *)
					val element = (case intr of
						  Leaf xs => find_index (PropLogic.eval assignment) xs
						| Node _  => raise REFUTE ("IDT_printer", "interpretation is not a leaf"))
					val _ = (if element<0 then raise REFUTE ("IDT_printer", "invalid interpretation (no value assigned)") else ())
					(* int option -- only recursive IDTs have an associated depth *)
					val depth = assoc (typs, Type (s, Ts))
					val typs' = (case depth of None => typs | Some n => overwrite (typs, (Type (s, Ts), n-1)))
					(* DatatypeAux.descr -> (DatatypeAux.dtyp * Term.typ) list -> DatatypeAux.dtyp -> Term.typ *)
					fun typ_of_dtyp descr typ_assoc (DatatypeAux.DtTFree a) =
						(* replace a 'DtTFree' variable by the associated type *)
						(the o assoc) (typ_assoc, DatatypeAux.DtTFree a)
					  | typ_of_dtyp descr typ_assoc (DatatypeAux.DtRec i) =
						let
							val (s, ds, _) = (the o assoc) (descr, i)
						in
							Type (s, map (typ_of_dtyp descr typ_assoc) ds)
						end
					  | typ_of_dtyp descr typ_assoc (DatatypeAux.DtType (s, ds)) =
						Type (s, map (typ_of_dtyp descr typ_assoc) ds)
					(* int list -> int *)
					fun sum xs = foldl op+ (0, xs)
					(* int list -> int *)
					fun product xs = foldl op* (1, xs)
					(* the size of an IDT is the sum (over its constructors) of the        *)
					(* product (over their arguments) of the size of the argument type     *)
					(* (Term.typ * int) list -> DatatypeAux.descr -> (DatatypeAux.dtyp * Term.typ) list -> (string * DatatypeAux.dtyp list) list -> int *)
					fun size_of_dtyp typs descr typ_assoc xs =
						sum (map (fn (_, ds) =>
							product (map (fn d =>
								let
									val T         = typ_of_dtyp descr typ_assoc d
									val (i, _, _) =
										(interpret thy (typs, []) {maxvars=0, next_idx=1, bounds=[], wellformed=True} (Free ("dummy", T))
										handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
					in
						size_of_type i
					end) ds)) xs)
					(* int -> DatatypeAux.dtyp list -> Term.term list *)
					fun make_args n [] =
						if n<>0 then
							raise REFUTE ("IDT_printer", "error computing the element: remainder is not 0")
						else
							[]
					  | make_args n (d::ds) =
						let
							val dT        = typ_of_dtyp descr typ_assoc d
							val (i, _, _) =
								(interpret thy (typs', []) {maxvars=0, next_idx=1, bounds=[], wellformed=True} (Free ("dummy", dT))
								handle CANNOT_INTERPRET _ => raise CANNOT_INTERPRET t)
							val size      = size_of_type i
							val consts    = make_constants i  (* we only need the (n mod size)-th element of *)
								(* this list, so there might be a more efficient implementation that does not *)
								(* generate all constants                                                     *)
						in
							(print thy (typs', []) (Free ("dummy", dT)) (nth_elem (n mod size, consts)) assignment)::(make_args (n div size) ds)
						end
					(* int -> (string * DatatypeAux.dtyp list) list -> Term.term *)
					fun make_term _ [] =
						raise REFUTE ("IDT_printer", "invalid interpretation (value too large - not enough constructors)")
					  | make_term n (c::cs) =
						let
							val c_size = size_of_dtyp typs' descr typ_assoc [c]
						in
							if n<c_size then
								let
									val (cname, cargs) = c
									val c_term = Const (cname, (map (typ_of_dtyp descr typ_assoc) cargs) ---> Type (s, Ts))
								in
									foldl op$ (c_term, rev (make_args n (rev cargs)))
								end
							else
								make_term (n-c_size) cs
						end
				in
					Some (make_term element constrs)
				end
			| None =>  (* not an inductive datatype *)
				None)
		| _ =>  (* a (free or schematic) type variable *)
			None
	end;


(* ------------------------------------------------------------------------- *)
(* use 'setup Refute.setup' in an Isabelle theory to initialize the 'Refute' *)
(* structure                                                                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Note: the interpreters and printers are used in reverse order; however,   *)
(*       an interpreter that can handle non-atomic terms ends up being       *)
(*       applied before the 'stlc_interpreter' breaks the term apart into    *)
(*       subterms that are then passed to other interpreters!                *)
(* ------------------------------------------------------------------------- *)

	(* (theory -> theory) list *)

	val setup =
		[RefuteData.init,
		 add_interpreter "stlc"            stlc_interpreter,
		 add_interpreter "Pure"            Pure_interpreter,
		 add_interpreter "HOLogic"         HOLogic_interpreter,
		 add_interpreter "set"             set_interpreter,
		 add_interpreter "IDT"             IDT_interpreter,
		 add_interpreter "Finite_Set.card" Finite_Set_card_interpreter,
		 add_printer "stlc" stlc_printer,
		 add_printer "set"  set_printer,
		 add_printer "IDT"  IDT_printer];

end
