(*  Title:      HOL/Tools/refute.ML
    Author:     Tjark Weber, TU Muenchen

Finite model generation for HOL formulas, using a SAT solver.
*)

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

  exception MAXVARS_EXCEEDED

  val add_interpreter : string -> (Proof.context -> model -> arguments -> term ->
    (interpretation * model * arguments) option) -> theory -> theory
  val add_printer : string -> (Proof.context -> model -> typ ->
    interpretation -> (int -> bool) -> term option) -> theory -> theory

  val interpret : Proof.context -> model -> arguments -> term ->
    (interpretation * model * arguments)

  val print : Proof.context -> model -> typ -> interpretation -> (int -> bool) -> term
  val print_model : Proof.context -> model -> (int -> bool) -> string

(* ------------------------------------------------------------------------- *)
(* Interface                                                                 *)
(* ------------------------------------------------------------------------- *)

  val set_default_param  : (string * string) -> theory -> theory
  val get_default_param  : Proof.context -> string -> string option
  val get_default_params : Proof.context -> (string * string) list
  val actual_params      : Proof.context -> (string * string) list -> params

  val find_model :
    Proof.context -> params -> term list -> term -> bool -> string

  (* tries to find a model for a formula: *)
  val satisfy_term :
    Proof.context -> (string * string) list -> term list -> term -> string
  (* tries to find a model that refutes a formula: *)
  val refute_term :
    Proof.context -> (string * string) list -> term list -> term -> string
  val refute_goal :
    Proof.context -> (string * string) list -> thm -> int -> string

  val setup : theory -> theory

(* ------------------------------------------------------------------------- *)
(* Additional functions used by Nitpick (to be factored out)                 *)
(* ------------------------------------------------------------------------- *)

  val get_classdef : theory -> string -> (string * term) option
  val norm_rhs : term -> term
  val get_def : theory -> string * typ -> (string * term) option
  val get_typedef : theory -> typ -> (string * term) option
  val is_IDT_constructor : theory -> string * typ -> bool
  val is_IDT_recursor : theory -> string * typ -> bool
  val is_const_of_class: theory -> string * typ -> bool
  val string_of_typ : typ -> string
end;

structure Refute : REFUTE =
struct

open Prop_Logic;

(* We use 'REFUTE' only for internal error conditions that should    *)
(* never occur in the first place (i.e. errors caused by bugs in our *)
(* code).  Otherwise (e.g. to indicate invalid input data) we use    *)
(* 'error'.                                                          *)
exception REFUTE of string * string;  (* ("in function", "cause") *)

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
      | itl (e, Node xs) = Library.foldl (tree_foldl f) (e,xs)
  in
    itl
  end;

(* 'a tree * 'b tree -> ('a * 'b) tree *)

fun tree_pair (t1, t2) =
  case t1 of
    Leaf x =>
      (case t2 of
          Leaf y => Leaf (x,y)
        | Node _ => raise REFUTE ("tree_pair",
            "trees are of different height (second tree is higher)"))
  | Node xs =>
      (case t2 of
          (* '~~' will raise an exception if the number of branches in   *)
          (* both trees is different at the current node                 *)
          Node ys => Node (map tree_pair (xs ~~ ys))
        | Leaf _  => raise REFUTE ("tree_pair",
            "trees are of different height (first tree is higher)"));

(* ------------------------------------------------------------------------- *)
(* params: parameters that control the translation into a propositional      *)
(*         formula/model generation                                          *)
(*                                                                           *)
(* The following parameters are supported (and required (!), except for      *)
(* "sizes" and "expect"):                                                    *)
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
(* "no_assms"    bool    If "true", assumptions in structured proofs are     *)
(*                       not considered.                                     *)
(* "expect"      string  Expected result ("genuine", "potential", "none", or *)
(*                       "unknown").                                         *)
(* ------------------------------------------------------------------------- *)

type params =
  {
    sizes    : (string * int) list,
    minsize  : int,
    maxsize  : int,
    maxvars  : int,
    maxtime  : int,
    satsolver: string,
    no_assms : bool,
    expect   : string
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
  (typ * int) list * (term * interpretation) list;

(* ------------------------------------------------------------------------- *)
(* arguments: additional arguments required during interpretation of terms   *)
(* ------------------------------------------------------------------------- *)

type arguments =
  {
    (* just passed unchanged from 'params': *)
    maxvars   : int,
    (* whether to use 'make_equality' or 'make_def_equality': *)
    def_eq    : bool,
    (* the following may change during the translation: *)
    next_idx  : int,
    bounds    : interpretation list,
    wellformed: prop_formula
  };


structure Data = Theory_Data
(
  type T =
    {interpreters: (string * (Proof.context -> model -> arguments -> term ->
      (interpretation * model * arguments) option)) list,
     printers: (string * (Proof.context -> model -> typ -> interpretation ->
      (int -> bool) -> term option)) list,
     parameters: string Symtab.table};
  val empty = {interpreters = [], printers = [], parameters = Symtab.empty};
  val extend = I;
  fun merge
    ({interpreters = in1, printers = pr1, parameters = pa1},
     {interpreters = in2, printers = pr2, parameters = pa2}) : T =
    {interpreters = AList.merge (op =) (K true) (in1, in2),
     printers = AList.merge (op =) (K true) (pr1, pr2),
     parameters = Symtab.merge (op =) (pa1, pa2)};
);

val get_data = Data.get o Proof_Context.theory_of;


(* ------------------------------------------------------------------------- *)
(* interpret: interprets the term 't' using a suitable interpreter; returns  *)
(*            the interpretation and a (possibly extended) model that keeps  *)
(*            track of the interpretation of subterms                        *)
(* ------------------------------------------------------------------------- *)

fun interpret ctxt model args t =
  case get_first (fn (_, f) => f ctxt model args t)
      (#interpreters (get_data ctxt)) of
    NONE => raise REFUTE ("interpret",
      "no interpreter for term " ^ quote (Syntax.string_of_term ctxt t))
  | SOME x => x;

(* ------------------------------------------------------------------------- *)
(* print: converts the interpretation 'intr', which must denote a term of    *)
(*        type 'T', into a term using a suitable printer                     *)
(* ------------------------------------------------------------------------- *)

fun print ctxt model T intr assignment =
  case get_first (fn (_, f) => f ctxt model T intr assignment)
      (#printers (get_data ctxt)) of
    NONE => raise REFUTE ("print",
      "no printer for type " ^ quote (Syntax.string_of_typ ctxt T))
  | SOME x => x;

(* ------------------------------------------------------------------------- *)
(* print_model: turns the model into a string, using a fixed interpretation  *)
(*              (given by an assignment for Boolean variables) and suitable  *)
(*              printers                                                     *)
(* ------------------------------------------------------------------------- *)

fun print_model ctxt model assignment =
  let
    val (typs, terms) = model
    val typs_msg =
      if null typs then
        "empty universe (no type variables in term)\n"
      else
        "Size of types: " ^ commas (map (fn (T, i) =>
          Syntax.string_of_typ ctxt T ^ ": " ^ string_of_int i) typs) ^ "\n"
    val show_consts_msg =
      if not (Config.get ctxt show_consts) andalso Library.exists (is_Const o fst) terms then
        "enable \"show_consts\" to show the interpretation of constants\n"
      else
        ""
    val terms_msg =
      if null terms then
        "empty interpretation (no free variables in term)\n"
      else
        cat_lines (map_filter (fn (t, intr) =>
          (* print constants only if 'show_consts' is true *)
          if Config.get ctxt show_consts orelse not (is_Const t) then
            SOME (Syntax.string_of_term ctxt t ^ ": " ^
              Syntax.string_of_term ctxt
                (print ctxt model (Term.type_of t) intr assignment))
          else
            NONE) terms) ^ "\n"
  in
    typs_msg ^ show_consts_msg ^ terms_msg
  end;


(* ------------------------------------------------------------------------- *)
(* PARAMETER MANAGEMENT                                                      *)
(* ------------------------------------------------------------------------- *)

fun add_interpreter name f = Data.map (fn {interpreters, printers, parameters} =>
  case AList.lookup (op =) interpreters name of
    NONE => {interpreters = (name, f) :: interpreters,
      printers = printers, parameters = parameters}
  | SOME _ => error ("Interpreter " ^ name ^ " already declared"));

fun add_printer name f = Data.map (fn {interpreters, printers, parameters} =>
  case AList.lookup (op =) printers name of
    NONE => {interpreters = interpreters,
      printers = (name, f) :: printers, parameters = parameters}
  | SOME _ => error ("Printer " ^ name ^ " already declared"));

(* ------------------------------------------------------------------------- *)
(* set_default_param: stores the '(name, value)' pair in Data's              *)
(*                    parameter table                                        *)
(* ------------------------------------------------------------------------- *)

fun set_default_param (name, value) = Data.map
  (fn {interpreters, printers, parameters} =>
    {interpreters = interpreters, printers = printers,
      parameters = Symtab.update (name, value) parameters});

(* ------------------------------------------------------------------------- *)
(* get_default_param: retrieves the value associated with 'name' from        *)
(*                    Data's parameter table                                 *)
(* ------------------------------------------------------------------------- *)

val get_default_param = Symtab.lookup o #parameters o get_data;

(* ------------------------------------------------------------------------- *)
(* get_default_params: returns a list of all '(name, value)' pairs that are  *)
(*                     stored in Data's parameter table                      *)
(* ------------------------------------------------------------------------- *)

val get_default_params = Symtab.dest o #parameters o get_data;

(* ------------------------------------------------------------------------- *)
(* actual_params: takes a (possibly empty) list 'params' of parameters that  *)
(*      override the default parameters currently specified, and             *)
(*      returns a record that can be passed to 'find_model'.                 *)
(* ------------------------------------------------------------------------- *)

fun actual_params ctxt override =
  let
    (* (string * string) list * string -> bool *)
    fun read_bool (parms, name) =
      case AList.lookup (op =) parms name of
        SOME "true" => true
      | SOME "false" => false
      | SOME s => error ("parameter " ^ quote name ^
          " (value is " ^ quote s ^ ") must be \"true\" or \"false\"")
      | NONE   => error ("parameter " ^ quote name ^
          " must be assigned a value")
    (* (string * string) list * string -> int *)
    fun read_int (parms, name) =
      case AList.lookup (op =) parms name of
        SOME s =>
          (case Int.fromString s of
            SOME i => i
          | NONE   => error ("parameter " ^ quote name ^
            " (value is " ^ quote s ^ ") must be an integer value"))
      | NONE => error ("parameter " ^ quote name ^
          " must be assigned a value")
    (* (string * string) list * string -> string *)
    fun read_string (parms, name) =
      case AList.lookup (op =) parms name of
        SOME s => s
      | NONE => error ("parameter " ^ quote name ^
        " must be assigned a value")
    (* 'override' first, defaults last: *)
    (* (string * string) list *)
    val allparams = override @ get_default_params ctxt
    (* int *)
    val minsize = read_int (allparams, "minsize")
    val maxsize = read_int (allparams, "maxsize")
    val maxvars = read_int (allparams, "maxvars")
    val maxtime = read_int (allparams, "maxtime")
    (* string *)
    val satsolver = read_string (allparams, "satsolver")
    val no_assms = read_bool (allparams, "no_assms")
    val expect = the_default "" (AList.lookup (op =) allparams "expect")
    (* all remaining parameters of the form "string=int" are collected in *)
    (* 'sizes'                                                            *)
    (* TODO: it is currently not possible to specify a size for a type    *)
    (*       whose name is one of the other parameters (e.g. 'maxvars')   *)
    (* (string * int) list *)
    val sizes = map_filter
      (fn (name, value) => Option.map (pair name) (Int.fromString value))
      (filter (fn (name, _) => name<>"minsize" andalso name<>"maxsize"
        andalso name<>"maxvars" andalso name<>"maxtime"
        andalso name<>"satsolver" andalso name<>"no_assms") allparams)
  in
    {sizes=sizes, minsize=minsize, maxsize=maxsize, maxvars=maxvars,
      maxtime=maxtime, satsolver=satsolver, no_assms=no_assms, expect=expect}
  end;


(* ------------------------------------------------------------------------- *)
(* TRANSLATION HOL -> PROPOSITIONAL LOGIC, BOOLEAN ASSIGNMENT -> MODEL       *)
(* ------------------------------------------------------------------------- *)

val typ_of_dtyp = ATP_Util.typ_of_dtyp

(* ------------------------------------------------------------------------- *)
(* close_form: universal closure over schematic variables in 't'             *)
(* ------------------------------------------------------------------------- *)

(* Term.term -> Term.term *)

fun close_form t =
  let
    (* (Term.indexname * Term.typ) list *)
    val vars = sort_wrt (fst o fst) (map dest_Var (Misc_Legacy.term_vars t))
  in
    fold (fn ((x, i), T) => fn t' =>
      Term.all T $ Abs (x, T, abstract_over (Var ((x, i), T), t'))) vars t
  end;

val monomorphic_term = ATP_Util.monomorphic_term
val specialize_type = ATP_Util.specialize_type

(* ------------------------------------------------------------------------- *)
(* is_const_of_class: returns 'true' iff 'Const (s, T)' is a constant that   *)
(*                    denotes membership to an axiomatic type class          *)
(* ------------------------------------------------------------------------- *)

fun is_const_of_class thy (s, T) =
  let
    val class_const_names = map Logic.const_of_class (Sign.all_classes thy)
  in
    (* I'm not quite sure if checking the name 's' is sufficient, *)
    (* or if we should also check the type 'T'.                   *)
    member (op =) class_const_names s
  end;

(* ------------------------------------------------------------------------- *)
(* is_IDT_constructor: returns 'true' iff 'Const (s, T)' is the constructor  *)
(*                     of an inductive datatype in 'thy'                     *)
(* ------------------------------------------------------------------------- *)

fun is_IDT_constructor thy (s, T) =
  (case body_type T of
    Type (s', _) =>
      (case Datatype.get_constrs thy s' of
        SOME constrs =>
          List.exists (fn (cname, cty) =>
            cname = s andalso Sign.typ_instance thy (T, cty)) constrs
      | NONE => false)
  | _  => false);

(* ------------------------------------------------------------------------- *)
(* is_IDT_recursor: returns 'true' iff 'Const (s, T)' is the recursion       *)
(*                  operator of an inductive datatype in 'thy'               *)
(* ------------------------------------------------------------------------- *)

fun is_IDT_recursor thy (s, T) =
  let
    val rec_names = Symtab.fold (append o #rec_names o snd)
      (Datatype.get_all thy) []
  in
    (* I'm not quite sure if checking the name 's' is sufficient, *)
    (* or if we should also check the type 'T'.                   *)
    member (op =) rec_names s
  end;

(* ------------------------------------------------------------------------- *)
(* norm_rhs: maps  f ?t1 ... ?tn == rhs  to  %t1...tn. rhs                   *)
(* ------------------------------------------------------------------------- *)

fun norm_rhs eqn =
  let
    fun lambda (v as Var ((x, _), T)) t = Abs (x, T, abstract_over (v, t))
      | lambda v t = raise TERM ("lambda", [v, t])
    val (lhs, rhs) = Logic.dest_equals eqn
    val (_, args) = Term.strip_comb lhs
  in
    fold lambda (rev args) rhs
  end

(* ------------------------------------------------------------------------- *)
(* get_def: looks up the definition of a constant                            *)
(* ------------------------------------------------------------------------- *)

fun get_def thy (s, T) =
  let
    (* (string * Term.term) list -> (string * Term.term) option *)
    fun get_def_ax [] = NONE
      | get_def_ax ((axname, ax) :: axioms) =
          (let
            val (lhs, _) = Logic.dest_equals ax  (* equations only *)
            val c        = Term.head_of lhs
            val (s', T') = Term.dest_Const c
          in
            if s=s' then
              let
                val typeSubs = Sign.typ_match thy (T', T) Vartab.empty
                val ax'      = monomorphic_term typeSubs ax
                val rhs      = norm_rhs ax'
              in
                SOME (axname, rhs)
              end
            else
              get_def_ax axioms
          end handle ERROR _         => get_def_ax axioms
                   | TERM _          => get_def_ax axioms
                   | Type.TYPE_MATCH => get_def_ax axioms)
  in
    get_def_ax (Theory.all_axioms_of thy)
  end;

(* ------------------------------------------------------------------------- *)
(* get_typedef: looks up the definition of a type, as created by "typedef"   *)
(* ------------------------------------------------------------------------- *)

fun get_typedef thy T =
  let
    (* (string * Term.term) list -> (string * Term.term) option *)
    fun get_typedef_ax [] = NONE
      | get_typedef_ax ((axname, ax) :: axioms) =
          (let
            (* Term.term -> Term.typ option *)
            fun type_of_type_definition (Const (s', T')) =
                  if s'= @{const_name type_definition} then
                    SOME T'
                  else
                    NONE
              | type_of_type_definition (Free _) = NONE
              | type_of_type_definition (Var _) = NONE
              | type_of_type_definition (Bound _) = NONE
              | type_of_type_definition (Abs (_, _, body)) =
                  type_of_type_definition body
              | type_of_type_definition (t1 $ t2) =
                  (case type_of_type_definition t1 of
                    SOME x => SOME x
                  | NONE => type_of_type_definition t2)
          in
            case type_of_type_definition ax of
              SOME T' =>
                let
                  val T'' = domain_type (domain_type T')
                  val typeSubs = Sign.typ_match thy (T'', T) Vartab.empty
                in
                  SOME (axname, monomorphic_term typeSubs ax)
                end
            | NONE => get_typedef_ax axioms
          end handle ERROR _         => get_typedef_ax axioms
                   | TERM _          => get_typedef_ax axioms
                   | Type.TYPE_MATCH => get_typedef_ax axioms)
  in
    get_typedef_ax (Theory.all_axioms_of thy)
  end;

(* ------------------------------------------------------------------------- *)
(* get_classdef: looks up the defining axiom for an axiomatic type class, as *)
(*               created by the "axclass" command                            *)
(* ------------------------------------------------------------------------- *)

fun get_classdef thy class =
  let
    val axname = class ^ "_class_def"
  in
    Option.map (pair axname)
      (AList.lookup (op =) (Theory.all_axioms_of thy) axname)
  end;

(* ------------------------------------------------------------------------- *)
(* unfold_defs: unfolds all defined constants in a term 't', beta-eta        *)
(*              normalizes the result term; certain constants are not        *)
(*              unfolded (cf. 'collect_axioms' and the various interpreters  *)
(*              below): if the interpretation respects a definition anyway,  *)
(*              that definition does not need to be unfolded                 *)
(* ------------------------------------------------------------------------- *)

(* Note: we could intertwine unfolding of constants and beta-(eta-)       *)
(*       normalization; this would save some unfolding for terms where    *)
(*       constants are eliminated by beta-reduction (e.g. 'K c1 c2').  On *)
(*       the other hand, this would cause additional work for terms where *)
(*       constants are duplicated by beta-reduction (e.g. 'S c1 c2 c3').  *)

fun unfold_defs thy t =
  let
    (* Term.term -> Term.term *)
    fun unfold_loop t =
      case t of
      (* Pure *)
        Const (@{const_name all}, _) => t
      | Const (@{const_name "=="}, _) => t
      | Const (@{const_name "==>"}, _) => t
      | Const (@{const_name TYPE}, _) => t  (* axiomatic type classes *)
      (* HOL *)
      | Const (@{const_name Trueprop}, _) => t
      | Const (@{const_name Not}, _) => t
      | (* redundant, since 'True' is also an IDT constructor *)
        Const (@{const_name True}, _) => t
      | (* redundant, since 'False' is also an IDT constructor *)
        Const (@{const_name False}, _) => t
      | Const (@{const_name undefined}, _) => t
      | Const (@{const_name The}, _) => t
      | Const (@{const_name Hilbert_Choice.Eps}, _) => t
      | Const (@{const_name All}, _) => t
      | Const (@{const_name Ex}, _) => t
      | Const (@{const_name HOL.eq}, _) => t
      | Const (@{const_name HOL.conj}, _) => t
      | Const (@{const_name HOL.disj}, _) => t
      | Const (@{const_name HOL.implies}, _) => t
      (* sets *)
      | Const (@{const_name Collect}, _) => t
      | Const (@{const_name Set.member}, _) => t
      (* other optimizations *)
      | Const (@{const_name Finite_Set.card}, _) => t
      | Const (@{const_name Finite_Set.finite}, _) => t
      | Const (@{const_name Orderings.less}, Type ("fun", [@{typ nat},
          Type ("fun", [@{typ nat}, @{typ bool}])])) => t
      | Const (@{const_name Groups.plus}, Type ("fun", [@{typ nat},
          Type ("fun", [@{typ nat}, @{typ nat}])])) => t
      | Const (@{const_name Groups.minus}, Type ("fun", [@{typ nat},
          Type ("fun", [@{typ nat}, @{typ nat}])])) => t
      | Const (@{const_name Groups.times}, Type ("fun", [@{typ nat},
          Type ("fun", [@{typ nat}, @{typ nat}])])) => t
      | Const (@{const_name List.append}, _) => t
(* UNSOUND
      | Const (@{const_name lfp}, _) => t
      | Const (@{const_name gfp}, _) => t
*)
      | Const (@{const_name fst}, _) => t
      | Const (@{const_name snd}, _) => t
      (* simply-typed lambda calculus *)
      | Const (s, T) =>
          (if is_IDT_constructor thy (s, T)
            orelse is_IDT_recursor thy (s, T) then
            t  (* do not unfold IDT constructors/recursors *)
          (* unfold the constant if there is a defining equation *)
          else
            case get_def thy (s, T) of
              SOME (axname, rhs) =>
              (* Note: if the term to be unfolded (i.e. 'Const (s, T)')  *)
              (* occurs on the right-hand side of the equation, i.e. in  *)
              (* 'rhs', we must not use this equation to unfold, because *)
              (* that would loop.  Here would be the right place to      *)
              (* check this.  However, getting this really right seems   *)
              (* difficult because the user may state arbitrary axioms,  *)
              (* which could interact with overloading to create loops.  *)
              ((*tracing (" unfolding: " ^ axname);*)
               unfold_loop rhs)
            | NONE => t)
      | Free _ => t
      | Var _ => t
      | Bound _ => t
      | Abs (s, T, body) => Abs (s, T, unfold_loop body)
      | t1 $ t2 => (unfold_loop t1) $ (unfold_loop t2)
    val result = Envir.beta_eta_contract (unfold_loop t)
  in
    result
  end;

(* ------------------------------------------------------------------------- *)
(* collect_axioms: collects (monomorphic, universally quantified, unfolded   *)
(*                 versions of) all HOL axioms that are relevant w.r.t 't'   *)
(* ------------------------------------------------------------------------- *)

(* Note: to make the collection of axioms more easily extensible, this    *)
(*       function could be based on user-supplied "axiom collectors",     *)
(*       similar to 'interpret'/interpreters or 'print'/printers          *)

(* Note: currently we use "inverse" functions to the definitional         *)
(*       mechanisms provided by Isabelle/HOL, e.g. for "axclass",         *)
(*       "typedef", "definition".  A more general approach could consider *)
(*       *every* axiom of the theory and collect it if it has a constant/ *)
(*       type/typeclass in common with the term 't'.                      *)

(* Which axioms are "relevant" for a particular term/type goes hand in    *)
(* hand with the interpretation of that term/type by its interpreter (see *)
(* way below): if the interpretation respects an axiom anyway, the axiom  *)
(* does not need to be added as a constraint here.                        *)

(* To avoid collecting the same axiom multiple times, we use an           *)
(* accumulator 'axs' which contains all axioms collected so far.          *)

fun collect_axioms ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt
    val _ = tracing "Adding axioms..."
    val axioms = Theory.all_axioms_of thy
    fun collect_this_axiom (axname, ax) axs =
      let
        val ax' = unfold_defs thy ax
      in
        if member (op aconv) axs ax' then axs
        else (tracing axname; collect_term_axioms ax' (ax' :: axs))
      end
    and collect_sort_axioms T axs =
      let
        val sort =
          (case T of
            TFree (_, sort) => sort
          | TVar (_, sort)  => sort
          | _ => raise REFUTE ("collect_axioms",
              "type " ^ Syntax.string_of_typ ctxt T ^ " is not a variable"))
        (* obtain axioms for all superclasses *)
        val superclasses = sort @ maps (Sign.super_classes thy) sort
        (* merely an optimization, because 'collect_this_axiom' disallows *)
        (* duplicate axioms anyway:                                       *)
        val superclasses = distinct (op =) superclasses
        val class_axioms = maps (fn class => map (fn ax =>
          ("<" ^ class ^ ">", Thm.prop_of ax))
          (#axioms (AxClass.get_info thy class) handle ERROR _ => []))
          superclasses
        (* replace the (at most one) schematic type variable in each axiom *)
        (* by the actual type 'T'                                          *)
        val monomorphic_class_axioms = map (fn (axname, ax) =>
          (case Term.add_tvars ax [] of
            [] => (axname, ax)
          | [(idx, S)] => (axname, monomorphic_term (Vartab.make [(idx, (S, T))]) ax)
          | _ =>
            raise REFUTE ("collect_axioms", "class axiom " ^ axname ^ " (" ^
              Syntax.string_of_term ctxt ax ^
              ") contains more than one type variable")))
          class_axioms
      in
        fold collect_this_axiom monomorphic_class_axioms axs
      end
    and collect_type_axioms T axs =
      case T of
      (* simple types *)
        Type ("prop", []) => axs
      | Type ("fun", [T1, T2]) => collect_type_axioms T2 (collect_type_axioms T1 axs)
      (* axiomatic type classes *)
      | Type ("itself", [T1]) => collect_type_axioms T1 axs
      | Type (s, Ts) =>
        (case Datatype.get_info thy s of
          SOME info =>  (* inductive datatype *)
            (* only collect relevant type axioms for the argument types *)
            fold collect_type_axioms Ts axs
        | NONE =>
          (case get_typedef thy T of
            SOME (axname, ax) =>
              collect_this_axiom (axname, ax) axs
          | NONE =>
            (* unspecified type, perhaps introduced with "typedecl" *)
            (* at least collect relevant type axioms for the argument types *)
            fold collect_type_axioms Ts axs))
      (* axiomatic type classes *)
      | TFree _ => collect_sort_axioms T axs
      (* axiomatic type classes *)
      | TVar _ => collect_sort_axioms T axs
    and collect_term_axioms t axs =
      case t of
      (* Pure *)
        Const (@{const_name all}, _) => axs
      | Const (@{const_name "=="}, _) => axs
      | Const (@{const_name "==>"}, _) => axs
      (* axiomatic type classes *)
      | Const (@{const_name TYPE}, T) => collect_type_axioms T axs
      (* HOL *)
      | Const (@{const_name Trueprop}, _) => axs
      | Const (@{const_name Not}, _) => axs
      (* redundant, since 'True' is also an IDT constructor *)
      | Const (@{const_name True}, _) => axs
      (* redundant, since 'False' is also an IDT constructor *)
      | Const (@{const_name False}, _) => axs
      | Const (@{const_name undefined}, T) => collect_type_axioms T axs
      | Const (@{const_name The}, T) =>
          let
            val ax = specialize_type thy (@{const_name The}, T)
              (the (AList.lookup (op =) axioms "HOL.the_eq_trivial"))
          in
            collect_this_axiom ("HOL.the_eq_trivial", ax) axs
          end
      | Const (@{const_name Hilbert_Choice.Eps}, T) =>
          let
            val ax = specialize_type thy (@{const_name Hilbert_Choice.Eps}, T)
              (the (AList.lookup (op =) axioms "Hilbert_Choice.someI"))
          in
            collect_this_axiom ("Hilbert_Choice.someI", ax) axs
          end
      | Const (@{const_name All}, T) => collect_type_axioms T axs
      | Const (@{const_name Ex}, T) => collect_type_axioms T axs
      | Const (@{const_name HOL.eq}, T) => collect_type_axioms T axs
      | Const (@{const_name HOL.conj}, _) => axs
      | Const (@{const_name HOL.disj}, _) => axs
      | Const (@{const_name HOL.implies}, _) => axs
      (* sets *)
      | Const (@{const_name Collect}, T) => collect_type_axioms T axs
      | Const (@{const_name Set.member}, T) => collect_type_axioms T axs
      (* other optimizations *)
      | Const (@{const_name Finite_Set.card}, T) => collect_type_axioms T axs
      | Const (@{const_name Finite_Set.finite}, T) =>
        collect_type_axioms T axs
      | Const (@{const_name Orderings.less}, T as Type ("fun", [@{typ nat},
        Type ("fun", [@{typ nat}, @{typ bool}])])) =>
          collect_type_axioms T axs
      | Const (@{const_name Groups.plus}, T as Type ("fun", [@{typ nat},
        Type ("fun", [@{typ nat}, @{typ nat}])])) =>
          collect_type_axioms T axs
      | Const (@{const_name Groups.minus}, T as Type ("fun", [@{typ nat},
        Type ("fun", [@{typ nat}, @{typ nat}])])) =>
          collect_type_axioms T axs
      | Const (@{const_name Groups.times}, T as Type ("fun", [@{typ nat},
        Type ("fun", [@{typ nat}, @{typ nat}])])) =>
          collect_type_axioms T axs
      | Const (@{const_name List.append}, T) => collect_type_axioms T axs
(* UNSOUND
      | Const (@{const_name lfp}, T) => collect_type_axioms T axs
      | Const (@{const_name gfp}, T) => collect_type_axioms T axs
*)
      | Const (@{const_name fst}, T) => collect_type_axioms T axs
      | Const (@{const_name snd}, T) => collect_type_axioms T axs
      (* simply-typed lambda calculus *)
      | Const (s, T) =>
          if is_const_of_class thy (s, T) then
            (* axiomatic type classes: add "OFCLASS(?'a::c, c_class)" *)
            (* and the class definition                               *)
            let
              val class = Logic.class_of_const s
              val of_class = Logic.mk_of_class (TVar (("'a", 0), [class]), class)
              val ax_in = SOME (specialize_type thy (s, T) of_class)
                (* type match may fail due to sort constraints *)
                handle Type.TYPE_MATCH => NONE
              val ax_1 = Option.map (fn ax => (Syntax.string_of_term ctxt ax, ax)) ax_in
              val ax_2 = Option.map (apsnd (specialize_type thy (s, T))) (get_classdef thy class)
            in
              collect_type_axioms T (fold collect_this_axiom (map_filter I [ax_1, ax_2]) axs)
            end
          else if is_IDT_constructor thy (s, T)
            orelse is_IDT_recursor thy (s, T)
          then
            (* only collect relevant type axioms *)
            collect_type_axioms T axs
          else
            (* other constants should have been unfolded, with some *)
            (* exceptions: e.g. Abs_xxx/Rep_xxx functions for       *)
            (* typedefs, or type-class related constants            *)
            (* only collect relevant type axioms *)
            collect_type_axioms T axs
      | Free (_, T) => collect_type_axioms T axs
      | Var (_, T) => collect_type_axioms T axs
      | Bound _ => axs
      | Abs (_, T, body) => collect_term_axioms body (collect_type_axioms T axs)
      | t1 $ t2 => collect_term_axioms t2 (collect_term_axioms t1 axs)
    val result = map close_form (collect_term_axioms t [])
    val _ = tracing " ...done."
  in
    result
  end;

(* ------------------------------------------------------------------------- *)
(* ground_types: collects all ground types in a term (including argument     *)
(*               types of other types), suppressing duplicates.  Does not    *)
(*               return function types, set types, non-recursive IDTs, or    *)
(*               'propT'.  For IDTs, also the argument types of constructors *)
(*               and all mutually recursive IDTs are considered.             *)
(* ------------------------------------------------------------------------- *)

fun ground_types ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt
    fun collect_types T acc =
      (case T of
        Type ("fun", [T1, T2]) => collect_types T1 (collect_types T2 acc)
      | Type ("prop", []) => acc
      | Type (s, Ts) =>
          (case Datatype.get_info thy s of
            SOME info =>  (* inductive datatype *)
              let
                val index = #index info
                val descr = #descr info
                val (_, typs, _) = the (AList.lookup (op =) descr index)
                val typ_assoc = typs ~~ Ts
                (* sanity check: every element in 'dtyps' must be a *)
                (* 'DtTFree'                                        *)
                val _ = if Library.exists (fn d =>
                  case d of Datatype_Aux.DtTFree _ => false | _ => true) typs then
                  raise REFUTE ("ground_types", "datatype argument (for type "
                    ^ Syntax.string_of_typ ctxt T ^ ") is not a variable")
                else ()
                (* required for mutually recursive datatypes; those need to   *)
                (* be added even if they are an instance of an otherwise non- *)
                (* recursive datatype                                         *)
                fun collect_dtyp d acc =
                  let
                    val dT = typ_of_dtyp descr typ_assoc d
                  in
                    case d of
                      Datatype_Aux.DtTFree _ =>
                      collect_types dT acc
                    | Datatype_Aux.DtType (_, ds) =>
                      collect_types dT (fold_rev collect_dtyp ds acc)
                    | Datatype_Aux.DtRec i =>
                      if member (op =) acc dT then
                        acc  (* prevent infinite recursion *)
                      else
                        let
                          val (_, dtyps, dconstrs) = the (AList.lookup (op =) descr i)
                          (* if the current type is a recursive IDT (i.e. a depth *)
                          (* is required), add it to 'acc'                        *)
                          val acc_dT = if Library.exists (fn (_, ds) =>
                            Library.exists Datatype_Aux.is_rec_type ds) dconstrs then
                              insert (op =) dT acc
                            else acc
                          (* collect argument types *)
                          val acc_dtyps = fold_rev collect_dtyp dtyps acc_dT
                          (* collect constructor types *)
                          val acc_dconstrs = fold_rev collect_dtyp (maps snd dconstrs) acc_dtyps
                        in
                          acc_dconstrs
                        end
                  end
              in
                (* argument types 'Ts' could be added here, but they are also *)
                (* added by 'collect_dtyp' automatically                      *)
                collect_dtyp (Datatype_Aux.DtRec index) acc
              end
          | NONE =>
            (* not an inductive datatype, e.g. defined via "typedef" or *)
            (* "typedecl"                                               *)
            insert (op =) T (fold collect_types Ts acc))
      | TFree _ => insert (op =) T acc
      | TVar _ => insert (op =) T acc)
  in
    fold_types collect_types t []
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
      case AList.lookup (op =) sizes (string_of_typ T) of
        SOME n => n
      | NONE => minsize
  in
    map (fn T => (T, size_of_typ T)) xs
  end;

(* ------------------------------------------------------------------------- *)
(* next_universe: enumerates all universes (i.e. assignments of sizes to     *)
(*                types), where the minimal size of a type is given by       *)
(*                'minsize', the maximal size is given by 'maxsize', and a   *)
(*                type may have a fixed size given in 'sizes'                *)
(* ------------------------------------------------------------------------- *)

(* (Term.typ * int) list -> (string * int) list -> int -> int ->
  (Term.typ * int) list option *)

fun next_universe xs sizes minsize maxsize =
  let
    (* creates the "first" list of length 'len', where the sum of all list *)
    (* elements is 'sum', and the length of the list is 'len'              *)
    (* int -> int -> int -> int list option *)
    fun make_first _ 0 sum =
          if sum = 0 then
            SOME []
          else
            NONE
      | make_first max len sum =
          if sum <= max orelse max < 0 then
            Option.map (fn xs' => sum :: xs') (make_first max (len-1) 0)
          else
            Option.map (fn xs' => max :: xs') (make_first max (len-1) (sum-max))
    (* enumerates all int lists with a fixed length, where 0<=x<='max' for *)
    (* all list elements x (unless 'max'<0)                                *)
    (* int -> int -> int -> int list -> int list option *)
    fun next max len sum [] =
          NONE
      | next max len sum [x] =
          (* we've reached the last list element, so there's no shift possible *)
          make_first max (len+1) (sum+x+1)  (* increment 'sum' by 1 *)
      | next max len sum (x1::x2::xs) =
          if x1>0 andalso (x2<max orelse max<0) then
            (* we can shift *)
            SOME (the (make_first max (len+1) (sum+x1-1)) @ (x2+1) :: xs)
          else
            (* continue search *)
            next max (len+1) (sum+x1) (x2::xs)
    (* only consider those types for which the size is not fixed *)
    val mutables = filter_out (AList.defined (op =) sizes o string_of_typ o fst) xs
    (* subtract 'minsize' from every size (will be added again at the end) *)
    val diffs = map (fn (_, n) => n-minsize) mutables
  in
    case next (maxsize-minsize) 0 0 diffs of
      SOME diffs' =>
        (* merge with those types for which the size is fixed *)
        SOME (fst (fold_map (fn (T, _) => fn ds =>
          case AList.lookup (op =) sizes (string_of_typ T) of
          (* return the fixed size *)
            SOME n => ((T, n), ds)
          (* consume the head of 'ds', add 'minsize' *)
          | NONE   => ((T, minsize + hd ds), tl ds))
          xs diffs'))
    | NONE => NONE
  end;

(* ------------------------------------------------------------------------- *)
(* toTrue: converts the interpretation of a Boolean value to a propositional *)
(*         formula that is true iff the interpretation denotes "true"        *)
(* ------------------------------------------------------------------------- *)

(* interpretation -> prop_formula *)

fun toTrue (Leaf [fm, _]) = fm
  | toTrue _ = raise REFUTE ("toTrue", "interpretation does not denote a Boolean value");

(* ------------------------------------------------------------------------- *)
(* toFalse: converts the interpretation of a Boolean value to a              *)
(*          propositional formula that is true iff the interpretation        *)
(*          denotes "false"                                                  *)
(* ------------------------------------------------------------------------- *)

(* interpretation -> prop_formula *)

fun toFalse (Leaf [_, fm]) = fm
  | toFalse _ = raise REFUTE ("toFalse", "interpretation does not denote a Boolean value");

(* ------------------------------------------------------------------------- *)
(* find_model: repeatedly calls 'interpret' with appropriate parameters,     *)
(*             applies a SAT solver, and (in case a model is found) displays *)
(*             the model to the user by calling 'print_model'                *)
(* {...}     : parameters that control the translation/model generation      *)
(* assm_ts   : assumptions to be considered unless "no_assms" is specified   *)
(* t         : term to be translated into a propositional formula            *)
(* negate    : if true, find a model that makes 't' false (rather than true) *)
(* ------------------------------------------------------------------------- *)

fun find_model ctxt
    {sizes, minsize, maxsize, maxvars, maxtime, satsolver, no_assms, expect}
    assm_ts t negate =
  let
    val thy = Proof_Context.theory_of ctxt
    (* string -> string *)
    fun check_expect outcome_code =
      if expect = "" orelse outcome_code = expect then outcome_code
      else error ("Unexpected outcome: " ^ quote outcome_code ^ ".")
    (* unit -> string *)
    fun wrapper () =
      let
        val timer = Timer.startRealTimer ()
        val t =
          if no_assms then t
          else if negate then Logic.list_implies (assm_ts, t)
          else Logic.mk_conjunction_list (t :: assm_ts)
        val u = unfold_defs thy t
        val _ = tracing ("Unfolded term: " ^ Syntax.string_of_term ctxt u)
        val axioms = collect_axioms ctxt u
        (* Term.typ list *)
        val types = fold (union (op =) o ground_types ctxt) (u :: axioms) []
        val _ = tracing ("Ground types: "
          ^ (if null types then "none."
             else commas (map (Syntax.string_of_typ ctxt) types)))
        (* we can only consider fragments of recursive IDTs, so we issue a  *)
        (* warning if the formula contains a recursive IDT                  *)
        (* TODO: no warning needed for /positive/ occurrences of IDTs       *)
        val maybe_spurious = Library.exists (fn
            Type (s, _) =>
              (case Datatype.get_info thy s of
                SOME info =>  (* inductive datatype *)
                  let
                    val index           = #index info
                    val descr           = #descr info
                    val (_, _, constrs) = the (AList.lookup (op =) descr index)
                  in
                    (* recursive datatype? *)
                    Library.exists (fn (_, ds) =>
                      Library.exists Datatype_Aux.is_rec_type ds) constrs
                  end
              | NONE => false)
          | _ => false) types
        val _ =
          if maybe_spurious then
            warning ("Term contains a recursive datatype; "
              ^ "countermodel(s) may be spurious!")
          else
            ()
        (* (Term.typ * int) list -> string *)
        fun find_model_loop universe =
          let
            val msecs_spent = Time.toMilliseconds (Timer.checkRealTimer timer)
            val _ = maxtime = 0 orelse msecs_spent < 1000 * maxtime
                    orelse raise TimeLimit.TimeOut
            val init_model = (universe, [])
            val init_args  = {maxvars = maxvars, def_eq = false, next_idx = 1,
              bounds = [], wellformed = True}
            val _ = tracing ("Translating term (sizes: "
              ^ commas (map (fn (_, n) => string_of_int n) universe) ^ ") ...")
            (* translate 'u' and all axioms *)
            val (intrs, (model, args)) = fold_map (fn t' => fn (m, a) =>
              let
                val (i, m', a') = interpret ctxt m a t'
              in
                (* set 'def_eq' to 'true' *)
                (i, (m', {maxvars = #maxvars a', def_eq = true,
                  next_idx = #next_idx a', bounds = #bounds a',
                  wellformed = #wellformed a'}))
              end) (u :: axioms) (init_model, init_args)
            (* make 'u' either true or false, and make all axioms true, and *)
            (* add the well-formedness side condition                       *)
            val fm_u = (if negate then toFalse else toTrue) (hd intrs)
            val fm_ax = Prop_Logic.all (map toTrue (tl intrs))
            val fm = Prop_Logic.all [#wellformed args, fm_ax, fm_u]
            val _ =
              (if satsolver = "dpll" orelse satsolver = "enumerate" then
                warning ("Using SAT solver " ^ quote satsolver ^
                         "; for better performance, consider installing an \
                         \external solver.")
               else ());
            val solver =
              SatSolver.invoke_solver satsolver
              handle Option.Option =>
                     error ("Unknown SAT solver: " ^ quote satsolver ^
                            ". Available solvers: " ^
                            commas (map (quote o fst) (!SatSolver.solvers)) ^ ".")
          in
            Output.urgent_message "Invoking SAT solver...";
            (case solver fm of
              SatSolver.SATISFIABLE assignment =>
                (Output.urgent_message ("Model found:\n" ^ print_model ctxt model
                  (fn i => case assignment i of SOME b => b | NONE => true));
                 if maybe_spurious then "potential" else "genuine")
            | SatSolver.UNSATISFIABLE _ =>
                (Output.urgent_message "No model exists.";
                case next_universe universe sizes minsize maxsize of
                  SOME universe' => find_model_loop universe'
                | NONE => (Output.urgent_message
                    "Search terminated, no larger universe within the given limits.";
                    "none"))
            | SatSolver.UNKNOWN =>
                (Output.urgent_message "No model found.";
                case next_universe universe sizes minsize maxsize of
                  SOME universe' => find_model_loop universe'
                | NONE => (Output.urgent_message
                  "Search terminated, no larger universe within the given limits.";
                  "unknown"))) handle SatSolver.NOT_CONFIGURED =>
              (error ("SAT solver " ^ quote satsolver ^ " is not configured.");
               "unknown")
          end
          handle MAXVARS_EXCEEDED =>
            (Output.urgent_message ("Search terminated, number of Boolean variables ("
              ^ string_of_int maxvars ^ " allowed) exceeded.");
              "unknown")

        val outcome_code = find_model_loop (first_universe types sizes minsize)
      in
        check_expect outcome_code
      end
  in
    (* some parameter sanity checks *)
    minsize>=1 orelse
      error ("\"minsize\" is " ^ string_of_int minsize ^ ", must be at least 1");
    maxsize>=1 orelse
      error ("\"maxsize\" is " ^ string_of_int maxsize ^ ", must be at least 1");
    maxsize>=minsize orelse
      error ("\"maxsize\" (=" ^ string_of_int maxsize ^
      ") is less than \"minsize\" (=" ^ string_of_int minsize ^ ").");
    maxvars>=0 orelse
      error ("\"maxvars\" is " ^ string_of_int maxvars ^ ", must be at least 0");
    maxtime>=0 orelse
      error ("\"maxtime\" is " ^ string_of_int maxtime ^ ", must be at least 0");
    (* enter loop with or without time limit *)
    Output.urgent_message ("Trying to find a model that "
      ^ (if negate then "refutes" else "satisfies") ^ ": "
      ^ Syntax.string_of_term ctxt t);
    if maxtime > 0 then (
      TimeLimit.timeLimit (Time.fromSeconds maxtime)
        wrapper ()
      handle TimeLimit.TimeOut =>
        (Output.urgent_message ("Search terminated, time limit (" ^
            string_of_int maxtime
            ^ (if maxtime=1 then " second" else " seconds") ^ ") exceeded.");
         check_expect "unknown")
    ) else wrapper ()
  end;


(* ------------------------------------------------------------------------- *)
(* INTERFACE, PART 2: FINDING A MODEL                                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* satisfy_term: calls 'find_model' to find a model that satisfies 't'       *)
(* params      : list of '(name, value)' pairs used to override default      *)
(*               parameters                                                  *)
(* ------------------------------------------------------------------------- *)

fun satisfy_term ctxt params assm_ts t =
  find_model ctxt (actual_params ctxt params) assm_ts t false;

(* ------------------------------------------------------------------------- *)
(* refute_term: calls 'find_model' to find a model that refutes 't'          *)
(* params     : list of '(name, value)' pairs used to override default       *)
(*              parameters                                                   *)
(* ------------------------------------------------------------------------- *)

fun refute_term ctxt params assm_ts t =
  let
    (* disallow schematic type variables, since we cannot properly negate  *)
    (* terms containing them (their logical meaning is that there EXISTS a *)
    (* type s.t. ...; to refute such a formula, we would have to show that *)
    (* for ALL types, not ...)                                             *)
    val _ = null (Term.add_tvars t []) orelse
      error "Term to be refuted contains schematic type variables"

    (* existential closure over schematic variables *)
    (* (Term.indexname * Term.typ) list *)
    val vars = sort_wrt (fst o fst) (map dest_Var (Misc_Legacy.term_vars t))
    (* Term.term *)
    val ex_closure = fold (fn ((x, i), T) => fn t' =>
      HOLogic.exists_const T $
        Abs (x, T, abstract_over (Var ((x, i), T), t'))) vars t
    (* Note: If 't' is of type 'propT' (rather than 'boolT'), applying   *)
    (* 'HOLogic.exists_const' is not type-correct.  However, this is not *)
    (* really a problem as long as 'find_model' still interprets the     *)
    (* resulting term correctly, without checking its type.              *)

    (* replace outermost universally quantified variables by Free's:     *)
    (* refuting a term with Free's is generally faster than refuting a   *)
    (* term with (nested) quantifiers, because quantifiers are expanded, *)
    (* while the SAT solver searches for an interpretation for Free's.   *)
    (* Also we get more information back that way, namely an             *)
    (* interpretation which includes values for the (formerly)           *)
    (* quantified variables.                                             *)
    (* maps  !!x1...xn. !xk...xm. t   to   t  *)
    fun strip_all_body (Const (@{const_name all}, _) $ Abs (_, _, t)) =
          strip_all_body t
      | strip_all_body (Const (@{const_name Trueprop}, _) $ t) =
          strip_all_body t
      | strip_all_body (Const (@{const_name All}, _) $ Abs (_, _, t)) =
          strip_all_body t
      | strip_all_body t = t
    (* maps  !!x1...xn. !xk...xm. t   to   [x1, ..., xn, xk, ..., xm]  *)
    fun strip_all_vars (Const (@{const_name all}, _) $ Abs (a, T, t)) =
          (a, T) :: strip_all_vars t
      | strip_all_vars (Const (@{const_name Trueprop}, _) $ t) =
          strip_all_vars t
      | strip_all_vars (Const (@{const_name All}, _) $ Abs (a, T, t)) =
          (a, T) :: strip_all_vars t
      | strip_all_vars t = [] : (string * typ) list
    val strip_t = strip_all_body ex_closure
    val frees = Term.rename_wrt_term strip_t (strip_all_vars ex_closure)
    val subst_t = Term.subst_bounds (map Free frees, strip_t)
  in
    find_model ctxt (actual_params ctxt params) assm_ts subst_t true
  end;

(* ------------------------------------------------------------------------- *)
(* refute_goal                                                               *)
(* ------------------------------------------------------------------------- *)

fun refute_goal ctxt params th i =
  let
    val t = th |> prop_of
  in
    if Logic.count_prems t = 0 then
      (Output.urgent_message "No subgoal!"; "none")
    else
      let
        val assms = map term_of (Assumption.all_assms_of ctxt)
        val (t, frees) = Logic.goal_params t i
      in
        refute_term ctxt params assms (subst_bounds (frees, t))
      end
  end


(* ------------------------------------------------------------------------- *)
(* INTERPRETERS: Auxiliary Functions                                         *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* make_constants: returns all interpretations for type 'T' that consist of  *)
(*                 unit vectors with 'True'/'False' only (no Boolean         *)
(*                 variables)                                                *)
(* ------------------------------------------------------------------------- *)

fun make_constants ctxt model T =
  let
    (* returns a list with all unit vectors of length n *)
    (* int -> interpretation list *)
    fun unit_vectors n =
      let
        (* returns the k-th unit vector of length n *)
        (* int * int -> interpretation *)
        fun unit_vector (k, n) =
          Leaf ((replicate (k-1) False) @ (True :: (replicate (n-k) False)))
        (* int -> interpretation list *)
        fun unit_vectors_loop k =
          if k>n then [] else unit_vector (k,n) :: unit_vectors_loop (k+1)
      in
        unit_vectors_loop 1
      end
    (* returns a list of lists, each one consisting of n (possibly *)
    (* identical) elements from 'xs'                               *)
    (* int -> 'a list -> 'a list list *)
    fun pick_all 1 xs = map single xs
      | pick_all n xs =
          let val rec_pick = pick_all (n - 1) xs in
            maps (fn x => map (cons x) rec_pick) xs
          end
    (* returns all constant interpretations that have the same tree *)
    (* structure as the interpretation argument                     *)
    (* interpretation -> interpretation list *)
    fun make_constants_intr (Leaf xs) = unit_vectors (length xs)
      | make_constants_intr (Node xs) = map Node (pick_all (length xs)
          (make_constants_intr (hd xs)))
    (* obtain the interpretation for a variable of type 'T' *)
    val (i, _, _) = interpret ctxt model {maxvars=0, def_eq=false, next_idx=1,
      bounds=[], wellformed=True} (Free ("dummy", T))
  in
    make_constants_intr i
  end;

(* ------------------------------------------------------------------------- *)
(* size_of_type: returns the number of elements in a type 'T' (i.e. 'length  *)
(*               (make_constants T)', but implemented more efficiently)      *)
(* ------------------------------------------------------------------------- *)

(* returns 0 for an empty ground type or a function type with empty      *)
(* codomain, but fails for a function type with empty domain --          *)
(* admissibility of datatype constructor argument types (see "Inductive  *)
(* datatypes in HOL - lessons learned ...", S. Berghofer, M. Wenzel,     *)
(* TPHOLs 99) ensures that recursive, possibly empty, datatype fragments *)
(* never occur as the domain of a function type that is the type of a    *)
(* constructor argument                                                  *)

fun size_of_type ctxt model T =
  let
    (* returns the number of elements that have the same tree structure as a *)
    (* given interpretation                                                  *)
    fun size_of_intr (Leaf xs) = length xs
      | size_of_intr (Node xs) = Integer.pow (length xs) (size_of_intr (hd xs))
    (* obtain the interpretation for a variable of type 'T' *)
    val (i, _, _) = interpret ctxt model {maxvars=0, def_eq=false, next_idx=1,
      bounds=[], wellformed=True} (Free ("dummy", T))
  in
    size_of_intr i
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
(* - two interpretations are 'equal' iff they are both defined and denote    *)
(*   the same value                                                          *)
(* - two interpretations are 'not_equal' iff they are both defined at least  *)
(*   partially, and a defined part denotes different values                  *)
(* - a completely undefined interpretation is neither 'equal' nor            *)
(*   'not_equal' to another interpretation                                   *)
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
            Leaf ys => Prop_Logic.dot_product (xs, ys)  (* defined and equal *)
          | Node _  => raise REFUTE ("make_equality",
            "second interpretation is higher"))
      | Node xs =>
          (case i2 of
            Leaf _  => raise REFUTE ("make_equality",
            "first interpretation is higher")
          | Node ys => Prop_Logic.all (map equal (xs ~~ ys))))
    (* interpretation * interpretation -> prop_formula *)
    fun not_equal (i1, i2) =
      (case i1 of
        Leaf xs =>
          (case i2 of
            (* defined and not equal *)
            Leaf ys => Prop_Logic.all ((Prop_Logic.exists xs)
            :: (Prop_Logic.exists ys)
            :: (map (fn (x,y) => SOr (SNot x, SNot y)) (xs ~~ ys)))
          | Node _  => raise REFUTE ("make_equality",
            "second interpretation is higher"))
      | Node xs =>
          (case i2 of
            Leaf _  => raise REFUTE ("make_equality",
            "first interpretation is higher")
          | Node ys => Prop_Logic.exists (map not_equal (xs ~~ ys))))
  in
    (* a value may be undefined; therefore 'not_equal' is not just the *)
    (* negation of 'equal'                                             *)
    Leaf [equal (i1, i2), not_equal (i1, i2)]
  end;

(* ------------------------------------------------------------------------- *)
(* make_def_equality: returns an interpretation that denotes (extensional)   *)
(*                    equality of two interpretations                        *)
(* This function treats undefined/partially defined interpretations          *)
(* different from 'make_equality': two undefined interpretations are         *)
(* considered equal, while a defined interpretation is considered not equal  *)
(* to an undefined interpretation.                                           *)
(* ------------------------------------------------------------------------- *)

(* interpretation * interpretation -> interpretation *)

fun make_def_equality (i1, i2) =
  let
    (* interpretation * interpretation -> prop_formula *)
    fun equal (i1, i2) =
      (case i1 of
        Leaf xs =>
          (case i2 of
            (* defined and equal, or both undefined *)
            Leaf ys => SOr (Prop_Logic.dot_product (xs, ys),
            SAnd (Prop_Logic.all (map SNot xs), Prop_Logic.all (map SNot ys)))
          | Node _  => raise REFUTE ("make_def_equality",
            "second interpretation is higher"))
      | Node xs =>
          (case i2 of
            Leaf _  => raise REFUTE ("make_def_equality",
            "first interpretation is higher")
          | Node ys => Prop_Logic.all (map equal (xs ~~ ys))))
    (* interpretation *)
    val eq = equal (i1, i2)
  in
    Leaf [eq, SNot eq]
  end;

(* ------------------------------------------------------------------------- *)
(* interpretation_apply: returns an interpretation that denotes the result   *)
(*                       of applying the function denoted by 'i1' to the     *)
(*                       argument denoted by 'i2'                            *)
(* ------------------------------------------------------------------------- *)

(* interpretation * interpretation -> interpretation *)

fun interpretation_apply (i1, i2) =
  let
    (* interpretation * interpretation -> interpretation *)
    fun interpretation_disjunction (tr1,tr2) =
      tree_map (fn (xs,ys) => map (fn (x,y) => SOr(x,y)) (xs ~~ ys))
        (tree_pair (tr1,tr2))
    (* prop_formula * interpretation -> interpretation *)
    fun prop_formula_times_interpretation (fm,tr) =
      tree_map (map (fn x => SAnd (fm,x))) tr
    (* prop_formula list * interpretation list -> interpretation *)
    fun prop_formula_list_dot_product_interpretation_list ([fm],[tr]) =
          prop_formula_times_interpretation (fm,tr)
      | prop_formula_list_dot_product_interpretation_list (fm::fms,tr::trees) =
          interpretation_disjunction (prop_formula_times_interpretation (fm,tr),
            prop_formula_list_dot_product_interpretation_list (fms,trees))
      | prop_formula_list_dot_product_interpretation_list (_,_) =
          raise REFUTE ("interpretation_apply", "empty list (in dot product)")
    (* concatenates 'x' with every list in 'xss', returning a new list of *)
    (* lists                                                              *)
    (* 'a -> 'a list list -> 'a list list *)
    fun cons_list x xss = map (cons x) xss
    (* returns a list of lists, each one consisting of one element from each *)
    (* element of 'xss'                                                      *)
    (* 'a list list -> 'a list list *)
    fun pick_all [xs] = map single xs
      | pick_all (xs::xss) =
          let val rec_pick = pick_all xss in
            maps (fn x => map (cons x) rec_pick) xs
          end
      | pick_all _ = raise REFUTE ("interpretation_apply", "empty list (in pick_all)")
    (* interpretation -> prop_formula list *)
    fun interpretation_to_prop_formula_list (Leaf xs) = xs
      | interpretation_to_prop_formula_list (Node trees) =
          map Prop_Logic.all (pick_all
            (map interpretation_to_prop_formula_list trees))
  in
    case i1 of
      Leaf _ =>
        raise REFUTE ("interpretation_apply", "first interpretation is a leaf")
    | Node xs =>
        prop_formula_list_dot_product_interpretation_list
          (interpretation_to_prop_formula_list i2, xs)
  end;

(* ------------------------------------------------------------------------- *)
(* eta_expand: eta-expands a term 't' by adding 'i' lambda abstractions      *)
(* ------------------------------------------------------------------------- *)

(* Term.term -> int -> Term.term *)

fun eta_expand t i =
  let
    val Ts = Term.binder_types (Term.fastype_of t)
    val t' = Term.incr_boundvars i t
  in
    fold_rev (fn T => fn term => Abs ("<eta_expand>", T, term))
      (List.take (Ts, i))
      (Term.list_comb (t', map Bound (i-1 downto 0)))
  end;

(* ------------------------------------------------------------------------- *)
(* size_of_dtyp: the size of (an initial fragment of) an inductive data type *)
(*               is the sum (over its constructors) of the product (over     *)
(*               their arguments) of the size of the argument types          *)
(* ------------------------------------------------------------------------- *)

fun size_of_dtyp ctxt typ_sizes descr typ_assoc constructors =
  Integer.sum (map (fn (_, dtyps) =>
    Integer.prod (map (size_of_type ctxt (typ_sizes, []) o
      (typ_of_dtyp descr typ_assoc)) dtyps))
        constructors);


(* ------------------------------------------------------------------------- *)
(* INTERPRETERS: Actual Interpreters                                         *)
(* ------------------------------------------------------------------------- *)

(* simply typed lambda calculus: Isabelle's basic term syntax, with type *)
(* variables, function types, and propT                                  *)

fun stlc_interpreter ctxt model args t =
  let
    val thy = Proof_Context.theory_of ctxt
    val (typs, terms) = model
    val {maxvars, def_eq, next_idx, bounds, wellformed} = args
    (* Term.typ -> (interpretation * model * arguments) option *)
    fun interpret_groundterm T =
      let
        (* unit -> (interpretation * model * arguments) option *)
        fun interpret_groundtype () =
          let
            (* the model must specify a size for ground types *)
            val size =
              if T = Term.propT then 2
              else the (AList.lookup (op =) typs T)
            val next = next_idx + size
            (* check if 'maxvars' is large enough *)
            val _ = (if next - 1 > maxvars andalso maxvars > 0 then
              raise MAXVARS_EXCEEDED else ())
            (* prop_formula list *)
            val fms  = map BoolVar (next_idx upto (next_idx + size - 1))
            (* interpretation *)
            val intr = Leaf fms
            (* prop_formula list -> prop_formula *)
            fun one_of_two_false [] = True
              | one_of_two_false (x::xs) = SAnd (Prop_Logic.all (map (fn x' =>
                  SOr (SNot x, SNot x')) xs), one_of_two_false xs)
            (* prop_formula *)
            val wf = one_of_two_false fms
          in
            (* extend the model, increase 'next_idx', add well-formedness *)
            (* condition                                                  *)
            SOME (intr, (typs, (t, intr)::terms), {maxvars = maxvars,
              def_eq = def_eq, next_idx = next, bounds = bounds,
              wellformed = SAnd (wellformed, wf)})
          end
      in
        case T of
          Type ("fun", [T1, T2]) =>
            let
              (* we create 'size_of_type ... T1' different copies of the        *)
              (* interpretation for 'T2', which are then combined into a single *)
              (* new interpretation                                             *)
              (* make fresh copies, with different variable indices *)
              (* 'idx': next variable index                         *)
              (* 'n'  : number of copies                            *)
              (* int -> int -> (int * interpretation list * prop_formula *)
              fun make_copies idx 0 = (idx, [], True)
                | make_copies idx n =
                    let
                      val (copy, _, new_args) = interpret ctxt (typs, [])
                        {maxvars = maxvars, def_eq = false, next_idx = idx,
                        bounds = [], wellformed = True} (Free ("dummy", T2))
                      val (idx', copies, wf') = make_copies (#next_idx new_args) (n-1)
                    in
                      (idx', copy :: copies, SAnd (#wellformed new_args, wf'))
                    end
              val (next, copies, wf) = make_copies next_idx
                (size_of_type ctxt model T1)
              (* combine copies into a single interpretation *)
              val intr = Node copies
            in
              (* extend the model, increase 'next_idx', add well-formedness *)
              (* condition                                                  *)
              SOME (intr, (typs, (t, intr)::terms), {maxvars = maxvars,
                def_eq = def_eq, next_idx = next, bounds = bounds,
                wellformed = SAnd (wellformed, wf)})
            end
        | Type _  => interpret_groundtype ()
        | TFree _ => interpret_groundtype ()
        | TVar  _ => interpret_groundtype ()
      end
  in
    case AList.lookup (op =) terms t of
      SOME intr =>
        (* return an existing interpretation *)
        SOME (intr, model, args)
    | NONE =>
        (case t of
          Const (_, T) => interpret_groundterm T
        | Free (_, T) => interpret_groundterm T
        | Var (_, T) => interpret_groundterm T
        | Bound i => SOME (nth (#bounds args) i, model, args)
        | Abs (x, T, body) =>
            let
              (* create all constants of type 'T' *)
              val constants = make_constants ctxt model T
              (* interpret the 'body' separately for each constant *)
              val (bodies, (model', args')) = fold_map
                (fn c => fn (m, a) =>
                  let
                    (* add 'c' to 'bounds' *)
                    val (i', m', a') = interpret ctxt m {maxvars = #maxvars a,
                      def_eq = #def_eq a, next_idx = #next_idx a,
                      bounds = (c :: #bounds a), wellformed = #wellformed a} body
                  in
                    (* keep the new model m' and 'next_idx' and 'wellformed', *)
                    (* but use old 'bounds'                                   *)
                    (i', (m', {maxvars = maxvars, def_eq = def_eq,
                      next_idx = #next_idx a', bounds = bounds,
                      wellformed = #wellformed a'}))
                  end)
                constants (model, args)
            in
              SOME (Node bodies, model', args')
            end
        | t1 $ t2 =>
            let
              (* interpret 't1' and 't2' separately *)
              val (intr1, model1, args1) = interpret ctxt model args t1
              val (intr2, model2, args2) = interpret ctxt model1 args1 t2
            in
              SOME (interpretation_apply (intr1, intr2), model2, args2)
            end)
  end;

fun Pure_interpreter ctxt model args t =
  case t of
    Const (@{const_name all}, _) $ t1 =>
      let
        val (i, m, a) = interpret ctxt model args t1
      in
        case i of
          Node xs =>
            (* 3-valued logic *)
            let
              val fmTrue  = Prop_Logic.all (map toTrue xs)
              val fmFalse = Prop_Logic.exists (map toFalse xs)
            in
              SOME (Leaf [fmTrue, fmFalse], m, a)
            end
        | _ =>
          raise REFUTE ("Pure_interpreter",
            "\"all\" is followed by a non-function")
      end
  | Const (@{const_name all}, _) =>
      SOME (interpret ctxt model args (eta_expand t 1))
  | Const (@{const_name "=="}, _) $ t1 $ t2 =>
      let
        val (i1, m1, a1) = interpret ctxt model args t1
        val (i2, m2, a2) = interpret ctxt m1 a1 t2
      in
        (* we use either 'make_def_equality' or 'make_equality' *)
        SOME ((if #def_eq args then make_def_equality else make_equality)
          (i1, i2), m2, a2)
      end
  | Const (@{const_name "=="}, _) $ t1 =>
      SOME (interpret ctxt model args (eta_expand t 1))
  | Const (@{const_name "=="}, _) =>
      SOME (interpret ctxt model args (eta_expand t 2))
  | Const (@{const_name "==>"}, _) $ t1 $ t2 =>
      (* 3-valued logic *)
      let
        val (i1, m1, a1) = interpret ctxt model args t1
        val (i2, m2, a2) = interpret ctxt m1 a1 t2
        val fmTrue = Prop_Logic.SOr (toFalse i1, toTrue i2)
        val fmFalse = Prop_Logic.SAnd (toTrue i1, toFalse i2)
      in
        SOME (Leaf [fmTrue, fmFalse], m2, a2)
      end
  | Const (@{const_name "==>"}, _) $ t1 =>
      SOME (interpret ctxt model args (eta_expand t 1))
  | Const (@{const_name "==>"}, _) =>
      SOME (interpret ctxt model args (eta_expand t 2))
  | _ => NONE;

fun HOLogic_interpreter ctxt model args t =
(* Providing interpretations directly is more efficient than unfolding the *)
(* logical constants.  In HOL however, logical constants can themselves be *)
(* arguments.  They are then translated using eta-expansion.               *)
  case t of
    Const (@{const_name Trueprop}, _) =>
      SOME (Node [TT, FF], model, args)
  | Const (@{const_name Not}, _) =>
      SOME (Node [FF, TT], model, args)
  (* redundant, since 'True' is also an IDT constructor *)
  | Const (@{const_name True}, _) =>
      SOME (TT, model, args)
  (* redundant, since 'False' is also an IDT constructor *)
  | Const (@{const_name False}, _) =>
      SOME (FF, model, args)
  | Const (@{const_name All}, _) $ t1 =>  (* similar to "all" (Pure) *)
      let
        val (i, m, a) = interpret ctxt model args t1
      in
        case i of
          Node xs =>
            (* 3-valued logic *)
            let
              val fmTrue = Prop_Logic.all (map toTrue xs)
              val fmFalse = Prop_Logic.exists (map toFalse xs)
            in
              SOME (Leaf [fmTrue, fmFalse], m, a)
            end
        | _ =>
          raise REFUTE ("HOLogic_interpreter",
            "\"All\" is followed by a non-function")
      end
  | Const (@{const_name All}, _) =>
      SOME (interpret ctxt model args (eta_expand t 1))
  | Const (@{const_name Ex}, _) $ t1 =>
      let
        val (i, m, a) = interpret ctxt model args t1
      in
        case i of
          Node xs =>
            (* 3-valued logic *)
            let
              val fmTrue = Prop_Logic.exists (map toTrue xs)
              val fmFalse = Prop_Logic.all (map toFalse xs)
            in
              SOME (Leaf [fmTrue, fmFalse], m, a)
            end
        | _ =>
          raise REFUTE ("HOLogic_interpreter",
            "\"Ex\" is followed by a non-function")
      end
  | Const (@{const_name Ex}, _) =>
      SOME (interpret ctxt model args (eta_expand t 1))
  | Const (@{const_name HOL.eq}, _) $ t1 $ t2 =>  (* similar to "==" (Pure) *)
      let
        val (i1, m1, a1) = interpret ctxt model args t1
        val (i2, m2, a2) = interpret ctxt m1 a1 t2
      in
        SOME (make_equality (i1, i2), m2, a2)
      end
  | Const (@{const_name HOL.eq}, _) $ t1 =>
      SOME (interpret ctxt model args (eta_expand t 1))
  | Const (@{const_name HOL.eq}, _) =>
      SOME (interpret ctxt model args (eta_expand t 2))
  | Const (@{const_name HOL.conj}, _) $ t1 $ t2 =>
      (* 3-valued logic *)
      let
        val (i1, m1, a1) = interpret ctxt model args t1
        val (i2, m2, a2) = interpret ctxt m1 a1 t2
        val fmTrue = Prop_Logic.SAnd (toTrue i1, toTrue i2)
        val fmFalse = Prop_Logic.SOr (toFalse i1, toFalse i2)
      in
        SOME (Leaf [fmTrue, fmFalse], m2, a2)
      end
  | Const (@{const_name HOL.conj}, _) $ t1 =>
      SOME (interpret ctxt model args (eta_expand t 1))
  | Const (@{const_name HOL.conj}, _) =>
      SOME (interpret ctxt model args (eta_expand t 2))
      (* this would make "undef" propagate, even for formulae like *)
      (* "False & undef":                                          *)
      (* SOME (Node [Node [TT, FF], Node [FF, FF]], model, args) *)
  | Const (@{const_name HOL.disj}, _) $ t1 $ t2 =>
      (* 3-valued logic *)
      let
        val (i1, m1, a1) = interpret ctxt model args t1
        val (i2, m2, a2) = interpret ctxt m1 a1 t2
        val fmTrue = Prop_Logic.SOr (toTrue i1, toTrue i2)
        val fmFalse = Prop_Logic.SAnd (toFalse i1, toFalse i2)
      in
        SOME (Leaf [fmTrue, fmFalse], m2, a2)
      end
  | Const (@{const_name HOL.disj}, _) $ t1 =>
      SOME (interpret ctxt model args (eta_expand t 1))
  | Const (@{const_name HOL.disj}, _) =>
      SOME (interpret ctxt model args (eta_expand t 2))
      (* this would make "undef" propagate, even for formulae like *)
      (* "True | undef":                                           *)
      (* SOME (Node [Node [TT, TT], Node [TT, FF]], model, args) *)
  | Const (@{const_name HOL.implies}, _) $ t1 $ t2 =>  (* similar to "==>" (Pure) *)
      (* 3-valued logic *)
      let
        val (i1, m1, a1) = interpret ctxt model args t1
        val (i2, m2, a2) = interpret ctxt m1 a1 t2
        val fmTrue = Prop_Logic.SOr (toFalse i1, toTrue i2)
        val fmFalse = Prop_Logic.SAnd (toTrue i1, toFalse i2)
      in
        SOME (Leaf [fmTrue, fmFalse], m2, a2)
      end
  | Const (@{const_name HOL.implies}, _) $ t1 =>
      SOME (interpret ctxt model args (eta_expand t 1))
  | Const (@{const_name HOL.implies}, _) =>
      SOME (interpret ctxt model args (eta_expand t 2))
      (* this would make "undef" propagate, even for formulae like *)
      (* "False --> undef":                                        *)
      (* SOME (Node [Node [TT, FF], Node [TT, TT]], model, args) *)
  | _ => NONE;

(* interprets variables and constants whose type is an IDT (this is        *)
(* relatively easy and merely requires us to compute the size of the IDT); *)
(* constructors of IDTs however are properly interpreted by                *)
(* 'IDT_constructor_interpreter'                                           *)

fun IDT_interpreter ctxt model args t =
  let
    val thy = Proof_Context.theory_of ctxt
    val (typs, terms) = model
    (* Term.typ -> (interpretation * model * arguments) option *)
    fun interpret_term (Type (s, Ts)) =
          (case Datatype.get_info thy s of
            SOME info =>  (* inductive datatype *)
              let
                (* int option -- only recursive IDTs have an associated depth *)
                val depth = AList.lookup (op =) typs (Type (s, Ts))
                (* sanity check: depth must be at least 0 *)
                val _ =
                  (case depth of SOME n =>
                    if n < 0 then
                      raise REFUTE ("IDT_interpreter", "negative depth")
                    else ()
                  | _ => ())
              in
                (* termination condition to avoid infinite recursion *)
                if depth = (SOME 0) then
                  (* return a leaf of size 0 *)
                  SOME (Leaf [], model, args)
                else
                  let
                    val index               = #index info
                    val descr               = #descr info
                    val (_, dtyps, constrs) = the (AList.lookup (op =) descr index)
                    val typ_assoc           = dtyps ~~ Ts
                    (* sanity check: every element in 'dtyps' must be a 'DtTFree' *)
                    val _ =
                      if Library.exists (fn d =>
                        case d of Datatype_Aux.DtTFree _ => false | _ => true) dtyps
                      then
                        raise REFUTE ("IDT_interpreter",
                          "datatype argument (for type "
                          ^ Syntax.string_of_typ ctxt (Type (s, Ts))
                          ^ ") is not a variable")
                      else ()
                    (* if the model specifies a depth for the current type, *)
                    (* decrement it to avoid infinite recursion             *)
                    val typs' = case depth of NONE => typs | SOME n =>
                      AList.update (op =) (Type (s, Ts), n-1) typs
                    (* recursively compute the size of the datatype *)
                    val size     = size_of_dtyp ctxt typs' descr typ_assoc constrs
                    val next_idx = #next_idx args
                    val next     = next_idx+size
                    (* check if 'maxvars' is large enough *)
                    val _        = (if next-1 > #maxvars args andalso
                      #maxvars args > 0 then raise MAXVARS_EXCEEDED else ())
                    (* prop_formula list *)
                    val fms      = map BoolVar (next_idx upto (next_idx+size-1))
                    (* interpretation *)
                    val intr     = Leaf fms
                    (* prop_formula list -> prop_formula *)
                    fun one_of_two_false [] = True
                      | one_of_two_false (x::xs) = SAnd (Prop_Logic.all (map (fn x' =>
                          SOr (SNot x, SNot x')) xs), one_of_two_false xs)
                    (* prop_formula *)
                    val wf = one_of_two_false fms
                  in
                    (* extend the model, increase 'next_idx', add well-formedness *)
                    (* condition                                                  *)
                    SOME (intr, (typs, (t, intr)::terms), {maxvars = #maxvars args,
                      def_eq = #def_eq args, next_idx = next, bounds = #bounds args,
                      wellformed = SAnd (#wellformed args, wf)})
                  end
              end
          | NONE =>  (* not an inductive datatype *)
              NONE)
      | interpret_term _ =  (* a (free or schematic) type variable *)
          NONE
  in
    case AList.lookup (op =) terms t of
      SOME intr =>
        (* return an existing interpretation *)
        SOME (intr, model, args)
    | NONE =>
        (case t of
          Free (_, T) => interpret_term T
        | Var (_, T) => interpret_term T
        | Const (_, T) => interpret_term T
        | _ => NONE)
  end;

(* This function imposes an order on the elements of a datatype fragment  *)
(* as follows: C_i x_1 ... x_n < C_j y_1 ... y_m iff i < j or             *)
(* (x_1, ..., x_n) < (y_1, ..., y_m).  With this order, a constructor is  *)
(* a function C_i that maps some argument indices x_1, ..., x_n to the    *)
(* datatype element given by index C_i x_1 ... x_n.  The idea remains the *)
(* same for recursive datatypes, although the computation of indices gets *)
(* a little tricky.                                                       *)

fun IDT_constructor_interpreter ctxt model args t =
  let
    val thy = Proof_Context.theory_of ctxt
    (* returns a list of canonical representations for terms of the type 'T' *)
    (* It would be nice if we could just use 'print' for this, but 'print'   *)
    (* for IDTs calls 'IDT_constructor_interpreter' again, and this could    *)
    (* lead to infinite recursion when we have (mutually) recursive IDTs.    *)
    (* (Term.typ * int) list -> Term.typ -> Term.term list *)
    fun canonical_terms typs T =
          (case T of
            Type ("fun", [T1, T2]) =>
            (* 'T2' might contain a recursive IDT, so we cannot use 'print' (at *)
            (* least not for 'T2'                                               *)
            let
              (* returns a list of lists, each one consisting of n (possibly *)
              (* identical) elements from 'xs'                               *)
              (* int -> 'a list -> 'a list list *)
              fun pick_all 1 xs = map single xs
                | pick_all n xs =
                    let val rec_pick = pick_all (n-1) xs in
                      maps (fn x => map (cons x) rec_pick) xs
                    end
              (* ["x1", ..., "xn"] *)
              val terms1 = canonical_terms typs T1
              (* ["y1", ..., "ym"] *)
              val terms2 = canonical_terms typs T2
              (* [[("x1", "y1"), ..., ("xn", "y1")], ..., *)
              (*   [("x1", "ym"), ..., ("xn", "ym")]]     *)
              val functions = map (curry (op ~~) terms1)
                (pick_all (length terms1) terms2)
              (* [["(x1, y1)", ..., "(xn, y1)"], ..., *)
              (*   ["(x1, ym)", ..., "(xn, ym)"]]     *)
              val pairss = map (map HOLogic.mk_prod) functions
              (* Term.typ *)
              val HOLogic_prodT = HOLogic.mk_prodT (T1, T2)
              val HOLogic_setT  = HOLogic.mk_setT HOLogic_prodT
              (* Term.term *)
              val HOLogic_empty_set = Const (@{const_abbrev Set.empty}, HOLogic_setT)
              val HOLogic_insert    =
                Const (@{const_name insert}, HOLogic_prodT --> HOLogic_setT --> HOLogic_setT)
            in
              (* functions as graphs, i.e. as a (HOL) set of pairs "(x, y)" *)
              map (fn ps => fold_rev (fn pair => fn acc => HOLogic_insert $ pair $ acc) ps
                HOLogic_empty_set) pairss
            end
      | Type (s, Ts) =>
          (case Datatype.get_info thy s of
            SOME info =>
              (case AList.lookup (op =) typs T of
                SOME 0 =>
                  (* termination condition to avoid infinite recursion *)
                  []  (* at depth 0, every IDT is empty *)
              | _ =>
                let
                  val index = #index info
                  val descr = #descr info
                  val (_, dtyps, constrs) = the (AList.lookup (op =) descr index)
                  val typ_assoc = dtyps ~~ Ts
                  (* sanity check: every element in 'dtyps' must be a 'DtTFree' *)
                  val _ =
                    if Library.exists (fn d =>
                      case d of Datatype_Aux.DtTFree _ => false | _ => true) dtyps
                    then
                      raise REFUTE ("IDT_constructor_interpreter",
                        "datatype argument (for type "
                        ^ Syntax.string_of_typ ctxt T
                        ^ ") is not a variable")
                    else ()
                  (* decrement depth for the IDT 'T' *)
                  val typs' =
                    (case AList.lookup (op =) typs T of NONE => typs
                    | SOME n => AList.update (op =) (T, n-1) typs)
                  fun constructor_terms terms [] = terms
                    | constructor_terms terms (d::ds) =
                        let
                          val dT = typ_of_dtyp descr typ_assoc d
                          val d_terms = canonical_terms typs' dT
                        in
                          (* C_i x_1 ... x_n < C_i y_1 ... y_n if *)
                          (* (x_1, ..., x_n) < (y_1, ..., y_n)    *)
                          constructor_terms
                            (map_product (curry op $) terms d_terms) ds
                        end
                in
                  (* C_i ... < C_j ... if i < j *)
                  maps (fn (cname, ctyps) =>
                    let
                      val cTerm = Const (cname,
                        map (typ_of_dtyp descr typ_assoc) ctyps ---> T)
                    in
                      constructor_terms [cTerm] ctyps
                    end) constrs
                end)
          | NONE =>
              (* not an inductive datatype; in this case the argument types in *)
              (* 'Ts' may not be IDTs either, so 'print' should be safe        *)
              map (fn intr => print ctxt (typs, []) T intr (K false))
                (make_constants ctxt (typs, []) T))
      | _ =>  (* TFree ..., TVar ... *)
          map (fn intr => print ctxt (typs, []) T intr (K false))
            (make_constants ctxt (typs, []) T))
    val (typs, terms) = model
  in
    case AList.lookup (op =) terms t of
      SOME intr =>
        (* return an existing interpretation *)
        SOME (intr, model, args)
    | NONE =>
        (case t of
          Const (s, T) =>
            (case body_type T of
              Type (s', Ts') =>
                (case Datatype.get_info thy s' of
                  SOME info =>  (* body type is an inductive datatype *)
                    let
                      val index               = #index info
                      val descr               = #descr info
                      val (_, dtyps, constrs) = the (AList.lookup (op =) descr index)
                      val typ_assoc           = dtyps ~~ Ts'
                      (* sanity check: every element in 'dtyps' must be a 'DtTFree' *)
                      val _ = if Library.exists (fn d =>
                          case d of Datatype_Aux.DtTFree _ => false | _ => true) dtyps
                        then
                          raise REFUTE ("IDT_constructor_interpreter",
                            "datatype argument (for type "
                            ^ Syntax.string_of_typ ctxt (Type (s', Ts'))
                            ^ ") is not a variable")
                        else ()
                      (* split the constructors into those occuring before/after *)
                      (* 'Const (s, T)'                                          *)
                      val (constrs1, constrs2) = take_prefix (fn (cname, ctypes) =>
                        not (cname = s andalso Sign.typ_instance thy (T,
                          map (typ_of_dtyp descr typ_assoc) ctypes
                            ---> Type (s', Ts')))) constrs
                    in
                      case constrs2 of
                        [] =>
                          (* 'Const (s, T)' is not a constructor of this datatype *)
                          NONE
                      | (_, ctypes)::cs =>
                          let
                            (* int option -- only /recursive/ IDTs have an associated *)
                            (*               depth                                    *)
                            val depth = AList.lookup (op =) typs (Type (s', Ts'))
                            (* this should never happen: at depth 0, this IDT fragment *)
                            (* is definitely empty, and in this case we don't need to  *)
                            (* interpret its constructors                              *)
                            val _ = (case depth of SOME 0 =>
                                raise REFUTE ("IDT_constructor_interpreter",
                                  "depth is 0")
                              | _ => ())
                            val typs' = (case depth of NONE => typs | SOME n =>
                              AList.update (op =) (Type (s', Ts'), n-1) typs)
                            (* elements of the datatype come before elements generated *)
                            (* by 'Const (s, T)' iff they are generated by a           *)
                            (* constructor in constrs1                                 *)
                            val offset = size_of_dtyp ctxt typs' descr typ_assoc constrs1
                            (* compute the total (current) size of the datatype *)
                            val total = offset +
                              size_of_dtyp ctxt typs' descr typ_assoc constrs2
                            (* sanity check *)
                            val _ = if total <> size_of_type ctxt (typs, [])
                              (Type (s', Ts')) then
                                raise REFUTE ("IDT_constructor_interpreter",
                                  "total is not equal to current size")
                              else ()
                            (* returns an interpretation where everything is mapped to *)
                            (* an "undefined" element of the datatype                  *)
                            fun make_undef [] = Leaf (replicate total False)
                              | make_undef (d::ds) =
                                  let
                                    (* compute the current size of the type 'd' *)
                                    val dT   = typ_of_dtyp descr typ_assoc d
                                    val size = size_of_type ctxt (typs, []) dT
                                  in
                                    Node (replicate size (make_undef ds))
                                  end
                            (* returns the interpretation for a constructor *)
                            fun make_constr [] offset =
                                  if offset < total then
                                    (Leaf (replicate offset False @ True ::
                                      (replicate (total - offset - 1) False)), offset + 1)
                                  else
                                    raise REFUTE ("IDT_constructor_interpreter",
                                      "offset >= total")
                              | make_constr (d::ds) offset =
                                  let
                                    (* Term.typ *)
                                    val dT = typ_of_dtyp descr typ_assoc d
                                    (* compute canonical term representations for all   *)
                                    (* elements of the type 'd' (with the reduced depth *)
                                    (* for the IDT)                                     *)
                                    val terms' = canonical_terms typs' dT
                                    (* sanity check *)
                                    val _ =
                                      if length terms' <> size_of_type ctxt (typs', []) dT
                                      then
                                        raise REFUTE ("IDT_constructor_interpreter",
                                          "length of terms' is not equal to old size")
                                      else ()
                                    (* compute canonical term representations for all   *)
                                    (* elements of the type 'd' (with the current depth *)
                                    (* for the IDT)                                     *)
                                    val terms = canonical_terms typs dT
                                    (* sanity check *)
                                    val _ =
                                      if length terms <> size_of_type ctxt (typs, []) dT
                                      then
                                        raise REFUTE ("IDT_constructor_interpreter",
                                          "length of terms is not equal to current size")
                                      else ()
                                    (* sanity check *)
                                    val _ =
                                      if length terms < length terms' then
                                        raise REFUTE ("IDT_constructor_interpreter",
                                          "current size is less than old size")
                                      else ()
                                    (* sanity check: every element of terms' must also be *)
                                    (*               present in terms                     *)
                                    val _ =
                                      if forall (member (op =) terms) terms' then ()
                                      else
                                        raise REFUTE ("IDT_constructor_interpreter",
                                          "element has disappeared")
                                    (* sanity check: the order on elements of terms' is    *)
                                    (*               the same in terms, for those elements *)
                                    val _ =
                                      let
                                        fun search (x::xs) (y::ys) =
                                              if x = y then search xs ys else search (x::xs) ys
                                          | search (x::xs) [] =
                                              raise REFUTE ("IDT_constructor_interpreter",
                                                "element order not preserved")
                                          | search [] _ = ()
                                      in search terms' terms end
                                    (* int * interpretation list *)
                                    val (intrs, new_offset) =
                                      fold_map (fn t_elem => fn off =>
                                        (* if 't_elem' existed at the previous depth,    *)
                                        (* proceed recursively, otherwise map the entire *)
                                        (* subtree to "undefined"                        *)
                                        if member (op =) terms' t_elem then
                                          make_constr ds off
                                        else
                                          (make_undef ds, off))
                                      terms offset
                                  in
                                    (Node intrs, new_offset)
                                  end
                          in
                            SOME (fst (make_constr ctypes offset), model, args)
                          end
                    end
                | NONE =>  (* body type is not an inductive datatype *)
                    NONE)
            | _ =>  (* body type is a (free or schematic) type variable *)
              NONE)
        | _ =>  (* term is not a constant *)
          NONE)
  end;

(* Difficult code ahead.  Make sure you understand the                *)
(* 'IDT_constructor_interpreter' and the order in which it enumerates *)
(* elements of an IDT before you try to understand this function.     *)

fun IDT_recursion_interpreter ctxt model args t =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    (* careful: here we descend arbitrarily deep into 't', possibly before *)
    (* any other interpreter for atomic terms has had a chance to look at  *)
    (* 't'                                                                 *)
    case strip_comb t of
      (Const (s, T), params) =>
        (* iterate over all datatypes in 'thy' *)
        Symtab.fold (fn (_, info) => fn result =>
          case result of
            SOME _ =>
              result  (* just keep 'result' *)
          | NONE =>
              if member (op =) (#rec_names info) s then
                (* we do have a recursion operator of one of the (mutually *)
                (* recursive) datatypes given by 'info'                    *)
                let
                  (* number of all constructors, including those of different  *)
                  (* (mutually recursive) datatypes within the same descriptor *)
                  val mconstrs_count =
                    Integer.sum (map (fn (_, (_, _, cs)) => length cs) (#descr info))
                in
                  if mconstrs_count < length params then
                    (* too many actual parameters; for now we'll use the *)
                    (* 'stlc_interpreter' to strip off one application   *)
                    NONE
                  else if mconstrs_count > length params then
                    (* too few actual parameters; we use eta expansion          *)
                    (* Note that the resulting expansion of lambda abstractions *)
                    (* by the 'stlc_interpreter' may be rather slow (depending  *)
                    (* on the argument types and the size of the IDT, of        *)
                    (* course).                                                 *)
                    SOME (interpret ctxt model args (eta_expand t
                      (mconstrs_count - length params)))
                  else  (* mconstrs_count = length params *)
                    let
                      (* interpret each parameter separately *)
                      val (p_intrs, (model', args')) = fold_map (fn p => fn (m, a) =>
                        let
                          val (i, m', a') = interpret ctxt m a p
                        in
                          (i, (m', a'))
                        end) params (model, args)
                      val (typs, _) = model'
                      (* 'index' is /not/ necessarily the index of the IDT that *)
                      (* the recursion operator is associated with, but merely  *)
                      (* the index of some mutually recursive IDT               *)
                      val index         = #index info
                      val descr         = #descr info
                      val (_, dtyps, _) = the (AList.lookup (op =) descr index)
                      (* sanity check: we assume that the order of constructors *)
                      (*               in 'descr' is the same as the order of   *)
                      (*               corresponding parameters, otherwise the  *)
                      (*               association code below won't match the   *)
                      (*               right constructors/parameters; we also   *)
                      (*               assume that the order of recursion       *)
                      (*               operators in '#rec_names info' is the    *)
                      (*               same as the order of corresponding       *)
                      (*               datatypes in 'descr'                     *)
                      val _ = if map fst descr <> (0 upto (length descr - 1)) then
                          raise REFUTE ("IDT_recursion_interpreter",
                            "order of constructors and corresponding parameters/" ^
                              "recursion operators and corresponding datatypes " ^
                              "different?")
                        else ()
                      (* sanity check: every element in 'dtyps' must be a *)
                      (*               'DtTFree'                          *)
                      val _ =
                        if Library.exists (fn d =>
                          case d of Datatype_Aux.DtTFree _ => false
                                  | _ => true) dtyps
                        then
                          raise REFUTE ("IDT_recursion_interpreter",
                            "datatype argument is not a variable")
                        else ()
                      (* the type of a recursion operator is *)
                      (* [T1, ..., Tn, IDT] ---> Tresult     *)
                      val IDT = nth (binder_types T) mconstrs_count
                      (* by our assumption on the order of recursion operators *)
                      (* and datatypes, this is the index of the datatype      *)
                      (* corresponding to the given recursion operator         *)
                      val idt_index = find_index (fn s' => s' = s) (#rec_names info)
                      (* mutually recursive types must have the same type   *)
                      (* parameters, unless the mutual recursion comes from *)
                      (* indirect recursion                                 *)
                      fun rec_typ_assoc acc [] = acc
                        | rec_typ_assoc acc ((d, T)::xs) =
                            (case AList.lookup op= acc d of
                              NONE =>
                                (case d of
                                  Datatype_Aux.DtTFree _ =>
                                  (* add the association, proceed *)
                                  rec_typ_assoc ((d, T)::acc) xs
                                | Datatype_Aux.DtType (s, ds) =>
                                    let
                                      val (s', Ts) = dest_Type T
                                    in
                                      if s=s' then
                                        rec_typ_assoc ((d, T)::acc) ((ds ~~ Ts) @ xs)
                                      else
                                        raise REFUTE ("IDT_recursion_interpreter",
                                          "DtType/Type mismatch")
                                    end
                                | Datatype_Aux.DtRec i =>
                                    let
                                      val (_, ds, _) = the (AList.lookup (op =) descr i)
                                      val (_, Ts)    = dest_Type T
                                    in
                                      rec_typ_assoc ((d, T)::acc) ((ds ~~ Ts) @ xs)
                                    end)
                            | SOME T' =>
                                if T=T' then
                                  (* ignore the association since it's already *)
                                  (* present, proceed                          *)
                                  rec_typ_assoc acc xs
                                else
                                  raise REFUTE ("IDT_recursion_interpreter",
                                    "different type associations for the same dtyp"))
                      val typ_assoc = filter
                        (fn (Datatype_Aux.DtTFree _, _) => true | (_, _) => false)
                        (rec_typ_assoc []
                          (#2 (the (AList.lookup (op =) descr idt_index)) ~~ (snd o dest_Type) IDT))
                      (* sanity check: typ_assoc must associate types to the   *)
                      (*               elements of 'dtyps' (and only to those) *)
                      val _ =
                        if not (eq_set (op =) (dtyps, map fst typ_assoc))
                        then
                          raise REFUTE ("IDT_recursion_interpreter",
                            "type association has extra/missing elements")
                        else ()
                      (* interpret each constructor in the descriptor (including *)
                      (* those of mutually recursive datatypes)                  *)
                      (* (int * interpretation list) list *)
                      val mc_intrs = map (fn (idx, (_, _, cs)) =>
                        let
                          val c_return_typ = typ_of_dtyp descr typ_assoc
                            (Datatype_Aux.DtRec idx)
                        in
                          (idx, map (fn (cname, cargs) =>
                            (#1 o interpret ctxt (typs, []) {maxvars=0,
                              def_eq=false, next_idx=1, bounds=[],
                              wellformed=True}) (Const (cname, map (typ_of_dtyp
                              descr typ_assoc) cargs ---> c_return_typ))) cs)
                        end) descr
                      (* associate constructors with corresponding parameters *)
                      (* (int * (interpretation * interpretation) list) list *)
                      val (mc_p_intrs, p_intrs') = fold_map
                        (fn (idx, c_intrs) => fn p_intrs' =>
                          let
                            val len = length c_intrs
                          in
                            ((idx, c_intrs ~~ List.take (p_intrs', len)),
                              List.drop (p_intrs', len))
                          end) mc_intrs p_intrs
                      (* sanity check: no 'p_intr' may be left afterwards *)
                      val _ =
                        if p_intrs' <> [] then
                          raise REFUTE ("IDT_recursion_interpreter",
                            "more parameter than constructor interpretations")
                        else ()
                      (* The recursion operator, applied to 'mconstrs_count'     *)
                      (* arguments, is a function that maps every element of the *)
                      (* inductive datatype to an element of some result type.   *)
                      (* Recursion operators for mutually recursive IDTs are     *)
                      (* translated simultaneously.                              *)
                      (* Since the order on datatype elements is given by an     *)
                      (* order on constructors (and then by the order on         *)
                      (* argument tuples), we can simply copy corresponding      *)
                      (* subtrees from 'p_intrs', in the order in which they are *)
                      (* given.                                                  *)
                      (* interpretation * interpretation -> interpretation list *)
                      fun ci_pi (Leaf xs, pi) =
                            (* if the constructor does not match the arguments to a *)
                            (* defined element of the IDT, the corresponding value  *)
                            (* of the parameter must be ignored                     *)
                            if List.exists (equal True) xs then [pi] else []
                        | ci_pi (Node xs, Node ys) = maps ci_pi (xs ~~ ys)
                        | ci_pi (Node _, Leaf _) =
                            raise REFUTE ("IDT_recursion_interpreter",
                              "constructor takes more arguments than the " ^
                                "associated parameter")
                      (* (int * interpretation list) list *)
                      val rec_operators = map (fn (idx, c_p_intrs) =>
                        (idx, maps ci_pi c_p_intrs)) mc_p_intrs
                      (* sanity check: every recursion operator must provide as  *)
                      (*               many values as the corresponding datatype *)
                      (*               has elements                              *)
                      val _ = map (fn (idx, intrs) =>
                        let
                          val T = typ_of_dtyp descr typ_assoc
                            (Datatype_Aux.DtRec idx)
                        in
                          if length intrs <> size_of_type ctxt (typs, []) T then
                            raise REFUTE ("IDT_recursion_interpreter",
                              "wrong number of interpretations for rec. operator")
                          else ()
                        end) rec_operators
                      (* For non-recursive datatypes, we are pretty much done at *)
                      (* this point.  For recursive datatypes however, we still  *)
                      (* need to apply the interpretations in 'rec_operators' to *)
                      (* (recursively obtained) interpretations for recursive    *)
                      (* constructor arguments.  To do so more efficiently, we   *)
                      (* copy 'rec_operators' into arrays first.  Each Boolean   *)
                      (* indicates whether the recursive arguments have been     *)
                      (* considered already.                                     *)
                      (* (int * (bool * interpretation) Array.array) list *)
                      val REC_OPERATORS = map (fn (idx, intrs) =>
                        (idx, Array.fromList (map (pair false) intrs)))
                        rec_operators
                      (* takes an interpretation, and if some leaf of this     *)
                      (* interpretation is the 'elem'-th element of the type,  *)
                      (* the indices of the arguments leading to this leaf are *)
                      (* returned                                              *)
                      (* interpretation -> int -> int list option *)
                      fun get_args (Leaf xs) elem =
                            if find_index (fn x => x = True) xs = elem then
                              SOME []
                            else
                              NONE
                        | get_args (Node xs) elem =
                            let
                              (* interpretation list * int -> int list option *)
                              fun search ([], _) =
                                NONE
                                | search (x::xs, n) =
                                (case get_args x elem of
                                  SOME result => SOME (n::result)
                                | NONE        => search (xs, n+1))
                            in
                              search (xs, 0)
                            end
                      (* returns the index of the constructor and indices for *)
                      (* its arguments that generate the 'elem'-th element of *)
                      (* the datatype given by 'idx'                          *)
                      (* int -> int -> int * int list *)
                      fun get_cargs idx elem =
                        let
                          (* int * interpretation list -> int * int list *)
                          fun get_cargs_rec (_, []) =
                                raise REFUTE ("IDT_recursion_interpreter",
                                  "no matching constructor found for datatype element")
                            | get_cargs_rec (n, x::xs) =
                                (case get_args x elem of
                                  SOME args => (n, args)
                                | NONE => get_cargs_rec (n+1, xs))
                        in
                          get_cargs_rec (0, the (AList.lookup (op =) mc_intrs idx))
                        end
                      (* computes one entry in 'REC_OPERATORS', and recursively *)
                      (* all entries needed for it, where 'idx' gives the       *)
                      (* datatype and 'elem' the element of it                  *)
                      (* int -> int -> interpretation *)
                      fun compute_array_entry idx elem =
                        let
                          val arr = the (AList.lookup (op =) REC_OPERATORS idx)
                          val (flag, intr) = Array.sub (arr, elem)
                        in
                          if flag then
                            (* simply return the previously computed result *)
                            intr
                          else
                            (* we have to apply 'intr' to interpretations for all *)
                            (* recursive arguments                                *)
                            let
                              (* int * int list *)
                              val (c, args) = get_cargs idx elem
                              (* find the indices of the constructor's /recursive/ *)
                              (* arguments                                         *)
                              val (_, _, constrs) = the (AList.lookup (op =) descr idx)
                              val (_, dtyps) = nth constrs c
                              val rec_dtyps_args = filter
                                (Datatype_Aux.is_rec_type o fst) (dtyps ~~ args)
                              (* map those indices to interpretations *)
                              val rec_dtyps_intrs = map (fn (dtyp, arg) =>
                                let
                                  val dT = typ_of_dtyp descr typ_assoc dtyp
                                  val consts = make_constants ctxt (typs, []) dT
                                  val arg_i = nth consts arg
                                in
                                  (dtyp, arg_i)
                                end) rec_dtyps_args
                              (* takes the dtyp and interpretation of an element, *)
                              (* and computes the interpretation for the          *)
                              (* corresponding recursive argument                 *)
                              fun rec_intr (Datatype_Aux.DtRec i) (Leaf xs) =
                                    (* recursive argument is "rec_i params elem" *)
                                    compute_array_entry i (find_index (fn x => x = True) xs)
                                | rec_intr (Datatype_Aux.DtRec _) (Node _) =
                                    raise REFUTE ("IDT_recursion_interpreter",
                                      "interpretation for IDT is a node")
                                | rec_intr (Datatype_Aux.DtType ("fun", [dt1, dt2])) (Node xs) =
                                    (* recursive argument is something like     *)
                                    (* "\<lambda>x::dt1. rec_? params (elem x)" *)
                                    Node (map (rec_intr dt2) xs)
                                | rec_intr (Datatype_Aux.DtType ("fun", [_, _])) (Leaf _) =
                                    raise REFUTE ("IDT_recursion_interpreter",
                                      "interpretation for function dtyp is a leaf")
                                | rec_intr _ _ =
                                    (* admissibility ensures that every recursive type *)
                                    (* is of the form 'Dt_1 -> ... -> Dt_k ->          *)
                                    (* (DtRec i)'                                      *)
                                    raise REFUTE ("IDT_recursion_interpreter",
                                      "non-recursive codomain in recursive dtyp")
                              (* obtain interpretations for recursive arguments *)
                              (* interpretation list *)
                              val arg_intrs = map (uncurry rec_intr) rec_dtyps_intrs
                              (* apply 'intr' to all recursive arguments *)
                              val result = fold (fn arg_i => fn i =>
                                interpretation_apply (i, arg_i)) arg_intrs intr
                              (* update 'REC_OPERATORS' *)
                              val _ = Array.update (arr, elem, (true, result))
                            in
                              result
                            end
                        end
                      val idt_size = Array.length (the (AList.lookup (op =) REC_OPERATORS idt_index))
                      (* sanity check: the size of 'IDT' should be 'idt_size' *)
                      val _ =
                          if idt_size <> size_of_type ctxt (typs, []) IDT then
                            raise REFUTE ("IDT_recursion_interpreter",
                              "unexpected size of IDT (wrong type associated?)")
                          else ()
                      (* interpretation *)
                      val rec_op = Node (map_range (compute_array_entry idt_index) idt_size)
                    in
                      SOME (rec_op, model', args')
                    end
                end
              else
                NONE  (* not a recursion operator of this datatype *)
          ) (Datatype.get_all thy) NONE
    | _ =>  (* head of term is not a constant *)
      NONE
  end;

fun set_interpreter ctxt model args t =
  let
    val (typs, terms) = model
  in
    case AList.lookup (op =) terms t of
      SOME intr =>
        (* return an existing interpretation *)
        SOME (intr, model, args)
    | NONE =>
        (case t of
        (* 'Collect' == identity *)
          Const (@{const_name Collect}, _) $ t1 =>
            SOME (interpret ctxt model args t1)
        | Const (@{const_name Collect}, _) =>
            SOME (interpret ctxt model args (eta_expand t 1))
        (* 'op :' == application *)
        | Const (@{const_name Set.member}, _) $ t1 $ t2 =>
            SOME (interpret ctxt model args (t2 $ t1))
        | Const (@{const_name Set.member}, _) $ t1 =>
            SOME (interpret ctxt model args (eta_expand t 1))
        | Const (@{const_name Set.member}, _) =>
            SOME (interpret ctxt model args (eta_expand t 2))
        | _ => NONE)
  end;

(* only an optimization: 'card' could in principle be interpreted with *)
(* interpreters available already (using its definition), but the code *)
(* below is more efficient                                             *)

fun Finite_Set_card_interpreter ctxt model args t =
  case t of
    Const (@{const_name Finite_Set.card},
        Type ("fun", [Type ("fun", [T, @{typ bool}]), @{typ nat}])) =>
      let
        (* interpretation -> int *)
        fun number_of_elements (Node xs) =
            fold (fn x => fn n =>
              if x = TT then
                n + 1
              else if x = FF then
                n
              else
                raise REFUTE ("Finite_Set_card_interpreter",
                  "interpretation for set type does not yield a Boolean"))
              xs 0
          | number_of_elements (Leaf _) =
              raise REFUTE ("Finite_Set_card_interpreter",
                "interpretation for set type is a leaf")
        val size_of_nat = size_of_type ctxt model (@{typ nat})
        (* takes an interpretation for a set and returns an interpretation *)
        (* for a 'nat' denoting the set's cardinality                      *)
        (* interpretation -> interpretation *)
        fun card i =
          let
            val n = number_of_elements i
          in
            if n < size_of_nat then
              Leaf ((replicate n False) @ True ::
                (replicate (size_of_nat-n-1) False))
            else
              Leaf (replicate size_of_nat False)
          end
        val set_constants =
          make_constants ctxt model (Type ("fun", [T, HOLogic.boolT]))
      in
        SOME (Node (map card set_constants), model, args)
      end
  | _ => NONE;

(* only an optimization: 'finite' could in principle be interpreted with  *)
(* interpreters available already (using its definition), but the code    *)
(* below is more efficient                                                *)

fun Finite_Set_finite_interpreter ctxt model args t =
  case t of
    Const (@{const_name Finite_Set.finite},
      Type ("fun", [Type ("fun", [T, @{typ bool}]),
                    @{typ bool}])) $ _ =>
        (* we only consider finite models anyway, hence EVERY set is *)
        (* "finite"                                                  *)
        SOME (TT, model, args)
  | Const (@{const_name Finite_Set.finite},
      Type ("fun", [Type ("fun", [T, @{typ bool}]),
                    @{typ bool}])) =>
      let
        val size_of_set =
          size_of_type ctxt model (Type ("fun", [T, HOLogic.boolT]))
      in
        (* we only consider finite models anyway, hence EVERY set is *)
        (* "finite"                                                  *)
        SOME (Node (replicate size_of_set TT), model, args)
      end
  | _ => NONE;

(* only an optimization: 'less' could in principle be interpreted with *)
(* interpreters available already (using its definition), but the code     *)
(* below is more efficient                                                 *)

fun Nat_less_interpreter ctxt model args t =
  case t of
    Const (@{const_name Orderings.less}, Type ("fun", [@{typ nat},
        Type ("fun", [@{typ nat}, @{typ bool}])])) =>
      let
        val size_of_nat = size_of_type ctxt model (@{typ nat})
        (* the 'n'-th nat is not less than the first 'n' nats, while it *)
        (* is less than the remaining 'size_of_nat - n' nats            *)
        (* int -> interpretation *)
        fun less n = Node ((replicate n FF) @ (replicate (size_of_nat - n) TT))
      in
        SOME (Node (map less (1 upto size_of_nat)), model, args)
      end
  | _ => NONE;

(* only an optimization: 'plus' could in principle be interpreted with *)
(* interpreters available already (using its definition), but the code     *)
(* below is more efficient                                                 *)

fun Nat_plus_interpreter ctxt model args t =
  case t of
    Const (@{const_name Groups.plus}, Type ("fun", [@{typ nat},
        Type ("fun", [@{typ nat}, @{typ nat}])])) =>
      let
        val size_of_nat = size_of_type ctxt model (@{typ nat})
        (* int -> int -> interpretation *)
        fun plus m n =
          let
            val element = m + n
          in
            if element > size_of_nat - 1 then
              Leaf (replicate size_of_nat False)
            else
              Leaf ((replicate element False) @ True ::
                (replicate (size_of_nat - element - 1) False))
          end
      in
        SOME (Node (map_range (fn m => Node (map_range (plus m) size_of_nat)) size_of_nat),
          model, args)
      end
  | _ => NONE;

(* only an optimization: 'minus' could in principle be interpreted *)
(* with interpreters available already (using its definition), but the *)
(* code below is more efficient                                        *)

fun Nat_minus_interpreter ctxt model args t =
  case t of
    Const (@{const_name Groups.minus}, Type ("fun", [@{typ nat},
        Type ("fun", [@{typ nat}, @{typ nat}])])) =>
      let
        val size_of_nat = size_of_type ctxt model (@{typ nat})
        (* int -> int -> interpretation *)
        fun minus m n =
          let
            val element = Int.max (m-n, 0)
          in
            Leaf ((replicate element False) @ True ::
              (replicate (size_of_nat - element - 1) False))
          end
      in
        SOME (Node (map_range (fn m => Node (map_range (minus m) size_of_nat)) size_of_nat),
          model, args)
      end
  | _ => NONE;

(* only an optimization: 'times' could in principle be interpreted *)
(* with interpreters available already (using its definition), but the *)
(* code below is more efficient                                        *)

fun Nat_times_interpreter ctxt model args t =
  case t of
    Const (@{const_name Groups.times}, Type ("fun", [@{typ nat},
        Type ("fun", [@{typ nat}, @{typ nat}])])) =>
      let
        val size_of_nat = size_of_type ctxt model (@{typ nat})
        (* nat -> nat -> interpretation *)
        fun mult m n =
          let
            val element = m * n
          in
            if element > size_of_nat - 1 then
              Leaf (replicate size_of_nat False)
            else
              Leaf ((replicate element False) @ True ::
                (replicate (size_of_nat - element - 1) False))
          end
      in
        SOME (Node (map_range (fn m => Node (map_range (mult m) size_of_nat)) size_of_nat),
          model, args)
      end
  | _ => NONE;

(* only an optimization: 'append' could in principle be interpreted with *)
(* interpreters available already (using its definition), but the code   *)
(* below is more efficient                                               *)

fun List_append_interpreter ctxt model args t =
  case t of
    Const (@{const_name List.append}, Type ("fun", [Type ("List.list", [T]), Type ("fun",
        [Type ("List.list", [_]), Type ("List.list", [_])])])) =>
      let
        val size_elem = size_of_type ctxt model T
        val size_list = size_of_type ctxt model (Type ("List.list", [T]))
        (* maximal length of lists; 0 if we only consider the empty list *)
        val list_length =
          let
            (* int -> int -> int -> int *)
            fun list_length_acc len lists total =
              if lists = total then
                len
              else if lists < total then
                list_length_acc (len+1) (lists*size_elem) (total-lists)
              else
                raise REFUTE ("List_append_interpreter",
                  "size_list not equal to 1 + size_elem + ... + " ^
                    "size_elem^len, for some len")
          in
            list_length_acc 0 1 size_list
          end
        val elements = 0 upto (size_list-1)
        (* FIXME: there should be a nice formula, which computes the same as *)
        (*        the following, but without all this intermediate tree      *)
        (*        length/offset stuff                                        *)
        (* associate each list with its length and offset in a complete tree *)
        (* of width 'size_elem' and depth 'length_list' (with 'size_list'    *)
        (* nodes total)                                                      *)
        (* (int * (int * int)) list *)
        val (lenoff_lists, _) = fold_map (fn elem => fn (offsets, off) =>
          (* corresponds to a pre-order traversal of the tree *)
          let
            val len = length offsets
            (* associate the given element with len/off *)
            val assoc = (elem, (len, off))
          in
            if len < list_length then
              (* go to first child node *)
              (assoc, (off :: offsets, off * size_elem))
            else if off mod size_elem < size_elem - 1 then
              (* go to next sibling node *)
              (assoc, (offsets, off + 1))
            else
              (* go back up the stack until we find a level where we can go *)
              (* to the next sibling node                                   *)
              let
                val offsets' = snd (chop_while
                  (fn off' => off' mod size_elem = size_elem - 1) offsets)
              in
                case offsets' of
                  [] =>
                    (* we're at the last node in the tree; the next value *)
                    (* won't be used anyway                               *)
                    (assoc, ([], 0))
                | off'::offs' =>
                    (* go to next sibling node *)
                    (assoc, (offs', off' + 1))
              end
          end) elements ([], 0)
        (* we also need the reverse association (from length/offset to *)
        (* index)                                                      *)
        val lenoff'_lists = map Library.swap lenoff_lists
        (* returns the interpretation for "(list no. m) @ (list no. n)" *)
        (* nat -> nat -> interpretation *)
        fun append m n =
          let
            val (len_m, off_m) = the (AList.lookup (op =) lenoff_lists m)
            val (len_n, off_n) = the (AList.lookup (op =) lenoff_lists n)
            val len_elem = len_m + len_n
            val off_elem = off_m * Integer.pow len_n size_elem + off_n
          in
            case AList.lookup op= lenoff'_lists (len_elem, off_elem) of
              NONE =>
                (* undefined *)
                Leaf (replicate size_list False)
            | SOME element =>
                Leaf ((replicate element False) @ True ::
                  (replicate (size_list - element - 1) False))
          end
      in
        SOME (Node (map (fn m => Node (map (append m) elements)) elements),
          model, args)
      end
  | _ => NONE;

(* UNSOUND

(* only an optimization: 'lfp' could in principle be interpreted with  *)
(* interpreters available already (using its definition), but the code *)
(* below is more efficient                                             *)

fun lfp_interpreter ctxt model args t =
  case t of
    Const (@{const_name lfp}, Type ("fun", [Type ("fun",
      [Type ("fun", [T, @{typ bool}]),
       Type ("fun", [_, @{typ bool}])]),
       Type ("fun", [_, @{typ bool}])])) =>
      let
        val size_elem = size_of_type ctxt model T
        (* the universe (i.e. the set that contains every element) *)
        val i_univ = Node (replicate size_elem TT)
        (* all sets with elements from type 'T' *)
        val i_sets =
          make_constants ctxt model (Type ("fun", [T, HOLogic.boolT]))
        (* all functions that map sets to sets *)
        val i_funs = make_constants ctxt model (Type ("fun",
          [Type ("fun", [T, @{typ bool}]),
           Type ("fun", [T, @{typ bool}])]))
        (* "lfp(f) == Inter({u. f(u) <= u})" *)
        (* interpretation * interpretation -> bool *)
        fun is_subset (Node subs, Node sups) =
              forall (fn (sub, sup) => (sub = FF) orelse (sup = TT)) (subs ~~ sups)
          | is_subset (_, _) =
              raise REFUTE ("lfp_interpreter",
                "is_subset: interpretation for set is not a node")
        (* interpretation * interpretation -> interpretation *)
        fun intersection (Node xs, Node ys) =
              Node (map (fn (x, y) => if x=TT andalso y=TT then TT else FF)
                (xs ~~ ys))
          | intersection (_, _) =
              raise REFUTE ("lfp_interpreter",
                "intersection: interpretation for set is not a node")
        (* interpretation -> interpretaion *)
        fun lfp (Node resultsets) =
              fold (fn (set, resultset) => fn acc =>
                if is_subset (resultset, set) then
                  intersection (acc, set)
                else
                  acc) (i_sets ~~ resultsets) i_univ
          | lfp _ =
              raise REFUTE ("lfp_interpreter",
                "lfp: interpretation for function is not a node")
      in
        SOME (Node (map lfp i_funs), model, args)
      end
  | _ => NONE;

(* only an optimization: 'gfp' could in principle be interpreted with  *)
(* interpreters available already (using its definition), but the code *)
(* below is more efficient                                             *)

fun gfp_interpreter ctxt model args t =
  case t of
    Const (@{const_name gfp}, Type ("fun", [Type ("fun",
      [Type ("fun", [T, @{typ bool}]),
       Type ("fun", [_, @{typ bool}])]),
       Type ("fun", [_, @{typ bool}])])) =>
    let
      val size_elem = size_of_type ctxt model T
      (* the universe (i.e. the set that contains every element) *)
      val i_univ = Node (replicate size_elem TT)
      (* all sets with elements from type 'T' *)
      val i_sets =
        make_constants ctxt model (Type ("fun", [T, HOLogic.boolT]))
      (* all functions that map sets to sets *)
      val i_funs = make_constants ctxt model (Type ("fun",
        [Type ("fun", [T, HOLogic.boolT]),
         Type ("fun", [T, HOLogic.boolT])]))
      (* "gfp(f) == Union({u. u <= f(u)})" *)
      (* interpretation * interpretation -> bool *)
      fun is_subset (Node subs, Node sups) =
            forall (fn (sub, sup) => (sub = FF) orelse (sup = TT))
              (subs ~~ sups)
        | is_subset (_, _) =
            raise REFUTE ("gfp_interpreter",
              "is_subset: interpretation for set is not a node")
      (* interpretation * interpretation -> interpretation *)
      fun union (Node xs, Node ys) =
            Node (map (fn (x,y) => if x=TT orelse y=TT then TT else FF)
                 (xs ~~ ys))
        | union (_, _) =
            raise REFUTE ("gfp_interpreter",
              "union: interpretation for set is not a node")
      (* interpretation -> interpretaion *)
      fun gfp (Node resultsets) =
            fold (fn (set, resultset) => fn acc =>
              if is_subset (set, resultset) then
                union (acc, set)
              else
                acc) (i_sets ~~ resultsets) i_univ
        | gfp _ =
            raise REFUTE ("gfp_interpreter",
              "gfp: interpretation for function is not a node")
    in
      SOME (Node (map gfp i_funs), model, args)
    end
  | _ => NONE;
*)

(* only an optimization: 'fst' could in principle be interpreted with  *)
(* interpreters available already (using its definition), but the code *)
(* below is more efficient                                             *)

fun Product_Type_fst_interpreter ctxt model args t =
  case t of
    Const (@{const_name fst}, Type ("fun", [Type (@{type_name Product_Type.prod}, [T, U]), _])) =>
      let
        val constants_T = make_constants ctxt model T
        val size_U = size_of_type ctxt model U
      in
        SOME (Node (maps (replicate size_U) constants_T), model, args)
      end
  | _ => NONE;

(* only an optimization: 'snd' could in principle be interpreted with  *)
(* interpreters available already (using its definition), but the code *)
(* below is more efficient                                             *)

fun Product_Type_snd_interpreter ctxt model args t =
  case t of
    Const (@{const_name snd}, Type ("fun", [Type (@{type_name Product_Type.prod}, [T, U]), _])) =>
      let
        val size_T = size_of_type ctxt model T
        val constants_U = make_constants ctxt model U
      in
        SOME (Node (flat (replicate size_T constants_U)), model, args)
      end
  | _ => NONE;


(* ------------------------------------------------------------------------- *)
(* PRINTERS                                                                  *)
(* ------------------------------------------------------------------------- *)

fun stlc_printer ctxt model T intr assignment =
  let
    (* string -> string *)
    val strip_leading_quote = perhaps (try (unprefix "'"))
    (* Term.typ -> string *)
    fun string_of_typ (Type (s, _)) = s
      | string_of_typ (TFree (x, _)) = strip_leading_quote x
      | string_of_typ (TVar ((x,i), _)) =
          strip_leading_quote x ^ string_of_int i
    (* interpretation -> int *)
    fun index_from_interpretation (Leaf xs) =
          find_index (Prop_Logic.eval assignment) xs
      | index_from_interpretation _ =
          raise REFUTE ("stlc_printer",
            "interpretation for ground type is not a leaf")
  in
    case T of
      Type ("fun", [T1, T2]) =>
        let
          (* create all constants of type 'T1' *)
          val constants = make_constants ctxt model T1
          (* interpretation list *)
          val results =
            (case intr of
              Node xs => xs
            | _ => raise REFUTE ("stlc_printer",
              "interpretation for function type is a leaf"))
          (* Term.term list *)
          val pairs = map (fn (arg, result) =>
            HOLogic.mk_prod
              (print ctxt model T1 arg assignment,
               print ctxt model T2 result assignment))
            (constants ~~ results)
          (* Term.typ *)
          val HOLogic_prodT = HOLogic.mk_prodT (T1, T2)
          val HOLogic_setT  = HOLogic.mk_setT HOLogic_prodT
          (* Term.term *)
          val HOLogic_empty_set = Const (@{const_abbrev Set.empty}, HOLogic_setT)
          val HOLogic_insert    =
            Const (@{const_name insert}, HOLogic_prodT --> HOLogic_setT --> HOLogic_setT)
        in
          SOME (fold_rev (fn pair => fn acc => HOLogic_insert $ pair $ acc) pairs HOLogic_empty_set)
        end
    | Type ("prop", []) =>
        (case index_from_interpretation intr of
          ~1 => SOME (HOLogic.mk_Trueprop (Const (@{const_name undefined}, HOLogic.boolT)))
        | 0  => SOME (HOLogic.mk_Trueprop HOLogic.true_const)
        | 1  => SOME (HOLogic.mk_Trueprop HOLogic.false_const)
        | _  => raise REFUTE ("stlc_interpreter",
          "illegal interpretation for a propositional value"))
    | Type _  =>
        if index_from_interpretation intr = (~1) then
          SOME (Const (@{const_name undefined}, T))
        else
          SOME (Const (string_of_typ T ^
            string_of_int (index_from_interpretation intr), T))
    | TFree _ =>
        if index_from_interpretation intr = (~1) then
          SOME (Const (@{const_name undefined}, T))
        else
          SOME (Const (string_of_typ T ^
            string_of_int (index_from_interpretation intr), T))
    | TVar _  =>
        if index_from_interpretation intr = (~1) then
          SOME (Const (@{const_name undefined}, T))
        else
          SOME (Const (string_of_typ T ^
            string_of_int (index_from_interpretation intr), T))
  end;

fun IDT_printer ctxt model T intr assignment =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    (case T of
      Type (s, Ts) =>
        (case Datatype.get_info thy s of
          SOME info =>  (* inductive datatype *)
            let
              val (typs, _)           = model
              val index               = #index info
              val descr               = #descr info
              val (_, dtyps, constrs) = the (AList.lookup (op =) descr index)
              val typ_assoc           = dtyps ~~ Ts
              (* sanity check: every element in 'dtyps' must be a 'DtTFree' *)
              val _ =
                if Library.exists (fn d =>
                  case d of Datatype_Aux.DtTFree _ => false | _ => true) dtyps
                then
                  raise REFUTE ("IDT_printer", "datatype argument (for type " ^
                    Syntax.string_of_typ ctxt (Type (s, Ts)) ^ ") is not a variable")
                else ()
              (* the index of the element in the datatype *)
              val element =
                (case intr of
                  Leaf xs => find_index (Prop_Logic.eval assignment) xs
                | Node _  => raise REFUTE ("IDT_printer",
                  "interpretation is not a leaf"))
            in
              if element < 0 then
                SOME (Const (@{const_name undefined}, Type (s, Ts)))
              else
                let
                  (* takes a datatype constructor, and if for some arguments this  *)
                  (* constructor generates the datatype's element that is given by *)
                  (* 'element', returns the constructor (as a term) as well as the *)
                  (* indices of the arguments                                      *)
                  fun get_constr_args (cname, cargs) =
                    let
                      val cTerm      = Const (cname,
                        map (typ_of_dtyp descr typ_assoc) cargs ---> Type (s, Ts))
                      val (iC, _, _) = interpret ctxt (typs, []) {maxvars=0,
                        def_eq=false, next_idx=1, bounds=[], wellformed=True} cTerm
                      (* interpretation -> int list option *)
                      fun get_args (Leaf xs) =
                            if find_index (fn x => x = True) xs = element then
                              SOME []
                            else
                              NONE
                        | get_args (Node xs) =
                            let
                              (* interpretation * int -> int list option *)
                              fun search ([], _) =
                                NONE
                                | search (x::xs, n) =
                                (case get_args x of
                                  SOME result => SOME (n::result)
                                | NONE        => search (xs, n+1))
                            in
                              search (xs, 0)
                            end
                    in
                      Option.map (fn args => (cTerm, cargs, args)) (get_args iC)
                    end
                  val (cTerm, cargs, args) =
                    (* we could speed things up by computing the correct          *)
                    (* constructor directly (rather than testing all              *)
                    (* constructors), based on the order in which constructors    *)
                    (* generate elements of datatypes; the current implementation *)
                    (* of 'IDT_printer' however is independent of the internals   *)
                    (* of 'IDT_constructor_interpreter'                           *)
                    (case get_first get_constr_args constrs of
                      SOME x => x
                    | NONE   => raise REFUTE ("IDT_printer",
                      "no matching constructor found for element " ^
                      string_of_int element))
                  val argsTerms = map (fn (d, n) =>
                    let
                      val dT = typ_of_dtyp descr typ_assoc d
                      (* we only need the n-th element of this list, so there   *)
                      (* might be a more efficient implementation that does not *)
                      (* generate all constants                                 *)
                      val consts = make_constants ctxt (typs, []) dT
                    in
                      print ctxt (typs, []) dT (nth consts n) assignment
                    end) (cargs ~~ args)
                in
                  SOME (list_comb (cTerm, argsTerms))
                end
            end
        | NONE =>  (* not an inductive datatype *)
            NONE)
    | _ =>  (* a (free or schematic) type variable *)
        NONE)
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

val setup =
   add_interpreter "stlc"    stlc_interpreter #>
   add_interpreter "Pure"    Pure_interpreter #>
   add_interpreter "HOLogic" HOLogic_interpreter #>
   add_interpreter "set"     set_interpreter #>
   add_interpreter "IDT"             IDT_interpreter #>
   add_interpreter "IDT_constructor" IDT_constructor_interpreter #>
   add_interpreter "IDT_recursion"   IDT_recursion_interpreter #>
   add_interpreter "Finite_Set.card"    Finite_Set_card_interpreter #>
   add_interpreter "Finite_Set.finite"  Finite_Set_finite_interpreter #>
   add_interpreter "Nat_Orderings.less" Nat_less_interpreter #>
   add_interpreter "Nat_HOL.plus"       Nat_plus_interpreter #>
   add_interpreter "Nat_HOL.minus"      Nat_minus_interpreter #>
   add_interpreter "Nat_HOL.times"      Nat_times_interpreter #>
   add_interpreter "List.append" List_append_interpreter #>
(* UNSOUND
   add_interpreter "lfp" lfp_interpreter #>
   add_interpreter "gfp" gfp_interpreter #>
*)
   add_interpreter "Product_Type.fst" Product_Type_fst_interpreter #>
   add_interpreter "Product_Type.snd" Product_Type_snd_interpreter #>
   add_printer "stlc" stlc_printer #>
   add_printer "IDT"  IDT_printer;



(** outer syntax commands 'refute' and 'refute_params' **)

(* argument parsing *)

(*optional list of arguments of the form [name1=value1, name2=value2, ...]*)

val scan_parm = Parse.name -- (Scan.optional (Parse.$$$ "=" |-- Parse.name) "true")
val scan_parms = Scan.optional (Parse.$$$ "[" |-- Parse.list scan_parm --| Parse.$$$ "]") [];


(* 'refute' command *)

val _ =
  Outer_Syntax.improper_command "refute"
    "try to find a model that refutes a given subgoal" Keyword.diag
    (scan_parms -- Scan.optional Parse.nat 1 >>
      (fn (parms, i) =>
        Toplevel.keep (fn state =>
          let
            val ctxt = Toplevel.context_of state;
            val {goal = st, ...} = Proof.raw_goal (Toplevel.proof_of state);
          in refute_goal ctxt parms st i; () end)));


(* 'refute_params' command *)

val _ =
  Outer_Syntax.command "refute_params"
    "show/store default parameters for the 'refute' command" Keyword.thy_decl
    (scan_parms >> (fn parms =>
      Toplevel.theory (fn thy =>
        let
          val thy' = fold set_default_param parms thy;
          val output =
            (case get_default_params (Proof_Context.init_global thy') of
              [] => "none"
            | new_defaults => cat_lines (map (fn (x, y) => x ^ "=" ^ y) new_defaults));
          val _ = writeln ("Default parameters for 'refute':\n" ^ output);
        in thy' end)));

end;

