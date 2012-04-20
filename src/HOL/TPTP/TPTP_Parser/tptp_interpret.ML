(*  Title:      HOL/TPTP/TPTP_Parser/tptp_interpret.ML
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Interprets TPTP problems in Isabelle/HOL.
*)

signature TPTP_INTERPRET =
sig
  (*Signature extension: typing information for variables and constants*)
  type var_types = (string * typ option) list
  type const_map = (string * term) list

  (*Mapping from TPTP types to Isabelle/HOL types. This map works over all
  base types. The map must be total wrt TPTP types.*)
  type type_map = (TPTP_Syntax.tptp_type * typ) list

  (*Inference info, when available, consists of the name of the inference rule
  and the names of the inferences involved in the reasoning step.*)
  type inference_info = (string * string list) option

  (*A parsed annotated formula is represented as a 5-tuple consisting of
  the formula's label, its role, the TPTP formula, its Isabelle/HOL meaning, and
  inference info*)
  type tptp_formula_meaning =
    string * TPTP_Syntax.role * term * inference_info

  (*In general, the meaning of a TPTP statement (which, through the Include
  directive, may include the meaning of an entire TPTP file, is a map from
  TPTP to Isabelle/HOL types, a map from TPTP constants to their Isabelle/HOL
  counterparts and their types, and a list of interpreted annotated formulas.*)
  type tptp_general_meaning =
    (type_map * const_map * tptp_formula_meaning list)

  (*cautious = indicates whether additional checks are made to check
      that all used types have been declared.
    problem_name = if given then it is used to qualify types & constants*)
  type config =
    {cautious : bool,
     problem_name : TPTP_Problem_Name.problem_name option}

  (*Generates a fresh Isabelle/HOL type for interpreting a TPTP type in a theory.*)
  val declare_type : config -> (TPTP_Syntax.tptp_type * string) -> type_map ->
    theory -> type_map * theory

  (*Map TPTP types to Isabelle/HOL types*)
  val interpret_type : config -> theory -> type_map ->
    TPTP_Syntax.tptp_type -> typ

  (*Map TPTP terms to Isabelle/HOL terms*)
  val interpret_term : bool -> config -> TPTP_Syntax.language ->
    const_map -> var_types -> type_map -> TPTP_Syntax.tptp_term -> theory ->
    term * theory

  val interpret_formula : config -> TPTP_Syntax.language -> const_map ->
    var_types -> type_map -> TPTP_Syntax.tptp_formula -> theory ->
    term * theory

  (*Interpret a TPTP line: return a "tptp_general_meaning" for that line,
  as well as an updated Isabelle theory including any types & constants
  which were specified in that line.
  Note that type/constant declarations do not result in any formulas being
  returned. A typical TPTP line might update the theory, and/or return one or
  more formulas. For instance, the "include" directive may update the theory
  and also return a list of formulas from the included file.
  Arguments:
    config = (see above)
    inclusion list = names of annotated formulas to interpret (since "include"
      directive can be selective wrt to such names)
    type_map = mapping of TPTP-types to Isabelle/HOL types. This argument may be
      given to force a specific mapping: this is usually done for using an
      imported TPTP problem in Isar.
    const_map = as previous, but for constants.
    path_prefix = path where TPTP problems etc are located (to help the "include"
      directive find the files.
    line = parsed TPTP line
    thy = theory where interpreted info will be stored.
  *)
  val interpret_line : config -> string list -> type_map -> const_map ->
    Path.T -> TPTP_Syntax.tptp_line -> theory -> tptp_general_meaning * theory

  (*Like "interpret_line" above, but works over a whole parsed problem.
    Arguments:
      config = as previously
      inclusion list = as previously
      path_prefix = as previously
      lines = parsed TPTP syntax
      type_map = as previously
      const_map = as previously
      thy = as previously
  *)
  val interpret_problem : config -> string list -> Path.T ->
    TPTP_Syntax.tptp_line list -> type_map -> const_map -> theory ->
    tptp_general_meaning * theory

  (*Like "interpret_problem" above, but it is given a filename rather than
  a parsed problem.*)
  val interpret_file : bool -> Path.T -> Path.T -> type_map -> const_map ->
    theory -> tptp_general_meaning * theory

  type position = string * int * int
  exception MISINTERPRET of position list * exn
  exception MISINTERPRET_FORMULA of string * TPTP_Syntax.tptp_formula
  exception MISINTERPRET_SYMBOL of string * TPTP_Syntax.symbol
  exception MISINTERPRET_TERM of string * TPTP_Syntax.tptp_term
  exception MISINTERPRET_TYPE of string * TPTP_Syntax.tptp_type

  val import_file : bool -> Path.T -> Path.T -> type_map -> const_map ->
    theory -> theory

  (*Imported TPTP files are stored as "manifests" in the theory.*)
  type manifest = TPTP_Problem_Name.problem_name * tptp_general_meaning
  val get_manifests : theory -> manifest list

  (*Returns the list of all files included in a directory and its
  subdirectories. This is only used for testing the parser/interpreter against
  all TPTP problems.*)
  val get_file_list : Path.T -> Path.T list
end

structure TPTP_Interpret : TPTP_INTERPRET =
struct

open TPTP_Syntax
type position = string * int * int
exception MISINTERPRET of position list * exn
exception MISINTERPRET_FORMULA of string * TPTP_Syntax.tptp_formula
exception MISINTERPRET_SYMBOL of string * TPTP_Syntax.symbol
exception MISINTERPRET_TERM of string * TPTP_Syntax.tptp_term
exception MISINTERPRET_TYPE of string * TPTP_Syntax.tptp_type


(* General stuff *)

type config =
  {cautious : bool,
   problem_name : TPTP_Problem_Name.problem_name option}


(* Interpretation *)

(** Signatures and other type abbrevations **)

type const_map = (string * term) list
type var_types = (string * typ option) list
type type_map = (TPTP_Syntax.tptp_type * typ) list
type inference_info = (string * string list) option
type tptp_formula_meaning =
  string * TPTP_Syntax.role * term * inference_info
type tptp_general_meaning =
  (type_map * const_map * tptp_formula_meaning list)

type manifest = TPTP_Problem_Name.problem_name * tptp_general_meaning

structure TPTP_Data = Theory_Data
(
  type T = manifest list
  val empty = []
  val extend = I
  fun merge data : T = Library.merge (op =) data
)
val get_manifests = TPTP_Data.get


(** Adding types to a signature **)

(*transform quoted names into acceptable ASCII strings*)
fun alphanumerate c =
  let
    val c' = ord c
    val out_of_range =
      ((c' > 64) andalso (c' < 91)) orelse ((c' > 96)
       andalso (c' < 123)) orelse ((c' > 47) andalso (c' < 58))
  in
    if (not out_of_range) andalso (not (c = "_")) then
      "_nom_" ^ Int.toString (ord c) ^ "_"
    else c
  end
fun alphanumerated_name prefix name =
  prefix ^ (raw_explode #> map alphanumerate #> implode) name

(*SMLNJ complains if type annotation not used below*)
fun mk_binding (config : config) ident =
  let
    val pre_binding = Binding.name (alphanumerated_name "bnd_" ident)
  in
    case #problem_name config of
      NONE => pre_binding
    | SOME prob =>
        Binding.qualify
         false
         (TPTP_Problem_Name.mangle_problem_name prob)
         pre_binding
  end

fun type_exists config thy ty_name =
  Sign.declared_tyname thy (Sign.full_name thy (mk_binding config ty_name))

(*Returns updated theory and the name of the final type's name -- i.e. if the
original name is already taken then the function looks for an available
alternative. It also returns an updated type_map if one has been passed to it.*)
fun declare_type (config : config) (thf_type, type_name) ty_map thy =
  if type_exists config thy type_name then
    raise MISINTERPRET_TYPE ("Type already exists", Atom_type type_name)
  else
    let
      val binding = mk_binding config type_name
      val final_fqn = Sign.full_name thy binding
      val thy' =
        Typedecl.typedecl_global (mk_binding config type_name, [], NoSyn) thy
        |> snd
      val typ_map_entry = (thf_type, (Type (final_fqn, [])))
      val ty_map' = typ_map_entry :: ty_map
    in (ty_map', thy') end


(** Adding constants to signature **)

fun full_name thy config const_name =
  Sign.full_name thy (mk_binding config const_name)

fun const_exists config thy const_name =
  Sign.declared_const thy (full_name thy config const_name)

fun declare_constant config const_name ty thy =
  if const_exists config thy const_name then
    raise MISINTERPRET_TERM
     ("Const already declared", Term_Func (Uninterpreted const_name, []))
  else
    Theory.specify_const
     ((mk_binding config const_name, ty), NoSyn) thy


(** Interpretation functions **)

(*Types in THF are encoded as formulas. This function translates them to type form.*)
(*FIXME possibly incomplete hack*)
fun fmlatype_to_type (Atom (THF_Atom_term (Term_Func (TypeSymbol typ, [])))) =
      Defined_type typ
  | fmlatype_to_type (Atom (THF_Atom_term (Term_Func (Uninterpreted str, [])))) =
      Atom_type str
  | fmlatype_to_type (Type_fmla (Fn_type (ty1, ty2))) =
      let
        val ty1' = case ty1 of
            Fn_type _ => fmlatype_to_type (Type_fmla ty1)
          | Fmla_type ty1 => fmlatype_to_type ty1
        val ty2' = case ty2 of
            Fn_type _ => fmlatype_to_type (Type_fmla ty2)
          | Fmla_type ty2 => fmlatype_to_type ty2
      in Fn_type (ty1', ty2') end

fun interpret_type config thy type_map thf_ty =
  let
    fun lookup_type ty_map thf_ty =
      (case AList.lookup (op =) ty_map thf_ty of
          NONE =>
            raise MISINTERPRET_TYPE
              ("Could not find the interpretation of this TPTP type in the \
               \mapping to Isabelle/HOL", thf_ty)
        | SOME ty => ty)
  in
    case thf_ty of
       Prod_type (thf_ty1, thf_ty2) =>
         Type ("Product_Type.prod",
          [interpret_type config thy type_map thf_ty1,
           interpret_type config thy type_map thf_ty2])
     | Fn_type (thf_ty1, thf_ty2) =>
         Type ("fun",
          [interpret_type config thy type_map thf_ty1,
           interpret_type config thy type_map thf_ty2])
     | Atom_type _ =>
         lookup_type type_map thf_ty
     | Defined_type tptp_base_type =>
         (case tptp_base_type of
            Type_Ind => @{typ ind}
          | Type_Bool => HOLogic.boolT
          | Type_Type => raise MISINTERPRET_TYPE ("No type interpretation", thf_ty)
          | Type_Int => Type ("Int.int", [])
         (*FIXME these types are currently unsupported, so they're treated as
         individuals*)
          | Type_Rat =>
              interpret_type config thy type_map (Defined_type Type_Ind)
          | Type_Real =>
              interpret_type config thy type_map (Defined_type Type_Ind)
          )
     | Sum_type _ =>
         raise MISINTERPRET_TYPE (*FIXME*)
          ("No type interpretation (sum type)", thf_ty)
     | Fmla_type tptp_ty =>
        fmlatype_to_type tptp_ty
        |> interpret_type config thy type_map
     | Subtype _ =>
         raise MISINTERPRET_TYPE (*FIXME*)
          ("No type interpretation (subtype)", thf_ty)
  end

fun the_const config thy language const_map_payload str =
  if language = THF then
    (case AList.lookup (op =) const_map_payload str of
        NONE => raise MISINTERPRET_TERM
          ("Could not find the interpretation of this constant in the \
            \mapping to Isabelle/HOL", Term_Func (Uninterpreted str, []))
      | SOME t => t)
  else
    if const_exists config thy str then
       Sign.mk_const thy ((Sign.full_name thy (mk_binding config str)), [])
    else raise MISINTERPRET_TERM
          ("Could not find the interpretation of this constant in the \
            \mapping to Isabelle/HOL", Term_Func (Uninterpreted str, []))

(*Eta-expands Isabelle/HOL binary function.
 "str" is the name of a polymorphic constant in Isabelle/HOL*)
fun mk_fun str =
  (Const (str, Term.dummyT) $ Bound 1 $ Bound 0)
   |> (Term.absdummy Term.dummyT #> Term.absdummy Term.dummyT)
(*As above, but swaps the function's arguments*)
fun mk_swapped_fun str =
  (Const (str, Term.dummyT) $ Bound 0 $ Bound 1)
   |> (Term.absdummy Term.dummyT #> Term.absdummy Term.dummyT)

fun dummy_term () =
  HOLogic.choice_const Term.dummyT $ Term.absdummy Term.dummyT @{term "True"}

fun interpret_symbol config language const_map symb thy =
  case symb of
     Uninterpreted n =>
       (*Constant would have been added to the map at the time of
       declaration*)
       the_const config thy language const_map n
   | Interpreted_ExtraLogic interpreted_symbol =>
       (case interpreted_symbol of (*FIXME incomplete,
                                     and doesn't work with $i*)
          Sum => mk_fun @{const_name Groups.plus}
        | UMinus =>
            (Const (@{const_name Groups.uminus}, Term.dummyT) $ Bound 0)
             |> Term.absdummy Term.dummyT
        | Difference => mk_fun @{const_name Groups.minus}
        | Product => mk_fun @{const_name Groups.times}
        | Quotient => mk_fun @{const_name Fields.divide}
        | Less => mk_fun @{const_name Orderings.less}
        | LessEq => mk_fun @{const_name Orderings.less_eq}
        | Greater => mk_swapped_fun @{const_name Orderings.less}
          (*FIXME would be nicer to expand "greater"
            and "greater_eq" abbreviations*)
        | GreaterEq => mk_swapped_fun @{const_name Orderings.less_eq}
        (* FIXME todo
        | Quotient_E | Quotient_T | Quotient_F | Remainder_E | Remainder_T
        | Remainder_F | Floor | Ceiling | Truncate | Round | To_Int | To_Rat
        | To_Real | EvalEq | Is_Int | Is_Rat*)
        | Apply => raise MISINTERPRET_SYMBOL ("Malformed term?", symb)
        | _ => dummy_term ()
        )
   | Interpreted_Logic logic_symbol =>
       (case logic_symbol of
          Equals => HOLogic.eq_const Term.dummyT
        | NEquals =>
           HOLogic.mk_not (HOLogic.eq_const Term.dummyT $ Bound 1 $ Bound 0)
           |> (Term.absdummy Term.dummyT #> Term.absdummy Term.dummyT)
        | Or => HOLogic.disj
        | And => HOLogic.conj
        | Iff => HOLogic.eq_const HOLogic.boolT
        | If => HOLogic.imp
        | Fi => @{term "\<lambda> x. \<lambda> y. y \<longrightarrow> x"}
        | Xor =>
            @{term
              "\<lambda> x. \<lambda> y. \<not> (x \<longleftrightarrow> y)"}
        | Nor => @{term "\<lambda> x. \<lambda> y. \<not> (x \<or> y)"}
        | Nand => @{term "\<lambda> x. \<lambda> y. \<not> (x \<and> y)"}
        | Not => HOLogic.Not
        | Op_Forall => HOLogic.all_const Term.dummyT
        | Op_Exists => HOLogic.exists_const Term.dummyT
        | True => @{term "True"}
        | False => @{term "False"}
        )
   | TypeSymbol _ =>
       raise MISINTERPRET_SYMBOL
        ("Cannot have TypeSymbol in term", symb)
   | System str =>
       raise MISINTERPRET_SYMBOL
        ("Cannot interpret system symbol", symb)

(*Apply a function to a list of arguments*)
val mapply = fold (fn x => fn y => y $ x)

fun mapply' (args, thy) f =
  let
    val (f', thy') = f thy
  in (mapply args f', thy') end

(*As above, but for products*)
fun mtimes thy =
  fold (fn x => fn y =>
    Sign.mk_const thy
    ("Product_Type.Pair",[Term.dummyT, Term.dummyT]) $ y $ x)

fun mtimes' (args, thy) f =
  let
    val (f', thy') = f thy
  in (mtimes thy' args f', thy') end


(*Adds constants to signature in FOL (since explicit type declaration isn't
expected). "formula_level" means that the constants are to be interpreted as
predicates, otherwise as functions over individuals.*)
fun FO_const_types config formula_level type_map tptp_t thy =
  let
    val ind_type = interpret_type config thy type_map (Defined_type Type_Ind)
    val value_type =
      if formula_level then
        interpret_type config thy type_map (Defined_type Type_Bool)
      else ind_type
  in case tptp_t of
      Term_Func (symb, tptp_ts) =>
        let
          val thy' = fold (FO_const_types config false type_map) tptp_ts thy
          val ty = fold (fn ty1 => fn ty2 => Type ("fun", [ty1, ty2]))
            (map (fn _ => ind_type) tptp_ts) value_type
        in
          case symb of
             Uninterpreted const_name =>
                 if const_exists config thy' const_name then thy'
                 else snd (declare_constant config const_name ty thy')
           | _ => thy'
        end
     | _ => thy
  end

(*like FO_const_types but works over symbols*)
fun symb_const_types config type_map formula_level const_name n_args thy =
  let
    val ind_type = interpret_type config thy type_map (Defined_type Type_Ind)
    val value_type =
      if formula_level then
        interpret_type config thy type_map (Defined_type Type_Bool)
      else interpret_type config thy type_map (Defined_type Type_Ind)
    fun mk_i_fun b n acc =
      if n = 0 then acc b
      else
        mk_i_fun b (n - 1) (fn ty => Type ("fun", [ind_type, acc ty]))
  in
    if const_exists config thy const_name then thy
    else
      snd (declare_constant config const_name
           (mk_i_fun value_type n_args I) thy)
  end

(*Next batch of functions give info about Isabelle/HOL types*)
fun is_fun (Type ("fun", _)) = true
  | is_fun _ = false
fun is_prod (Type ("Product_Type.prod", _)) = true
  | is_prod _ = false
fun dom_type (Type ("fun", [ty1, _])) = ty1
fun is_prod_typed thy config symb =
  let
    fun symb_type const_name =
      Sign.the_const_type thy (full_name thy config const_name)
  in
    case symb of
       Uninterpreted const_name =>
         if is_fun (symb_type const_name) then
           symb_type const_name |> dom_type |> is_prod
         else false
     | _ => false
   end


(*
 Information needed to be carried around:
 - constant mapping: maps constant names to Isabelle terms with fully-qualified
    names. This is fixed, and it is determined by declaration lines earlier
    in the script (i.e. constants must be declared before appearing in terms.
 - type context: maps bound variables to their Isabelle type. This is discarded
    after each call of interpret_term since variables' cannot be bound across
    terms.
*)
fun interpret_term formula_level config language const_map var_types type_map
 tptp_t thy =
  case tptp_t of
    Term_Func (symb, tptp_ts) =>
       let
         val thy' = FO_const_types config formula_level type_map tptp_t thy
         fun typeof_const const_name = Sign.the_const_type thy'
             (Sign.full_name thy' (mk_binding config const_name))
       in
         case symb of
           Interpreted_ExtraLogic Apply =>
             (*apply the head of the argument list to the tail*)
             (mapply'
               (fold_map (interpret_term false config language const_map
                var_types type_map) (tl tptp_ts) thy')
               (interpret_term formula_level config language const_map
                var_types type_map (hd tptp_ts)))
           | _ =>
              (*apply symb to tptp_ts*)
              if is_prod_typed thy' config symb then
                let
                  val (t, thy'') =
                    mtimes'
                      (fold_map (interpret_term false config language const_map
                       var_types type_map) (tl tptp_ts) thy')
                      (interpret_term false config language const_map
                       var_types type_map (hd tptp_ts))
                in (interpret_symbol config language const_map symb thy' $ t, thy'')
                end
              else
                (
                mapply'
                  (fold_map (interpret_term false config language const_map
                   var_types type_map) tptp_ts thy')
                  (`(interpret_symbol config language const_map symb))
                )
       end
  | Term_Var n =>
     (if language = THF orelse language = TFF then
        (case AList.lookup (op =) var_types n of
           SOME ty =>
             (case ty of
                SOME ty => Free (n, ty)
              | NONE => Free (n, Term.dummyT) (*to infer the variable's type*)
             )
         | NONE =>
             raise MISINTERPRET_TERM ("Could not type variable", tptp_t))
      else (*variables range over individuals*)
        Free (n, interpret_type config thy type_map (Defined_type Type_Ind)),
      thy)
  | Term_Conditional (tptp_formula, tptp_t1, tptp_t2) =>
      (mk_fun @{const_name If}, thy)
  | Term_Num (number_kind, num) =>
      let
        val num_term =
          if number_kind = Int_num then
            HOLogic.mk_number @{typ "int"} (the (Int.fromString num))
          else dummy_term () (*FIXME: not yet supporting rationals and reals*)
      in (num_term, thy) end
  | Term_Distinct_Object str =>
      declare_constant config ("do_" ^ str)
        (interpret_type config thy type_map (Defined_type Type_Ind)) thy

(*Given a list of "'a option", then applies a function to each element if that
element is SOME value, otherwise it leaves it as NONE.*)
fun map_opt f xs =
  fold
  (fn x => fn y =>
    (if Option.isSome x then
       SOME (f (Option.valOf x))
     else NONE) :: y
  ) xs []

fun interpret_formula config language const_map var_types type_map tptp_fmla thy =
  case tptp_fmla of
      Pred app =>
        interpret_term true config language const_map
         var_types type_map (Term_Func app) thy
    | Fmla (symbol, tptp_formulas) =>
       (case symbol of
          Interpreted_ExtraLogic Apply =>
            mapply'
              (fold_map (interpret_formula config language const_map
               var_types type_map) (tl tptp_formulas) thy)
              (interpret_formula config language const_map
               var_types type_map (hd tptp_formulas))
        | Uninterpreted const_name =>
            let
              val (args, thy') = (fold_map (interpret_formula config language
               const_map var_types type_map) tptp_formulas thy)
              val thy' = symb_const_types config type_map true const_name
               (length tptp_formulas) thy'
            in
              (if is_prod_typed thy' config symbol then
                 mtimes thy' args (interpret_symbol config language
                  const_map symbol thy')
               else
                mapply args
                 (interpret_symbol config language const_map symbol thy'),
              thy')
            end
        | _ =>
            let
              val (args, thy') =
                fold_map
                 (interpret_formula config language
                  const_map var_types type_map)
                 tptp_formulas thy
            in
              (if is_prod_typed thy' config symbol then
                 mtimes thy' args (interpret_symbol config language
                  const_map symbol thy')
               else
                 mapply args
                  (interpret_symbol config language const_map symbol thy'),
               thy')
            end)
    | Sequent _ =>
        (*FIXME unsupported*)
        raise MISINTERPRET_FORMULA ("'Sequent' unsupported", tptp_fmla)
    | Quant (quantifier, bindings, tptp_formula) =>
        let
          val (bound_vars, bound_var_types) = ListPair.unzip bindings
          val bound_var_types' : typ option list =
            (map_opt : (tptp_type -> typ) ->
             (tptp_type option list) -> typ option list)
            (interpret_type config thy type_map) bound_var_types
          val var_types' =
            ListPair.zip (bound_vars, List.rev bound_var_types')
            |> List.rev
          fun fold_bind f =
            fold
              (fn (n, ty) => fn t =>
                 case ty of
                   NONE =>
                     f (n,
                        if language = THF then Term.dummyT
                        else
                          interpret_type config thy type_map
                           (Defined_type Type_Ind),
                        t)
                 | SOME ty => f (n, ty, t)
              )
              var_types'
        in case quantifier of
          Forall =>
            interpret_formula config language const_map (var_types' @ var_types)
             type_map tptp_formula thy
            |>> fold_bind HOLogic.mk_all
        | Exists =>
            interpret_formula config language const_map (var_types' @ var_types)
             type_map tptp_formula thy
            |>> fold_bind HOLogic.mk_exists
        | Lambda =>
            interpret_formula config language const_map (var_types' @ var_types)
             type_map tptp_formula thy
            |>> fold_bind (fn (n, ty, rest) => lambda (Free (n, ty)) rest)
        | Epsilon =>
            let val (t, thy') =
              interpret_formula config language const_map var_types type_map
               (Quant (Lambda, bindings, tptp_formula)) thy
            in ((HOLogic.choice_const Term.dummyT) $ t, thy') end
        | Iota =>
            let val (t, thy') =
              interpret_formula config language const_map var_types type_map
               (Quant (Lambda, bindings, tptp_formula)) thy
            in (Const (@{const_name The}, Term.dummyT) $ t, thy') end
        | Dep_Prod =>
            raise MISINTERPRET_FORMULA ("Unsupported", tptp_fmla)
        | Dep_Sum =>
            raise MISINTERPRET_FORMULA ("Unsupported", tptp_fmla)
        end
    | Conditional (fmla1, fmla2, fmla3) =>
        let
          val interp = interpret_formula config language const_map var_types type_map
          val (((fmla1', fmla2'), fmla3'), thy') =
            interp fmla1 thy
            ||>> interp fmla2
            ||>> interp fmla3
        in (HOLogic.mk_conj (HOLogic.mk_imp (fmla1', fmla2'),
                             HOLogic.mk_imp (HOLogic.mk_not fmla1', fmla3')),
            thy')
        end
    | Let (tptp_let_list, tptp_formula) => (*FIXME not yet implemented*)
        raise MISINTERPRET_FORMULA ("'Let' not yet implemented", tptp_fmla)
    | Atom tptp_atom =>
        (case tptp_atom of
          TFF_Typed_Atom (symbol, tptp_type_opt) =>
            (*FIXME ignoring type info*)
            (interpret_symbol config language const_map symbol thy, thy)
        | THF_Atom_term tptp_term =>
            interpret_term true config language const_map var_types
             type_map tptp_term thy
        | THF_Atom_conn_term symbol =>
            (interpret_symbol config language const_map symbol thy, thy))
    | Type_fmla _ =>
         raise MISINTERPRET_FORMULA
          ("Cannot interpret types as formulas", tptp_fmla)
    | THF_typing (tptp_formula, _) => (*FIXME ignoring type info*)
        interpret_formula config language
         const_map var_types type_map tptp_formula thy

(*Extract the type from a typing*)
local
  fun extract_type tptp_type =
    case tptp_type of
        Fmla_type typ => fmlatype_to_type typ
      | _ => tptp_type
in
  fun typeof_typing (THF_typing (_, tptp_type)) = extract_type tptp_type
  fun typeof_tff_typing (Atom (TFF_Typed_Atom (_, SOME tptp_type))) =
    extract_type tptp_type
end
fun nameof_typing
  (THF_typing
     ((Atom (THF_Atom_term (Term_Func (Uninterpreted str, [])))), _)) = str
fun nameof_tff_typing (Atom (TFF_Typed_Atom (Uninterpreted str, _))) = str

fun interpret_line config inc_list type_map const_map path_prefix line thy =
  case line of
     Include (_, quoted_path, inc_list) =>
       interpret_file'
        config
        inc_list
        path_prefix
        (Path.append
          path_prefix
          (quoted_path
           |> unenclose
           |> Path.explode))
        type_map
        const_map
        thy
   | Annotated_Formula (_, lang, label, role, tptp_formula, annotation_opt) =>
       (*interpret a line only if "label" is in "inc_list", or if "inc_list" is
          empty (in which case interpret all lines)*)
       (*FIXME could work better if inc_list were sorted*)
       if null inc_list orelse is_some (List.find (fn x => x = label) inc_list) then
         case role of
           Role_Type =>
             let
               val thy_name = Context.theory_name thy
               val (tptp_ty, name) =
                 if lang = THF then
                   (typeof_typing tptp_formula (*assuming tptp_formula is a typing*),
                    nameof_typing tptp_formula (*and that the LHS is a (atom) name*))
                 else
                   (typeof_tff_typing tptp_formula,
                    nameof_tff_typing tptp_formula)
             in
               case tptp_ty of
                 Defined_type Type_Type => (*add new type*)
                   (*generate an Isabelle/HOL type to interpret this TPTP type,
                   and add it to both the Isabelle/HOL theory and to the type_map*)
                    let
                      val (type_map', thy') =
                        declare_type
                         config
                         (Atom_type name, name)
                         type_map
                         thy
                    in ((type_map',
                         const_map,
                         []),
                        thy')
                    end

               | _ => (*declaration of constant*)
                  (*Here we populate the map from constants to the Isabelle/HOL
                  terms they map to (which in turn contain their types).*)
                  let
                    val ty = interpret_type config thy type_map tptp_ty
                    (*make sure that the theory contains all the types appearing
                    in this constant's signature. Exception is thrown if encounter
                    an undeclared types.*)
                    val (t, thy') =
                      let
                        fun analyse_type thy thf_ty =
                           if #cautious config then
                            case thf_ty of
                               Fn_type (thf_ty1, thf_ty2) =>
                                 (analyse_type thy thf_ty1;
                                 analyse_type thy thf_ty2)
                             | Atom_type ty_name =>
                                 if type_exists config thy ty_name then ()
                                 else
                                  raise MISINTERPRET_TYPE
                                   ("Type (in signature of " ^
                                      name ^ ") has not been declared",
                                     Atom_type ty_name)
                             | _ => ()
                           else () (*skip test if we're not being cautious.*)
                      in
                        analyse_type thy tptp_ty;
                        declare_constant config name ty thy
                      end
                    (*register a mapping from name to t. Constants' type
                    declarations should occur at most once, so it's justified to
                    use "::". Note that here we use a constant's name rather
                    than the possibly- new one, since all references in the
                    theory will be to this name.*)
                    val const_map' = ((name, t) :: const_map)
                  in ((type_map,(*type_map unchanged, since a constant's
                                  declaration shouldn't include any new types.*)
                       const_map',(*typing table of constant was extended*)
                       []),(*no formulas were interpreted*)
                      thy')(*theory was extended with new constant*)
                  end
             end

         | _ => (*i.e. the AF is not a type declaration*)
             let
               (*gather interpreted term, and the map of types occurring in that term*)
               val (t, thy') =
                 interpret_formula config lang
                  const_map [] type_map tptp_formula thy
                 |>> HOLogic.mk_Trueprop
               (*type_maps grow monotonically, so return the newest value (type_mapped);
               there's no need to unify it with the type_map parameter.*)
             in
              ((type_map, const_map,
                [(label, role,
                  Syntax.check_term (Proof_Context.init_global thy') t,
                  TPTP_Proof.extract_inference_info annotation_opt)]), thy')
             end
       else (*do nothing if we're not to includ this AF*)
         ((type_map, const_map, []), thy)

and interpret_problem config inc_list path_prefix lines type_map const_map thy =
  let
    val thy_name = Context.theory_name thy
  in
    fold (fn line =>
           fn ((type_map, const_map, lines), thy) =>
             let
               (*process the line, ignoring the type-context for variables*)
               val ((type_map', const_map', l'), thy') =
                 interpret_line config inc_list type_map const_map path_prefix line thy
                   handle
                     (*package all exceptions to include position information,
                       even relating to multiple levels of "include"ed files*)
                       (*FIXME "exn" contents may appear garbled due to markup
                         FIXME this appears as ML source position *)
                       MISINTERPRET (pos_list, exn)  =>
                         raise MISINTERPRET
                           (TPTP_Syntax.pos_of_line line :: pos_list, exn)
                     | exn => raise MISINTERPRET
                         ([TPTP_Syntax.pos_of_line line], exn)
             in
               ((type_map',
                 const_map',
                 l' @ lines),(*append is sufficient, union would be overkill*)
                thy')
             end)
         lines (*lines of the problem file*)
         ((type_map, const_map, []), thy) (*initial values*)
  end

and interpret_file' config inc_list path_prefix file_name =
  let
    val file_name' = Path.expand file_name
  in
    if Path.is_absolute file_name' then
      Path.implode file_name
      |> TPTP_Parser.parse_file
      |> interpret_problem config inc_list path_prefix
    else error "Could not determine absolute path to file"
  end

and interpret_file cautious path_prefix file_name =
  let
    val config =
      {cautious = cautious,
       problem_name =
        SOME (TPTP_Problem_Name.parse_problem_name ((Path.base #> Path.implode)
         file_name))}
  in interpret_file' config [] path_prefix file_name end

fun import_file cautious path_prefix file_name type_map const_map thy =
  let
    val prob_name =
      TPTP_Problem_Name.parse_problem_name (Path.implode (Path.base file_name))
    val (result, thy') =
      interpret_file cautious path_prefix file_name type_map const_map thy
  (*FIXME doesn't check if problem has already been interpreted*)
  in TPTP_Data.map (cons ((prob_name, result))) thy' end

val _ =
  Outer_Syntax.improper_command @{command_spec "import_tptp"} "import TPTP problem"
    (Parse.path >> (fn path =>
      Toplevel.theory (fn thy =>
       (*NOTE: assumes include files are located at $TPTP/Axioms
         (which is how TPTP is organised)*)
       import_file true (Path.explode "$TPTP") path [] [] thy)))


(*Used for debugging. Returns all files contained within a directory or its
subdirectories. Follows symbolic links, filters away directories.*)
fun get_file_list path =
  let
    fun check_file_entry f rest =
      let
        (*NOTE needed since don't have File.is_link and File.read_link*)
        val f_str = Path.implode f
      in
        if File.is_dir f then
          rest (*filter out directories*)
        else if OS.FileSys.isLink f_str then
          (*follow links -- NOTE this breaks if links are relative paths*)
          check_file_entry (Path.explode (OS.FileSys.readLink f_str)) rest
        else f :: rest
      end
  in
    File.read_dir path
    |> map
        (Path.explode
        #> Path.append path)
    |> (fn l => fold check_file_entry l [])
  end

end
