(*  Title:      HOL/TPTP/TPTP_Parser/tptp_syntax.ML
    Author:     Nik Sultana, Cambridge University Computer Laboratory

TPTP abstract syntax and parser-related definitions.
*)

signature TPTP_SYNTAX =
sig
  exception TPTP_SYNTAX of string
  val debug: ('a -> unit) -> 'a -> unit

(*Note that in THF "^ [X] : ^ [Y] : f @ g" should parse
  as "(^ [X] : (^ [Y] : f)) @ g"
*)

  datatype number_kind = Int_num | Real_num | Rat_num

  datatype status_value =
      Suc | Unp | Sap | Esa | Sat | Fsa
    | Thm | Eqv | Tac | Wec | Eth | Tau
    | Wtc | Wth | Cax | Sca | Tca | Wca
    | Cup | Csp | Ecs | Csa | Cth | Ceq
    | Unc | Wcc | Ect | Fun | Uns | Wuc
    | Wct | Scc | Uca | Noc

  type name = string
  type atomic_word = string
  type inference_rule = atomic_word
  type file_info = name option
  type single_quoted = string
  type file_name = single_quoted
  type creator_name = atomic_word
  type variable = string
  type upper_word = string

  datatype language = FOF | CNF | TFF | THF | FOT | TFF_with_arithmetic
  and role =
     Role_Axiom | Role_Hypothesis | Role_Definition | Role_Assumption |
     Role_Lemma | Role_Theorem | Role_Conjecture | Role_Negated_Conjecture |
     Role_Plain | Role_Fi_Domain | Role_Fi_Functors | Role_Fi_Predicates |
     Role_Type | Role_Unknown

  and general_data = (*Bind of variable * formula_data*)
     Atomic_Word of string
   | Application of string * general_term list (*general_function*)
   | V of upper_word (*variable*)
   | Number of number_kind * string
   | Distinct_Object of string
   | (*formula_data*) Formula_Data of language * tptp_formula (* $thf(<thf_formula>) *)
   | (*formula_data*) Term_Data of tptp_term

  and interpreted_symbol =
    UMinus | Sum | Difference | Product | Quotient | Quotient_E |
    Quotient_T | Quotient_F | Remainder_E | Remainder_T | Remainder_F |
    Floor | Ceiling | Truncate | Round | To_Int | To_Rat | To_Real |
    (*FIXME these should be in defined_pred, but that's not being used in TPTP*)
    Less | LessEq | Greater | GreaterEq | EvalEq | Is_Int | Is_Rat |
    Distinct | Apply

  and logic_symbol = Equals | NEquals | Or | And | Iff | If | Fi | Xor |
    Nor | Nand | Not | Op_Forall | Op_Exists |
    (*FIXME these should be in defined_pred, but that's not being used in TPTP*)
    True | False

  and quantifier = (*interpreted binders*)
    Forall | Exists | Epsilon | Iota | Lambda | Dep_Prod | Dep_Sum

  and tptp_base_type =
    Type_Ind | Type_Bool | Type_Type | Type_Int | Type_Rat | Type_Real

  and symbol =
      Uninterpreted of string
    | Interpreted_ExtraLogic of interpreted_symbol
    | Interpreted_Logic of logic_symbol
    | TypeSymbol of tptp_base_type
    | System of string

  and general_term =
      General_Data of general_data (*general_data*)
    | General_Term of general_data * general_term (*general_data : general_term*)
    | General_List of general_term list

  and tptp_term =
      Term_Func of symbol * tptp_term list
    | Term_Var of string
    | Term_Conditional of tptp_formula * tptp_term * tptp_term
    | Term_Num of number_kind * string
    | Term_Distinct_Object of string
    | Term_Let of tptp_let list * tptp_term (*FIXME remove list?*)

  and tptp_atom =
      TFF_Typed_Atom of symbol * tptp_type option (*only TFF*)
    | THF_Atom_term of tptp_term   (*from here on, only THF*)
    | THF_Atom_conn_term of symbol

  and tptp_formula =
      Pred of symbol * tptp_term list
    | Fmla of symbol * tptp_formula list
    | Sequent of tptp_formula list * tptp_formula list
    | Quant of quantifier * (string * tptp_type option) list * tptp_formula
    | Conditional of tptp_formula * tptp_formula * tptp_formula
    | Let of tptp_let list * tptp_formula (*FIXME remove list?*)
    | Atom of tptp_atom
    | Type_fmla of tptp_type
    | THF_typing of tptp_formula * tptp_type (*only THF*)

  and tptp_let =
      Let_fmla of (string * tptp_type option) * tptp_formula
    | Let_term of (string * tptp_type option) * tptp_term (*only TFF*)

  and tptp_type =
      Prod_type of tptp_type * tptp_type
    | Fn_type of tptp_type * tptp_type
    | Atom_type of string
    | Defined_type of tptp_base_type
    | Sum_type of tptp_type * tptp_type (*only THF*)
    | Fmla_type of tptp_formula
    | Subtype of symbol * symbol (*only THF*)

  type general_list = general_term list
  type parent_details = general_list
  type useful_info = general_term list
  type info = useful_info

  type annotation = general_term * general_term list

  exception DEQUOTE of string

  type position = string * int * int

  datatype tptp_line =
      Annotated_Formula of position * language * string * role *
        tptp_formula * annotation option
   |  Include of string * string list

  type tptp_problem = tptp_line list

  val dequote : single_quoted -> single_quoted

  val role_to_string : role -> string

  val status_to_string : status_value -> string

  val nameof_tff_atom_type : tptp_type -> string

  (*Returns the list of all files included in a directory and its
  subdirectories. This is only used for testing the parser/interpreter against
  all THF problems.*)
  val get_file_list : Path.T -> Path.T list

  val string_of_tptp_term : tptp_term -> string
  val string_of_tptp_formula : tptp_formula -> string

end


structure TPTP_Syntax : TPTP_SYNTAX =
struct

exception TPTP_SYNTAX of string

datatype number_kind = Int_num | Real_num | Rat_num

datatype status_value =
    Suc | Unp | Sap | Esa | Sat | Fsa
  | Thm | Eqv | Tac | Wec | Eth | Tau
  | Wtc | Wth | Cax | Sca | Tca | Wca
  | Cup | Csp | Ecs | Csa | Cth | Ceq
  | Unc | Wcc | Ect | Fun | Uns | Wuc
  | Wct | Scc | Uca | Noc

type name = string
type atomic_word = string
type inference_rule = atomic_word
type file_info = name option
type single_quoted = string
type file_name = single_quoted
type creator_name = atomic_word
type variable = string
type upper_word = string

datatype language = FOF | CNF | TFF | THF | FOT | TFF_with_arithmetic
and role =
  Role_Axiom | Role_Hypothesis | Role_Definition | Role_Assumption |
  Role_Lemma | Role_Theorem | Role_Conjecture | Role_Negated_Conjecture |
  Role_Plain | Role_Fi_Domain | Role_Fi_Functors | Role_Fi_Predicates |
  Role_Type | Role_Unknown
and general_data = (*Bind of variable * formula_data*)
    Atomic_Word of string
  | Application of string * (general_term list)
  | V of upper_word (*variable*)
  | Number of number_kind * string
  | Distinct_Object of string
  | (*formula_data*) Formula_Data of language * tptp_formula (* $thf(<thf_formula>) *)
  | (*formula_data*) Term_Data of tptp_term

  and interpreted_symbol =
    UMinus | Sum | Difference | Product | Quotient | Quotient_E |
    Quotient_T | Quotient_F | Remainder_E | Remainder_T | Remainder_F |
    Floor | Ceiling | Truncate | Round | To_Int | To_Rat | To_Real |
    Less | LessEq | Greater | GreaterEq | EvalEq | Is_Int | Is_Rat |
    Distinct |
    Apply

  and logic_symbol = Equals | NEquals | Or | And | Iff | If | Fi | Xor |
    Nor | Nand | Not | Op_Forall | Op_Exists |
    True | False

  and quantifier = (*interpreted binders*)
    Forall | Exists | Epsilon | Iota | Lambda | Dep_Prod | Dep_Sum

  and tptp_base_type =
    Type_Ind | Type_Bool | Type_Type | Type_Int | Type_Rat | Type_Real

  and symbol =
      Uninterpreted of string
    | Interpreted_ExtraLogic of interpreted_symbol
    | Interpreted_Logic of logic_symbol
    | TypeSymbol of tptp_base_type
    | System of string

  and general_term =
      General_Data of general_data (*general_data*)
    | General_Term of general_data * general_term (*general_data : general_term*)
    | General_List of general_term list

  and tptp_term =
      Term_Func of symbol * tptp_term list
    | Term_Var of string
    | Term_Conditional of tptp_formula * tptp_term * tptp_term
    | Term_Num of number_kind * string
    | Term_Distinct_Object of string
    | Term_Let of tptp_let list * tptp_term (*FIXME remove list?*)

  and tptp_atom =
      TFF_Typed_Atom of symbol * tptp_type option (*only TFF*)
    | THF_Atom_term of tptp_term   (*from here on, only THF*)
    | THF_Atom_conn_term of symbol

  and tptp_formula =
      Pred of symbol * tptp_term list
    | Fmla of symbol * tptp_formula list
    | Sequent of tptp_formula list * tptp_formula list
    | Quant of quantifier * (string * tptp_type option) list * tptp_formula
    | Conditional of tptp_formula * tptp_formula * tptp_formula
    | Let of tptp_let list * tptp_formula
    | Atom of tptp_atom
    | Type_fmla of tptp_type
    | THF_typing of tptp_formula * tptp_type

  and tptp_let =
      Let_fmla of (string * tptp_type option) * tptp_formula
    | Let_term of (string * tptp_type option) * tptp_term

  and tptp_type =
      Prod_type of tptp_type * tptp_type
    | Fn_type of tptp_type * tptp_type
    | Atom_type of string
    | Defined_type of tptp_base_type
    | Sum_type of tptp_type * tptp_type
    | Fmla_type of tptp_formula
    | Subtype of symbol * symbol

type general_list = general_term list
type parent_details = general_list
type useful_info = general_term list
type info = useful_info

(*type annotation = (source * info option)*)
type annotation = general_term * general_term list

exception DEQUOTE of string

type position = string * int * int

datatype tptp_line =
    Annotated_Formula of position * language * string * role * tptp_formula * annotation option
 |  Include of string * string list

type tptp_problem = tptp_line list

fun debug f x = if !Runtime.debug then (f x; ()) else ()

fun nameof_tff_atom_type (Atom_type str) = str
  | nameof_tff_atom_type _ = raise TPTP_SYNTAX "nameof_tff_atom_type called on non-atom type"

(*Used for debugging. Returns all files contained within a directory or its
subdirectories. Follows symbolic links, filters away directories.*)
fun get_file_list path =
  let
    fun check_file_entry f rest =
      let
        (*NOTE needed since no File.is_link and File.read_link*)
        val f_str = Path.implode f
      in
        if File.is_dir f then
          rest @ get_file_list f
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

fun role_to_string role =
  case role of
      Role_Axiom => "axiom"
    | Role_Hypothesis => "hypothesis"
    | Role_Definition => "definition"
    | Role_Assumption => "assumption"
    | Role_Lemma => "lemma"
    | Role_Theorem => "theorem"
    | Role_Conjecture => "conjecture"
    | Role_Negated_Conjecture => "negated_conjecture"
    | Role_Plain => "plain"
    | Role_Fi_Domain => "fi_domain"
    | Role_Fi_Functors => "fi_functors"
    | Role_Fi_Predicates => "fi_predicates"
    | Role_Type => "type"
    | Role_Unknown => "unknown"

(*accepts a string "'abc'" and returns "abc"*)
fun dequote str : single_quoted =
  if str = "" then
    raise (DEQUOTE "empty string")
  else
    (unprefix "'" str
    |> unsuffix "'"
    handle (Fail str) =>
      if str = "unprefix" then
        raise DEQUOTE ("string doesn't open with quote:" ^ str)
      else if str = "unsuffix" then
        raise DEQUOTE ("string doesn't close with quote:" ^ str)
      else raise Fail str)


(* Printing parsed TPTP formulas *)
(*FIXME this is not pretty-printing, just printing*)

fun status_to_string status_value =
  case status_value of
      Suc => "suc"	| Unp => "unp"
    | Sap => "sap"  | Esa => "esa"
    | Sat => "sat"  | Fsa => "fsa"
    | Thm => "thm"  | Wuc => "wuc"
    | Eqv => "eqv"	| Tac => "tac"
    | Wec => "wec"	| Eth => "eth"
    | Tau => "tau"	| Wtc => "wtc"
    | Wth => "wth"	| Cax => "cax"
    | Sca => "sca"	| Tca => "tca"
    | Wca => "wca"	| Cup => "cup"
    | Csp => "csp"	| Ecs => "ecs"
    | Csa => "csa"	| Cth => "cth"
    | Ceq => "ceq"	| Unc => "unc"
    | Wcc => "wcc"	| Ect => "ect"
    | Fun => "fun"	| Uns => "uns"
    | Wct => "wct"	| Scc => "scc"
    | Uca => "uca"	| Noc => "noc"

fun string_of_tptp_term x =
  case x of
      Term_Func (symbol, tptp_term_list) =>
        "(" ^ string_of_symbol symbol ^ " " ^
        String.concatWith " " (map string_of_tptp_term tptp_term_list) ^ ")"
    | Term_Var str => str
    | Term_Conditional (tptp_formula, tptp_term1, tptp_term2) => "" (*FIXME*)
    | Term_Num (_, str) => str
    | Term_Distinct_Object str => str

and string_of_symbol (Uninterpreted str) = str
  | string_of_symbol (Interpreted_ExtraLogic interpreted_symbol) = string_of_interpreted_symbol interpreted_symbol
  | string_of_symbol (Interpreted_Logic logic_symbol) = string_of_logic_symbol logic_symbol
  | string_of_symbol (TypeSymbol tptp_base_type) = string_of_tptp_base_type tptp_base_type
  | string_of_symbol (System str) = str

and string_of_tptp_base_type Type_Ind = "$i"
  | string_of_tptp_base_type Type_Bool = "$o"
  | string_of_tptp_base_type Type_Type = "$tType"
  | string_of_tptp_base_type Type_Int = "$int"
  | string_of_tptp_base_type Type_Rat = "$rat"
  | string_of_tptp_base_type Type_Real = "$real"

and string_of_interpreted_symbol x =
  case x of
      UMinus => "$uminus"
    | Sum => "$sum"
    | Difference => "$difference"
    | Product => "$product"
    | Quotient => "$quotient"
    | Quotient_E => "$quotient_e"
    | Quotient_T => "$quotient_t"
    | Quotient_F => "$quotient_f"
    | Remainder_E => "$remainder_e"
    | Remainder_T => "$remainder_t"
    | Remainder_F => "$remainder_f"
    | Floor => "$floor"
    | Ceiling => "$ceiling"
    | Truncate => "$truncate"
    | Round => "$round"
    | To_Int => "$to_int"
    | To_Rat => "$to_rat"
    | To_Real => "$to_real"
    | Less => "$less"
    | LessEq => "$lesseq"
    | Greater => "$greater"
    | GreaterEq => "$greatereq"
    | EvalEq => "$evaleq"
    | Is_Int => "$is_int"
    | Is_Rat => "$is_rat"
    | Apply => "@"

and string_of_logic_symbol Equals = "="
  | string_of_logic_symbol NEquals = "!="
  | string_of_logic_symbol Or = "|"
  | string_of_logic_symbol And = "&"
  | string_of_logic_symbol Iff = "<=>"
  | string_of_logic_symbol If = "=>"
  | string_of_logic_symbol Fi = "<="
  | string_of_logic_symbol Xor = "<~>"
  | string_of_logic_symbol Nor = "~|"
  | string_of_logic_symbol Nand = "~&"
  | string_of_logic_symbol Not = "~"
  | string_of_logic_symbol Op_Forall = "!!"
  | string_of_logic_symbol Op_Exists = "??"
  | string_of_logic_symbol True = "$true"
  | string_of_logic_symbol False = "$false"

and string_of_quantifier Forall = "!"
  | string_of_quantifier Exists  = "?"
  | string_of_quantifier Epsilon  = "@+"
  | string_of_quantifier Iota  = "@-"
  | string_of_quantifier Lambda  = "^"
  | string_of_quantifier Dep_Prod = "!>"
  | string_of_quantifier Dep_Sum  = "?*"

and string_of_tptp_atom (TFF_Typed_Atom (symbol, tptp_type_option)) =
    (case tptp_type_option of
       NONE => string_of_symbol symbol
     | SOME tptp_type =>
         string_of_symbol symbol ^ " : " ^ string_of_tptp_type tptp_type)
  | string_of_tptp_atom (THF_Atom_term tptp_term) = string_of_tptp_term tptp_term
  | string_of_tptp_atom (THF_Atom_conn_term symbol) = string_of_symbol symbol

and string_of_tptp_formula (Pred (symbol, tptp_term_list)) =
      "(" ^ string_of_symbol symbol ^
      String.concatWith " " (map string_of_tptp_term tptp_term_list) ^ ")"
  | string_of_tptp_formula (Fmla (symbol, tptp_formula_list)) =
      "(" ^
      string_of_symbol symbol ^
      String.concatWith " " (map string_of_tptp_formula tptp_formula_list) ^ ")"
  | string_of_tptp_formula (Sequent (tptp_formula_list1, tptp_formula_list2)) = "" (*FIXME*)
  | string_of_tptp_formula (Quant (quantifier, varlist, tptp_formula)) =
      string_of_quantifier quantifier ^ "[" ^
      String.concatWith ", " (map (fn (n, ty) =>
        case ty of
          NONE => n
        | SOME ty => n ^ " : " ^ string_of_tptp_type ty) varlist) ^ "] : (" ^
      string_of_tptp_formula tptp_formula ^ ")"
  | string_of_tptp_formula (Conditional _) = "" (*FIXME*)
  | string_of_tptp_formula (Let _) = "" (*FIXME*)
  | string_of_tptp_formula (Atom tptp_atom) = string_of_tptp_atom tptp_atom
  | string_of_tptp_formula (Type_fmla tptp_type) = string_of_tptp_type tptp_type
  | string_of_tptp_formula (THF_typing (tptp_formula, tptp_type)) =
      string_of_tptp_formula tptp_formula ^ " : " ^ string_of_tptp_type tptp_type

and string_of_tptp_type (Prod_type (tptp_type1, tptp_type2)) =
      string_of_tptp_type tptp_type1 ^ " * " ^ string_of_tptp_type tptp_type2
  | string_of_tptp_type (Fn_type (tptp_type1, tptp_type2)) =
      string_of_tptp_type tptp_type1 ^ " > " ^ string_of_tptp_type tptp_type2
  | string_of_tptp_type (Atom_type str) = str
  | string_of_tptp_type (Defined_type tptp_base_type) =
      string_of_tptp_base_type tptp_base_type
  | string_of_tptp_type (Sum_type (tptp_type1, tptp_type2)) = ""
  | string_of_tptp_type (Fmla_type tptp_formula) = string_of_tptp_formula tptp_formula
  | string_of_tptp_type (Subtype (symbol1, symbol2)) =
      string_of_symbol symbol1 ^ " << " ^ string_of_symbol symbol2

end
