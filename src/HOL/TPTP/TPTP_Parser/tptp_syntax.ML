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
    Type_Ind | Type_Bool | Type_Type | Type_Int | Type_Rat | Type_Real | Type_Dummy

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
      Term_FuncG of symbol * tptp_type list (*special hack for TPTP_Interpret*) * tptp_term list
    | Term_Var of string
    | Term_Conditional of tptp_formula * tptp_term * tptp_term
    | Term_Num of number_kind * string
    | Term_Distinct_Object of string
    | Term_Let of tptp_let * tptp_term

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
    | Let of tptp_let * tptp_formula
    | Atom of tptp_atom
    | Type_fmla of tptp_type
    | THF_typing of tptp_formula * tptp_type (*only THF*)

  and tptp_let =
      Let_fmla of (string * tptp_type option) list * tptp_formula
    | Let_term of (string * tptp_type option) list * tptp_term

  and tptp_type =
      Prod_type of tptp_type * tptp_type
    | Fn_type of tptp_type * tptp_type
    | Atom_type of string * tptp_type list
    | Var_type of string
    | Defined_type of tptp_base_type
    | Sum_type of tptp_type * tptp_type (*only THF*)
    | Fmla_type of tptp_formula
    | Subtype of symbol * symbol (*only THF*)

  val Term_Func: symbol * tptp_term list -> tptp_term (*for Yacc parser*)

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
   |  Include of position * string * string list

  type tptp_problem = tptp_line list

  val dequote : single_quoted -> single_quoted

  val role_to_string : role -> string

  val status_to_string : status_value -> string

  val pos_of_line : tptp_line -> position

  (*Returns the list of all files included in a directory and its
  subdirectories. This is only used for testing the parser/interpreter against
  all THF problems.*)
  val get_file_list : Path.T -> Path.T list

  val read_status : string -> status_value
  val string_of_tptp_term : tptp_term -> string
  val string_of_interpreted_symbol : interpreted_symbol -> string
  val string_of_tptp_formula : tptp_formula -> string

  val latex_of_tptp_formula : tptp_formula -> string

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
    Type_Ind | Type_Bool | Type_Type | Type_Int | Type_Rat | Type_Real | Type_Dummy

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
      Term_FuncG of symbol * tptp_type list (*special hack for TPTP_Interpret*) * tptp_term list
    | Term_Var of string
    | Term_Conditional of tptp_formula * tptp_term * tptp_term
    | Term_Num of number_kind * string
    | Term_Distinct_Object of string
    | Term_Let of tptp_let * tptp_term

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
    | Let of tptp_let * tptp_formula
    | Atom of tptp_atom
    | Type_fmla of tptp_type
    | THF_typing of tptp_formula * tptp_type

  and tptp_let =
      Let_fmla of (string * tptp_type option) list * tptp_formula
    | Let_term of (string * tptp_type option) list * tptp_term

  and tptp_type =
      Prod_type of tptp_type * tptp_type
    | Fn_type of tptp_type * tptp_type
    | Atom_type of string * tptp_type list
    | Var_type of string
    | Defined_type of tptp_base_type
    | Sum_type of tptp_type * tptp_type
    | Fmla_type of tptp_formula
    | Subtype of symbol * symbol

fun Term_Func (symb, ts) = Term_FuncG (symb, [], ts)

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
 |  Include of position * string * string list

type tptp_problem = tptp_line list

fun debug f x = if Options.default_bool \<^system_option>\<open>ML_exception_trace\<close> then (f x; ()) else ()

fun pos_of_line tptp_line =
  case tptp_line of
      Annotated_Formula (position, _, _, _, _, _) => position
   |  Include (position, _, _) => position

(*Used for debugging. Returns all files contained within a directory or its
subdirectories. Follows symbolic links, filters away directories.
Files are ordered by size*)
fun get_file_list path =
  let
    fun get_file_list' acc paths =
      case paths of
          [] => acc
        | (f :: fs) =>
            let
              (*NOTE needed since no File.is_link and File.read_link*)
              val f_str = Path.implode f
            in
              if File.is_dir f then
                let
                  val contents =
                    File.read_dir f
                    |> map
                        (Path.explode
                        #> Path.append f)
                in
                  get_file_list' acc (fs @ contents)
                end
              else if OS.FileSys.isLink f_str then
                (*follow links -- NOTE this breaks if links are relative paths*)
                get_file_list' acc (Path.explode (OS.FileSys.readLink f_str) :: fs)
              else
                get_file_list' ((f, OS.FileSys.fileSize f_str) :: acc) fs
            end
  in
    get_file_list' [] [path]
    |> sort (fn ((_, n1), (_, n2)) => Int.compare (n1, n2))
    |> map fst
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

exception UNRECOGNISED_STATUS of string
fun read_status status =
  case status of
      "suc" => Suc  | "unp" => Unp
    | "sap" => Sap  | "esa" => Esa
    | "sat" => Sat  | "fsa" => Fsa
    | "thm" => Thm  | "wuc" => Wuc
    | "eqv" => Eqv  | "tac" => Tac
    | "wec" => Wec  | "eth" => Eth
    | "tau" => Tau  | "wtc" => Wtc
    | "wth" => Wth  | "cax" => Cax
    | "sca" => Sca  | "tca" => Tca
    | "wca" => Wca  | "cup" => Cup
    | "csp" => Csp  | "ecs" => Ecs
    | "csa" => Csa  | "cth" => Cth
    | "ceq" => Ceq  | "unc" => Unc
    | "wcc" => Wcc  | "ect" => Ect
    | "fun" => Fun  | "uns" => Uns
    | "wct" => Wct  | "scc" => Scc
    | "uca" => Uca  | "noc" => Noc
    | thing => raise (UNRECOGNISED_STATUS thing)

(* Printing parsed TPTP formulas *)
(*FIXME this is not pretty-printing, just printing*)

fun status_to_string status_value =
  case status_value of
      Suc => "suc"  | Unp => "unp"
    | Sap => "sap"  | Esa => "esa"
    | Sat => "sat"  | Fsa => "fsa"
    | Thm => "thm"  | Wuc => "wuc"
    | Eqv => "eqv"  | Tac => "tac"
    | Wec => "wec"  | Eth => "eth"
    | Tau => "tau"  | Wtc => "wtc"
    | Wth => "wth"  | Cax => "cax"
    | Sca => "sca"  | Tca => "tca"
    | Wca => "wca"  | Cup => "cup"
    | Csp => "csp"  | Ecs => "ecs"
    | Csa => "csa"  | Cth => "cth"
    | Ceq => "ceq"  | Unc => "unc"
    | Wcc => "wcc"  | Ect => "ect"
    | Fun => "fun"  | Uns => "uns"
    | Wct => "wct"  | Scc => "scc"
    | Uca => "uca"  | Noc => "noc"

fun string_of_tptp_term x =
  case x of
      Term_FuncG (symbol, tptp_type_list, tptp_term_list) =>
        "(" ^ string_of_symbol symbol ^ " " ^
        implode_space (map string_of_tptp_type tptp_type_list
          @ map string_of_tptp_term tptp_term_list) ^ ")"
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
  | string_of_tptp_base_type Type_Dummy = "$_"

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
    | Distinct => "$distinct"
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
      implode_space (map string_of_tptp_term tptp_term_list) ^ ")"
  | string_of_tptp_formula (Fmla (symbol, tptp_formula_list)) =
      "(" ^
      string_of_symbol symbol ^
      implode_space (map string_of_tptp_formula tptp_formula_list) ^ ")"
  | string_of_tptp_formula (Sequent (tptp_formula_list1, tptp_formula_list2)) = "" (*FIXME*)
  | string_of_tptp_formula (Quant (quantifier, varlist, tptp_formula)) =
      string_of_quantifier quantifier ^ "[" ^
      space_implode ", " (map (fn (n, ty) =>
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
  | string_of_tptp_type (Atom_type (str, [])) = str
  | string_of_tptp_type (Atom_type (str, tptp_types)) =
      str ^ "(" ^ commas (map string_of_tptp_type tptp_types) ^ ")"
  | string_of_tptp_type (Var_type str) = str
  | string_of_tptp_type (Defined_type tptp_base_type) =
      string_of_tptp_base_type tptp_base_type
  | string_of_tptp_type (Sum_type (tptp_type1, tptp_type2)) = ""
  | string_of_tptp_type (Fmla_type tptp_formula) = string_of_tptp_formula tptp_formula
  | string_of_tptp_type (Subtype (symbol1, symbol2)) =
      string_of_symbol symbol1 ^ " << " ^ string_of_symbol symbol2

(*FIXME formatting details haven't been fully worked out -- don't use this function for anything serious in its current form!*)
(*TODO Add subscripting*)
(*infix symbols, including \subset, \cup, \cap*)
fun latex_of_tptp_term x =
  case x of
      Term_FuncG (Interpreted_Logic Equals, [], [tptp_t1, tptp_t2]) =>
        "(" ^ latex_of_tptp_term tptp_t1 ^ " = " ^ latex_of_tptp_term tptp_t2 ^ ")"
    | Term_FuncG (Interpreted_Logic NEquals, [], [tptp_t1, tptp_t2]) =>
        "(" ^ latex_of_tptp_term tptp_t1 ^ " \\\\neq " ^ latex_of_tptp_term tptp_t2 ^ ")"
    | Term_FuncG (Interpreted_Logic Or, [], [tptp_t1, tptp_t2]) =>
        "(" ^ latex_of_tptp_term tptp_t1 ^ " \\\\vee " ^ latex_of_tptp_term tptp_t2 ^ ")"
    | Term_FuncG (Interpreted_Logic And, [], [tptp_t1, tptp_t2]) =>
        "(" ^ latex_of_tptp_term tptp_t1 ^ " \\\\wedge " ^ latex_of_tptp_term tptp_t2 ^ ")"
    | Term_FuncG (Interpreted_Logic Iff, [], [tptp_t1, tptp_t2]) =>
        "(" ^ latex_of_tptp_term tptp_t1 ^ " \\\\longleftrightarrow " ^ latex_of_tptp_term tptp_t2 ^ ")"
    | Term_FuncG (Interpreted_Logic If, [], [tptp_t1, tptp_t2]) =>
        "(" ^ latex_of_tptp_term tptp_t1 ^ " \\\\longrightarrow " ^ latex_of_tptp_term tptp_t2 ^ ")"

    | Term_FuncG (symbol, tptp_type_list, tptp_term_list) =>
        (*"(" ^*) latex_of_symbol symbol ^ "\\\\, " ^
        space_implode "\\\\, " (map latex_of_tptp_type tptp_type_list
          @ map latex_of_tptp_term tptp_term_list) (*^ ")"*)
    | Term_Var str => "\\\\mathrm{" ^ str ^ "}"
    | Term_Conditional (tptp_formula, tptp_term1, tptp_term2) => "" (*FIXME*)
    | Term_Num (_, str) => str
    | Term_Distinct_Object str => str (*FIXME*)

and latex_of_symbol (Uninterpreted str) =
    if str = "emptyset" then "\\\\emptyset"
    else "\\\\mathrm{" ^ str ^ "}"
  | latex_of_symbol (Interpreted_ExtraLogic interpreted_symbol) = latex_of_interpreted_symbol interpreted_symbol
  | latex_of_symbol (Interpreted_Logic logic_symbol) = latex_of_logic_symbol logic_symbol
  | latex_of_symbol (TypeSymbol tptp_base_type) = latex_of_tptp_base_type tptp_base_type
  | latex_of_symbol (System str) = "\\\\mathrm{" ^ str ^ "}"

and latex_of_tptp_base_type Type_Ind = "\\\\iota "
  | latex_of_tptp_base_type Type_Bool = "o"
  | latex_of_tptp_base_type Type_Type = "\\\\mathcal{T} "
  | latex_of_tptp_base_type Type_Int = "\\\\mathsf{int} "
  | latex_of_tptp_base_type Type_Rat = "\\\\mathsf{rat} "
  | latex_of_tptp_base_type Type_Real = "\\\\mathsf{real} "
  | latex_of_tptp_base_type Type_Dummy = "\\\\mathsf{\\\\_} "

and latex_of_interpreted_symbol x =
  case x of
      UMinus => "-"
    | Sum => "-"
    | Difference => "-"
    | Product => "*"
    | Quotient => "/"
    | Quotient_E => "" (*FIXME*)
    | Quotient_T => "" (*FIXME*)
    | Quotient_F => "" (*FIXME*)
    | Remainder_E => "" (*FIXME*)
    | Remainder_T => "" (*FIXME*)
    | Remainder_F => "" (*FIXME*)
    | Floor => "" (*FIXME*)
    | Ceiling => "" (*FIXME*)
    | Truncate => "" (*FIXME*)
    | Round => "" (*FIXME*)
    | To_Int => "" (*FIXME*)
    | To_Rat => "" (*FIXME*)
    | To_Real => "" (*FIXME*)
    | Less => "<"
    | LessEq => "\\\\leq "
    | Greater => ">"
    | GreaterEq => "\\\\geq "
    | EvalEq => "" (*FIXME*)
    | Is_Int => "" (*FIXME*)
    | Is_Rat => "" (*FIXME*)
    | Distinct => "" (*FIXME*)
    | Apply => "\\\\;"

and latex_of_logic_symbol Equals = "="
  | latex_of_logic_symbol NEquals = "\\\\neq "
  | latex_of_logic_symbol Or = "\\\\vee "
  | latex_of_logic_symbol And = "\\\\wedge "
  | latex_of_logic_symbol Iff = "\\\\longleftrightarrow "
  | latex_of_logic_symbol If = "\\\\longrightarrow "
  | latex_of_logic_symbol Fi = "\\\\longleftarrow "
  | latex_of_logic_symbol Xor = "\\\\oplus "
  | latex_of_logic_symbol Nor = "\\\\not\\\\vee "
  | latex_of_logic_symbol Nand = "\\\\not\\\\wedge "
  | latex_of_logic_symbol Not = "\\\\neg "
  | latex_of_logic_symbol Op_Forall = "\\\\forall "
  | latex_of_logic_symbol Op_Exists = "\\\\exists "
  | latex_of_logic_symbol True = "\\\\mathsf{true} "
  | latex_of_logic_symbol False = "\\\\mathsf{false} "

and latex_of_quantifier Forall = "\\\\forall "
  | latex_of_quantifier Exists  = "\\\\exists "
  | latex_of_quantifier Epsilon  = "\\\\varepsilon "
  | latex_of_quantifier Iota  = "" (*FIXME*)
  | latex_of_quantifier Lambda  = "\\\\lambda "
  | latex_of_quantifier Dep_Prod = "\\\\Pi "
  | latex_of_quantifier Dep_Sum  = "\\\\Sigma "

and latex_of_tptp_atom (TFF_Typed_Atom (symbol, tptp_type_option)) =
    (case tptp_type_option of
       NONE => latex_of_symbol symbol
     | SOME tptp_type =>
         latex_of_symbol symbol ^ " : " ^ latex_of_tptp_type tptp_type)
  | latex_of_tptp_atom (THF_Atom_term tptp_term) = latex_of_tptp_term tptp_term
  | latex_of_tptp_atom (THF_Atom_conn_term symbol) = latex_of_symbol symbol

and latex_of_tptp_formula (Pred (Interpreted_Logic Equals, [tptp_t1, tptp_t2])) =
      "(" ^ latex_of_tptp_term tptp_t1 ^ " = " ^ latex_of_tptp_term tptp_t2 ^ ")"
  | latex_of_tptp_formula (Pred (Interpreted_Logic NEquals, [tptp_t1, tptp_t2])) =
      "(" ^ latex_of_tptp_term tptp_t1 ^ " \\\\neq " ^ latex_of_tptp_term tptp_t2 ^ ")"
  | latex_of_tptp_formula (Pred (Interpreted_Logic Or, [tptp_t1, tptp_t2])) =
      "(" ^ latex_of_tptp_term tptp_t1 ^ " \\\\vee " ^ latex_of_tptp_term tptp_t2 ^ ")"
  | latex_of_tptp_formula (Pred (Interpreted_Logic And, [tptp_t1, tptp_t2])) =
      "(" ^ latex_of_tptp_term tptp_t1 ^ " \\\\wedge " ^ latex_of_tptp_term tptp_t2 ^ ")"
  | latex_of_tptp_formula (Pred (Interpreted_Logic Iff, [tptp_t1, tptp_t2])) =
      "(" ^ latex_of_tptp_term tptp_t1 ^ " \\\\longleftrightarrow " ^ latex_of_tptp_term tptp_t2 ^ ")"
  | latex_of_tptp_formula (Pred (Interpreted_Logic If, [tptp_t1, tptp_t2])) =
      "(" ^ latex_of_tptp_term tptp_t1 ^ " \\\\longrightarrow " ^ latex_of_tptp_term tptp_t2 ^ ")"

  | latex_of_tptp_formula (x as (Pred (symbol, tptp_term_list))) =
      latex_of_symbol symbol ^
       space_implode "\\\\, " (map latex_of_tptp_term tptp_term_list)

  | latex_of_tptp_formula (Fmla (Interpreted_ExtraLogic Apply, [Fmla (Interpreted_ExtraLogic Apply, [Atom (THF_Atom_term (Term_FuncG (Uninterpreted "union", [], []))), tptp_f1]), tptp_f2])) =
      "(" ^ latex_of_tptp_formula tptp_f1 ^ " \\\\cup " ^ latex_of_tptp_formula tptp_f2 ^ ")"

  | latex_of_tptp_formula (Fmla (Interpreted_ExtraLogic Apply, [Fmla (Interpreted_ExtraLogic Apply, [Atom (THF_Atom_term (Term_FuncG (Uninterpreted "subset", [], []))), tptp_f1]), tptp_f2])) =
      "(" ^ latex_of_tptp_formula tptp_f1 ^ " \\\\subset " ^ latex_of_tptp_formula tptp_f2 ^ ")"

  | latex_of_tptp_formula (Fmla (Interpreted_Logic Equals, [tptp_f1, tptp_f2])) =
      "(" ^ latex_of_tptp_formula tptp_f1 ^ " = " ^ latex_of_tptp_formula tptp_f2 ^ ")"
  | latex_of_tptp_formula (Fmla (Interpreted_Logic NEquals, [tptp_f1, tptp_f2])) =
      "(" ^ latex_of_tptp_formula tptp_f1 ^ " \\\\neq " ^ latex_of_tptp_formula tptp_f2 ^ ")"
  | latex_of_tptp_formula (Fmla (Interpreted_Logic Or, [tptp_f1, tptp_f2])) =
      "(" ^ latex_of_tptp_formula tptp_f1 ^ " \\\\vee " ^ latex_of_tptp_formula tptp_f2 ^ ")"
  | latex_of_tptp_formula (Fmla (Interpreted_Logic And, [tptp_f1, tptp_f2])) =
      "(" ^ latex_of_tptp_formula tptp_f1 ^ " \\\\wedge " ^ latex_of_tptp_formula tptp_f2 ^ ")"
  | latex_of_tptp_formula (Fmla (Interpreted_Logic Iff, [tptp_f1, tptp_f2])) =
      "(" ^ latex_of_tptp_formula tptp_f1 ^ " \\\\longleftrightarrow " ^ latex_of_tptp_formula tptp_f2 ^ ")"
  | latex_of_tptp_formula (Fmla (Interpreted_Logic If, [tptp_f1, tptp_f2])) =
      "(" ^ latex_of_tptp_formula tptp_f1 ^ " \\\\longrightarrow " ^ latex_of_tptp_formula tptp_f2 ^ ")"

  | latex_of_tptp_formula (x as (Fmla (symbol, tptp_formula_list))) =
      latex_of_symbol symbol ^
        space_implode "\\\\, " (map latex_of_tptp_formula tptp_formula_list)

  | latex_of_tptp_formula (Sequent (tptp_formula_list1, tptp_formula_list2)) = "" (*FIXME*)
  | latex_of_tptp_formula (Quant (quantifier, varlist, tptp_formula)) =
      latex_of_quantifier quantifier ^
      space_implode ", " (map (fn (n, ty) =>
        case ty of
          NONE => "\\\\mathrm{" ^ n ^ "}"
        | SOME ty => "\\\\mathrm{" ^ n ^ "} : " ^ latex_of_tptp_type ty) varlist) ^ ". (" ^
      latex_of_tptp_formula tptp_formula ^ ")"
  | latex_of_tptp_formula (Conditional _) = "" (*FIXME*)
  | latex_of_tptp_formula (Let _) = "" (*FIXME*)
  | latex_of_tptp_formula (Atom tptp_atom) = latex_of_tptp_atom tptp_atom
  | latex_of_tptp_formula (Type_fmla tptp_type) = latex_of_tptp_type tptp_type
  | latex_of_tptp_formula (THF_typing (tptp_formula, tptp_type)) =
      latex_of_tptp_formula tptp_formula ^ " : " ^ latex_of_tptp_type tptp_type

and latex_of_tptp_type (Prod_type (tptp_type1, tptp_type2)) =
      latex_of_tptp_type tptp_type1 ^ " \\\\times " ^ latex_of_tptp_type tptp_type2
  | latex_of_tptp_type (Fn_type (tptp_type1, tptp_type2)) =
      latex_of_tptp_type tptp_type1 ^ " \\\\to " ^ latex_of_tptp_type tptp_type2
  | latex_of_tptp_type (Atom_type (str, [])) = "\\\\mathrm{" ^ str ^ "}"
  | latex_of_tptp_type (Atom_type (str, tptp_types)) =
    "\\\\mathrm{" ^ str ^ "}(" ^ commas (map latex_of_tptp_type tptp_types) ^ ")"
  | latex_of_tptp_type (Var_type str) = "\\\\mathrm{" ^ str ^ "}"
  | latex_of_tptp_type (Defined_type tptp_base_type) =
      latex_of_tptp_base_type tptp_base_type
  | latex_of_tptp_type (Sum_type (tptp_type1, tptp_type2)) = ""
  | latex_of_tptp_type (Fmla_type tptp_formula) = latex_of_tptp_formula tptp_formula
  | latex_of_tptp_type (Subtype (symbol1, symbol2)) = "" (*FIXME*)

end
