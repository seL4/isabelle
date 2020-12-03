(*  Title:      HOL/Tools/ATP/atp_problem.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

Abstract representation of ATP problems and TPTP syntax.
*)

signature ATP_PROBLEM =
sig
  datatype ('a, 'b) atp_term =
    ATerm of ('a * 'b list) * ('a, 'b) atp_term list |
    AAbs of (('a * 'b) * ('a, 'b) atp_term) * ('a, 'b) atp_term list
  datatype atp_quantifier = AForall | AExists
  datatype atp_connective = ANot | AAnd | AOr | AImplies | AIff
  datatype ('a, 'b, 'c, 'd) atp_formula =
    ATyQuant of atp_quantifier * ('b * 'd list) list
        * ('a, 'b, 'c, 'd) atp_formula |
    AQuant of atp_quantifier * ('a * 'b option) list
        * ('a, 'b, 'c, 'd) atp_formula |
    AConn of atp_connective * ('a, 'b, 'c, 'd) atp_formula list |
    AAtom of 'c

  datatype 'a atp_type =
    AType of ('a * 'a list) * 'a atp_type list |
    AFun of 'a atp_type * 'a atp_type |
    APi of 'a list * 'a atp_type

  type term_order =
    {is_lpo : bool,
     gen_weights : bool,
     gen_prec : bool,
     gen_simp : bool}

  datatype fool = Without_FOOL | With_FOOL
  datatype polymorphism = Monomorphic | Polymorphic
  datatype thf_flavor = THF_Lambda_Free | THF_Without_Choice | THF_With_Choice

  datatype atp_format =
    CNF |
    CNF_UEQ |
    FOF |
    TFF of fool * polymorphism |
    THF of fool * polymorphism * thf_flavor |
    DFG of polymorphism

  datatype atp_formula_role =
    Axiom | Definition | Lemma | Hypothesis | Conjecture | Negated_Conjecture |
    Plain | Type_Role | Unknown

  datatype 'a atp_problem_line =
    Class_Decl of string * 'a * 'a list |
    Type_Decl of string * 'a * int |
    Sym_Decl of string * 'a * 'a atp_type |
    Datatype_Decl of
      string * ('a * 'a list) list * 'a atp_type * ('a, 'a atp_type) atp_term list * bool |
    Class_Memb of string * ('a * 'a list) list * 'a atp_type * 'a |
    Formula of (string * string) * atp_formula_role
               * ('a, 'a atp_type, ('a, 'a atp_type) atp_term, 'a) atp_formula
               * (string, string atp_type) atp_term option
               * (string, string atp_type) atp_term list
  type 'a atp_problem = (string * 'a atp_problem_line list) list

  val tptp_cnf : string
  val tptp_fof : string
  val tptp_tff : string
  val tptp_thf : string
  val tptp_has_type : string
  val tptp_type_of_types : string
  val tptp_bool_type : string
  val tptp_individual_type : string
  val tptp_fun_type : string
  val tptp_product_type : string
  val tptp_forall : string
  val tptp_ho_forall : string
  val tptp_pi_binder : string
  val tptp_exists : string
  val tptp_ho_exists : string
  val tptp_choice : string
  val tptp_ho_choice : string
  val tptp_hilbert_choice : string
  val tptp_hilbert_the : string
  val tptp_not : string
  val tptp_and : string
  val tptp_not_and : string
  val tptp_or : string
  val tptp_not_or : string
  val tptp_implies : string
  val tptp_if : string
  val tptp_iff : string
  val tptp_not_iff : string
  val tptp_app : string
  val tptp_not_infix : string
  val tptp_equal : string
  val tptp_not_equal : string
  val tptp_old_equal : string
  val tptp_false : string
  val tptp_true : string
  val tptp_lambda : string
  val tptp_empty_list : string
  val tptp_unary_builtins : string list
  val tptp_binary_builtins : string list
  val dfg_individual_type : string
  val isabelle_info_prefix : string
  val isabelle_info : bool -> string -> int -> (string, 'a) atp_term list
  val extract_isabelle_status : (string, 'a) atp_term list -> string option
  val extract_isabelle_rank : (string, 'a) atp_term list -> int
  val inductionN : string
  val introN : string
  val inductiveN : string
  val elimN : string
  val simpN : string
  val non_rec_defN : string
  val rec_defN : string
  val rankN : string
  val minimum_rank : int
  val default_rank : int
  val default_term_order_weight : int
  val is_tptp_equal : string -> bool
  val is_built_in_tptp_symbol : string -> bool
  val is_tptp_variable : string -> bool
  val is_tptp_user_symbol : string -> bool
  val bool_atype : (string * string) atp_type
  val individual_atype : (string * string) atp_type
  val mk_anot : ('a, 'b, 'c, 'd) atp_formula -> ('a, 'b, 'c, 'd) atp_formula
  val mk_aconn :
    atp_connective -> ('a, 'b, 'c, 'd) atp_formula
    -> ('a, 'b, 'c, 'd) atp_formula -> ('a, 'b, 'c, 'd) atp_formula
  val mk_app : (string, 'a) atp_term -> (string, 'a) atp_term -> (string, 'a) atp_term
  val mk_apps :  (string, 'a) atp_term -> (string, 'a) atp_term list -> (string, 'a) atp_term
  val mk_simple_aterm:  'a -> ('a, 'b) atp_term
  val aconn_fold :
    bool option -> (bool option -> 'a -> 'b -> 'b) -> atp_connective * 'a list
    -> 'b -> 'b
  val aconn_map :
    bool option -> (bool option -> 'a -> ('b, 'c, 'd, 'e) atp_formula)
    -> atp_connective * 'a list -> ('b, 'c, 'd, 'e) atp_formula
  val formula_fold :
    bool option -> (bool option -> 'c -> 'e -> 'e)
    -> ('a, 'b, 'c, 'd) atp_formula -> 'e -> 'e
  val formula_map :
    ('c -> 'e) -> ('a, 'b, 'c, 'd) atp_formula -> ('a, 'b, 'e, 'd) atp_formula
  val strip_atype : 'a atp_type -> 'a list * ('a atp_type list * 'a atp_type)
  val is_format_higher_order : atp_format -> bool
  val tptp_string_of_format : atp_format -> string
  val tptp_string_of_role : atp_formula_role -> string
  val tptp_string_of_line : atp_format -> string atp_problem_line -> string
  val lines_of_atp_problem :
    atp_format -> term_order -> (unit -> (string * int) list)
    -> string atp_problem -> string list
  val ensure_cnf_problem :
    (string * string) atp_problem -> (string * string) atp_problem
  val filter_cnf_ueq_problem :
    (string * string) atp_problem -> (string * string) atp_problem
  val declared_in_atp_problem : 'a atp_problem -> ('a list * 'a list) * 'a list
  val nice_atp_problem :
    bool -> atp_format -> ('a * (string * string) atp_problem_line list) list
    -> ('a * string atp_problem_line list) list
       * (string Symtab.table * string Symtab.table) option
end;

structure ATP_Problem : ATP_PROBLEM =
struct

open ATP_Util

val parens = enclose "(" ")"

(** ATP problem **)

datatype ('a, 'b) atp_term =
  ATerm of ('a * 'b list) * ('a, 'b) atp_term list |
  AAbs of (('a * 'b) * ('a, 'b) atp_term) * ('a, 'b) atp_term list
datatype atp_quantifier = AForall | AExists
datatype atp_connective = ANot | AAnd | AOr | AImplies | AIff
datatype ('a, 'b, 'c, 'd) atp_formula =
  ATyQuant of atp_quantifier * ('b * 'd list) list
      * ('a, 'b, 'c, 'd) atp_formula |
  AQuant of atp_quantifier * ('a * 'b option) list
      * ('a, 'b, 'c, 'd) atp_formula |
  AConn of atp_connective * ('a, 'b, 'c, 'd) atp_formula list |
  AAtom of 'c

datatype 'a atp_type =
  AType of ('a * 'a list) * 'a atp_type list |
  AFun of 'a atp_type * 'a atp_type |
  APi of 'a list * 'a atp_type

type term_order =
  {is_lpo : bool,
   gen_weights : bool,
   gen_prec : bool,
   gen_simp : bool}

datatype fool = Without_FOOL | With_FOOL
datatype polymorphism = Monomorphic | Polymorphic
datatype thf_flavor = THF_Lambda_Free | THF_Without_Choice | THF_With_Choice

datatype atp_format =
  CNF |
  CNF_UEQ |
  FOF |
  TFF of fool * polymorphism |
  THF of fool * polymorphism * thf_flavor |
  DFG of polymorphism

datatype atp_formula_role =
  Axiom | Definition | Lemma | Hypothesis | Conjecture | Negated_Conjecture |
  Plain | Type_Role | Unknown

datatype 'a atp_problem_line =
  Class_Decl of string * 'a * 'a list |
  Type_Decl of string * 'a * int |
  Sym_Decl of string * 'a * 'a atp_type |
  Datatype_Decl of
    string * ('a * 'a list) list * 'a atp_type * ('a, 'a atp_type) atp_term list * bool |
  Class_Memb of string * ('a * 'a list) list * 'a atp_type * 'a |
  Formula of (string * string) * atp_formula_role
             * ('a, 'a atp_type, ('a, 'a atp_type) atp_term, 'a) atp_formula
             * (string, string atp_type) atp_term option
             * (string, string atp_type) atp_term list
type 'a atp_problem = (string * 'a atp_problem_line list) list

(* official TPTP syntax *)
val tptp_cnf = "cnf"
val tptp_fof = "fof"
val tptp_tff = "tff"
val tptp_thf = "thf"
val tptp_has_type = ":"
val tptp_type_of_types = "$tType"
val tptp_bool_type = "$o"
val tptp_individual_type = "$i"
val tptp_fun_type = ">"
val tptp_product_type = "*"
val tptp_forall = "!"
val tptp_ho_forall = "!!"
val tptp_pi_binder = "!>"
val tptp_exists = "?"
val tptp_ho_exists = "??"
val tptp_choice = "@+"
val tptp_ho_choice = "@@+"
val tptp_not = "~"
val tptp_and = "&"
val tptp_not_and = "~&"
val tptp_or = "|"
val tptp_not_or = "~|"
val tptp_implies = "=>"
val tptp_if = "<="
val tptp_iff = "<=>"
val tptp_not_iff = "<~>"
val tptp_app = "@"
val tptp_hilbert_choice = "@+"
val tptp_hilbert_the = "@-"
val tptp_not_infix = "!"
val tptp_equal = "="
val tptp_not_equal = "!="
val tptp_old_equal = "equal"
val tptp_false = "$false"
val tptp_true = "$true"
val tptp_lambda = "^"
val tptp_empty_list = "[]"

val tptp_unary_builtins = [tptp_not]
val tptp_binary_builtins =
  [tptp_and, tptp_or, tptp_implies, tptp_if, tptp_iff, tptp_not_iff, tptp_equal]

val dfg_individual_type = "iii" (* cannot clash *)

val isabelle_info_prefix = "isabelle_"

val inductionN = "induction"
val introN = "intro"
val inductiveN = "inductive"
val elimN = "elim"
val simpN = "simp"
val non_rec_defN = "non_rec_def"
val rec_defN = "rec_def"

val rankN = "rank"

val minimum_rank = 0
val default_rank = 1000
val default_term_order_weight = 1

(* Currently, only SPASS 3.8ds and (to a lesser extent) Metis can process Isabelle
   metainformation. *)
fun isabelle_info generate_info status rank =
  if generate_info then
    [] |> rank <> default_rank
          ? cons (ATerm ((isabelle_info_prefix ^ rankN, []),
                         [ATerm ((string_of_int rank, []), [])]))
       |> status <> "" ? cons (ATerm ((isabelle_info_prefix ^ status, []), []))
  else
    []

fun extract_isabelle_status (ATerm ((s, []), []) :: _) =
    try (unprefix isabelle_info_prefix) s
  | extract_isabelle_status _ = NONE

fun extract_isabelle_rank (tms as _ :: _) =
    (case List.last tms of
       ATerm ((_, []), [ATerm ((rank, []), [])]) => the (Int.fromString rank)
     | _ => default_rank)
  | extract_isabelle_rank _ = default_rank

fun is_tptp_equal s = (s = tptp_equal orelse s = tptp_old_equal)
fun is_built_in_tptp_symbol s =
  s = tptp_old_equal orelse not (Char.isAlpha (String.sub (s, 0)))
fun is_tptp_variable s = s <> "" andalso Char.isUpper (String.sub (s, 0))
val is_tptp_user_symbol = not o (is_tptp_variable orf is_built_in_tptp_symbol)

val bool_atype = AType ((`I tptp_bool_type, []), [])
val individual_atype = AType ((`I tptp_individual_type, []), [])

fun raw_polarities_of_conn ANot = (SOME false, NONE)
  | raw_polarities_of_conn AAnd = (SOME true, SOME true)
  | raw_polarities_of_conn AOr = (SOME true, SOME true)
  | raw_polarities_of_conn AImplies = (SOME false, SOME true)
  | raw_polarities_of_conn AIff = (NONE, NONE)
fun polarities_of_conn NONE = K (NONE, NONE)
  | polarities_of_conn (SOME pos) =
    raw_polarities_of_conn #> not pos ? apply2 (Option.map not)

fun mk_anot (AConn (ANot, [phi])) = phi
  | mk_anot phi = AConn (ANot, [phi])
fun mk_aconn c phi1 phi2 = AConn (c, [phi1, phi2])

fun mk_app t u = ATerm ((tptp_app, []), [t, u])
fun mk_apps f xs = fold (fn x => fn f => mk_app f x) xs f

fun mk_simple_aterm p = ATerm ((p, []), [])

fun aconn_fold pos f (ANot, [phi]) = f (Option.map not pos) phi
  | aconn_fold pos f (AImplies, [phi1, phi2]) =
    f (Option.map not pos) phi1 #> f pos phi2
  | aconn_fold pos f (AAnd, phis) = fold (f pos) phis
  | aconn_fold pos f (AOr, phis) = fold (f pos) phis
  | aconn_fold _ f (_, phis) = fold (f NONE) phis

fun aconn_map pos f (ANot, [phi]) = AConn (ANot, [f (Option.map not pos) phi])
  | aconn_map pos f (AImplies, [phi1, phi2]) =
    AConn (AImplies, [f (Option.map not pos) phi1, f pos phi2])
  | aconn_map pos f (AAnd, phis) = AConn (AAnd, map (f pos) phis)
  | aconn_map pos f (AOr, phis) = AConn (AOr, map (f pos) phis)
  | aconn_map _ f (c, phis) = AConn (c, map (f NONE) phis)

fun formula_fold pos f =
  let
    fun fld pos (AQuant (_, _, phi)) = fld pos phi
      | fld pos (ATyQuant (_, _, phi)) = fld pos phi
      | fld pos (AConn conn) = aconn_fold pos fld conn
      | fld pos (AAtom tm) = f pos tm
  in fld pos end

fun formula_map f (AQuant (q, xs, phi)) = AQuant (q, xs, formula_map f phi)
  | formula_map f (ATyQuant (q, xs, phi)) = ATyQuant (q, xs, formula_map f phi)
  | formula_map f (AConn (c, phis)) = AConn (c, map (formula_map f) phis)
  | formula_map f (AAtom tm) = AAtom (f tm)

fun strip_api (APi (tys, ty)) = strip_api ty |>> append tys
  | strip_api ty = ([], ty)

fun strip_afun (AFun (ty1, ty2)) = strip_afun ty2 |>> cons ty1
  | strip_afun ty = ([], ty)

fun strip_atype ty = ty |> strip_api ||> strip_afun

fun is_function_atype ty = snd (snd (strip_atype ty)) <> AType ((tptp_bool_type, []), [])
fun is_predicate_atype ty = not (is_function_atype ty)
fun is_nontrivial_predicate_atype (AType _) = false
  | is_nontrivial_predicate_atype ty = is_predicate_atype ty

fun is_format_higher_order (THF _) = true
  | is_format_higher_order _ = false
fun is_format_typed (TFF _) = true
  | is_format_typed (THF _) = true
  | is_format_typed (DFG _) = true
  | is_format_typed _ = false

fun is_format_with_fool (THF (With_FOOL, _, _)) = true
  | is_format_with_fool (TFF (With_FOOL, _)) = true
  | is_format_with_fool _ = false

fun tptp_string_of_role Axiom = "axiom"
  | tptp_string_of_role Definition = "definition"
  | tptp_string_of_role Lemma = "lemma"
  | tptp_string_of_role Hypothesis = "hypothesis"
  | tptp_string_of_role Conjecture = "conjecture"
  | tptp_string_of_role Negated_Conjecture = "negated_conjecture"
  | tptp_string_of_role Plain = "plain"
  | tptp_string_of_role Type_Role = "type"
  | tptp_string_of_role Unknown = "unknown"

fun tptp_string_of_app _ func [] = func
  | tptp_string_of_app format func args =
    if is_format_higher_order format then
      "(" ^ space_implode (" " ^ tptp_app ^ " ") (func :: args) ^ ")"
    else
      func ^ "(" ^ commas args ^ ")"

fun uncurry_type (APi (tys, ty)) = APi (tys, uncurry_type ty)
  | uncurry_type (ty as AFun (ty1 as AType _, ty2)) =
    (case uncurry_type ty2 of
       AFun (ty' as AType ((s, _), tys), ty) =>
       AFun (AType ((tptp_product_type, []),
         ty1 :: (if s = tptp_product_type then tys else [ty'])), ty)
     | _ => ty)
  | uncurry_type (ty as AType _) = ty
  | uncurry_type _ =
    raise Fail "unexpected higher-order type in first-order format"

val suffix_type_of_types = suffix (" " ^ tptp_has_type ^ " " ^ tptp_type_of_types)

fun str_of_type format ty =
  let
    val dfg = (case format of DFG _ => true | _ => false)
    fun str _ (AType ((s, _), [])) =
        if dfg andalso s = tptp_individual_type then dfg_individual_type else s
      | str rhs (AType ((s, _), tys)) =
        if s = tptp_fun_type then
          let val [ty1, ty2] = tys in
            str rhs (AFun (ty1, ty2))
          end
        else
          let val ss = tys |> map (str false) in
            if s = tptp_product_type then
              ss |> space_implode
                        (if dfg then ", " else " " ^ tptp_product_type ^ " ")
                 |> (not dfg andalso length ss > 1) ? parens
            else
              tptp_string_of_app format s ss
          end
      | str rhs (AFun (ty1, ty2)) =
        (str false ty1 |> dfg ? parens) ^ " " ^
        (if dfg then "" else tptp_fun_type ^ " ") ^ str true ty2
        |> not rhs ? parens
      | str _ (APi (ss, ty)) =
        if dfg then
          "[" ^ commas ss ^ "], " ^ str true ty
        else
          tptp_pi_binder ^ "[" ^ commas (map suffix_type_of_types ss) ^ "]: " ^
          str false ty
  in str true ty end

fun string_of_type (format as THF _) ty = str_of_type format ty
  | string_of_type format ty = str_of_type format (uncurry_type ty)

fun tptp_string_of_quantifier AForall = tptp_forall
  | tptp_string_of_quantifier AExists = tptp_exists

fun tptp_string_of_connective ANot = tptp_not
  | tptp_string_of_connective AAnd = tptp_and
  | tptp_string_of_connective AOr = tptp_or
  | tptp_string_of_connective AImplies = tptp_implies
  | tptp_string_of_connective AIff = tptp_iff

fun string_of_bound_var format (s, ty) =
  s ^
  (if is_format_typed format then
     " " ^ tptp_has_type ^ " " ^
     (ty |> the_default (AType ((tptp_individual_type, []), [])) |> string_of_type format)
   else
     "")

fun tptp_string_of_term _ (ATerm ((s, []), [])) =
    s |> member (op =) (tptp_unary_builtins @ tptp_binary_builtins) s ? parens
  | tptp_string_of_term format (ATerm ((s, tys), ts)) =
    let
      val of_type = string_of_type format
      val of_term = tptp_string_of_term format
      fun app () =
        tptp_string_of_app format s
          (map (of_type #> is_format_higher_order format ? parens) tys @ map of_term ts)
    in
      if s = tptp_empty_list then
        (* used for lists in the optional "source" field of a derivation *)
        "[" ^ commas (map of_term ts) ^ "]"
      else if is_tptp_equal s then
        space_implode (" " ^ tptp_equal ^ " ") (map of_term ts)
        |> (is_format_higher_order format orelse is_format_with_fool format) ? parens
      else if s = tptp_ho_forall orelse s = tptp_ho_exists then
        (case ts of
          [AAbs (((s', ty), tm), [])] =>
          (* Use syntactic sugar "!" and "?" instead of "!!" and "??" whenever possible, to work
             around LEO-II, Leo-III, and Satallax parser limitation. *)
          tptp_string_of_formula format
              (AQuant (if s = tptp_ho_forall then AForall else AExists,
                      [(s', SOME ty)], AAtom tm))
        | _ => app ())
      else if s = tptp_choice then
        (case ts of
          [AAbs (((s', ty), tm), args)] =>
          (* There is code in "ATP_Problem_Generate" to ensure that "Eps" is always applied to an
             abstraction. *)
          tptp_string_of_app format
              (tptp_choice ^ "[" ^ s' ^ " : " ^ of_type ty ^
               "]: " ^ of_term tm ^ ""
               |> parens) (map of_term args)
        | _ => app ())
      else if member (op =) tptp_unary_builtins s then
        (* generate e.g. "~ t" instead of "~ @ t". *)
        (case ts of [t] => s ^ " " ^ (of_term t |> parens) |> parens)
      else if member (op =) tptp_binary_builtins s then
        (* generate e.g. "t1 & t2" instead of "& @ t1 @ t2". *)
        (case ts of
          [t1, t2] => (of_term t1 |> parens) ^ " " ^ s ^ " " ^ (of_term t2 |> parens) |> parens
        | _ => app ())
      else
        app ()
    end
  | tptp_string_of_term (format as THF _) (AAbs (((s, ty), tm), args)) =
    tptp_string_of_app format
        ("(^[" ^ s ^ " : " ^ string_of_type format ty ^ "]: " ^
         tptp_string_of_term format tm ^ ")")
        (map (tptp_string_of_term format) args)
  | tptp_string_of_term _ _ =
    raise Fail "unexpected term in first-order format"
and tptp_string_of_formula format (ATyQuant (q, xs, phi)) =
    tptp_string_of_quantifier q ^
    "[" ^
    commas (map (suffix_type_of_types o string_of_type format o fst) xs) ^
    "]: " ^ tptp_string_of_formula format phi
    |> parens
  | tptp_string_of_formula format (AQuant (q, xs, phi)) =
    tptp_string_of_quantifier q ^
    "[" ^ commas (map (string_of_bound_var format) xs) ^ "]: " ^
    tptp_string_of_formula format phi
    |> parens
  | tptp_string_of_formula format
        (AConn (ANot, [AAtom (ATerm (("=" (* tptp_equal *), []), ts))])) =
    space_implode (" " ^ tptp_not_infix ^ tptp_equal ^ " ")
                  (map (tptp_string_of_term format) ts)
    |> is_format_higher_order format ? parens
  | tptp_string_of_formula format (AConn (c, [phi])) =
    tptp_string_of_connective c ^ " " ^
    (tptp_string_of_formula format phi
     |> is_format_higher_order format ? parens)
    |> parens
  | tptp_string_of_formula format (AConn (c, phis)) =
    space_implode (" " ^ tptp_string_of_connective c ^ " ")
                  (map (tptp_string_of_formula format) phis)
    |> parens
  | tptp_string_of_formula format (AAtom tm) = tptp_string_of_term format tm

fun tptp_string_of_format CNF = tptp_cnf
  | tptp_string_of_format CNF_UEQ = tptp_cnf
  | tptp_string_of_format FOF = tptp_fof
  | tptp_string_of_format (TFF _) = tptp_tff
  | tptp_string_of_format (THF _) = tptp_thf
  | tptp_string_of_format (DFG _) = raise Fail "non-TPTP format"

val atype_of_types = AType ((tptp_type_of_types, []), [])

fun nary_type_decl_type n = funpow n (curry AFun atype_of_types) atype_of_types

fun maybe_alt "" = ""
  | maybe_alt s = " % " ^ s

fun tptp_string_of_line format (Type_Decl (ident, ty, ary)) =
    tptp_string_of_line format (Sym_Decl (ident, ty, nary_type_decl_type ary))
  | tptp_string_of_line format (Sym_Decl (ident, sym, ty)) =
    tptp_string_of_format format ^ "(" ^ ident ^ ", type,\n    " ^ sym ^
    " : " ^ string_of_type format ty ^ ").\n"
  | tptp_string_of_line format (Formula ((ident, alt), kind, phi, source, info)) =
    tptp_string_of_format format ^ "(" ^ ident ^ ", " ^
    tptp_string_of_role kind ^ "," ^ "\n    (" ^
    tptp_string_of_formula format phi ^ ")" ^
    (case source of
      SOME tm => ", " ^ tptp_string_of_term format tm
    | NONE => if null info then "" else ", []") ^
    (case info of
      [] => ""
    | tms => ", [" ^ commas (map (tptp_string_of_term format) tms) ^ "]") ^
    ")." ^ maybe_alt alt ^ "\n"

fun tptp_lines format =
  maps (fn (_, []) => []
         | (heading, lines) =>
           "\n% " ^ heading ^ " (" ^ string_of_int (length lines) ^ ")\n" ::
           map (tptp_string_of_line format) lines)

fun arity_of_type (APi (tys, ty)) =
    arity_of_type ty |>> Integer.add (length tys)
  | arity_of_type (AFun (_, ty)) = arity_of_type ty ||> Integer.add 1
  | arity_of_type _ = (0, 0)

fun string_of_arity (0, n) = string_of_int n
  | string_of_arity (m, n) = string_of_int m ^ "+" ^ string_of_int n

val dfg_class_inter = space_implode " & "

fun dfg_string_of_term (ATerm ((s, tys), tms)) =
    s ^
    (if null tys then ""
     else "<" ^ commas (map (string_of_type (DFG Polymorphic)) tys) ^ ">") ^
    (if null tms then ""
     else "(" ^ commas (map dfg_string_of_term tms) ^ ")")
  | dfg_string_of_term _ = raise Fail "unexpected atom in first-order format"

fun dfg_string_of_formula poly gen_simp info =
  let
    val str_of_typ = string_of_type (DFG poly)
    fun str_of_bound_typ (ty, []) = str_of_typ ty
      | str_of_bound_typ (ty, cls) = str_of_typ ty ^ " : " ^ dfg_class_inter cls
    fun suffix_tag top_level s =
      if top_level then
        (case extract_isabelle_status info of
          SOME s' =>
          if s' = non_rec_defN then s ^ ":lt"
          else if (s' = simpN orelse s' = rec_defN) andalso gen_simp then s ^ ":lr"
          else s
        | NONE => s)
      else
        s
    fun str_of_atom top_level (ATerm ((s, tys), tms)) =
        let
          val s' =
            if is_tptp_equal s then "equal" |> suffix_tag top_level
            else if s = tptp_true then "true"
            else if s = tptp_false then "false"
            else s
        in dfg_string_of_term (ATerm ((s', tys), tms)) end
      | str_of_atom _ _ = raise Fail "unexpected atom in first-order format"
    fun str_of_quant AForall = "forall"
      | str_of_quant AExists = "exists"
    fun str_of_conn _ ANot = "not"
      | str_of_conn _ AAnd = "and"
      | str_of_conn _ AOr = "or"
      | str_of_conn _ AImplies = "implies"
      | str_of_conn top_level AIff = "equiv" |> suffix_tag top_level
    fun str_of_formula top_level (ATyQuant (q, xs, phi)) =
        str_of_quant q ^ "_sorts([" ^ commas (map str_of_bound_typ xs) ^ "], " ^
        str_of_formula top_level phi ^ ")"
      | str_of_formula top_level (AQuant (q, xs, phi)) =
        str_of_quant q ^ "([" ^
        commas (map (string_of_bound_var (DFG poly)) xs) ^ "], " ^
        str_of_formula top_level phi ^ ")"
      | str_of_formula top_level (AConn (c, phis)) =
        str_of_conn top_level c ^ "(" ^
        commas (map (str_of_formula false) phis) ^ ")"
      | str_of_formula top_level (AAtom tm) = str_of_atom top_level tm
  in str_of_formula true end

fun maybe_enclose bef aft "" = "% " ^ bef ^ aft
  | maybe_enclose bef aft s = bef ^ s ^ aft

fun dfg_lines poly {is_lpo, gen_weights, gen_prec, gen_simp} ord_info problem =
  let
    val typ = string_of_type (DFG poly)
    val term = dfg_string_of_term
    fun spair (s, s') = "(" ^ s ^ ", " ^ s' ^ ")"
    fun tm_ary sym ty = spair (sym, string_of_arity (arity_of_type ty))
    fun ty_ary 0 ty = ty
      | ty_ary n ty = "(" ^ ty ^ ", " ^ string_of_int n ^ ")"
    fun fun_typ sym ty = "function(" ^ sym ^ ", " ^ typ ty ^ ")."
    fun pred_typ sym ty =
      let
        val (ty_vars, (tys, _)) =
          strip_atype ty
          |>> (fn [] => [] | xs => ["[" ^ commas xs ^ "]"])
      in "predicate(" ^ commas (sym :: ty_vars @ map typ tys) ^ ")." end
    fun bound_tvar (ty, []) = ty
      | bound_tvar (ty, cls) = ty ^ " : " ^ dfg_class_inter cls
    fun binder_typ xs ty =
      (if null xs then "" else "[" ^ commas (map bound_tvar xs) ^ "], ") ^
      typ ty
    fun sort_decl xs ty cl = "sort(" ^ binder_typ xs ty ^ ", " ^ cl ^ ")."
    fun datatype_decl xs ty tms exhaust =
      "datatype(" ^ commas (binder_typ xs ty :: map term tms @ (if exhaust then [] else ["..."])) ^
      ")."
    fun subclass_of sub super = "subclass(" ^ sub ^ ", " ^ super ^ ")."
    fun formula pred (Formula ((ident, alt), kind, phi, _, info)) =
        if pred kind then
          let val rank = extract_isabelle_rank info in
            "formula(" ^ dfg_string_of_formula poly gen_simp info phi ^ ", " ^ ident ^
            (if rank = default_rank then "" else ", " ^ string_of_int rank) ^
            ")." ^ maybe_alt alt
            |> SOME
          end
        else
          NONE
      | formula _ _ = NONE
    fun filt f = problem |> map (map_filter f o snd) |> filter_out null
    val func_aries =
      filt (fn Sym_Decl (_, sym, ty) =>
               if is_function_atype ty then SOME (tm_ary sym ty) else NONE
             | _ => NONE)
      |> flat |> commas |> maybe_enclose "functions [" "]."
    val pred_aries =
      filt (fn Sym_Decl (_, sym, ty) =>
               if is_predicate_atype ty then SOME (tm_ary sym ty) else NONE
             | _ => NONE)
      |> flat |> commas |> maybe_enclose "predicates [" "]."
    val sorts =
      filt (try (fn Type_Decl (_, ty, ary) => ty_ary ary ty)) @
      [[ty_ary 0 dfg_individual_type]]
      |> flat |> commas |> maybe_enclose "sorts [" "]."
    val classes =
      filt (try (fn Class_Decl (_, cl, _) => cl))
      |> flat |> commas |> maybe_enclose "classes [" "]."
    val ord_info = if gen_weights orelse gen_prec then ord_info () else []
    val do_term_order_weights =
      (if gen_weights then ord_info else [])
      |> map (spair o apsnd string_of_int) |> commas
      |> maybe_enclose "weights [" "]."
    val syms = [func_aries, pred_aries, do_term_order_weights, sorts, classes]
    val func_decls =
      filt (fn Sym_Decl (_, sym, ty) =>
               if is_function_atype ty then SOME (fun_typ sym ty) else NONE
             | _ => NONE) |> flat
    val pred_decls =
      filt (fn Sym_Decl (_, sym, ty) =>
               if is_nontrivial_predicate_atype ty then SOME (pred_typ sym ty)
               else NONE
             | _ => NONE) |> flat
    val datatype_decls =
      filt (try (fn Datatype_Decl (_, xs, ty, tms, exhaust) => datatype_decl xs ty tms exhaust))
      |> flat
    val sort_decls =
      filt (try (fn Class_Memb (_, xs, ty, cl) => sort_decl xs ty cl)) |> flat
    val subclass_decls =
      filt (try (fn Class_Decl (_, sub, supers) =>
                    map (subclass_of sub) supers))
      |> flat |> flat
    val decls =
      func_decls @ pred_decls @ datatype_decls @ sort_decls @ subclass_decls
    val axioms =
      filt (formula (curry (op <>) Conjecture)) |> separate [""] |> flat
    val conjs =
      filt (formula (curry (op =) Conjecture)) |> separate [""] |> flat
    val settings =
      (if is_lpo then ["set_flag(Ordering, 1)."] else []) @
      (if gen_prec then
         [ord_info |> map fst |> rev |> commas
                   |> maybe_enclose "set_precedence(" ")."]
       else
         [])
    fun list_of _ [] = []
      | list_of heading ss =
        "list_of_" ^ heading ^ ".\n" :: map (suffix "\n") ss @
        ["end_of_list.\n\n"]
  in
    "\nbegin_problem(isabelle).\n\n" ::
    list_of "descriptions"
            ["name({**}).", "author({**}).", "status(unknown).",
             "description({**})."] @
    list_of "symbols" syms @
    list_of "declarations" decls @
    list_of "formulae(axioms)" axioms @
    list_of "formulae(conjectures)" conjs @
    list_of "settings(SPASS)" settings @
    ["end_problem.\n"]
  end

fun lines_of_atp_problem format ord ord_info problem =
  "% This file was generated by Isabelle (most likely Sledgehammer)\n\
  \% " ^ timestamp () ^ "\n" ::
  (case format of
     DFG poly => dfg_lines poly ord ord_info
   | _ => tptp_lines format) problem


(** CNF (Metis) and CNF UEQ (Waldmeister) **)

fun is_line_negated (Formula (_, _, AConn (ANot, _), _, _)) = true
  | is_line_negated _ = false

fun is_line_cnf_ueq (Formula (_, _, AAtom (ATerm (((s, _), _), _)), _, _)) =
    is_tptp_equal s
  | is_line_cnf_ueq _ = false

fun open_conjecture_term (ATerm (((s, s'), tys), tms)) =
    ATerm ((if is_tptp_variable s then (s |> Name.desymbolize (SOME false), s')
            else (s, s'), tys), tms |> map open_conjecture_term)
  | open_conjecture_term _ = raise Fail "unexpected higher-order term"
fun open_formula conj =
  let
    (* We are conveniently assuming that all bound variable names are
       distinct, which should be the case for the formulas we generate. *)
    fun opn (pos as SOME true) (AQuant (AForall, _, phi)) = opn pos phi
      | opn (pos as SOME false) (AQuant (AExists, _, phi)) = opn pos phi
      | opn pos (AConn (ANot, [phi])) = mk_anot (opn (Option.map not pos) phi)
      | opn pos (AConn (c, [phi1, phi2])) =
        let val (pos1, pos2) = polarities_of_conn pos c in
          AConn (c, [opn pos1 phi1, opn pos2 phi2])
        end
      | opn _ (AAtom t) = AAtom (t |> conj ? open_conjecture_term)
      | opn _ phi = phi
  in opn (SOME (not conj)) end
fun open_formula_line (Formula (ident, kind, phi, source, info)) =
    Formula (ident, kind, open_formula (kind = Conjecture) phi, source, info)
  | open_formula_line line = line

fun negate_conjecture_line (Formula (ident, Conjecture, phi, source, info)) =
    Formula (ident, Hypothesis, mk_anot phi, source, info)
  | negate_conjecture_line line = line

exception CLAUSIFY of unit

(* This "clausification" only expands syntactic sugar, such as "phi => psi" to
   "~ phi | psi" and "phi <=> psi" to "~ phi | psi" and "~ psi | phi". We don't
   attempt to distribute conjunctions over disjunctions. *)
fun clausify_formula pos (phi as AAtom _) = [phi |> not pos ? mk_anot]
  | clausify_formula pos (AConn (ANot, [phi])) = clausify_formula (not pos) phi
  | clausify_formula true (AConn (AOr, [phi1, phi2])) =
    (phi1, phi2) |> apply2 (clausify_formula true)
                 |> uncurry (map_product (mk_aconn AOr))
  | clausify_formula false (AConn (AAnd, [phi1, phi2])) =
    (phi1, phi2) |> apply2 (clausify_formula false)
                 |> uncurry (map_product (mk_aconn AOr))
  | clausify_formula true (AConn (AImplies, [phi1, phi2])) =
    clausify_formula true (AConn (AOr, [mk_anot phi1, phi2]))
  | clausify_formula true (AConn (AIff, phis)) =
    clausify_formula true (AConn (AImplies, phis)) @
    clausify_formula true (AConn (AImplies, rev phis))
  | clausify_formula _ _ = raise CLAUSIFY ()

fun clausify_formula_line (Formula ((ident, alt), kind, phi, source, info)) =
    let
      val (n, phis) = phi |> try (clausify_formula true) |> these |> `length
    in
      map2 (fn phi => fn j =>
               Formula ((ident ^ replicate_string (j - 1) "x", alt), kind, phi,
                        source, info))
           phis (1 upto n)
    end
  | clausify_formula_line _ = []

fun ensure_cnf_line line =
  line |> open_formula_line |> negate_conjecture_line |> clausify_formula_line

fun ensure_cnf_problem problem = problem |> map (apsnd (maps ensure_cnf_line))

fun filter_cnf_ueq_problem problem =
  problem
  |> map (apsnd (map open_formula_line #> filter is_line_cnf_ueq
                 #> map negate_conjecture_line))
  |> (fn problem =>
         let
           val lines = problem |> maps snd
           val conjs = lines |> filter is_line_negated
         in if length conjs = 1 andalso conjs <> lines then problem else [] end)


(** Symbol declarations **)

fun add_declared_in_line (Class_Decl (_, cl, _)) = apfst (apfst (cons cl))
  | add_declared_in_line (Type_Decl (_, ty, _)) = apfst (apsnd (cons ty))
  | add_declared_in_line (Sym_Decl (_, sym, _)) = apsnd (cons sym)
  | add_declared_in_line _ = I
fun declared_in_atp_problem problem =
  fold (fold add_declared_in_line o snd) problem (([], []), [])

(** Nice names **)

val no_qualifiers =
  let
    fun skip [] = []
      | skip (#"." :: cs) = skip cs
      | skip (c :: cs) = if Char.isAlphaNum c then skip cs else c :: keep cs
    and keep [] = []
      | keep (#"." :: cs) = skip cs
      | keep (c :: cs) = c :: keep cs
  in String.explode #> rev #> keep #> rev #> String.implode end

(* Long names can slow down the ATPs. *)
val max_readable_name_size = 20

(* "equal" is reserved by some ATPs. "op" is also reserved, to avoid the
   unreadable "op_1", "op_2", etc., in the problem files. "eq" is reserved to
   ensure that "HOL.eq" is correctly mapped to equality (not clear whether this
   is still necessary). *)
val reserved_nice_names = [tptp_old_equal, "op", "eq"]

(* hack to get the same hashing across Mirabelle runs (see "mirabelle.pl") *)
fun cleanup_mirabelle_name s =
  let
    val mirabelle_infix = "_Mirabelle_"
    val random_suffix_len = 10
    val (s1, s2) = Substring.position mirabelle_infix (Substring.full s)
  in
    if Substring.isEmpty s2 then
      s
    else
      Substring.string s1 ^
      Substring.string (Substring.triml (size mirabelle_infix + random_suffix_len) s2)
  end

fun readable_name protect full_name s =
  (if s = full_name then
     s
   else
     s |> no_qualifiers
       |> unquote_tvar
       |> Name.desymbolize (SOME (Char.isUpper (String.sub (full_name, 0))))
       |> (fn s =>
              if size s > max_readable_name_size then
                String.substring (s, 0, max_readable_name_size div 2 - 4) ^
                string_of_int (hash_string (cleanup_mirabelle_name full_name)) ^
                String.extract (s, size s - max_readable_name_size div 2 + 4, NONE)
              else
                s)
       |> (fn s =>
              if member (op =) reserved_nice_names s then full_name else s))
  |> protect

fun nice_name _ (full_name, _) NONE = (full_name, NONE)
  | nice_name protect (full_name, desired_name) (SOME the_pool) =
    if is_built_in_tptp_symbol full_name then
      (full_name, SOME the_pool)
    else
      (case Symtab.lookup (fst the_pool) full_name of
        SOME nice_name => (nice_name, SOME the_pool)
      | NONE =>
        let
          val nice_prefix = readable_name protect full_name desired_name
          fun add j =
            let
              val nice_name = nice_prefix ^ (if j = 1 then "" else string_of_int j)
            in
              (case Symtab.lookup (snd the_pool) nice_name of
                SOME full_name' =>
                if full_name = full_name' then (nice_name, the_pool) else add (j + 1)
              | NONE =>
                (nice_name,
                 (Symtab.update_new (full_name, nice_name) (fst the_pool),
                  Symtab.update_new (nice_name, full_name) (snd the_pool))))
            end
        in add 1 |> apsnd SOME end)

fun avoid_clash_with_dfg_keywords s =
  let val n = String.size s in
    if n < 2 orelse (n = 2 andalso String.sub (s, 0) = String.sub (s, 1)) orelse
       String.isSubstring "_" s then
      s
    else if is_tptp_variable s then
      s ^ "_"
    else
      String.substring (s, 0, n - 1) ^
      String.str (Char.toUpper (String.sub (s, n - 1)))
  end

fun nice_atp_problem readable_names format problem =
  let
    val empty_pool =
      if readable_names then SOME (Symtab.empty, Symtab.empty) else NONE
    val avoid_clash =
      (case format of
        DFG _ => avoid_clash_with_dfg_keywords
      | _ => I)
    val nice_name = nice_name avoid_clash

    fun nice_bound_tvars xs =
      fold_map (nice_name o fst) xs
      ##>> fold_map (fold_map nice_name o snd) xs
      #>> op ~~

    fun nice_type (AType ((name, clss), tys)) =
        nice_name name ##>> fold_map nice_name clss ##>> fold_map nice_type tys #>> AType
      | nice_type (AFun (ty1, ty2)) = nice_type ty1 ##>> nice_type ty2 #>> AFun
      | nice_type (APi (names, ty)) = fold_map nice_name names ##>> nice_type ty #>> APi

    fun nice_term (ATerm ((name, tys), ts)) =
        nice_name name ##>> fold_map nice_type tys ##>> fold_map nice_term ts #>> ATerm
      | nice_term (AAbs (((name, ty), tm), args)) =
        nice_name name ##>> nice_type ty ##>> nice_term tm ##>> fold_map nice_term args #>> AAbs

    fun nice_formula (ATyQuant (q, xs, phi)) =
        fold_map (nice_type o fst) xs
        ##>> fold_map (fold_map nice_name o snd) xs
        ##>> nice_formula phi
        #>> (fn ((tys, cls), phi) => ATyQuant (q, tys ~~ cls, phi))
      | nice_formula (AQuant (q, xs, phi)) =
        fold_map (nice_name o fst) xs
        ##>> fold_map (fn (_, NONE) => pair NONE
                        | (_, SOME ty) => nice_type ty #>> SOME) xs
        ##>> nice_formula phi
        #>> (fn ((ss, ts), phi) => AQuant (q, ss ~~ ts, phi))
      | nice_formula (AConn (c, phis)) =
        fold_map nice_formula phis #>> curry AConn c
      | nice_formula (AAtom tm) = nice_term tm #>> AAtom

    fun nice_line (Class_Decl (ident, cl, cls)) =
        nice_name cl ##>> fold_map nice_name cls
        #>> (fn (cl, cls) => Class_Decl (ident, cl, cls))
      | nice_line (Type_Decl (ident, ty, ary)) =
        nice_name ty #>> (fn ty => Type_Decl (ident, ty, ary))
      | nice_line (Sym_Decl (ident, sym, ty)) =
        nice_name sym ##>> nice_type ty #>> (fn (sym, ty) => Sym_Decl (ident, sym, ty))
      | nice_line (Datatype_Decl (ident, xs, ty, tms, exhaust)) =
        nice_bound_tvars xs ##>> nice_type ty ##>> fold_map nice_term tms
        #>> (fn ((xs, ty), tms) => Datatype_Decl (ident, xs, ty, tms, exhaust))
      | nice_line (Class_Memb (ident, xs, ty, cl)) =
        nice_bound_tvars xs ##>> nice_type ty ##>> nice_name cl
        #>> (fn ((xs, ty), cl) => Class_Memb (ident, xs, ty, cl))
      | nice_line (Formula (ident, kind, phi, source, info)) =
        nice_formula phi #>> (fn phi => Formula (ident, kind, phi, source, info))

    fun nice_problem problem =
      fold_map (fn (heading, lines) => fold_map nice_line lines #>> pair heading) problem
  in
    nice_problem problem empty_pool
  end

end;
