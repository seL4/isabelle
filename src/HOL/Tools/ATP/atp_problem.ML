(*  Title:      HOL/Tools/ATP/atp_problem.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

Abstract representation of ATP problems and TPTP syntax.
*)

signature ATP_PROBLEM =
sig
  datatype ('a, 'b) ho_term =
    ATerm of 'a * ('a, 'b) ho_term list |
    AAbs of ('a * 'b) * ('a, 'b) ho_term
  datatype quantifier = AForall | AExists
  datatype connective = ANot | AAnd | AOr | AImplies | AIff
  datatype ('a, 'b, 'c) formula =
    AQuant of quantifier * ('a * 'b option) list * ('a, 'b, 'c) formula |
    AConn of connective * ('a, 'b, 'c) formula list |
    AAtom of 'c

  datatype 'a ho_type = AType of 'a | AFun of 'a ho_type * 'a ho_type

  datatype thf_flavor = Without_Choice | With_Choice
  datatype format =
    CNF |
    CNF_UEQ |
    FOF |
    TFF |
    THF of thf_flavor

  datatype formula_kind = Axiom | Definition | Lemma | Hypothesis | Conjecture
  datatype 'a problem_line =
    Decl of string * 'a * 'a ho_type |
    Formula of string * formula_kind
               * ('a, 'a ho_type, ('a, 'a ho_type) ho_term) formula
               * (string, string ho_type) ho_term option
               * (string, string ho_type) ho_term option
  type 'a problem = (string * 'a problem_line list) list

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
  val tptp_exists : string
  val tptp_ho_exists : string
  val tptp_choice : string
  val tptp_not : string
  val tptp_and : string
  val tptp_or : string
  val tptp_implies : string
  val tptp_if : string
  val tptp_iff : string
  val tptp_not_iff : string
  val tptp_app : string
  val tptp_not_infix : string
  val tptp_equal : string
  val tptp_old_equal : string
  val tptp_false : string
  val tptp_true : string
  val tptp_empty_list : string
  val is_tptp_equal : string -> bool
  val is_built_in_tptp_symbol : string -> bool
  val is_tptp_variable : string -> bool
  val is_tptp_user_symbol : string -> bool
  val mk_anot : ('a, 'b, 'c) formula -> ('a, 'b, 'c) formula
  val mk_aconn :
    connective -> ('a, 'b, 'c) formula -> ('a, 'b, 'c) formula
    -> ('a, 'b, 'c) formula
  val aconn_fold :
    bool option -> (bool option -> 'a -> 'b -> 'b) -> connective * 'a list
    -> 'b -> 'b
  val aconn_map :
    bool option -> (bool option -> 'a -> ('b, 'c, 'd) formula)
    -> connective * 'a list -> ('b, 'c, 'd) formula
  val formula_fold :
    bool option -> (bool option -> 'c -> 'd -> 'd) -> ('a, 'b, 'c) formula
    -> 'd -> 'd
  val formula_map : ('c -> 'd) -> ('a, 'b, 'c) formula -> ('a, 'b, 'd) formula
  val is_format_thf : format -> bool
  val is_format_typed : format -> bool
  val tptp_lines_for_atp_problem : format -> string problem -> string list
  val ensure_cnf_problem :
    (string * string) problem -> (string * string) problem
  val filter_cnf_ueq_problem :
    (string * string) problem -> (string * string) problem
  val declare_undeclared_syms_in_atp_problem :
    string -> string -> (string * string) problem -> (string * string) problem
  val nice_atp_problem :
    bool -> ('a * (string * string) problem_line list) list
    -> ('a * string problem_line list) list
       * (string Symtab.table * string Symtab.table) option
end;

structure ATP_Problem : ATP_PROBLEM =
struct

open ATP_Util


(** ATP problem **)

datatype ('a, 'b) ho_term =
  ATerm of 'a * ('a, 'b) ho_term list |
  AAbs of ('a * 'b) * ('a, 'b) ho_term
datatype quantifier = AForall | AExists
datatype connective = ANot | AAnd | AOr | AImplies | AIff
datatype ('a, 'b, 'c) formula =
  AQuant of quantifier * ('a * 'b option) list * ('a, 'b, 'c) formula |
  AConn of connective * ('a, 'b, 'c) formula list |
  AAtom of 'c

datatype 'a ho_type = AType of 'a | AFun of 'a ho_type * 'a ho_type

datatype thf_flavor = Without_Choice | With_Choice
datatype format =
  CNF |
  CNF_UEQ |
  FOF |
  TFF |
  THF of thf_flavor

datatype formula_kind = Axiom | Definition | Lemma | Hypothesis | Conjecture
datatype 'a problem_line =
  Decl of string * 'a * 'a ho_type |
  Formula of string * formula_kind * ('a, 'a ho_type, ('a, 'a ho_type) ho_term) formula
             * (string, string ho_type) ho_term option * (string, string ho_type) ho_term option
type 'a problem = (string * 'a problem_line list) list

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
val tptp_exists = "?"
val tptp_ho_exists = "??"
val tptp_choice = "@+"
val tptp_not = "~"
val tptp_and = "&"
val tptp_or = "|"
val tptp_implies = "=>"
val tptp_if = "<="
val tptp_iff = "<=>"
val tptp_not_iff = "<~>"
val tptp_app = "@"
val tptp_not_infix = "!"
val tptp_equal = "="
val tptp_old_equal = "equal"
val tptp_false = "$false"
val tptp_true = "$true"
val tptp_empty_list = "[]"

fun is_tptp_equal s = (s = tptp_equal orelse s = tptp_old_equal)
fun is_built_in_tptp_symbol s =
  s = tptp_old_equal orelse not (Char.isAlpha (String.sub (s, 0)))
fun is_tptp_variable s = Char.isUpper (String.sub (s, 0))
val is_tptp_user_symbol = not o (is_tptp_variable orf is_built_in_tptp_symbol)

fun raw_polarities_of_conn ANot = (SOME false, NONE)
  | raw_polarities_of_conn AAnd = (SOME true, SOME true)
  | raw_polarities_of_conn AOr = (SOME true, SOME true)
  | raw_polarities_of_conn AImplies = (SOME false, SOME true)
  | raw_polarities_of_conn AIff = (NONE, NONE)
fun polarities_of_conn NONE = K (NONE, NONE)
  | polarities_of_conn (SOME pos) =
    raw_polarities_of_conn #> not pos ? pairself (Option.map not)

fun mk_anot (AConn (ANot, [phi])) = phi
  | mk_anot phi = AConn (ANot, [phi])
fun mk_aconn c phi1 phi2 = AConn (c, [phi1, phi2])

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
    fun aux pos (AQuant (_, _, phi)) = aux pos phi
      | aux pos (AConn conn) = aconn_fold pos aux conn
      | aux pos (AAtom tm) = f pos tm
  in aux pos end

fun formula_map f (AQuant (q, xs, phi)) = AQuant (q, xs, formula_map f phi)
  | formula_map f (AConn (c, phis)) = AConn (c, map (formula_map f) phis)
  | formula_map f (AAtom tm) = AAtom (f tm)

fun is_format_thf (THF _) = true
  | is_format_thf _ = false
fun is_format_typed TFF = true
  | is_format_typed (THF _) = true
  | is_format_typed _ = false

fun string_for_kind Axiom = "axiom"
  | string_for_kind Definition = "definition"
  | string_for_kind Lemma = "lemma"
  | string_for_kind Hypothesis = "hypothesis"
  | string_for_kind Conjecture = "conjecture"

fun strip_tff_type (AFun (AType s, ty)) = strip_tff_type ty |>> cons s
  | strip_tff_type (AFun (AFun _, _)) =
    raise Fail "unexpected higher-order type in first-order format"
  | strip_tff_type (AType s) = ([], s)

fun string_for_type (THF _) ty =
    let
      fun aux _ (AType s) = s
        | aux rhs (AFun (ty1, ty2)) =
          aux false ty1 ^ " " ^ tptp_fun_type ^ " " ^ aux true ty2
          |> not rhs ? enclose "(" ")"
    in aux true ty end
  | string_for_type TFF ty =
    (case strip_tff_type ty of
       ([], s) => s
     | ([s'], s) => s' ^ " " ^ tptp_fun_type ^ " " ^ s
     | (ss, s) =>
       "(" ^ space_implode (" " ^ tptp_product_type ^ " ") ss ^ ") " ^
       tptp_fun_type ^ " " ^ s)
  | string_for_type _ _ = raise Fail "unexpected type in untyped format"

fun string_for_quantifier AForall = tptp_forall
  | string_for_quantifier AExists = tptp_exists

fun string_for_connective ANot = tptp_not
  | string_for_connective AAnd = tptp_and
  | string_for_connective AOr = tptp_or
  | string_for_connective AImplies = tptp_implies
  | string_for_connective AIff = tptp_iff

fun string_for_bound_var format (s, ty) =
  s ^ (if is_format_typed format then
         " " ^ tptp_has_type ^ " " ^
         string_for_type format (ty |> the_default (AType tptp_individual_type))
       else
         "")

fun string_for_term _ (ATerm (s, [])) = s
  | string_for_term format (ATerm (s, ts)) =
    if s = tptp_empty_list then
      (* used for lists in the optional "source" field of a derivation *)
      "[" ^ commas (map (string_for_term format) ts) ^ "]"
    else if is_tptp_equal s then
      space_implode (" " ^ tptp_equal ^ " ") (map (string_for_term format) ts)
      |> is_format_thf format ? enclose "(" ")"
    else
      (case (s = tptp_ho_forall orelse s = tptp_ho_exists,
             s = tptp_choice andalso format = THF With_Choice, ts) of
         (true, _, [AAbs ((s', ty), tm)]) =>
         (* Use syntactic sugar "!" and "?" instead of "!!" and "??" whenever
            possible, to work around LEO-II 1.2.8 parser limitation. *)
         string_for_formula format
             (AQuant (if s = tptp_ho_forall then AForall else AExists,
                      [(s', SOME ty)], AAtom tm))
       | (_, true, [AAbs ((s', ty), tm)]) =>
         (*There is code in ATP_Translate to ensure that Eps is always applied
           to an abstraction*)
         tptp_choice ^ "[" ^ s' ^ " : " ^ string_for_type format ty ^ "] : " ^
           string_for_term format tm ^ ""
         |> enclose "(" ")"

       | _ =>
         let val ss = map (string_for_term format) ts in
           if is_format_thf format then
             "(" ^ space_implode (" " ^ tptp_app ^ " ") (s :: ss) ^ ")"
           else
             s ^ "(" ^ commas ss ^ ")"
         end)
  | string_for_term (format as THF _) (AAbs ((s, ty), tm)) =
    "(^[" ^ s ^ " : " ^ string_for_type format ty ^ "] : " ^
    string_for_term format tm ^ ")"
  | string_for_term _ _ = raise Fail "unexpected term in first-order format"
and string_for_formula format (AQuant (q, xs, phi)) =
    string_for_quantifier q ^
    "[" ^ commas (map (string_for_bound_var format) xs) ^ "] : " ^
    string_for_formula format phi
    |> enclose "(" ")"
  | string_for_formula format
        (AConn (ANot, [AAtom (ATerm ("=" (* tptp_equal *), ts))])) =
    space_implode (" " ^ tptp_not_infix ^ tptp_equal ^ " ")
                  (map (string_for_term format) ts)
    |> is_format_thf format ? enclose "(" ")"
  | string_for_formula format (AConn (c, [phi])) =
    string_for_connective c ^ " " ^
    (string_for_formula format phi |> is_format_thf format ? enclose "(" ")")
    |> enclose "(" ")"
  | string_for_formula format (AConn (c, phis)) =
    space_implode (" " ^ string_for_connective c ^ " ")
                  (map (string_for_formula format) phis)
    |> enclose "(" ")"
  | string_for_formula format (AAtom tm) = string_for_term format tm

fun the_source (SOME source) = source
  | the_source NONE =
    ATerm ("inference",
           ATerm ("isabelle", []) :: replicate 2 (ATerm ("[]", [])))

fun string_for_format CNF = tptp_cnf
  | string_for_format CNF_UEQ = tptp_cnf
  | string_for_format FOF = tptp_fof
  | string_for_format TFF = tptp_tff
  | string_for_format (THF _) = tptp_thf

fun string_for_problem_line format (Decl (ident, sym, ty)) =
    string_for_format format ^ "(" ^ ident ^ ", type,\n    " ^ sym ^ " : " ^
    string_for_type format ty ^ ").\n"
  | string_for_problem_line format (Formula (ident, kind, phi, source, info)) =
    string_for_format format ^ "(" ^ ident ^ ", " ^ string_for_kind kind ^
    ",\n    (" ^ string_for_formula format phi ^ ")" ^
    (case (source, info) of
       (NONE, NONE) => ""
     | (SOME tm, NONE) => ", " ^ string_for_term format tm
     | (_, SOME tm) =>
       ", " ^ string_for_term format (the_source source) ^
       ", " ^ string_for_term format tm) ^ ").\n"
fun tptp_lines_for_atp_problem format problem =
  "% This file was generated by Isabelle (most likely Sledgehammer)\n\
  \% " ^ timestamp () ^ "\n" ::
  maps (fn (_, []) => []
         | (heading, lines) =>
           "\n% " ^ heading ^ " (" ^ string_of_int (length lines) ^ ")\n" ::
           map (string_for_problem_line format) lines)
       problem


(** CNF (Metis) and CNF UEQ (Waldmeister) **)

fun is_problem_line_negated (Formula (_, _, AConn (ANot, _), _, _)) = true
  | is_problem_line_negated _ = false

fun is_problem_line_cnf_ueq (Formula (_, _, AAtom (ATerm ((s, _), _)), _, _)) =
    is_tptp_equal s
  | is_problem_line_cnf_ueq _ = false

fun open_conjecture_term (ATerm ((s, s'), tms)) =
    ATerm (if is_tptp_variable s then (s |> Name.desymbolize false, s')
           else (s, s'), tms |> map open_conjecture_term)
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
    (phi1, phi2) |> pairself (clausify_formula true)
                 |> uncurry (map_product (mk_aconn AOr))
  | clausify_formula false (AConn (AAnd, [phi1, phi2])) =
    (phi1, phi2) |> pairself (clausify_formula false)
                 |> uncurry (map_product (mk_aconn AOr))
  | clausify_formula true (AConn (AImplies, [phi1, phi2])) =
    clausify_formula true (AConn (AOr, [mk_anot phi1, phi2]))
  | clausify_formula true (AConn (AIff, phis)) =
    clausify_formula true (AConn (AImplies, phis)) @
    clausify_formula true (AConn (AImplies, rev phis))
  | clausify_formula _ _ = raise CLAUSIFY ()

fun clausify_formula_line (Formula (ident, kind, phi, source, info)) =
    let
      val (n, phis) = phi |> try (clausify_formula true) |> these |> `length
    in
      map2 (fn phi => fn j =>
               Formula (ident ^ replicate_string (j - 1) "x", kind, phi, source,
                        info))
           phis (1 upto n)
    end
  | clausify_formula_line _ = []

fun ensure_cnf_problem_line line =
  line |> open_formula_line |> negate_conjecture_line |> clausify_formula_line

fun ensure_cnf_problem problem =
  problem |> map (apsnd (maps ensure_cnf_problem_line))

fun filter_cnf_ueq_problem problem =
  problem
  |> map (apsnd (map open_formula_line
                 #> filter is_problem_line_cnf_ueq
                 #> map negate_conjecture_line))
  |> (fn problem =>
         let
           val lines = problem |> maps snd
           val conjs = lines |> filter is_problem_line_negated
         in if length conjs = 1 andalso conjs <> lines then problem else [] end)


(** Symbol declarations **)

(* TFF allows implicit declarations of types, function symbols, and predicate
   symbols (with "$i" as the type of individuals), but some provers (e.g.,
   SNARK) require explicit declarations. The situation is similar for THF. *)

val atype_of_types = AType (`I tptp_type_of_types)
val bool_atype = AType (`I tptp_bool_type)
val individual_atype = AType (`I tptp_individual_type)

fun default_type pred_sym =
  let
    fun typ 0 = if pred_sym then bool_atype else individual_atype
      | typ ary = AFun (individual_atype, typ (ary - 1))
  in typ end

fun add_declared_syms_in_problem_line (Decl (_, sym, _)) = insert (op =) sym
  | add_declared_syms_in_problem_line _ = I
fun declared_syms_in_problem problem =
  fold (fold add_declared_syms_in_problem_line o snd) problem []

fun undeclared_syms_in_problem declared problem =
  let
    fun do_sym name ty =
      if member (op =) declared name then I else AList.default (op =) (name, ty)
    fun do_type (AFun (ty1, ty2)) = fold do_type [ty1, ty2]
      | do_type (AType name) = do_sym name (K atype_of_types)
    fun do_term pred_sym (ATerm (name as (s, _), tms)) =
        is_tptp_user_symbol s
        ? do_sym name (fn _ => default_type pred_sym (length tms))
        #> fold (do_term false) tms
      | do_term _ (AAbs ((_, ty), tm)) = do_type ty #> do_term false tm
    fun do_formula (AQuant (_, xs, phi)) =
        fold do_type (map_filter snd xs) #> do_formula phi
      | do_formula (AConn (_, phis)) = fold do_formula phis
      | do_formula (AAtom tm) = do_term true tm
    fun do_problem_line (Decl (_, _, ty)) = do_type ty
      | do_problem_line (Formula (_, _, phi, _, _)) = do_formula phi
  in
    fold (fold do_problem_line o snd) problem []
    |> filter_out (is_built_in_tptp_symbol o fst o fst)
  end

fun declare_undeclared_syms_in_atp_problem prefix heading problem =
  let
    fun decl_line (x as (s, _), ty) = Decl (prefix ^ s, x, ty ())
    val declared = problem |> declared_syms_in_problem
    val decls =
      problem |> undeclared_syms_in_problem declared
              |> sort_wrt (fst o fst)
              |> map decl_line
  in (heading, decls) :: problem end

(** Nice names **)

fun empty_name_pool readable_names =
  if readable_names then SOME (Symtab.empty, Symtab.empty) else NONE

fun pool_fold f xs z = pair z #> fold_rev (fn x => uncurry (f x)) xs
fun pool_map f xs =
  pool_fold (fn x => fn ys => fn pool => f x pool |>> (fn y => y :: ys)) xs []

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

fun readable_name full_name s =
  if s = full_name then
    s
  else
    s |> no_qualifiers
      |> perhaps (try (unprefix "'"))
      |> Name.desymbolize (Char.isUpper (String.sub (full_name, 0)))
      |> (fn s =>
             if size s > max_readable_name_size then
               String.substring (s, 0, max_readable_name_size div 2 - 4) ^
               string_of_int (hash_string full_name) ^
               String.extract (s, size s - max_readable_name_size div 2 + 4,
                               NONE)
             else
               s)
      |> (fn s => if member (op =) reserved_nice_names s then full_name else s)

fun nice_name (full_name, _) NONE = (full_name, NONE)
  | nice_name (full_name, desired_name) (SOME the_pool) =
    if is_built_in_tptp_symbol full_name then
      (full_name, SOME the_pool)
    else case Symtab.lookup (fst the_pool) full_name of
      SOME nice_name => (nice_name, SOME the_pool)
    | NONE =>
      let
        val nice_prefix = readable_name full_name desired_name
        fun add j =
          let
            val nice_name =
              nice_prefix ^ (if j = 0 then "" else string_of_int j)
          in
            case Symtab.lookup (snd the_pool) nice_name of
              SOME full_name' =>
              if full_name = full_name' then (nice_name, the_pool)
              else add (j + 1)
            | NONE =>
              (nice_name,
               (Symtab.update_new (full_name, nice_name) (fst the_pool),
                Symtab.update_new (nice_name, full_name) (snd the_pool)))
          end
      in add 0 |> apsnd SOME end

fun nice_type (AType name) = nice_name name #>> AType
  | nice_type (AFun (ty1, ty2)) = nice_type ty1 ##>> nice_type ty2 #>> AFun
fun nice_term (ATerm (name, ts)) =
    nice_name name ##>> pool_map nice_term ts #>> ATerm
  | nice_term (AAbs ((name, ty), tm)) =
    nice_name name ##>> nice_type ty ##>> nice_term tm #>> AAbs
fun nice_formula (AQuant (q, xs, phi)) =
    pool_map nice_name (map fst xs)
    ##>> pool_map (fn NONE => pair NONE
                    | SOME ty => nice_type ty #>> SOME) (map snd xs)
    ##>> nice_formula phi
    #>> (fn ((ss, ts), phi) => AQuant (q, ss ~~ ts, phi))
  | nice_formula (AConn (c, phis)) =
    pool_map nice_formula phis #>> curry AConn c
  | nice_formula (AAtom tm) = nice_term tm #>> AAtom
fun nice_problem_line (Decl (ident, sym, ty)) =
    nice_name sym ##>> nice_type ty #>> (fn (sym, ty) => Decl (ident, sym, ty))
  | nice_problem_line (Formula (ident, kind, phi, source, info)) =
    nice_formula phi #>> (fn phi => Formula (ident, kind, phi, source, info))
fun nice_problem problem =
  pool_map (fn (heading, lines) =>
               pool_map nice_problem_line lines #>> pair heading) problem
fun nice_atp_problem readable_names problem =
  nice_problem problem (empty_name_pool readable_names)

end;
