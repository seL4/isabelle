(*  Title:      HOL/Tools/Nitpick/kodkod.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

ML interface for Kodkod.
*)

signature KODKOD =
sig
  type n_ary_index = int * int
  type setting = string * string

  datatype tuple =
    Tuple of int list |
    TupleIndex of n_ary_index |
    TupleReg of n_ary_index

  datatype tuple_set =
    TupleUnion of tuple_set * tuple_set |
    TupleDifference of tuple_set * tuple_set |
    TupleIntersect of tuple_set * tuple_set |
    TupleProduct of tuple_set * tuple_set |
    TupleProject of tuple_set * int |
    TupleSet of tuple list |
    TupleRange of tuple * tuple |
    TupleArea of tuple * tuple |
    TupleAtomSeq of int * int |
    TupleSetReg of n_ary_index

  datatype tuple_assign =
    AssignTuple of n_ary_index * tuple |
    AssignTupleSet of n_ary_index * tuple_set

  type bound = (n_ary_index * string) list * tuple_set list
  type int_bound = int option * tuple_set list

  datatype formula =
    All of decl list * formula |
    Exist of decl list * formula |
    FormulaLet of expr_assign list * formula |
    FormulaIf of formula * formula * formula |
    Or of formula * formula |
    Iff of formula * formula |
    Implies of formula * formula |
    And of formula * formula |
    Not of formula |
    Acyclic of n_ary_index |
    Function of n_ary_index * rel_expr * rel_expr |
    Functional of n_ary_index * rel_expr * rel_expr |
    TotalOrdering of n_ary_index * rel_expr * rel_expr * rel_expr |
    Subset of rel_expr * rel_expr |
    RelEq of rel_expr * rel_expr |
    IntEq of int_expr * int_expr |
    LT of int_expr * int_expr |
    LE of int_expr * int_expr |
    No of rel_expr |
    Lone of rel_expr |
    One of rel_expr |
    Some of rel_expr |
    False |
    True |
    FormulaReg of int
  and rel_expr =
    RelLet of expr_assign list * rel_expr |
    RelIf of formula * rel_expr * rel_expr |
    Union of rel_expr * rel_expr |
    Difference of rel_expr * rel_expr |
    Override of rel_expr * rel_expr |
    Intersect of rel_expr * rel_expr |
    Product of rel_expr * rel_expr |
    IfNo of rel_expr * rel_expr |
    Project of rel_expr * int_expr list |
    Join of rel_expr * rel_expr |
    Closure of rel_expr |
    ReflexiveClosure of rel_expr |
    Transpose of rel_expr |
    Comprehension of decl list * formula |
    Bits of int_expr |
    Int of int_expr |
    Iden |
    Ints |
    None |
    Univ |
    Atom of int |
    AtomSeq of int * int |
    Rel of n_ary_index |
    Var of n_ary_index |
    RelReg of n_ary_index
  and int_expr =
    Sum of decl list * int_expr |
    IntLet of expr_assign list * int_expr |
    IntIf of formula * int_expr * int_expr |
    SHL of int_expr * int_expr |
    SHA of int_expr * int_expr |
    SHR of int_expr * int_expr |
    Add of int_expr * int_expr |
    Sub of int_expr * int_expr |
    Mult of int_expr * int_expr |
    Div of int_expr * int_expr |
    Mod of int_expr * int_expr |
    Cardinality of rel_expr |
    SetSum of rel_expr |
    BitOr of int_expr * int_expr |
    BitXor of int_expr * int_expr |
    BitAnd of int_expr * int_expr |
    BitNot of int_expr |
    Neg of int_expr |
    Absolute of int_expr |
    Signum of int_expr |
    Num of int |
    IntReg of int
  and decl =
    DeclNo of n_ary_index * rel_expr |
    DeclLone of n_ary_index * rel_expr |
    DeclOne of n_ary_index * rel_expr |
    DeclSome of n_ary_index * rel_expr |
    DeclSet of n_ary_index * rel_expr
  and expr_assign =
    AssignFormulaReg of int * formula |
    AssignRelReg of n_ary_index * rel_expr |
    AssignIntReg of int * int_expr

  type 'a fold_expr_funcs =
    {formula_func: formula -> 'a -> 'a,
     rel_expr_func: rel_expr -> 'a -> 'a,
     int_expr_func: int_expr -> 'a -> 'a}

  val fold_formula : 'a fold_expr_funcs -> formula -> 'a -> 'a
  val fold_rel_expr : 'a fold_expr_funcs -> rel_expr -> 'a -> 'a
  val fold_int_expr : 'a fold_expr_funcs -> int_expr -> 'a -> 'a
  val fold_decl : 'a fold_expr_funcs -> decl -> 'a -> 'a
  val fold_expr_assign : 'a fold_expr_funcs -> expr_assign -> 'a -> 'a

  type 'a fold_tuple_funcs =
    {tuple_func: tuple -> 'a -> 'a,
     tuple_set_func: tuple_set -> 'a -> 'a}

  val fold_tuple : 'a fold_tuple_funcs -> tuple -> 'a -> 'a
  val fold_tuple_set : 'a fold_tuple_funcs -> tuple_set -> 'a -> 'a
  val fold_tuple_assign : 'a fold_tuple_funcs -> tuple_assign -> 'a -> 'a
  val fold_bound :
      'a fold_expr_funcs -> 'a fold_tuple_funcs -> bound -> 'a -> 'a
  val fold_int_bound : 'a fold_tuple_funcs -> int_bound -> 'a -> 'a

  type problem =
    {comment: string,
     settings: setting list,
     univ_card: int,
     tuple_assigns: tuple_assign list,
     bounds: bound list,
     int_bounds: int_bound list,
     expr_assigns: expr_assign list,
     formula: formula}

  type raw_bound = n_ary_index * int list list

  datatype outcome =
    JavaNotFound |
    JavaTooOld |
    KodkodiNotInstalled |
    Normal of (int * raw_bound list) list * int list * string |
    TimedOut of int list |
    Error of string * int list

  exception SYNTAX of string * string

  val max_arity : int -> int
  val arity_of_rel_expr : rel_expr -> int
  val is_problem_trivially_false : problem -> bool
  val problems_equivalent : problem * problem -> bool
  val solve_any_problem :
    bool -> bool -> Time.time option -> int -> int -> problem list -> outcome
end;

structure Kodkod : KODKOD =
struct

type n_ary_index = int * int

type setting = string * string

datatype tuple =
  Tuple of int list |
  TupleIndex of n_ary_index |
  TupleReg of n_ary_index

datatype tuple_set =
  TupleUnion of tuple_set * tuple_set |
  TupleDifference of tuple_set * tuple_set |
  TupleIntersect of tuple_set * tuple_set |
  TupleProduct of tuple_set * tuple_set |
  TupleProject of tuple_set * int |
  TupleSet of tuple list |
  TupleRange of tuple * tuple |
  TupleArea of tuple * tuple |
  TupleAtomSeq of int * int |
  TupleSetReg of n_ary_index

datatype tuple_assign =
  AssignTuple of n_ary_index * tuple |
  AssignTupleSet of n_ary_index * tuple_set

type bound = (n_ary_index * string) list * tuple_set list
type int_bound = int option * tuple_set list

datatype formula =
  All of decl list * formula |
  Exist of decl list * formula |
  FormulaLet of expr_assign list * formula |
  FormulaIf of formula * formula * formula |
  Or of formula * formula |
  Iff of formula * formula |
  Implies of formula * formula |
  And of formula * formula |
  Not of formula |
  Acyclic of n_ary_index |
  Function of n_ary_index * rel_expr * rel_expr |
  Functional of n_ary_index * rel_expr * rel_expr |
  TotalOrdering of n_ary_index * rel_expr * rel_expr * rel_expr |
  Subset of rel_expr * rel_expr |
  RelEq of rel_expr * rel_expr |
  IntEq of int_expr * int_expr |
  LT of int_expr * int_expr |
  LE of int_expr * int_expr |
  No of rel_expr |
  Lone of rel_expr |
  One of rel_expr |
  Some of rel_expr |
  False |
  True |
  FormulaReg of int
and rel_expr =
  RelLet of expr_assign list * rel_expr |
  RelIf of formula * rel_expr * rel_expr |
  Union of rel_expr * rel_expr |
  Difference of rel_expr * rel_expr |
  Override of rel_expr * rel_expr |
  Intersect of rel_expr * rel_expr |
  Product of rel_expr * rel_expr |
  IfNo of rel_expr * rel_expr |
  Project of rel_expr * int_expr list |
  Join of rel_expr * rel_expr |
  Closure of rel_expr |
  ReflexiveClosure of rel_expr |
  Transpose of rel_expr |
  Comprehension of decl list * formula |
  Bits of int_expr |
  Int of int_expr |
  Iden |
  Ints |
  None |
  Univ |
  Atom of int |
  AtomSeq of int * int |
  Rel of n_ary_index |
  Var of n_ary_index |
  RelReg of n_ary_index
and int_expr =
  Sum of decl list * int_expr |
  IntLet of expr_assign list * int_expr |
  IntIf of formula * int_expr * int_expr |
  SHL of int_expr * int_expr |
  SHA of int_expr * int_expr |
  SHR of int_expr * int_expr |
  Add of int_expr * int_expr |
  Sub of int_expr * int_expr |
  Mult of int_expr * int_expr |
  Div of int_expr * int_expr |
  Mod of int_expr * int_expr |
  Cardinality of rel_expr |
  SetSum of rel_expr |
  BitOr of int_expr * int_expr |
  BitXor of int_expr * int_expr |
  BitAnd of int_expr * int_expr |
  BitNot of int_expr |
  Neg of int_expr |
  Absolute of int_expr |
  Signum of int_expr |
  Num of int |
  IntReg of int
and decl =
  DeclNo of n_ary_index * rel_expr |
  DeclLone of n_ary_index * rel_expr |
  DeclOne of n_ary_index * rel_expr |
  DeclSome of n_ary_index * rel_expr |
  DeclSet of n_ary_index * rel_expr
and expr_assign =
  AssignFormulaReg of int * formula |
  AssignRelReg of n_ary_index * rel_expr |
  AssignIntReg of int * int_expr

type problem =
  {comment: string,
   settings: setting list,
   univ_card: int,
   tuple_assigns: tuple_assign list,
   bounds: bound list,
   int_bounds: int_bound list,
   expr_assigns: expr_assign list,
   formula: formula}

type raw_bound = n_ary_index * int list list

datatype outcome =
  JavaNotFound |
  JavaTooOld |
  KodkodiNotInstalled |
  Normal of (int * raw_bound list) list * int list * string |
  TimedOut of int list |
  Error of string * int list

exception SYNTAX of string * string

type 'a fold_expr_funcs =
  {formula_func: formula -> 'a -> 'a,
   rel_expr_func: rel_expr -> 'a -> 'a,
   int_expr_func: int_expr -> 'a -> 'a}

fun is_new_kodkodi_version () =
  case getenv "KODKODI_VERSION" of
    "" => false
  | s => dict_ord int_ord (s |> space_explode "."
                             |> map (the_default 0 o Int.fromString),
                           [1, 2, 13]) = GREATER

(** Auxiliary functions on Kodkod problems **)

fun fold_formula (F : 'a fold_expr_funcs) formula =
  case formula of
    All (ds, f) => fold (fold_decl F) ds #> fold_formula F f
  | Exist (ds, f) => fold (fold_decl F) ds #> fold_formula F f
  | FormulaLet (bs, f) => fold (fold_expr_assign F) bs #> fold_formula F f
  | FormulaIf (f, f1, f2) =>
    fold_formula F f #> fold_formula F f1 #> fold_formula F f2
  | Or (f1, f2) => fold_formula F f1 #> fold_formula F f2
  | Iff (f1, f2) => fold_formula F f1 #> fold_formula F f2
  | Implies (f1, f2) => fold_formula F f1 #> fold_formula F f2
  | And (f1, f2) => fold_formula F f1 #> fold_formula F f2
  | Not f => fold_formula F f
  | Acyclic x => fold_rel_expr F (Rel x)
  | Function (x, r1, r2) =>
    fold_rel_expr F (Rel x) #> fold_rel_expr F r1 #> fold_rel_expr F r2
  | Functional (x, r1, r2) =>
    fold_rel_expr F (Rel x) #> fold_rel_expr F r1 #> fold_rel_expr F r2
  | TotalOrdering (x, r1, r2, r3) =>
    fold_rel_expr F (Rel x) #> fold_rel_expr F r1 #> fold_rel_expr F r2
    #> fold_rel_expr F r3
  | Subset (r1, r2) => fold_rel_expr F r1 #> fold_rel_expr F r2
  | RelEq (r1, r2) => fold_rel_expr F r1 #> fold_rel_expr F r2
  | IntEq (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | LT (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | LE (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | No r => fold_rel_expr F r
  | Lone r => fold_rel_expr F r
  | One r => fold_rel_expr F r
  | Some r => fold_rel_expr F r
  | False => #formula_func F formula
  | True => #formula_func F formula
  | FormulaReg _ => #formula_func F formula
and fold_rel_expr F rel_expr =
  case rel_expr of
    RelLet (bs, r) => fold (fold_expr_assign F) bs #> fold_rel_expr F r
  | RelIf (f, r1, r2) =>
    fold_formula F f #> fold_rel_expr F r1 #> fold_rel_expr F r2
  | Union (r1, r2) => fold_rel_expr F r1 #> fold_rel_expr F r2
  | Difference (r1, r2) => fold_rel_expr F r1 #> fold_rel_expr F r2
  | Override (r1, r2) => fold_rel_expr F r1 #> fold_rel_expr F r2
  | Intersect (r1, r2) => fold_rel_expr F r1 #> fold_rel_expr F r2
  | Product (r1, r2) => fold_rel_expr F r1 #> fold_rel_expr F r2
  | IfNo (r1, r2) => fold_rel_expr F r1 #> fold_rel_expr F r2
  | Project (r1, is) => fold_rel_expr F r1 #> fold (fold_int_expr F) is
  | Join (r1, r2) => fold_rel_expr F r1 #> fold_rel_expr F r2
  | Closure r => fold_rel_expr F r
  | ReflexiveClosure r => fold_rel_expr F r
  | Transpose r => fold_rel_expr F r
  | Comprehension (ds, f) => fold (fold_decl F) ds #> fold_formula F f
  | Bits i => fold_int_expr F i
  | Int i => fold_int_expr F i
  | Iden => #rel_expr_func F rel_expr
  | Ints => #rel_expr_func F rel_expr
  | None => #rel_expr_func F rel_expr
  | Univ => #rel_expr_func F rel_expr
  | Atom _ => #rel_expr_func F rel_expr
  | AtomSeq _ => #rel_expr_func F rel_expr
  | Rel _ => #rel_expr_func F rel_expr
  | Var _ => #rel_expr_func F rel_expr
  | RelReg _ => #rel_expr_func F rel_expr
and fold_int_expr F int_expr =
  case int_expr of
    Sum (ds, i) => fold (fold_decl F) ds #> fold_int_expr F i
  | IntLet (bs, i) => fold (fold_expr_assign F) bs #> fold_int_expr F i
  | IntIf (f, i1, i2) =>
    fold_formula F f #> fold_int_expr F i1 #> fold_int_expr F i2
  | SHL (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | SHA (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | SHR (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | Add (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | Sub (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | Mult (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | Div (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | Mod (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | Cardinality r => fold_rel_expr F r
  | SetSum r => fold_rel_expr F r
  | BitOr (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | BitXor (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | BitAnd (i1, i2) => fold_int_expr F i1 #> fold_int_expr F i2
  | BitNot i => fold_int_expr F i
  | Neg i => fold_int_expr F i
  | Absolute i => fold_int_expr F i
  | Signum i => fold_int_expr F i
  | Num _ => #int_expr_func F int_expr
  | IntReg _ => #int_expr_func F int_expr
and fold_decl F decl =
  case decl of
    DeclNo (x, r) => fold_rel_expr F (Var x) #> fold_rel_expr F r
  | DeclLone (x, r) => fold_rel_expr F (Var x) #> fold_rel_expr F r
  | DeclOne (x, r) => fold_rel_expr F (Var x) #> fold_rel_expr F r
  | DeclSome (x, r) => fold_rel_expr F (Var x) #> fold_rel_expr F r
  | DeclSet (x, r) => fold_rel_expr F (Var x) #> fold_rel_expr F r
and fold_expr_assign F assign =
  case assign of
    AssignFormulaReg (x, f) => fold_formula F (FormulaReg x) #> fold_formula F f
  | AssignRelReg (x, r) => fold_rel_expr F (RelReg x) #> fold_rel_expr F r
  | AssignIntReg (x, i) => fold_int_expr F (IntReg x) #> fold_int_expr F i

type 'a fold_tuple_funcs =
  {tuple_func: tuple -> 'a -> 'a,
   tuple_set_func: tuple_set -> 'a -> 'a}

fun fold_tuple (F : 'a fold_tuple_funcs) = #tuple_func F
fun fold_tuple_set F tuple_set =
  case tuple_set of
    TupleUnion (ts1, ts2) => fold_tuple_set F ts1 #> fold_tuple_set F ts2
  | TupleDifference (ts1, ts2) => fold_tuple_set F ts1 #> fold_tuple_set F ts2
  | TupleIntersect (ts1, ts2) => fold_tuple_set F ts1 #> fold_tuple_set F ts2
  | TupleProduct (ts1, ts2) => fold_tuple_set F ts1 #> fold_tuple_set F ts2
  | TupleProject (ts, _) => fold_tuple_set F ts
  | TupleSet ts => fold (fold_tuple F) ts
  | TupleRange (t1, t2) => fold_tuple F t1 #> fold_tuple F t2
  | TupleArea (t1, t2) => fold_tuple F t1 #> fold_tuple F t2
  | TupleAtomSeq _ => #tuple_set_func F tuple_set
  | TupleSetReg _ => #tuple_set_func F tuple_set
fun fold_tuple_assign F assign =
  case assign of
    AssignTuple (x, t) => fold_tuple F (TupleReg x) #> fold_tuple F t
  | AssignTupleSet (x, ts) =>
    fold_tuple_set F (TupleSetReg x) #> fold_tuple_set F ts
fun fold_bound expr_F tuple_F (zs, tss) =
  fold (fold_rel_expr expr_F) (map (Rel o fst) zs)
  #> fold (fold_tuple_set tuple_F) tss
fun fold_int_bound F (_, tss) = fold (fold_tuple_set F) tss

fun max_arity univ_card = floor (Math.ln 2147483647.0
                                 / Math.ln (Real.fromInt univ_card))
fun arity_of_rel_expr (RelLet (_, r)) = arity_of_rel_expr r
  | arity_of_rel_expr (RelIf (_, r1, _)) = arity_of_rel_expr r1
  | arity_of_rel_expr (Union (r1, _)) = arity_of_rel_expr r1
  | arity_of_rel_expr (Difference (r1, _)) = arity_of_rel_expr r1
  | arity_of_rel_expr (Override (r1, _)) = arity_of_rel_expr r1
  | arity_of_rel_expr (Intersect (r1, _)) = arity_of_rel_expr r1
  | arity_of_rel_expr (Product (r1, r2)) = sum_arities_of_rel_exprs r1 r2
  | arity_of_rel_expr (IfNo (r1, _)) = arity_of_rel_expr r1
  | arity_of_rel_expr (Project (_, is)) = length is
  | arity_of_rel_expr (Join (r1, r2)) = sum_arities_of_rel_exprs r1 r2 - 2
  | arity_of_rel_expr (Closure _) = 2
  | arity_of_rel_expr (ReflexiveClosure _) = 2
  | arity_of_rel_expr (Transpose _) = 2
  | arity_of_rel_expr (Comprehension (ds, _)) =
    fold (curry op + o arity_of_decl) ds 0
  | arity_of_rel_expr (Bits _) = 1
  | arity_of_rel_expr (Int _) = 1
  | arity_of_rel_expr Iden = 2
  | arity_of_rel_expr Ints = 1
  | arity_of_rel_expr None = 1
  | arity_of_rel_expr Univ = 1
  | arity_of_rel_expr (Atom _) = 1
  | arity_of_rel_expr (AtomSeq _) = 1
  | arity_of_rel_expr (Rel (n, _)) = n
  | arity_of_rel_expr (Var (n, _)) = n
  | arity_of_rel_expr (RelReg (n, _)) = n
and sum_arities_of_rel_exprs r1 r2 = arity_of_rel_expr r1 + arity_of_rel_expr r2
and arity_of_decl (DeclNo ((n, _), _)) = n
  | arity_of_decl (DeclLone ((n, _), _)) = n
  | arity_of_decl (DeclOne ((n, _), _)) = n
  | arity_of_decl (DeclSome ((n, _), _)) = n
  | arity_of_decl (DeclSet ((n, _), _)) = n

fun is_problem_trivially_false ({formula = False, ...} : problem) = true
  | is_problem_trivially_false _ = false

val chop_solver = take 2 o space_explode ","

fun settings_equivalent ([], []) = true
  | settings_equivalent ((key1, value1) :: settings1,
                         (key2, value2) :: settings2) =
    key1 = key2 andalso
    (value1 = value2 orelse key1 = "delay" orelse
     (key1 = "solver" andalso chop_solver value1 = chop_solver value2)) andalso
    settings_equivalent (settings1, settings2)
  | settings_equivalent _ = false

fun problems_equivalent (p1 : problem, p2 : problem) =
  #univ_card p1 = #univ_card p2 andalso
  #formula p1 = #formula p2 andalso
  #bounds p1 = #bounds p2 andalso
  #expr_assigns p1 = #expr_assigns p2 andalso
  #tuple_assigns p1 = #tuple_assigns p2 andalso
  #int_bounds p1 = #int_bounds p2 andalso
  settings_equivalent (#settings p1, #settings p2)

(** Serialization of problem **)

fun base_name j =
  if j < 0 then string_of_int (~j - 1) ^ "'" else string_of_int j

fun n_ary_name (1, j) prefix _ _ = prefix ^ base_name j
  | n_ary_name (2, j) _ prefix _ = prefix ^ base_name j
  | n_ary_name (n, j) _ _ prefix = prefix ^ string_of_int n ^ "_" ^ base_name j

fun atom_name j = "A" ^ base_name j
fun atom_seq_name (k, 0) = "u" ^ base_name k
  | atom_seq_name (k, j0) = "u" ^ base_name k ^ "@" ^ base_name j0
fun formula_reg_name j = "$f" ^ base_name j
fun rel_reg_name j = "$e" ^ base_name j
fun int_reg_name j = "$i" ^ base_name j

fun tuple_name x = n_ary_name x "A" "P" "T"
fun rel_name new_kodkodi (n, j) =
  n_ary_name (n, if new_kodkodi then j
                 else if j >= 0 then 2 * j
                 else 2 * ~j - 1) "s" "r" "m"
fun var_name x = n_ary_name x "S" "R" "M"
fun tuple_reg_name x = n_ary_name x "$A" "$P" "$T"
fun tuple_set_reg_name x = n_ary_name x "$a" "$p" "$t"

fun inline_comment "" = ""
  | inline_comment comment =
    " /* " ^ translate_string (fn "\n" => " " | "*" => "* " | s => s) comment ^
    " */"
fun block_comment "" = ""
  | block_comment comment = prefix_lines "// " comment ^ "\n"

fun commented_rel_name new_kodkodi (x, s) =
  rel_name new_kodkodi x ^ inline_comment s

fun string_for_tuple (Tuple js) = "[" ^ commas (map atom_name js) ^ "]"
  | string_for_tuple (TupleIndex x) = tuple_name x
  | string_for_tuple (TupleReg x) = tuple_reg_name x

val no_prec = 100
val prec_TupleUnion = 1
val prec_TupleIntersect = 2
val prec_TupleProduct = 3
val prec_TupleProject = 4

fun precedence_ts (TupleUnion _) = prec_TupleUnion
  | precedence_ts (TupleDifference _) = prec_TupleUnion
  | precedence_ts (TupleIntersect _) = prec_TupleIntersect
  | precedence_ts (TupleProduct _) = prec_TupleProduct
  | precedence_ts (TupleProject _) = prec_TupleProject
  | precedence_ts _ = no_prec

fun string_for_tuple_set tuple_set =
  let
    fun sub tuple_set outer_prec =
      let
        val prec = precedence_ts tuple_set
        val need_parens = (prec < outer_prec)
      in
        (if need_parens then "(" else "") ^
        (case tuple_set of
           TupleUnion (ts1, ts2) => sub ts1 prec ^ " + " ^ sub ts2 (prec + 1)
         | TupleDifference (ts1, ts2) =>
           sub ts1 prec ^ " - " ^ sub ts2 (prec + 1)
         | TupleIntersect (ts1, ts2) => sub ts1 prec ^ " & " ^ sub ts2 prec
         | TupleProduct (ts1, ts2) => sub ts1 prec ^ "->" ^ sub ts2 prec
         | TupleProject (ts, c) => sub ts prec ^ "[" ^ string_of_int c ^ "]"
         | TupleSet ts => "{" ^ commas (map string_for_tuple ts) ^ "}"
         | TupleRange (t1, t2) =>
           "{" ^ string_for_tuple t1 ^
           (if t1 = t2 then "" else " .. " ^ string_for_tuple t2) ^ "}"
         | TupleArea (t1, t2) =>
           "{" ^ string_for_tuple t1 ^ " # " ^ string_for_tuple t2 ^ "}"
         | TupleAtomSeq x => atom_seq_name x
         | TupleSetReg x => tuple_set_reg_name x) ^
        (if need_parens then ")" else "")
      end
  in sub tuple_set 0 end

fun string_for_tuple_assign (AssignTuple (x, t)) =
    tuple_reg_name x ^ " := " ^ string_for_tuple t ^ "\n"
  | string_for_tuple_assign (AssignTupleSet (x, ts)) =
    tuple_set_reg_name x ^ " := " ^ string_for_tuple_set ts ^ "\n"

fun string_for_bound new_kodkodi (zs, tss) =
  "bounds " ^ commas (map (commented_rel_name new_kodkodi) zs) ^ ": " ^
  (if length tss = 1 then "" else "[") ^ commas (map string_for_tuple_set tss) ^
  (if length tss = 1 then "" else "]") ^ "\n"

fun int_string_for_bound (opt_n, tss) =
  (case opt_n of
     SOME n => signed_string_of_int n ^ ": "
   | NONE => "") ^ "[" ^ commas (map string_for_tuple_set tss) ^ "]"

val prec_All = 1
val prec_Or = 2
val prec_Iff = 3
val prec_Implies = 4
val prec_And = 5
val prec_Not = 6
val prec_Eq = 7
val prec_Some = 8
val prec_SHL = 9
val prec_Add = 10
val prec_Mult = 11
val prec_Override = 12
val prec_Intersect = 13
val prec_Product = 14
val prec_IfNo = 15
val prec_Project = 17
val prec_Join = 18
val prec_BitNot = 19

fun precedence_f (All _) = prec_All
  | precedence_f (Exist _) = prec_All
  | precedence_f (FormulaLet _) = prec_All
  | precedence_f (FormulaIf _) = prec_All
  | precedence_f (Or _) = prec_Or
  | precedence_f (Iff _) = prec_Iff
  | precedence_f (Implies _) = prec_Implies
  | precedence_f (And _) = prec_And
  | precedence_f (Not _) = prec_Not
  | precedence_f (Acyclic _) = no_prec
  | precedence_f (Function _) = no_prec
  | precedence_f (Functional _) = no_prec
  | precedence_f (TotalOrdering _) = no_prec
  | precedence_f (Subset _) = prec_Eq
  | precedence_f (RelEq _) = prec_Eq
  | precedence_f (IntEq _) = prec_Eq
  | precedence_f (LT _) = prec_Eq
  | precedence_f (LE _) = prec_Eq
  | precedence_f (No _) = prec_Some
  | precedence_f (Lone _) = prec_Some
  | precedence_f (One _) = prec_Some
  | precedence_f (Some _) = prec_Some
  | precedence_f False = no_prec
  | precedence_f True = no_prec
  | precedence_f (FormulaReg _) = no_prec
and precedence_r (RelLet _) = prec_All
  | precedence_r (RelIf _) = prec_All
  | precedence_r (Union _) = prec_Add
  | precedence_r (Difference _) = prec_Add
  | precedence_r (Override _) = prec_Override
  | precedence_r (Intersect _) = prec_Intersect
  | precedence_r (Product _) = prec_Product
  | precedence_r (IfNo _) = prec_IfNo
  | precedence_r (Project _) = prec_Project
  | precedence_r (Join _) = prec_Join
  | precedence_r (Closure _) = prec_BitNot
  | precedence_r (ReflexiveClosure _) = prec_BitNot
  | precedence_r (Transpose _) = prec_BitNot
  | precedence_r (Comprehension _) = no_prec
  | precedence_r (Bits _) = no_prec
  | precedence_r (Int _) = no_prec
  | precedence_r Iden = no_prec
  | precedence_r Ints = no_prec
  | precedence_r None = no_prec
  | precedence_r Univ = no_prec
  | precedence_r (Atom _) = no_prec
  | precedence_r (AtomSeq _) = no_prec
  | precedence_r (Rel _) = no_prec
  | precedence_r (Var _) = no_prec
  | precedence_r (RelReg _) = no_prec
and precedence_i (Sum _) = prec_All
  | precedence_i (IntLet _) = prec_All
  | precedence_i (IntIf _) = prec_All
  | precedence_i (SHL _) = prec_SHL
  | precedence_i (SHA _) = prec_SHL
  | precedence_i (SHR _) = prec_SHL
  | precedence_i (Add _) = prec_Add
  | precedence_i (Sub _) = prec_Add
  | precedence_i (Mult _) = prec_Mult
  | precedence_i (Div _) = prec_Mult
  | precedence_i (Mod _) = prec_Mult
  | precedence_i (Cardinality _) = no_prec
  | precedence_i (SetSum _) = no_prec
  | precedence_i (BitOr _) = prec_Intersect
  | precedence_i (BitXor _) = prec_Intersect
  | precedence_i (BitAnd _) = prec_Intersect
  | precedence_i (BitNot _) = prec_BitNot
  | precedence_i (Neg _) = prec_BitNot
  | precedence_i (Absolute _) = prec_BitNot
  | precedence_i (Signum _) = prec_BitNot
  | precedence_i (Num _) = no_prec
  | precedence_i (IntReg _) = no_prec

fun write_problem_file out problems =
  let
    val new_kodkodi = is_new_kodkodi_version ()
    val rel_name = rel_name new_kodkodi
    fun out_outmost_f (And (f1, f2)) =
        (out_outmost_f f1; out "\n   && "; out_outmost_f f2)
      | out_outmost_f f = out_f f prec_And
    and out_f formula outer_prec =
      let
        val prec = precedence_f formula
        val need_parens = (prec < outer_prec)
      in
        (if need_parens then out "(" else ());
        (case formula of
           All (ds, f) => (out "all ["; out_decls ds; out "] | "; out_f f prec)
         | Exist (ds, f) =>
           (out "some ["; out_decls ds; out "] | "; out_f f prec)
         | FormulaLet (bs, f) =>
           (out "let ["; out_assigns bs; out "] | "; out_f f prec)
         | FormulaIf (f, f1, f2) =>
           (out "if "; out_f f prec; out " then "; out_f f1 prec; out " else ";
            out_f f2 prec)
         | Or (f1, f2) => (out_f f1 prec; out " || "; out_f f2 prec)
         | Iff (f1, f2) => (out_f f1 prec; out " <=> "; out_f f2 prec)
         | Implies (f1, f2) => (out_f f1 (prec + 1); out " => "; out_f f2 prec)
         | And (f1, f2) => (out_f f1 prec; out " && "; out_f f2 prec)
         | Not f => (out "! "; out_f f prec)
         | Acyclic x => out ("ACYCLIC(" ^ rel_name x ^ ")")
         | Function (x, r1, r2) =>
           (out ("FUNCTION(" ^ rel_name x ^ ", "); out_r r1 0; out " -> one ";
            out_r r2 0; out ")")
         | Functional (x, r1, r2) =>
           (out ("FUNCTION(" ^ rel_name x ^ ", "); out_r r1 0; out " -> lone ";
            out_r r2 0; out ")")
         | TotalOrdering (x, r1, r2, r3) =>
           (out ("TOTAL_ORDERING(" ^ rel_name x ^ ", "); out_r r1 0; out ", ";
            out_r r2 0; out ", "; out_r r3 0; out ")")
         | Subset (r1, r2) => (out_r r1 prec; out " in "; out_r r2 prec)
         | RelEq (r1, r2) => (out_r r1 prec; out " = "; out_r r2 prec)
         | IntEq (i1, i2) => (out_i i1 prec; out " = "; out_i i2 prec)
         | LT (i1, i2) => (out_i i1 prec; out " < "; out_i i2 prec)
         | LE (i1, i2) => (out_i i1 prec; out " <= "; out_i i2 prec)
         | No r => (out "no "; out_r r prec)
         | Lone r => (out "lone "; out_r r prec)
         | One r => (out "one "; out_r r prec)
         | Some r => (out "some "; out_r r prec)
         | False => out "false"
         | True => out "true"
         | FormulaReg j => out (formula_reg_name j));
        (if need_parens then out ")" else ())
      end
    and out_r rel_expr outer_prec =
      let
        val prec = precedence_r rel_expr
        val need_parens = (prec < outer_prec)
      in
        (if need_parens then out "(" else ());
        (case rel_expr of
           RelLet (bs, r) =>
           (out "let ["; out_assigns bs; out "] | "; out_r r prec)
         | RelIf (f, r1, r2) =>
           (out "if "; out_f f prec; out " then "; out_r r1 prec;
            out " else "; out_r r2 prec)
         | Union (r1, r2) => (out_r r1 prec; out " + "; out_r r2 (prec + 1))
         | Difference (r1, r2) =>
           (out_r r1 prec; out " - "; out_r r2 (prec + 1))
         | Override (r1, r2) => (out_r r1 prec; out " ++ "; out_r r2 prec)
         | Intersect (r1, r2) => (out_r r1 prec; out " & "; out_r r2 prec)
         | Product (r1, r2) => (out_r r1 prec; out "->"; out_r r2 prec)
         | IfNo (r1, r2) => (out_r r1 prec; out "\\"; out_r r2 prec)
         | Project (r1, is) => (out_r r1 prec; out "["; out_columns is; out "]")
         | Join (r1, r2) => (out_r r1 prec; out "."; out_r r2 (prec + 1))
         | Closure r => (out "^"; out_r r prec)
         | ReflexiveClosure r => (out "*"; out_r r prec)
         | Transpose r => (out "~"; out_r r prec)
         | Comprehension (ds, f) =>
           (out "{["; out_decls ds; out "] | "; out_f f 0; out "}")
         | Bits i => (out "Bits["; out_i i 0; out "]")
         | Int i => (out "Int["; out_i i 0; out "]")
         | Iden => out "iden"
         | Ints => out "ints"
         | None => out "none"
         | Univ => out "univ"
         | Atom j => out (atom_name j)
         | AtomSeq x => out (atom_seq_name x)
         | Rel x => out (rel_name x)
         | Var x => out (var_name x)
         | RelReg (_, j) => out (rel_reg_name j));
        (if need_parens then out ")" else ())
      end
    and out_i int_expr outer_prec =
      let
        val prec = precedence_i int_expr
        val need_parens = (prec < outer_prec)
      in
        (if need_parens then out "(" else ());
        (case int_expr of
           Sum (ds, i) => (out "sum ["; out_decls ds; out "] | "; out_i i prec)
         | IntLet (bs, i) =>
           (out "let ["; out_assigns bs; out "] | "; out_i i prec)
         | IntIf (f, i1, i2) =>
           (out "if "; out_f f prec; out " then "; out_i i1 prec;
            out " else "; out_i i2 prec)
         | SHL (i1, i2) => (out_i i1 prec; out " << "; out_i i2 (prec + 1))
         | SHA (i1, i2) => (out_i i1 prec; out " >> "; out_i i2 (prec + 1))
         | SHR (i1, i2) => (out_i i1 prec; out " >>> "; out_i i2 (prec + 1))
         | Add (i1, i2) => (out_i i1 prec; out " + "; out_i i2 (prec + 1))
         | Sub (i1, i2) => (out_i i1 prec; out " - "; out_i i2 (prec + 1))
         | Mult (i1, i2) => (out_i i1 prec; out " * "; out_i i2 (prec + 1))
         | Div (i1, i2) => (out_i i1 prec; out " / "; out_i i2 (prec + 1))
         | Mod (i1, i2) => (out_i i1 prec; out " % "; out_i i2 (prec + 1))
         | Cardinality r => (out "#("; out_r r 0; out ")")
         | SetSum r => (out "sum("; out_r r 0; out ")")
         | BitOr (i1, i2) => (out_i i1 prec; out " | "; out_i i2 prec)
         | BitXor (i1, i2) => (out_i i1 prec; out " ^ "; out_i i2 prec)
         | BitAnd (i1, i2) => (out_i i1 prec; out " & "; out_i i2 prec)
         | BitNot i => (out "~"; out_i i prec)
         | Neg i => (out "-"; out_i i prec)
         | Absolute i => (out "abs "; out_i i prec)
         | Signum i => (out "sgn "; out_i i prec)
         | Num k => out (signed_string_of_int k)
         | IntReg j => out (int_reg_name j));
        (if need_parens then out ")" else ())
      end
    and out_decls [] = ()
      | out_decls [d] = out_decl d
      | out_decls (d :: ds) = (out_decl d; out ", "; out_decls ds)
    and out_decl (DeclNo (x, r)) =
        (out (var_name x); out " : no "; out_r r 0)
      | out_decl (DeclLone (x, r)) =
        (out (var_name x); out " : lone "; out_r r 0)
      | out_decl (DeclOne (x, r)) =
        (out (var_name x); out " : one "; out_r r 0)
      | out_decl (DeclSome (x, r)) =
        (out (var_name x); out " : some "; out_r r 0)
      | out_decl (DeclSet (x, r)) =
        (out (var_name x); out " : set "; out_r r 0)
    and out_assigns [] = ()
      | out_assigns [b] = out_assign b
      | out_assigns (b :: bs) = (out_assign b; out ", "; out_assigns bs)
    and out_assign (AssignFormulaReg (j, f)) =
        (out (formula_reg_name j); out " := "; out_f f 0)
      | out_assign (AssignRelReg ((_, j), r)) =
        (out (rel_reg_name j); out " := "; out_r r 0)
      | out_assign (AssignIntReg (j, i)) =
        (out (int_reg_name j); out " := "; out_i i 0)
    and out_columns [] = ()
      | out_columns [i] = out_i i 0
      | out_columns (i :: is) = (out_i i 0; out ", "; out_columns is)
    and out_problem {comment, settings, univ_card, tuple_assigns, bounds,
                     int_bounds, expr_assigns, formula} =
        (out ("\n" ^ block_comment comment ^
              implode (map (fn (key, value) => key ^ ": " ^ value ^ "\n")
                            settings) ^
              "univ: " ^ atom_seq_name (univ_card, 0) ^ "\n" ^
              implode (map string_for_tuple_assign tuple_assigns) ^
              implode (map (string_for_bound new_kodkodi) bounds) ^
              (if int_bounds = [] then
                 ""
               else
                 "int_bounds: " ^
                 commas (map int_string_for_bound int_bounds) ^ "\n"));
         map (fn b => (out_assign b; out ";")) expr_assigns;
         out "solve "; out_outmost_f formula; out ";\n")
  in
    out ("// This file was generated by Isabelle (most likely Nitpick)\n" ^
         "// " ^ ATP_Util.timestamp () ^ "\n");
    map out_problem problems
  end

(** Parsing of solution **)

fun is_ident_char s =
  Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s orelse
  s = "_" orelse s = "'" orelse s = "$"

fun strip_blanks [] = []
  | strip_blanks (" " :: ss) = strip_blanks ss
  | strip_blanks [s1, " "] = [s1]
  | strip_blanks (s1 :: " " :: s2 :: ss) =
    if is_ident_char s1 andalso is_ident_char s2 then
      s1 :: " " :: strip_blanks (s2 :: ss)
    else
      strip_blanks (s1 :: s2 :: ss)
  | strip_blanks (s :: ss) = s :: strip_blanks ss

val scan_nat =
  Scan.repeat1 (Scan.one Symbol.is_ascii_digit)
  >> (the o Int.fromString o space_implode "")
fun scan_rel_name new_kodkodi =
  ($$ "s" |-- scan_nat >> pair 1
   || $$ "r" |-- scan_nat >> pair 2
   || ($$ "m" |-- scan_nat --| $$ "_") -- scan_nat) -- Scan.option ($$ "'")
  >> (fn ((n, j), SOME _) => (n, ~j - 1)
       | ((n, j), NONE) => (n, if new_kodkodi then j
                               else if j mod 2 = 0 then j div 2
                               else ~(j + 1) div 2))
val scan_atom = $$ "A" |-- scan_nat
fun parse_non_empty_list scan = scan ::: Scan.repeat ($$ "," |-- scan)
fun parse_list scan = parse_non_empty_list scan || Scan.succeed []
val parse_tuple = $$ "[" |-- parse_list scan_atom --| $$ "]"
val parse_tuple_set = $$ "[" |-- parse_list parse_tuple --| $$ "]"
fun parse_assignment new_kodkodi =
  (scan_rel_name new_kodkodi --| $$ "=") -- parse_tuple_set
fun parse_instance new_kodkodi =
  Scan.this_string "relations:"
  |-- $$ "{" |-- parse_list (parse_assignment new_kodkodi) --| $$ "}"

fun extract_instance new_kodkodi =
  fst o Scan.finite Symbol.stopper
            (Scan.error (!! (fn _ =>
                                raise SYNTAX ("Kodkod.extract_instance",
                                              "ill-formed Kodkodi output"))
                            (parse_instance new_kodkodi)))
  o strip_blanks o raw_explode

val problem_marker = "*** PROBLEM "
val outcome_marker = "---OUTCOME---\n"
val instance_marker = "---INSTANCE---\n"

fun read_section_body marker =
  Substring.string o fst o Substring.position "\n\n"
  o Substring.triml (size marker)

fun read_next_instance new_kodkodi s =
  let val s = Substring.position instance_marker s |> snd in
    if Substring.isEmpty s then
      raise SYNTAX ("Kodkod.read_next_instance", "expected \"INSTANCE\" marker")
    else
      read_section_body instance_marker s |> extract_instance new_kodkodi
  end

fun read_next_outcomes new_kodkodi j (s, ps, js) =
  let val (s1, s2) = Substring.position outcome_marker s in
    if Substring.isEmpty s2 orelse
       not (Substring.isEmpty (Substring.position problem_marker s1
                               |> snd)) then
      (s, ps, js)
    else
      let
        val outcome = read_section_body outcome_marker s2
        val s = Substring.triml (size outcome_marker) s2
      in
        if String.isSuffix "UNSATISFIABLE" outcome then
          read_next_outcomes new_kodkodi j (s, ps, j :: js)
        else if String.isSuffix "SATISFIABLE" outcome then
          read_next_outcomes new_kodkodi j
                           (s, (j, read_next_instance new_kodkodi s2) :: ps, js)
        else
          raise SYNTAX ("Kodkod.read_next_outcomes",
                        "unknown outcome " ^ quote outcome)
      end
  end

fun read_next_problems new_kodkodi (s, ps, js) =
  let val s = Substring.position problem_marker s |> snd in
    if Substring.isEmpty s then
      (ps, js)
    else
      let
        val s = Substring.triml (size problem_marker) s
        val j_plus_1 = s |> Substring.takel (not_equal #" ") |> Substring.string
                         |> Int.fromString |> the
        val j = j_plus_1 - 1
      in
        read_next_problems new_kodkodi
                           (read_next_outcomes new_kodkodi j (s, ps, js))
      end
  end
  handle Option.Option => raise SYNTAX ("Kodkod.read_next_problems",
                                        "expected number after \"PROBLEM\"")

fun read_output_file new_kodkodi path =
  (false,
   read_next_problems new_kodkodi (Substring.full (File.read path), [], [])
   |>> rev ||> rev)
  handle IO.Io _ => (true, ([], [])) | OS.SysErr _ => (true, ([], []))

(** Main Kodkod entry point **)

val created_temp_dir = Unsynchronized.ref false

fun serial_string_and_temporary_dir_for_overlord overlord =
  if overlord then
    ("", getenv "ISABELLE_HOME_USER")
  else
    let
      val dir = getenv "ISABELLE_TMP"
      val _ = if !created_temp_dir then ()
              else (created_temp_dir := true; Isabelle_System.mkdirs (Path.explode dir))
    in (serial_string (), dir) end

(* The fudge term below is to account for Kodkodi's slow start-up time, which
   is partly due to the JVM and partly due to the ML "bash" function. *)
val fudge_ms = 250

fun milliseconds_until_deadline deadline =
  case deadline of
    NONE => ~1
  | SOME time =>
    Int.max (0, Time.toMilliseconds (Time.- (time, Time.now ())) - fudge_ms)

fun uncached_solve_any_problem overlord deadline max_threads max_solutions
                               problems =
  let
    val new_kodkodi = is_new_kodkodi_version ()
    val j = find_index (curry (op =) True o #formula) problems
    val indexed_problems = if j >= 0 then
                             [(j, nth problems j)]
                           else
                             filter_out (is_problem_trivially_false o snd)
                                        (0 upto length problems - 1 ~~ problems)
    val triv_js = filter_out (AList.defined (op =) indexed_problems)
                             (0 upto length problems - 1)
    val reindex = fst o nth indexed_problems
  in
    if null indexed_problems then
      Normal ([], triv_js, "")
    else
      let
        val (serial_str, temp_dir) =
          serial_string_and_temporary_dir_for_overlord overlord
        fun path_for suf =
          Path.explode (temp_dir ^ "/kodkodi" ^ serial_str ^ "." ^ suf)
        val in_path = path_for "kki"
        val in_buf = Unsynchronized.ref Buffer.empty
        fun out s = Unsynchronized.change in_buf (Buffer.add s)
        val out_path = path_for "out"
        val err_path = path_for "err"
        val _ = write_problem_file out (map snd indexed_problems)
        val _ = File.write_buffer in_path (!in_buf)
        fun remove_temporary_files () =
          if overlord then ()
          else List.app (K () o try File.rm) [in_path, out_path, err_path]
      in
        let
          val ms = milliseconds_until_deadline deadline
          val outcome =
            let
              val code =
                Isabelle_System.bash ("cd " ^ File.shell_quote temp_dir ^ ";\n\
                      \\"$KODKODI\"/bin/kodkodi" ^
                      (if ms >= 0 then " -max-msecs " ^ string_of_int ms
                       else "") ^
                      (if max_solutions > 1 then " -solve-all" else "") ^
                      " -max-solutions " ^ string_of_int max_solutions ^
                      (if max_threads > 0 then
                         " -max-threads " ^ string_of_int max_threads
                       else
                         "") ^
                      " < " ^ File.shell_path in_path ^
                      " > " ^ File.shell_path out_path ^
                      " 2> " ^ File.shell_path err_path)
              val (io_error, (ps, nontriv_js)) =
                read_output_file new_kodkodi out_path
                ||> apfst (map (apfst reindex)) ||> apsnd (map reindex)
              val js = triv_js @ nontriv_js
              val first_error =
                (File.fold_lines (fn line => fn "" => line | s => s) err_path ""
                 handle IO.Io _ => "" | OS.SysErr _ => "")
                |> perhaps (try (unsuffix "\r"))
                |> perhaps (try (unsuffix "."))
                |> perhaps (try (unprefix "Solve error: "))
                |> perhaps (try (unprefix "Error: "))
              fun has_error s =
                first_error |> Substring.full |> Substring.position s |> snd
                            |> Substring.isEmpty |> not
            in
              if null ps then
                if code = 2 then
                  TimedOut js
                else if code = 0 then
                  Normal ([], js, first_error)
                else if code = 127 then
                  JavaNotFound
                else if has_error "UnsupportedClassVersionError" then
                  JavaTooOld
                else if has_error "NoClassDefFoundError" then
                  KodkodiNotInstalled
                else if first_error <> "" then
                  Error (first_error, js)
                else if io_error then
                  Error ("I/O error", js)
                else
                  Error ("Unknown error", js)
              else
                Normal (ps, js, first_error)
            end
        in remove_temporary_files (); outcome end
      end
  end

val cached_outcome =
  Synchronized.var "Kodkod.cached_outcome"
                   (NONE : ((int * problem list) * outcome) option)

fun solve_any_problem debug overlord deadline max_threads max_solutions
                      problems =
  let
    fun do_solve () =
      uncached_solve_any_problem overlord deadline max_threads max_solutions
                                 problems
  in
    if debug orelse overlord then
      do_solve ()
    else
      case AList.lookup (fn ((max1, ps1), (max2, ps2)) =>
                            max1 = max2 andalso length ps1 = length ps2 andalso
                            forall problems_equivalent (ps1 ~~ ps2))
                        (the_list (Synchronized.value cached_outcome))
                        (max_solutions, problems) of
        SOME outcome => outcome
      | NONE =>
        let val outcome = do_solve () in
          (case outcome of
             Normal (_, _, "") =>
             Synchronized.change cached_outcome
                                 (K (SOME ((max_solutions, problems), outcome)))
           | _ => ());
          outcome
        end
  end

end;
