(*  Title:      HOL/Tools/Nitpick/nitpick_nut.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Nitpick underlying terms (nuts).
*)

signature NITPICK_NUT =
sig
  type styp = Nitpick_Util.styp
  type hol_context = Nitpick_HOL.hol_context
  type scope = Nitpick_Scope.scope
  type name_pool = Nitpick_Peephole.name_pool
  type rep = Nitpick_Rep.rep

  datatype cst =
    False |
    True |
    Iden |
    Num of int |
    Unknown |
    Unrep |
    Suc |
    Add |
    Subtract |
    Multiply |
    Divide |
    Gcd |
    Lcm |
    Fracs |
    NormFrac |
    NatToInt |
    IntToNat

  datatype op1 =
    Not |
    Finite |
    Converse |
    Closure |
    SingletonSet |
    IsUnknown |
    SafeThe |
    First |
    Second |
    Cast

  datatype op2 =
    All |
    Exist |
    Or |
    And |
    Less |
    Subset |
    DefEq |
    Eq |
    Triad |
    Composition |
    Apply |
    Lambda

  datatype op3 =
    Let |
    If

  datatype nut =
    Cst of cst * typ * rep |
    Op1 of op1 * typ * rep * nut |
    Op2 of op2 * typ * rep * nut * nut |
    Op3 of op3 * typ * rep * nut * nut * nut |
    Tuple of typ * rep * nut list |
    Construct of nut list * typ * rep * nut list |
    BoundName of int * typ * rep * string |
    FreeName of string * typ * rep |
    ConstName of string * typ * rep |
    BoundRel of Kodkod.n_ary_index * typ * rep * string |
    FreeRel of Kodkod.n_ary_index * typ * rep * string |
    RelReg of int * typ * rep |
    FormulaReg of int * typ * rep

  structure NameTable : TABLE

  exception NUT of string * nut list

  val string_for_nut : Proof.context -> nut -> string
  val inline_nut : nut -> bool
  val type_of : nut -> typ
  val rep_of : nut -> rep
  val nickname_of : nut -> string
  val is_skolem_name : nut -> bool
  val is_eval_name : nut -> bool
  val is_Cst : cst -> nut -> bool
  val fold_nut : (nut -> 'a -> 'a) -> nut -> 'a -> 'a
  val map_nut : (nut -> nut) -> nut -> nut
  val untuple : (nut -> 'a) -> nut -> 'a list
  val add_free_and_const_names :
    nut -> nut list * nut list -> nut list * nut list
  val name_ord : (nut * nut) -> order
  val the_name : 'a NameTable.table -> nut -> 'a
  val the_rel : nut NameTable.table -> nut -> Kodkod.n_ary_index
  val nut_from_term : hol_context -> op2 -> term -> nut
  val is_fully_representable_set : nut -> bool
  val choose_reps_for_free_vars :
    scope -> styp list -> nut list -> rep NameTable.table
    -> nut list * rep NameTable.table
  val choose_reps_for_consts :
    scope -> bool -> nut list -> rep NameTable.table
    -> nut list * rep NameTable.table
  val choose_reps_for_all_sels :
    scope -> rep NameTable.table -> nut list * rep NameTable.table
  val choose_reps_in_nut :
    scope -> bool -> rep NameTable.table -> bool -> nut -> nut
  val rename_free_vars :
    nut list -> name_pool -> nut NameTable.table
    -> nut list * name_pool * nut NameTable.table
  val rename_vars_in_nut : name_pool -> nut NameTable.table -> nut -> nut
end;

structure Nitpick_Nut : NITPICK_NUT =
struct

open Nitpick_Util
open Nitpick_HOL
open Nitpick_Scope
open Nitpick_Peephole
open Nitpick_Rep

structure KK = Kodkod

datatype cst =
  False |
  True |
  Iden |
  Num of int |
  Unknown |
  Unrep |
  Suc |
  Add |
  Subtract |
  Multiply |
  Divide |
  Gcd |
  Lcm |
  Fracs |
  NormFrac |
  NatToInt |
  IntToNat

datatype op1 =
  Not |
  Finite |
  Converse |
  Closure |
  SingletonSet |
  IsUnknown |
  SafeThe |
  First |
  Second |
  Cast

datatype op2 =
  All |
  Exist |
  Or |
  And |
  Less |
  Subset |
  DefEq |
  Eq |
  Triad |
  Composition |
  Apply |
  Lambda

datatype op3 =
  Let |
  If

datatype nut =
  Cst of cst * typ * rep |
  Op1 of op1 * typ * rep * nut |
  Op2 of op2 * typ * rep * nut * nut |
  Op3 of op3 * typ * rep * nut * nut * nut |
  Tuple of typ * rep * nut list |
  Construct of nut list * typ * rep * nut list |
  BoundName of int * typ * rep * string |
  FreeName of string * typ * rep |
  ConstName of string * typ * rep |
  BoundRel of KK.n_ary_index * typ * rep * string |
  FreeRel of KK.n_ary_index * typ * rep * string |
  RelReg of int * typ * rep |
  FormulaReg of int * typ * rep

exception NUT of string * nut list

fun string_for_cst False = "False"
  | string_for_cst True = "True"
  | string_for_cst Iden = "Iden"
  | string_for_cst (Num j) = "Num " ^ signed_string_of_int j
  | string_for_cst Unknown = "Unknown"
  | string_for_cst Unrep = "Unrep"
  | string_for_cst Suc = "Suc"
  | string_for_cst Add = "Add"
  | string_for_cst Subtract = "Subtract"
  | string_for_cst Multiply = "Multiply"
  | string_for_cst Divide = "Divide"
  | string_for_cst Gcd = "Gcd"
  | string_for_cst Lcm = "Lcm"
  | string_for_cst Fracs = "Fracs"
  | string_for_cst NormFrac = "NormFrac"
  | string_for_cst NatToInt = "NatToInt"
  | string_for_cst IntToNat = "IntToNat"

fun string_for_op1 Not = "Not"
  | string_for_op1 Finite = "Finite"
  | string_for_op1 Converse = "Converse"
  | string_for_op1 Closure = "Closure"
  | string_for_op1 SingletonSet = "SingletonSet"
  | string_for_op1 IsUnknown = "IsUnknown"
  | string_for_op1 SafeThe = "SafeThe"
  | string_for_op1 First = "First"
  | string_for_op1 Second = "Second"
  | string_for_op1 Cast = "Cast"

fun string_for_op2 All = "All"
  | string_for_op2 Exist = "Exist"
  | string_for_op2 Or = "Or"
  | string_for_op2 And = "And"
  | string_for_op2 Less = "Less"
  | string_for_op2 Subset = "Subset"
  | string_for_op2 DefEq = "DefEq"
  | string_for_op2 Eq = "Eq"
  | string_for_op2 Triad = "Triad"
  | string_for_op2 Composition = "Composition"
  | string_for_op2 Apply = "Apply"
  | string_for_op2 Lambda = "Lambda"

fun string_for_op3 Let = "Let"
  | string_for_op3 If = "If"

fun basic_string_for_nut indent ctxt u =
  let
    val sub = basic_string_for_nut (indent + 1) ctxt
  in
    (if indent = 0 then "" else "\n" ^ implode (replicate (2 * indent) " ")) ^
    "(" ^
    (case u of
       Cst (c, T, R) =>
       "Cst " ^ string_for_cst c ^ " " ^ Syntax.string_of_typ ctxt T ^ " " ^
       string_for_rep R
     | Op1 (oper, T, R, u1) =>
       "Op1 " ^ string_for_op1 oper ^ " " ^ Syntax.string_of_typ ctxt T ^ " " ^
       string_for_rep R ^ " " ^ sub u1
     | Op2 (oper, T, R, u1, u2) =>
       "Op2 " ^ string_for_op2 oper ^ " " ^ Syntax.string_of_typ ctxt T ^ " " ^
       string_for_rep R ^ " " ^ sub u1 ^ " " ^ sub u2
     | Op3 (oper, T, R, u1, u2, u3) =>
       "Op3 " ^ string_for_op3 oper ^ " " ^ Syntax.string_of_typ ctxt T ^ " " ^
       string_for_rep R ^ " " ^ sub u1 ^ " " ^ sub u2 ^ " " ^ sub u3
     | Tuple (T, R, us) =>
       "Tuple " ^ Syntax.string_of_typ ctxt T ^ " " ^ string_for_rep R ^
       implode (map sub us)
     | Construct (us', T, R, us) =>
       "Construct " ^ implode (map sub us') ^ " " ^
       Syntax.string_of_typ ctxt T ^ " " ^ string_for_rep R ^ " " ^
       implode (map sub us)
     | BoundName (j, T, R, nick) =>
       "BoundName " ^ signed_string_of_int j ^ " " ^
       Syntax.string_of_typ ctxt T ^ " " ^ string_for_rep R ^ " " ^ nick
     | FreeName (s, T, R) =>
       "FreeName " ^ s ^ " " ^ Syntax.string_of_typ ctxt T ^ " " ^
       string_for_rep R
     | ConstName (s, T, R) =>
       "ConstName " ^ s ^ " " ^ Syntax.string_of_typ ctxt T ^ " " ^
       string_for_rep R
     | BoundRel ((n, j), T, R, nick) =>
       "BoundRel " ^ string_of_int n ^ "." ^ signed_string_of_int j ^ " " ^
       Syntax.string_of_typ ctxt T ^ " " ^ string_for_rep R ^ " " ^ nick
     | FreeRel ((n, j), T, R, nick) =>
       "FreeRel " ^ string_of_int n ^ "." ^ signed_string_of_int j ^ " " ^
       Syntax.string_of_typ ctxt T ^ " " ^ string_for_rep R ^ " " ^ nick
     | RelReg (j, T, R) =>
       "RelReg " ^ signed_string_of_int j ^ " " ^ Syntax.string_of_typ ctxt T ^
       " " ^ string_for_rep R
     | FormulaReg (j, T, R) =>
       "FormulaReg " ^ signed_string_of_int j ^ " " ^
       Syntax.string_of_typ ctxt T ^ " " ^ string_for_rep R) ^
    ")"
  end
val string_for_nut = basic_string_for_nut 0

fun inline_nut (Op1 _) = false
  | inline_nut (Op2 _) = false
  | inline_nut (Op3 _) = false
  | inline_nut (Tuple (_, _, us)) = forall inline_nut us
  | inline_nut _ = true

fun type_of (Cst (_, T, _)) = T
  | type_of (Op1 (_, T, _, _)) = T
  | type_of (Op2 (_, T, _, _, _)) = T
  | type_of (Op3 (_, T, _, _, _, _)) = T
  | type_of (Tuple (T, _, _)) = T
  | type_of (Construct (_, T, _, _)) = T
  | type_of (BoundName (_, T, _, _)) = T
  | type_of (FreeName (_, T, _)) = T
  | type_of (ConstName (_, T, _)) = T
  | type_of (BoundRel (_, T, _, _)) = T
  | type_of (FreeRel (_, T, _, _)) = T
  | type_of (RelReg (_, T, _)) = T
  | type_of (FormulaReg (_, T, _)) = T

fun rep_of (Cst (_, _, R)) = R
  | rep_of (Op1 (_, _, R, _)) = R
  | rep_of (Op2 (_, _, R, _, _)) = R
  | rep_of (Op3 (_, _, R, _, _, _)) = R
  | rep_of (Tuple (_, R, _)) = R
  | rep_of (Construct (_, _, R, _)) = R
  | rep_of (BoundName (_, _, R, _)) = R
  | rep_of (FreeName (_, _, R)) = R
  | rep_of (ConstName (_, _, R)) = R
  | rep_of (BoundRel (_, _, R, _)) = R
  | rep_of (FreeRel (_, _, R, _)) = R
  | rep_of (RelReg (_, _, R)) = R
  | rep_of (FormulaReg (_, _, R)) = R

fun nickname_of (BoundName (_, _, _, nick)) = nick
  | nickname_of (FreeName (s, _, _)) = s
  | nickname_of (ConstName (s, _, _)) = s
  | nickname_of (BoundRel (_, _, _, nick)) = nick
  | nickname_of (FreeRel (_, _, _, nick)) = nick
  | nickname_of u = raise NUT ("Nitpick_Nut.nickname_of", [u])

fun is_skolem_name u =
  space_explode name_sep (nickname_of u)
  |> exists (String.isPrefix skolem_prefix)
  handle NUT ("Nitpick_Nut.nickname_of", _) => false
fun is_eval_name u =
  String.isPrefix eval_prefix (nickname_of u)
  handle NUT ("Nitpick_Nut.nickname_of", _) => false
fun is_Cst cst (Cst (cst', _, _)) = (cst = cst')
  | is_Cst _ _ = false

fun fold_nut f u =
  case u of
    Op1 (_, _, _, u1) => fold_nut f u1
  | Op2 (_, _, _, u1, u2) => fold_nut f u1 #> fold_nut f u2
  | Op3 (_, _, _, u1, u2, u3) => fold_nut f u1 #> fold_nut f u2 #> fold_nut f u3
  | Tuple (_, _, us) => fold (fold_nut f) us
  | Construct (us', _, _, us) => fold (fold_nut f) us #> fold (fold_nut f) us'
  | _ => f u
fun map_nut f u =
  case u of
    Op1 (oper, T, R, u1) => Op1 (oper, T, R, map_nut f u1)
  | Op2 (oper, T, R, u1, u2) => Op2 (oper, T, R, map_nut f u1, map_nut f u2)
  | Op3 (oper, T, R, u1, u2, u3) =>
    Op3 (oper, T, R, map_nut f u1, map_nut f u2, map_nut f u3)
  | Tuple (T, R, us) => Tuple (T, R, map (map_nut f) us)
  | Construct (us', T, R, us) =>
    Construct (map (map_nut f) us', T, R, map (map_nut f) us)
  | _ => f u

fun name_ord (BoundName (j1, _, _, _), BoundName (j2, _, _, _)) =
    int_ord (j1, j2)
  | name_ord (BoundName _, _) = LESS
  | name_ord (_, BoundName _) = GREATER
  | name_ord (FreeName (s1, T1, _), FreeName (s2, T2, _)) =
    (case fast_string_ord (s1, s2) of
       EQUAL => Term_Ord.typ_ord (T1, T2)
     | ord => ord)
  | name_ord (FreeName _, _) = LESS
  | name_ord (_, FreeName _) = GREATER
  | name_ord (ConstName (s1, T1, _), ConstName (s2, T2, _)) =
    (case fast_string_ord (s1, s2) of
       EQUAL => Term_Ord.typ_ord (T1, T2)
     | ord => ord)
  | name_ord (u1, u2) = raise NUT ("Nitpick_Nut.name_ord", [u1, u2])

fun num_occurrences_in_nut needle_u stack_u =
  fold_nut (fn u => if u = needle_u then Integer.add 1 else I) stack_u 0
val is_subnut_of = not_equal 0 oo num_occurrences_in_nut

fun substitute_in_nut needle_u needle_u' =
  map_nut (fn u => if u = needle_u then needle_u' else u)

val add_free_and_const_names =
  fold_nut (fn u => case u of
                      FreeName _ => apfst (insert (op =) u)
                    | ConstName _ => apsnd (insert (op =) u)
                    | _ => I)

fun modify_name_rep (BoundName (j, T, _, nick)) R = BoundName (j, T, R, nick)
  | modify_name_rep (FreeName (s, T, _)) R = FreeName (s, T, R)
  | modify_name_rep (ConstName (s, T, _)) R = ConstName (s, T, R)
  | modify_name_rep u _ = raise NUT ("Nitpick_Nut.modify_name_rep", [u])

structure NameTable = Table(type key = nut val ord = name_ord)

fun the_name table name =
  case NameTable.lookup table name of
    SOME u => u
  | NONE => raise NUT ("Nitpick_Nut.the_name", [name])
fun the_rel table name =
  case the_name table name of
    FreeRel (x, _, _, _) => x
  | u => raise NUT ("Nitpick_Nut.the_rel", [u])

fun mk_fst (_, Const (@{const_name Pair}, T) $ t1 $ _) = (domain_type T, t1)
  | mk_fst (T, t) =
    let val res_T = fst (HOLogic.dest_prodT T) in
      (res_T, Const (@{const_name fst}, T --> res_T) $ t)
    end
fun mk_snd (_, Const (@{const_name Pair}, T) $ _ $ t2) =
    (domain_type (range_type T), t2)
  | mk_snd (T, t) =
    let val res_T = snd (HOLogic.dest_prodT T) in
      (res_T, Const (@{const_name snd}, T --> res_T) $ t)
    end
fun factorize (z as (Type (@{type_name prod}, _), _)) =
    maps factorize [mk_fst z, mk_snd z]
  | factorize z = [z]

fun nut_from_term (hol_ctxt as {thy, ctxt, stds, ...}) eq =
  let
    fun aux eq ss Ts t =
      let
        val sub = aux Eq ss Ts
        val sub' = aux eq ss Ts
        fun sub_abs s T = aux eq (s :: ss) (T :: Ts)
        fun sub_equals T t1 t2 =
          let
            val (binder_Ts, body_T) = strip_type (domain_type T)
            val n = length binder_Ts
          in
            if eq = Eq andalso n > 0 then
              let
                val t1 = incr_boundvars n t1
                val t2 = incr_boundvars n t2
                val xs = map Bound (n - 1 downto 0)
                val equation = Const (@{const_name HOL.eq},
                                      body_T --> body_T --> bool_T)
                                   $ betapplys (t1, xs) $ betapplys (t2, xs)
                val t =
                  fold_rev (fn T => fn (t, j) =>
                               (Const (@{const_name All}, T --> bool_T)
                                $ Abs ("x" ^ nat_subscript j, T, t), j - 1))
                           binder_Ts (equation, n) |> fst
              in sub' t end
            else
              Op2 (eq, bool_T, Any, aux Eq ss Ts t1, aux Eq ss Ts t2)
          end
        fun do_quantifier quant s T t1 =
          let
            val bound_u = BoundName (length Ts, T, Any, s)
            val body_u = sub_abs s T t1
          in Op2 (quant, bool_T, Any, bound_u, body_u) end
        fun do_apply t0 ts =
          let
            val (ts', t2) = split_last ts
            val t1 = list_comb (t0, ts')
            val T1 = fastype_of1 (Ts, t1)
          in Op2 (Apply, pseudo_range_type T1, Any, sub t1, sub t2) end
        fun do_construct (x as (_, T)) ts =
          case num_binder_types T - length ts of
            0 => Construct (map ((fn (s', T') => ConstName (s', T', Any))
                                  o nth_sel_for_constr x)
                                (~1 upto num_sels_for_constr_type T - 1),
                            body_type T, Any,
                            ts |> map (`(curry fastype_of1 Ts))
                               |> maps factorize |> map (sub o snd))
          | k => sub (eta_expand Ts t k)
      in
        case strip_comb t of
          (Const (@{const_name all}, _), [Abs (s, T, t1)]) =>
          do_quantifier All s T t1
        | (t0 as Const (@{const_name all}, _), [t1]) =>
          sub' (t0 $ eta_expand Ts t1 1)
        | (Const (@{const_name "=="}, T), [t1, t2]) => sub_equals T t1 t2
        | (Const (@{const_name "==>"}, _), [t1, t2]) =>
          Op2 (Or, prop_T, Any, Op1 (Not, prop_T, Any, sub t1), sub' t2)
        | (Const (@{const_name Pure.conjunction}, _), [t1, t2]) =>
          Op2 (And, prop_T, Any, sub' t1, sub' t2)
        | (Const (@{const_name Trueprop}, _), [t1]) => sub' t1
        | (Const (@{const_name Not}, _), [t1]) =>
          (case sub t1 of
             Op1 (Not, _, _, u11) => u11
           | u1 => Op1 (Not, bool_T, Any, u1))
        | (Const (@{const_name False}, T), []) => Cst (False, T, Any)
        | (Const (@{const_name True}, T), []) => Cst (True, T, Any)
        | (Const (@{const_name All}, _), [Abs (s, T, t1)]) =>
          do_quantifier All s T t1
        | (t0 as Const (@{const_name All}, _), [t1]) =>
          sub' (t0 $ eta_expand Ts t1 1)
        | (Const (@{const_name Ex}, _), [Abs (s, T, t1)]) =>
          do_quantifier Exist s T t1
        | (t0 as Const (@{const_name Ex}, _), [t1]) =>
          sub' (t0 $ eta_expand Ts t1 1)
        | (Const (@{const_name HOL.eq}, T), [t1]) =>
          Op1 (SingletonSet, range_type T, Any, sub t1)
        | (Const (@{const_name HOL.eq}, T), [t1, t2]) => sub_equals T t1 t2
        | (Const (@{const_name HOL.conj}, _), [t1, t2]) =>
          Op2 (And, bool_T, Any, sub' t1, sub' t2)
        | (Const (@{const_name HOL.disj}, _), [t1, t2]) =>
          Op2 (Or, bool_T, Any, sub t1, sub t2)
        | (Const (@{const_name HOL.implies}, _), [t1, t2]) =>
          Op2 (Or, bool_T, Any, Op1 (Not, bool_T, Any, sub t1), sub' t2)
        | (Const (@{const_name If}, T), [t1, t2, t3]) =>
          Op3 (If, nth_range_type 3 T, Any, sub t1, sub t2, sub t3)
        | (Const (@{const_name Let}, T), [t1, Abs (s, T', t2)]) =>
          Op3 (Let, nth_range_type 2 T, Any, BoundName (length Ts, T', Any, s),
               sub t1, sub_abs s T' t2)
        | (t0 as Const (@{const_name Let}, _), [t1, t2]) =>
          sub (t0 $ t1 $ eta_expand Ts t2 1)
        | (Const (@{const_name Pair}, T), [t1, t2]) =>
          Tuple (nth_range_type 2 T, Any, map sub [t1, t2])
        | (Const (@{const_name fst}, T), [t1]) =>
          Op1 (First, range_type T, Any, sub t1)
        | (Const (@{const_name snd}, T), [t1]) =>
          Op1 (Second, range_type T, Any, sub t1)
        | (Const (@{const_name Set.member}, _), [t1, t2]) => do_apply t2 [t1]
        | (Const (@{const_name Collect}, _), [t1]) => sub t1
        | (Const (@{const_name Id}, T), []) => Cst (Iden, T, Any)
        | (Const (@{const_name converse}, T), [t1]) =>
          Op1 (Converse, range_type T, Any, sub t1)
        | (Const (@{const_name trancl}, T), [t1]) =>
          Op1 (Closure, range_type T, Any, sub t1)
        | (Const (@{const_name rel_comp}, T), [t1, t2]) =>
          Op2 (Composition, nth_range_type 2 T, Any, sub t1, sub t2)
        | (Const (x as (s as @{const_name Suc}, T)), []) =>
          if is_built_in_const thy stds x then Cst (Suc, T, Any)
          else if is_constr ctxt stds x then do_construct x []
          else ConstName (s, T, Any)
        | (Const (@{const_name finite}, T), [t1]) =>
          (if is_finite_type hol_ctxt (domain_type T) then
             Cst (True, bool_T, Any)
           else case t1 of
             Const (@{const_name top}, _) => Cst (False, bool_T, Any)
           | _ => Op1 (Finite, bool_T, Any, sub t1))
        | (Const (@{const_name nat}, T), []) => Cst (IntToNat, T, Any)
        | (Const (x as (s as @{const_name zero_class.zero}, T)), []) =>
          if is_built_in_const thy stds x then Cst (Num 0, T, Any)
          else if is_constr ctxt stds x then do_construct x []
          else ConstName (s, T, Any)
        | (Const (x as (s as @{const_name one_class.one}, T)), []) =>
          if is_built_in_const thy stds x then Cst (Num 1, T, Any)
          else ConstName (s, T, Any)
        | (Const (x as (s as @{const_name plus_class.plus}, T)), []) =>
          if is_built_in_const thy stds x then Cst (Add, T, Any)
          else ConstName (s, T, Any)
        | (Const (x as (s as @{const_name minus_class.minus}, T)), []) =>
          if is_built_in_const thy stds x then Cst (Subtract, T, Any)
          else ConstName (s, T, Any)
        | (Const (x as (s as @{const_name times_class.times}, T)), []) =>
          if is_built_in_const thy stds x then Cst (Multiply, T, Any)
          else ConstName (s, T, Any)
        | (Const (x as (s as @{const_name div_class.div}, T)), []) =>
          if is_built_in_const thy stds x then Cst (Divide, T, Any)
          else ConstName (s, T, Any)
        | (t0 as Const (x as (@{const_name ord_class.less}, _)),
           ts as [t1, t2]) =>
          if is_built_in_const thy stds x then
            Op2 (Less, bool_T, Any, sub t1, sub t2)
          else
            do_apply t0 ts
        | (t0 as Const (x as (@{const_name ord_class.less_eq}, T)),
           ts as [t1, t2]) =>
          if is_set_like_type (domain_type T) then
            Op2 (Subset, bool_T, Any, sub t1, sub t2)
          else if is_built_in_const thy stds x then
            (* FIXME: find out if this case is necessary *)
            Op1 (Not, bool_T, Any, Op2 (Less, bool_T, Any, sub t2, sub t1))
          else
            do_apply t0 ts
        | (Const (@{const_name nat_gcd}, T), []) => Cst (Gcd, T, Any)
        | (Const (@{const_name nat_lcm}, T), []) => Cst (Lcm, T, Any)
        | (Const (x as (s as @{const_name uminus_class.uminus}, T)), []) =>
          if is_built_in_const thy stds x then
            let val num_T = domain_type T in
              Op2 (Apply, num_T --> num_T, Any,
                   Cst (Subtract, num_T --> num_T --> num_T, Any),
                   Cst (Num 0, num_T, Any))
            end
          else
            ConstName (s, T, Any)
        | (Const (@{const_name unknown}, T), []) => Cst (Unknown, T, Any)
        | (Const (@{const_name is_unknown}, _), [t1]) =>
          Op1 (IsUnknown, bool_T, Any, sub t1)
        | (Const (@{const_name safe_The},
                  Type (@{type_name fun}, [_, T2])), [t1]) =>
          Op1 (SafeThe, T2, Any, sub t1)
        | (Const (@{const_name Frac}, T), []) => Cst (Fracs, T, Any)
        | (Const (@{const_name norm_frac}, T), []) => Cst (NormFrac, T, Any)
        | (Const (@{const_name of_nat}, T as @{typ "nat => int"}), []) =>
          Cst (NatToInt, T, Any)
        | (Const (@{const_name of_nat},
                  T as @{typ "unsigned_bit word => signed_bit word"}), []) =>
          Cst (NatToInt, T, Any)
        | (t0 as Const (x as (s, T)), ts) =>
          if is_constr ctxt stds x then
            do_construct x ts
          else if String.isPrefix numeral_prefix s then
            Cst (Num (the (Int.fromString (unprefix numeral_prefix s))), T, Any)
          else
            (case arity_of_built_in_const thy stds x of
               SOME n =>
               (case n - length ts of
                  0 => raise TERM ("Nitpick_Nut.nut_from_term.aux", [t])
                | k => if k > 0 then sub (eta_expand Ts t k)
                       else do_apply t0 ts)
             | NONE => if null ts then ConstName (s, T, Any)
                       else do_apply t0 ts)
        | (Free (s, T), []) => FreeName (s, T, Any)
        | (Var _, []) => raise TERM ("Nitpick_Nut.nut_from_term.aux", [t])
        | (Bound j, []) =>
          BoundName (length Ts - j - 1, nth Ts j, Any, nth ss j)
        | (Abs (s, T, t1), []) =>
          Op2 (Lambda, T --> fastype_of1 (T :: Ts, t1), Any,
               BoundName (length Ts, T, Any, s), sub_abs s T t1)
        | (t0, ts) => do_apply t0 ts
      end
  in aux eq [] [] end

fun is_fully_representable_set u =
  not (is_opt_rep (rep_of u)) andalso
  case u of
    FreeName _ => true
  | Op1 (SingletonSet, _, _, _) => true
  | Op1 (Converse, _, _, u1) => is_fully_representable_set u1
  | Op2 (Lambda, _, _, _, Cst (False, _, _)) => true
  | Op2 (oper, _, _, u1, _) =>
    if oper = Apply then
      case u1 of
        ConstName (s, _, _) =>
        is_sel_like_and_no_discr s orelse s = @{const_name set}
      | _ => false
    else
      false
  | _ => false

fun rep_for_abs_fun scope T =
  let val (R1, R2) = best_non_opt_symmetric_reps_for_fun_type scope T in
    Func (R1, (card_of_rep R1 <> card_of_rep R2 ? Opt) R2)
  end

fun choose_rep_for_free_var scope pseudo_frees v (vs, table) =
  let
    val R = (if exists (curry (op =) (nickname_of v) o fst) pseudo_frees then
               best_opt_set_rep_for_type
             else
               best_non_opt_set_rep_for_type) scope (type_of v)
    val v = modify_name_rep v R
  in (v :: vs, NameTable.update (v, R) table) end
fun choose_rep_for_const (scope as {hol_ctxt = {ctxt, ...}, ...}) total_consts v
                         (vs, table) =
  let
    val x as (s, T) = (nickname_of v, type_of v)
    val R = (if is_abs_fun ctxt x then
               rep_for_abs_fun
             else if is_rep_fun ctxt x then
               Func oo best_non_opt_symmetric_reps_for_fun_type
             else if total_consts orelse is_skolem_name v orelse
                     member (op =) [@{const_name bisim},
                                    @{const_name bisim_iterator_max}]
                            (original_name s) then
               best_non_opt_set_rep_for_type
             else if member (op =) [@{const_name set}, @{const_name distinct},
                                    @{const_name ord_class.less},
                                    @{const_name ord_class.less_eq}]
                            (original_name s) then
               best_set_rep_for_type
             else
               best_opt_set_rep_for_type) scope T
    val v = modify_name_rep v R
  in (v :: vs, NameTable.update (v, R) table) end

fun choose_reps_for_free_vars scope pseudo_frees vs table =
  fold (choose_rep_for_free_var scope pseudo_frees) vs ([], table)
fun choose_reps_for_consts scope total_consts vs table =
  fold (choose_rep_for_const scope total_consts) vs ([], table)

fun choose_rep_for_nth_sel_for_constr (scope as {hol_ctxt, binarize, ...})
                                      (x as (_, T)) n (vs, table) =
  let
    val (s', T') = binarized_and_boxed_nth_sel_for_constr hol_ctxt binarize x n
    val R' = if n = ~1 orelse is_word_type (body_type T) orelse
                (is_fun_type (range_type T') andalso
                 is_boolean_type (body_type T')) then
               best_non_opt_set_rep_for_type scope T'
             else
               best_opt_set_rep_for_type scope T' |> unopt_rep
    val v = ConstName (s', T', R')
  in (v :: vs, NameTable.update (v, R') table) end
fun choose_rep_for_sels_for_constr scope (x as (_, T)) =
  fold_rev (choose_rep_for_nth_sel_for_constr scope x)
           (~1 upto num_sels_for_constr_type T - 1)
fun choose_rep_for_sels_of_datatype _ ({deep = false, ...} : datatype_spec) = I
  | choose_rep_for_sels_of_datatype scope {constrs, ...} =
    fold_rev (choose_rep_for_sels_for_constr scope o #const) constrs
fun choose_reps_for_all_sels (scope as {datatypes, ...}) =
  fold (choose_rep_for_sels_of_datatype scope) datatypes o pair []

val min_univ_card = 2

fun choose_rep_for_bound_var scope v =
  let
    val R = best_one_rep_for_type scope (type_of v)
    val arity = arity_of_rep R
  in
    if arity > KK.max_arity min_univ_card then
      raise TOO_LARGE ("Nitpick_Nut.choose_rep_for_bound_var",
                       "arity " ^ string_of_int arity ^ " of bound variable \
                       \too large")
    else
      NameTable.update (v, R)
  end

(* A nut is said to be constructive if whenever it evaluates to unknown in our
   three-valued logic, it would evaluate to an unrepresentable value ("Unrep")
   according to the HOL semantics. For example, "Suc n" is constructive if "n"
   is representable or "Unrep", because unknown implies "Unrep". *)
fun is_constructive u =
  is_Cst Unrep u orelse
  (not (is_fun_type (type_of u)) andalso not (is_opt_rep (rep_of u))) orelse
  case u of
    Cst (Num _, _, _) => true
  | Cst (cst, T, _) => body_type T = nat_T andalso (cst = Suc orelse cst = Add)
  | Op2 (Apply, _, _, u1, u2) => forall is_constructive [u1, u2]
  | Op3 (If, _, _, u1, u2, u3) =>
    not (is_opt_rep (rep_of u1)) andalso forall is_constructive [u2, u3]
  | Tuple (_, _, us) => forall is_constructive us
  | Construct (_, _, _, us) => forall is_constructive us
  | _ => false

fun unknown_boolean T R =
  Cst (case R of Formula Pos => False | Formula Neg => True | _ => Unknown,
       T, R)

fun s_op1 oper T R u1 =
  ((if oper = Not then
      if is_Cst True u1 then Cst (False, T, R)
      else if is_Cst False u1 then Cst (True, T, R)
      else raise SAME ()
    else
      raise SAME ())
   handle SAME () => Op1 (oper, T, R, u1))
fun s_op2 oper T R u1 u2 =
  ((case oper of
      All => if is_subnut_of u1 u2 then Op2 (All, T, R, u1, u2) else u2
    | Exist => if is_subnut_of u1 u2 then Op2 (Exist, T, R, u1, u2) else u2
    | Or =>
      if exists (is_Cst True) [u1, u2] then Cst (True, T, unopt_rep R)
      else if is_Cst False u1 then u2
      else if is_Cst False u2 then u1
      else raise SAME ()
    | And =>
      if exists (is_Cst False) [u1, u2] then Cst (False, T, unopt_rep R)
      else if is_Cst True u1 then u2
      else if is_Cst True u2 then u1
      else raise SAME ()
    | Eq =>
      (case pairself (is_Cst Unrep) (u1, u2) of
         (true, true) => unknown_boolean T R
       | (false, false) => raise SAME ()
       | _ => if forall (is_opt_rep o rep_of) [u1, u2] then raise SAME ()
              else Cst (False, T, Formula Neut))
    | Triad =>
      if is_Cst True u1 then u1
      else if is_Cst False u2 then u2
      else raise SAME ()
    | Apply =>
      if is_Cst Unrep u1 then
        Cst (Unrep, T, R)
      else if is_Cst Unrep u2 then
        if is_boolean_type T then
          if is_fully_representable_set u1 then Cst (False, T, Formula Neut)
          else unknown_boolean T R
        else if is_constructive u1 then
          Cst (Unrep, T, R)
        else case u1 of
          Op2 (Apply, _, _, ConstName (@{const_name List.append}, _, _), _) =>
          Cst (Unrep, T, R)
        | _ => raise SAME ()
      else
        raise SAME ()
    | _ => raise SAME ())
   handle SAME () => Op2 (oper, T, R, u1, u2))
fun s_op3 oper T R u1 u2 u3 =
  ((case oper of
      Let =>
      if inline_nut u2 orelse num_occurrences_in_nut u1 u3 < 2 then
        substitute_in_nut u1 u2 u3
      else
        raise SAME ()
    | _ => raise SAME ())
   handle SAME () => Op3 (oper, T, R, u1, u2, u3))
fun s_tuple T R us =
  if exists (is_Cst Unrep) us then Cst (Unrep, T, R) else Tuple (T, R, us)

fun untuple f (Tuple (_, _, us)) = maps (untuple f) us
  | untuple f u = [f u]

fun choose_reps_in_nut (scope as {card_assigns, bits, datatypes, ofs, ...})
                       unsound table def =
  let
    val bool_atom_R = Atom (2, offset_of_type ofs bool_T)
    fun bool_rep polar opt =
      if polar = Neut andalso opt then Opt bool_atom_R else Formula polar
    fun triad u1 u2 = s_op2 Triad (type_of u1) (Opt bool_atom_R) u1 u2
    fun triad_fn f = triad (f Pos) (f Neg)
    fun unrepify_nut_in_nut table def polar needle_u =
      let val needle_T = type_of needle_u in
        substitute_in_nut needle_u (Cst (if is_fun_type needle_T then Unknown
                                         else Unrep, needle_T, Any))
        #> aux table def polar
      end
    and aux table def polar u =
      let
        val gsub = aux table
        val sub = gsub false Neut
      in
        case u of
          Cst (False, T, _) => Cst (False, T, Formula Neut)
        | Cst (True, T, _) => Cst (True, T, Formula Neut)
        | Cst (Num j, T, _) =>
          if is_word_type T then
            Cst (if is_twos_complement_representable bits j then Num j
                 else Unrep, T, best_opt_set_rep_for_type scope T)
          else
             let
               val (k, j0) = spec_of_type scope T
               val ok = (if T = int_T then atom_for_int (k, j0) j <> ~1
                         else j < k)
             in
               if ok then Cst (Num j, T, Atom (k, j0))
               else Cst (Unrep, T, Opt (Atom (k, j0)))
             end
        | Cst (Suc, T as Type (@{type_name fun}, [T1, _]), _) =>
          let val R = Atom (spec_of_type scope T1) in
            Cst (Suc, T, Func (R, Opt R))
          end
        | Cst (Fracs, T, _) =>
          Cst (Fracs, T, best_non_opt_set_rep_for_type scope T)
        | Cst (NormFrac, T, _) =>
          let val R1 = Atom (spec_of_type scope (domain_type T)) in
            Cst (NormFrac, T, Func (R1, Func (R1, Opt (Struct [R1, R1]))))
          end
        | Cst (cst, T, _) =>
          if cst = Unknown orelse cst = Unrep then
            case (is_boolean_type T, polar |> unsound ? flip_polarity) of
              (true, Pos) => Cst (False, T, Formula Pos)
            | (true, Neg) => Cst (True, T, Formula Neg)
            | _ => Cst (cst, T, best_opt_set_rep_for_type scope T)
          else if member (op =) [Add, Subtract, Multiply, Divide, Gcd, Lcm]
                         cst then
            let
              val T1 = domain_type T
              val R1 = Atom (spec_of_type scope T1)
              val total = T1 = nat_T andalso
                          (cst = Subtract orelse cst = Divide orelse cst = Gcd)
            in Cst (cst, T, Func (R1, Func (R1, (not total ? Opt) R1))) end
          else if cst = NatToInt orelse cst = IntToNat then
            let
              val (dom_card, dom_j0) = spec_of_type scope (domain_type T)
              val (ran_card, ran_j0) = spec_of_type scope (range_type T)
              val total = not (is_word_type (domain_type T)) andalso
                          (if cst = NatToInt then
                             max_int_for_card ran_card >= dom_card + 1
                           else
                             max_int_for_card dom_card < ran_card)
            in
              Cst (cst, T, Func (Atom (dom_card, dom_j0),
                                 Atom (ran_card, ran_j0) |> not total ? Opt))
            end
          else
            Cst (cst, T, best_set_rep_for_type scope T)
        | Op1 (Not, T, _, u1) =>
          (case gsub def (flip_polarity polar) u1 of
             Op2 (Triad, T, _, u11, u12) =>
             triad (s_op1 Not T (Formula Pos) u12)
                   (s_op1 Not T (Formula Neg) u11)
           | u1' => s_op1 Not T (flip_rep_polarity (rep_of u1')) u1')
        | Op1 (IsUnknown, T, _, u1) =>
          let val u1 = sub u1 in
            if is_opt_rep (rep_of u1) then Op1 (IsUnknown, T, Formula Neut, u1)
            else Cst (False, T, Formula Neut)
          end
        | Op1 (oper, T, _, u1) =>
          let
            val u1 = sub u1
            val R1 = rep_of u1
            val R = case oper of
                      Finite => bool_rep polar (is_opt_rep R1)
                    | _ => (if is_opt_rep R1 then best_opt_set_rep_for_type
                            else best_non_opt_set_rep_for_type) scope T
          in s_op1 oper T R u1 end
        | Op2 (Less, T, _, u1, u2) =>
          let
            val u1 = sub u1
            val u2 = sub u2
            val R = bool_rep polar (exists (is_opt_rep o rep_of) [u1, u2])
          in s_op2 Less T R u1 u2 end
        | Op2 (Subset, T, _, u1, u2) =>
          let
            val u1 = sub u1
            val u2 = sub u2
            val opt = exists (is_opt_rep o rep_of) [u1, u2]
            val R = bool_rep polar opt
          in
            if is_opt_rep R then
              triad_fn (fn polar => s_op2 Subset T (Formula polar) u1 u2)
            else if not opt orelse unsound orelse polar = Neg orelse
                    is_concrete_type datatypes true (type_of u1) then
              s_op2 Subset T R u1 u2
            else
              Cst (False, T, Formula Pos)
          end
        | Op2 (DefEq, T, _, u1, u2) =>
          s_op2 DefEq T (Formula Neut) (sub u1) (sub u2)
        | Op2 (Eq, T, _, u1, u2) =>
          let
            val u1' = sub u1
            val u2' = sub u2
            fun non_opt_case () = s_op2 Eq T (Formula polar) u1' u2'
            fun opt_opt_case () =
              if polar = Neut then
                triad_fn (fn polar => s_op2 Eq T (Formula polar) u1' u2')
              else
                non_opt_case ()
            fun hybrid_case u =
              (* hackish optimization *)
              if is_constructive u then s_op2 Eq T (Formula Neut) u1' u2'
              else opt_opt_case ()
          in
            if unsound orelse polar = Neg orelse
               is_concrete_type datatypes true (type_of u1) then
              case (is_opt_rep (rep_of u1'), is_opt_rep (rep_of u2')) of
                (true, true) => opt_opt_case ()
              | (true, false) => hybrid_case u1'
              | (false, true) => hybrid_case u2'
              | (false, false) => non_opt_case ()
            else
              Cst (False, T, Formula Pos)
              |> polar = Neut ? (fn pos_u => triad pos_u (gsub def Neg u))
          end
        | Op2 (Apply, T, _, u1, u2) =>
          let
            val u1 = sub u1
            val u2 = sub u2
            val T1 = type_of u1
            val R1 = rep_of u1
            val R2 = rep_of u2
            val opt =
              case (u1, is_opt_rep R2) of
                (ConstName (@{const_name set}, _, _), false) => false
              | _ => exists is_opt_rep [R1, R2]
            val ran_R =
              if is_boolean_type T then
                bool_rep polar opt
              else
                lazy_range_rep ofs T1 (fn () => card_of_type card_assigns T)
                               (unopt_rep R1)
                |> opt ? opt_rep ofs T
          in s_op2 Apply T ran_R u1 u2 end
        | Op2 (Lambda, T, _, u1, u2) =>
          (case best_set_rep_for_type scope T of
             R as Func (R1, _) =>
             let
               val table' = NameTable.update (u1, R1) table
               val u1' = aux table' false Neut u1
               val u2' = aux table' false Neut u2
               val R =
                 if is_opt_rep (rep_of u2') orelse
                    (pseudo_range_type T = bool_T andalso
                     not (is_Cst False (unrepify_nut_in_nut table false Neut
                                                            u1 u2))) then
                   opt_rep ofs T R
                 else
                   unopt_rep R
             in s_op2 Lambda T R u1' u2' end
           | _ => raise NUT ("Nitpick_Nut.choose_reps_in_nut.aux", [u]))
        | Op2 (oper, T, _, u1, u2) =>
          if oper = All orelse oper = Exist then
            let
              val table' = fold (choose_rep_for_bound_var scope) (untuple I u1)
                                table
              val u1' = aux table' def polar u1
              val u2' = aux table' def polar u2
            in
              if polar = Neut andalso is_opt_rep (rep_of u2') then
                triad_fn (fn polar => gsub def polar u)
              else
                let val quant_u = s_op2 oper T (Formula polar) u1' u2' in
                  if def orelse
                     (unsound andalso (polar = Pos) = (oper = All)) orelse
                     is_complete_type datatypes true (type_of u1) then
                    quant_u
                  else
                    let
                      val connective = if oper = All then And else Or
                      val unrepified_u = unrepify_nut_in_nut table def polar
                                                             u1 u2
                    in
                      s_op2 connective T
                            (min_rep (rep_of quant_u) (rep_of unrepified_u))
                            quant_u unrepified_u
                    end
                end
            end
          else if oper = Or orelse oper = And then
            let
              val u1' = gsub def polar u1
              val u2' = gsub def polar u2
            in
              (if polar = Neut then
                 case (is_opt_rep (rep_of u1'), is_opt_rep (rep_of u2')) of
                   (true, true) => triad_fn (fn polar => gsub def polar u)
                 | (true, false) =>
                   s_op2 oper T (Opt bool_atom_R)
                         (triad_fn (fn polar => gsub def polar u1)) u2'
                 | (false, true) =>
                   s_op2 oper T (Opt bool_atom_R)
                         u1' (triad_fn (fn polar => gsub def polar u2))
                 | (false, false) => raise SAME ()
               else
                 raise SAME ())
              handle SAME () => s_op2 oper T (Formula polar) u1' u2'
            end
          else
            let
              val u1 = sub u1
              val u2 = sub u2
              val R =
                best_non_opt_set_rep_for_type scope T
                |> exists (is_opt_rep o rep_of) [u1, u2] ? opt_rep ofs T
            in s_op2 oper T R u1 u2 end
        | Op3 (Let, T, _, u1, u2, u3) =>
          let
            val u2 = sub u2
            val R2 = rep_of u2
            val table' = NameTable.update (u1, R2) table
            val u1 = modify_name_rep u1 R2
            val u3 = aux table' false polar u3
          in s_op3 Let T (rep_of u3) u1 u2 u3 end
        | Op3 (If, T, _, u1, u2, u3) =>
          let
            val u1 = sub u1
            val u2 = gsub def polar u2
            val u3 = gsub def polar u3
            val min_R = min_rep (rep_of u2) (rep_of u3)
            val R = min_R |> is_opt_rep (rep_of u1) ? opt_rep ofs T
          in s_op3 If T R u1 u2 u3 end
        | Tuple (T, _, us) =>
          let
            val Rs = map (best_one_rep_for_type scope o type_of) us
            val us = map sub us
            val R' = Struct Rs
                     |> exists (is_opt_rep o rep_of) us ? opt_rep ofs T
          in s_tuple T R' us end
        | Construct (us', T, _, us) =>
          let
            val us = map sub us
            val Rs = map rep_of us
            val R = best_one_rep_for_type scope T
            val {total, ...} =
              constr_spec datatypes (original_name (nickname_of (hd us')), T)
            val opt = exists is_opt_rep Rs orelse not total
          in Construct (map sub us', T, R |> opt ? Opt, us) end
        | _ =>
          let val u = modify_name_rep u (the_name table u) in
            if polar = Neut orelse not (is_boolean_type (type_of u)) orelse
               not (is_opt_rep (rep_of u)) then
              u
            else
              s_op1 Cast (type_of u) (Formula polar) u
          end
      end
  in aux table def Pos end

fun fresh_n_ary_index n [] ys = (0, (n, 1) :: ys)
  | fresh_n_ary_index n ((m, j) :: xs) ys =
    if m = n then (j, ys @ ((m, j + 1) :: xs))
    else fresh_n_ary_index n xs ((m, j) :: ys)
fun fresh_rel n {rels, vars, formula_reg, rel_reg} =
  let val (j, rels') = fresh_n_ary_index n rels [] in
    (j, {rels = rels', vars = vars, formula_reg = formula_reg,
         rel_reg = rel_reg})
  end
fun fresh_var n {rels, vars, formula_reg, rel_reg} =
  let val (j, vars') = fresh_n_ary_index n vars [] in
    (j, {rels = rels, vars = vars', formula_reg = formula_reg,
         rel_reg = rel_reg})
  end
fun fresh_formula_reg {rels, vars, formula_reg, rel_reg} =
  (formula_reg, {rels = rels, vars = vars, formula_reg = formula_reg + 1,
                 rel_reg = rel_reg})
fun fresh_rel_reg {rels, vars, formula_reg, rel_reg} =
  (rel_reg, {rels = rels, vars = vars, formula_reg = formula_reg,
             rel_reg = rel_reg + 1})

fun rename_plain_var v (ws, pool, table) =
  let
    val is_formula = (rep_of v = Formula Neut)
    val fresh = if is_formula then fresh_formula_reg else fresh_rel_reg
    val (j, pool) = fresh pool
    val constr = if is_formula then FormulaReg else RelReg
    val w = constr (j, type_of v, rep_of v)
  in (w :: ws, pool, NameTable.update (v, w) table) end

fun shape_tuple (T as Type (@{type_name prod}, [T1, T2])) (R as Struct [R1, R2])
                us =
    let val arity1 = arity_of_rep R1 in
      Tuple (T, R, [shape_tuple T1 R1 (List.take (us, arity1)),
                    shape_tuple T2 R2 (List.drop (us, arity1))])
    end
  | shape_tuple (T as Type (@{type_name fun}, [_, T2])) (R as Vect (k, R')) us =
    Tuple (T, R, map (shape_tuple T2 R') (batch_list (length us div k) us))
  | shape_tuple T _ [u] =
    if type_of u = T then u else raise NUT ("Nitpick_Nut.shape_tuple", [u])
  | shape_tuple _ _ us = raise NUT ("Nitpick_Nut.shape_tuple", us)

fun rename_n_ary_var rename_free v (ws, pool, table) =
  let
    val T = type_of v
    val R = rep_of v
    val arity = arity_of_rep R
    val nick = nickname_of v
    val (constr, fresh) = if rename_free then (FreeRel, fresh_rel)
                          else (BoundRel, fresh_var)
  in
    if not rename_free andalso arity > 1 then
      let
        val atom_schema = atom_schema_of_rep R
        val type_schema = type_schema_of_rep T R
        val (js, pool) = funpow arity (fn (js, pool) =>
                                          let val (j, pool) = fresh 1 pool in
                                            (j :: js, pool)
                                          end)
                                ([], pool)
        val ws' = map3 (fn j => fn x => fn T =>
                           constr ((1, j), T, Atom x,
                                   nick ^ " [" ^ string_of_int j ^ "]"))
                       (rev js) atom_schema type_schema
      in (ws' @ ws, pool, NameTable.update (v, shape_tuple T R ws') table) end
    else
      let
        val (j, pool) =
          case v of
            ConstName _ =>
            if is_sel_like_and_no_discr nick then
              case domain_type T of
                @{typ "unsigned_bit word"} =>
                (snd unsigned_bit_word_sel_rel, pool)
              | @{typ "signed_bit word"} => (snd signed_bit_word_sel_rel, pool)
              | _ => fresh arity pool
            else
              fresh arity pool
          | _ => fresh arity pool
        val w = constr ((arity, j), T, R, nick)
      in (w :: ws, pool, NameTable.update (v, w) table) end
  end

fun rename_free_vars vs pool table =
  let
    val (vs, pool, table) = fold (rename_n_ary_var true) vs ([], pool, table)
  in (rev vs, pool, table) end

fun rename_vars_in_nut pool table u =
  case u of
    Cst _ => u
  | Op1 (oper, T, R, u1) => Op1 (oper, T, R, rename_vars_in_nut pool table u1)
  | Op2 (oper, T, R, u1, u2) =>
    if oper = All orelse oper = Exist orelse oper = Lambda then
      let
        val (_, pool, table) = fold (rename_n_ary_var false) (untuple I u1)
                                    ([], pool, table)
      in
        Op2 (oper, T, R, rename_vars_in_nut pool table u1,
             rename_vars_in_nut pool table u2)
      end
    else
      Op2 (oper, T, R, rename_vars_in_nut pool table u1,
           rename_vars_in_nut pool table u2)
  | Op3 (Let, T, R, u1, u2, u3) =>
    if inline_nut u2 then
      let
        val u2 = rename_vars_in_nut pool table u2
        val table = NameTable.update (u1, u2) table
      in rename_vars_in_nut pool table u3 end
    else
      let
        val bs = untuple I u1
        val (_, pool, table') = fold rename_plain_var bs ([], pool, table)
      in
        Op3 (Let, T, R, rename_vars_in_nut pool table' u1,
             rename_vars_in_nut pool table u2,
             rename_vars_in_nut pool table' u3)
      end
  | Op3 (oper, T, R, u1, u2, u3) =>
    Op3 (oper, T, R, rename_vars_in_nut pool table u1,
         rename_vars_in_nut pool table u2, rename_vars_in_nut pool table u3)
  | Tuple (T, R, us) => Tuple (T, R, map (rename_vars_in_nut pool table) us)
  | Construct (us', T, R, us) =>
    Construct (map (rename_vars_in_nut pool table) us', T, R,
               map (rename_vars_in_nut pool table) us)
  | _ => the_name table u

end;
