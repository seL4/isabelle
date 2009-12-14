(*  Title:      HOL/Tools/Nitpick/nitpick_nut.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009

Nitpick underlying terms (nuts).
*)

signature NITPICK_NUT =
sig
  type special_fun = Nitpick_HOL.special_fun
  type extended_context = Nitpick_HOL.extended_context
  type scope = Nitpick_Scope.scope
  type name_pool = Nitpick_Peephole.name_pool
  type rep = Nitpick_Rep.rep

  datatype cst =
    Unity |
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
    Modulo |
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
    Tha |
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
    The |
    Eps |
    Triad |
    Union |
    SetDifference |
    Intersect |
    Composition |
    Product |
    Image |
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
  val is_FreeName : nut -> bool
  val is_Cst : cst -> nut -> bool
  val fold_nut : (nut -> 'a -> 'a) -> nut -> 'a -> 'a
  val map_nut : (nut -> nut) -> nut -> nut
  val untuple : (nut -> 'a) -> nut -> 'a list
  val add_free_and_const_names :
    nut -> nut list * nut list -> nut list * nut list
  val name_ord : (nut * nut) -> order
  val the_name : 'a NameTable.table -> nut -> 'a
  val the_rel : nut NameTable.table -> nut -> Kodkod.n_ary_index
  val nut_from_term : extended_context -> op2 -> term -> nut
  val choose_reps_for_free_vars :
    scope -> nut list -> rep NameTable.table -> nut list * rep NameTable.table
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

datatype cst =
  Unity |
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
  Modulo |
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
  Tha |
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
  The |
  Eps |
  Triad |
  Union |
  SetDifference |
  Intersect |
  Composition |
  Product |
  Image |
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

exception NUT of string * nut list

(* cst -> string *)
fun string_for_cst Unity = "Unity"
  | string_for_cst False = "False"
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
  | string_for_cst Modulo = "Modulo"
  | string_for_cst Gcd = "Gcd"
  | string_for_cst Lcm = "Lcm"
  | string_for_cst Fracs = "Fracs"
  | string_for_cst NormFrac = "NormFrac"
  | string_for_cst NatToInt = "NatToInt"
  | string_for_cst IntToNat = "IntToNat"

(* op1 -> string *)
fun string_for_op1 Not = "Not"
  | string_for_op1 Finite = "Finite"
  | string_for_op1 Converse = "Converse"
  | string_for_op1 Closure = "Closure"
  | string_for_op1 SingletonSet = "SingletonSet"
  | string_for_op1 Tha = "Tha"
  | string_for_op1 First = "First"
  | string_for_op1 Second = "Second"
  | string_for_op1 Cast = "Cast"

(* op2 -> string *)
fun string_for_op2 All = "All"
  | string_for_op2 Exist = "Exist"
  | string_for_op2 Or = "Or"
  | string_for_op2 And = "And"
  | string_for_op2 Less = "Less"
  | string_for_op2 Subset = "Subset"
  | string_for_op2 DefEq = "DefEq"
  | string_for_op2 Eq = "Eq"
  | string_for_op2 The = "The"
  | string_for_op2 Eps = "Eps"
  | string_for_op2 Triad = "Triad"
  | string_for_op2 Union = "Union"
  | string_for_op2 SetDifference = "SetDifference"
  | string_for_op2 Intersect = "Intersect"
  | string_for_op2 Composition = "Composition"
  | string_for_op2 Product = "Product"
  | string_for_op2 Image = "Image"
  | string_for_op2 Apply = "Apply"
  | string_for_op2 Lambda = "Lambda"

(* op3 -> string *)
fun string_for_op3 Let = "Let"
  | string_for_op3 If = "If"

(* int -> Proof.context -> nut -> string *)
fun basic_string_for_nut indent ctxt u =
  let
    (* nut -> string *)
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
       "Construct " ^ implode (map sub us') ^ Syntax.string_of_typ ctxt T ^
       " " ^ string_for_rep R ^ " " ^ implode (map sub us)
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
(* Proof.context -> nut -> string *)
val string_for_nut = basic_string_for_nut 0

(* nut -> bool *)
fun inline_nut (Op1 _) = false
  | inline_nut (Op2 _) = false
  | inline_nut (Op3 _) = false
  | inline_nut (Tuple (_, _, us)) = forall inline_nut us
  | inline_nut _ = true

(* nut -> typ *)
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

(* nut -> rep *)
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

(* nut -> string *)
fun nickname_of (BoundName (_, _, _, nick)) = nick
  | nickname_of (FreeName (s, _, _)) = s
  | nickname_of (ConstName (s, _, _)) = s
  | nickname_of (BoundRel (_, _, _, nick)) = nick
  | nickname_of (FreeRel (_, _, _, nick)) = nick
  | nickname_of u = raise NUT ("Nitpick_Nut.nickname_of", [u])

(* nut -> bool *)
fun is_skolem_name u =
  space_explode name_sep (nickname_of u)
  |> exists (String.isPrefix skolem_prefix)
  handle NUT ("Nitpick_Nut.nickname_of", _) => false
fun is_eval_name u =
  String.isPrefix eval_prefix (nickname_of u)
  handle NUT ("Nitpick_Nut.nickname_of", _) => false
fun is_FreeName (FreeName _) = true
  | is_FreeName _ = false
(* cst -> nut -> bool *)
fun is_Cst cst (Cst (cst', _, _)) = (cst = cst')
  | is_Cst _ _ = false

(* (nut -> 'a -> 'a) -> nut -> 'a -> 'a *)
fun fold_nut f u =
  case u of
    Op1 (_, _, _, u1) => fold_nut f u1
  | Op2 (_, _, _, u1, u2) => fold_nut f u1 #> fold_nut f u2
  | Op3 (_, _, _, u1, u2, u3) => fold_nut f u1 #> fold_nut f u2 #> fold_nut f u3
  | Tuple (_, _, us) => fold (fold_nut f) us
  | Construct (us', _, _, us) => fold (fold_nut f) us #> fold (fold_nut f) us'
  | _ => f u
(* (nut -> nut) -> nut -> nut *)
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

(* nut * nut -> order *)
fun name_ord (BoundName (j1, _, _, _), BoundName (j2, _, _, _)) =
    int_ord (j1, j2)
  | name_ord (BoundName _, _) = LESS
  | name_ord (_, BoundName _) = GREATER
  | name_ord (FreeName (s1, T1, _), FreeName (s2, T2, _)) =
    (case fast_string_ord (s1, s2) of
       EQUAL => TermOrd.typ_ord (T1, T2)
     | ord => ord)
  | name_ord (FreeName _, _) = LESS
  | name_ord (_, FreeName _) = GREATER
  | name_ord (ConstName (s1, T1, _), ConstName (s2, T2, _)) =
    (case fast_string_ord (s1, s2) of
       EQUAL => TermOrd.typ_ord (T1, T2)
     | ord => ord)
  | name_ord (u1, u2) = raise NUT ("Nitpick_Nut.name_ord", [u1, u2])

(* nut -> nut -> int *)
fun num_occs_in_nut needle_u stack_u =
  fold_nut (fn u => if u = needle_u then Integer.add 1 else I) stack_u 0
(* nut -> nut -> bool *)
val is_subterm_of = not_equal 0 oo num_occs_in_nut

(* nut -> nut -> nut -> nut *)
fun substitute_in_nut needle_u needle_u' =
  map_nut (fn u => if u = needle_u then needle_u' else u)

(* nut -> nut list * nut list -> nut list * nut list *)
val add_free_and_const_names =
  fold_nut (fn u => case u of
                      FreeName _ => apfst (insert (op =) u)
                    | ConstName _ => apsnd (insert (op =) u)
                    | _ => I)

(* nut -> rep -> nut *)
fun modify_name_rep (BoundName (j, T, _, nick)) R = BoundName (j, T, R, nick)
  | modify_name_rep (FreeName (s, T, _)) R = FreeName (s, T, R)
  | modify_name_rep (ConstName (s, T, _)) R = ConstName (s, T, R)
  | modify_name_rep u _ = raise NUT ("Nitpick_Nut.modify_name_rep", [u])

structure NameTable = Table(type key = nut val ord = name_ord)

(* 'a NameTable.table -> nut -> 'a *)
fun the_name table name =
  case NameTable.lookup table name of
    SOME u => u
  | NONE => raise NUT ("Nitpick_Nut.the_name", [name])
(* nut NameTable.table -> nut -> Kodkod.n_ary_index *)
fun the_rel table name =
  case the_name table name of
    FreeRel (x, _, _, _) => x
  | u => raise NUT ("Nitpick_Nut.the_rel", [u])

(* typ * term -> typ * term *)
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
(* typ * term -> (typ * term) list *)
fun factorize (z as (Type ("*", _), _)) = maps factorize [mk_fst z, mk_snd z]
  | factorize z = [z]

(* extended_context -> op2 -> term -> nut *)
fun nut_from_term (ext_ctxt as {thy, fast_descrs, special_funs, ...}) eq =
  let
    (* string list -> typ list -> term -> nut *)
    fun aux eq ss Ts t =
      let
        (* term -> nut *)
        val sub = aux Eq ss Ts
        val sub' = aux eq ss Ts
        (* string -> typ -> term -> nut *)
        fun sub_abs s T = aux eq (s :: ss) (T :: Ts)
        (* typ -> term -> term -> nut *)
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
                val equation = Const (@{const_name "op ="},
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
        (* op2 -> string -> typ -> term -> nut *)
        fun do_quantifier quant s T t1 =
          let
            val bound_u = BoundName (length Ts, T, Any, s)
            val body_u = sub_abs s T t1
          in
            if is_subterm_of bound_u body_u then
              Op2 (quant, bool_T, Any, bound_u, body_u)
            else
              body_u
          end
        (* term -> term list -> nut *)
        fun do_apply t0 ts =
          let
            val (ts', t2) = split_last ts
            val t1 = list_comb (t0, ts')
            val T1 = fastype_of1 (Ts, t1)
          in Op2 (Apply, range_type T1, Any, sub t1, sub t2) end
      in
        case strip_comb t of
          (Const (@{const_name all}, _), [Abs (s, T, t1)]) =>
          do_quantifier All s T t1
        | (t0 as Const (@{const_name all}, T), [t1]) =>
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
        | (t0 as Const (@{const_name All}, T), [t1]) =>
          sub' (t0 $ eta_expand Ts t1 1)
        | (Const (@{const_name Ex}, _), [Abs (s, T, t1)]) =>
          do_quantifier Exist s T t1
        | (t0 as Const (@{const_name Ex}, T), [t1]) =>
          sub' (t0 $ eta_expand Ts t1 1)
        | (t0 as Const (@{const_name The}, T), [t1]) =>
          if fast_descrs then
            Op2 (The, range_type T, Any, sub t1,
                 sub (Const (@{const_name undefined_fast_The}, range_type T)))
          else
            do_apply t0 [t1]
        | (t0 as Const (@{const_name Eps}, T), [t1]) =>
          if fast_descrs then
            Op2 (Eps, range_type T, Any, sub t1,
                 sub (Const (@{const_name undefined_fast_Eps}, range_type T)))
          else
            do_apply t0 [t1]
        | (Const (@{const_name "op ="}, T), [t1, t2]) => sub_equals T t1 t2
        | (Const (@{const_name "op &"}, _), [t1, t2]) =>
          Op2 (And, bool_T, Any, sub' t1, sub' t2)
        | (Const (@{const_name "op |"}, _), [t1, t2]) =>
          Op2 (Or, bool_T, Any, sub t1, sub t2)
        | (Const (@{const_name "op -->"}, _), [t1, t2]) =>
          Op2 (Or, bool_T, Any, Op1 (Not, bool_T, Any, sub t1), sub' t2)
        | (Const (@{const_name If}, T), [t1, t2, t3]) =>
          Op3 (If, nth_range_type 3 T, Any, sub t1, sub t2, sub t3)
        | (Const (@{const_name Let}, T), [t1, Abs (s, T', t2)]) =>
          Op3 (Let, nth_range_type 2 T, Any, BoundName (length Ts, T', Any, s),
               sub t1, sub_abs s T' t2)
        | (t0 as Const (@{const_name Let}, T), [t1, t2]) =>
          sub (t0 $ t1 $ eta_expand Ts t2 1)
        | (Const (@{const_name unknown}, T), []) => Cst (Unknown, T, Any)
        | (@{const Unity}, []) => Cst (Unity, @{typ unit}, Any)
        | (Const (@{const_name Pair}, T), [t1, t2]) =>
          Tuple (nth_range_type 2 T, Any, map sub [t1, t2])
        | (Const (@{const_name fst}, T), [t1]) =>
          Op1 (First, range_type T, Any, sub t1)
        | (Const (@{const_name snd}, T), [t1]) =>
          Op1 (Second, range_type T, Any, sub t1)
        | (Const (@{const_name Id}, T), []) => Cst (Iden, T, Any)
        | (Const (@{const_name insert}, T), [t1, t2]) =>
          (case t2 of
             Abs (_, _, @{const False}) =>
             Op1 (SingletonSet, nth_range_type 2 T, Any, sub t1)
           | _ =>
             Op2 (Union, nth_range_type 2 T, Any,
                  Op1 (SingletonSet, nth_range_type 2 T, Any, sub t1), sub t2))
        | (Const (@{const_name converse}, T), [t1]) =>
          Op1 (Converse, range_type T, Any, sub t1)
        | (Const (@{const_name trancl}, T), [t1]) =>
          Op1 (Closure, range_type T, Any, sub t1)
        | (Const (@{const_name rel_comp}, T), [t1, t2]) =>
          Op2 (Composition, nth_range_type 2 T, Any, sub t1, sub t2)
        | (Const (@{const_name Sigma}, T), [t1, Abs (s, T', t2')]) =>
          Op2 (Product, nth_range_type 2 T, Any, sub t1, sub_abs s T' t2')
        | (Const (@{const_name image}, T), [t1, t2]) =>
          Op2 (Image, nth_range_type 2 T, Any, sub t1, sub t2)
        | (Const (@{const_name Suc}, T), []) => Cst (Suc, T, Any)
        | (Const (@{const_name finite}, T), [t1]) =>
          (if is_finite_type ext_ctxt (domain_type T) then
             Cst (True, bool_T, Any)
           else case t1 of
             Const (@{const_name top}, _) => Cst (False, bool_T, Any)
           | _ => Op1 (Finite, bool_T, Any, sub t1))
        | (Const (@{const_name nat}, T), []) => Cst (IntToNat, T, Any)
        | (Const (@{const_name zero_nat_inst.zero_nat}, T), []) =>
          Cst (Num 0, T, Any)
        | (Const (@{const_name one_nat_inst.one_nat}, T), []) =>
          Cst (Num 1, T, Any)
        | (Const (@{const_name plus_nat_inst.plus_nat}, T), []) =>
          Cst (Add, T, Any)
        | (Const (@{const_name minus_nat_inst.minus_nat}, T), []) =>
          Cst (Subtract, T, Any)
        | (Const (@{const_name times_nat_inst.times_nat}, T), []) =>
          Cst (Multiply, T, Any)
        | (Const (@{const_name div_nat_inst.div_nat}, T), []) =>
          Cst (Divide, T, Any)
        | (Const (@{const_name div_nat_inst.mod_nat}, T), []) =>
          Cst (Modulo, T, Any)
        | (Const (@{const_name ord_nat_inst.less_nat}, T), [t1, t2]) =>
          Op2 (Less, bool_T, Any, sub t1, sub t2)
        | (Const (@{const_name ord_nat_inst.less_eq_nat}, T), [t1, t2]) =>
          Op1 (Not, bool_T, Any, Op2 (Less, bool_T, Any, sub t2, sub t1))
        | (Const (@{const_name nat_gcd}, T), []) => Cst (Gcd, T, Any)
        | (Const (@{const_name nat_lcm}, T), []) => Cst (Lcm, T, Any)
        | (Const (@{const_name zero_int_inst.zero_int}, T), []) =>
          Cst (Num 0, T, Any)
        | (Const (@{const_name one_int_inst.one_int}, T), []) =>
          Cst (Num 1, T, Any)
        | (Const (@{const_name plus_int_inst.plus_int}, T), []) =>
          Cst (Add, T, Any)
        | (Const (@{const_name minus_int_inst.minus_int}, T), []) =>
          Cst (Subtract, T, Any)
        | (Const (@{const_name times_int_inst.times_int}, T), []) =>
          Cst (Multiply, T, Any)
        | (Const (@{const_name div_int_inst.div_int}, T), []) =>
          Cst (Divide, T, Any)
        | (Const (@{const_name div_int_inst.mod_int}, T), []) =>
          Cst (Modulo, T, Any)
        | (Const (@{const_name uminus_int_inst.uminus_int}, T), []) =>
          Op2 (Apply, int_T --> int_T, Any,
               Cst (Subtract, [int_T, int_T] ---> int_T, Any),
               Cst (Num 0, int_T, Any))
        | (Const (@{const_name ord_int_inst.less_int}, T), [t1, t2]) =>
          Op2 (Less, bool_T, Any, sub t1, sub t2)
        | (Const (@{const_name ord_int_inst.less_eq_int}, T), [t1, t2]) =>
          Op1 (Not, bool_T, Any, Op2 (Less, bool_T, Any, sub t2, sub t1))
        | (Const (@{const_name Tha}, Type ("fun", [_, T2])), [t1]) =>
          Op1 (Tha, T2, Any, sub t1)
        | (Const (@{const_name Frac}, T), []) => Cst (Fracs, T, Any)
        | (Const (@{const_name norm_frac}, T), []) => Cst (NormFrac, T, Any)
        | (Const (@{const_name of_nat}, T as @{typ "nat => int"}), []) =>
          Cst (NatToInt, T, Any)
        | (Const (@{const_name lower_semilattice_fun_inst.inf_fun}, T),
                  [t1, t2]) =>
          Op2 (Intersect, nth_range_type 2 T, Any, sub t1, sub t2)
        | (Const (@{const_name upper_semilattice_fun_inst.sup_fun}, T),
                  [t1, t2]) =>
          Op2 (Union, nth_range_type 2 T, Any, sub t1, sub t2)
        | (t0 as Const (@{const_name minus_fun_inst.minus_fun}, T), [t1, t2]) =>
          Op2 (SetDifference, nth_range_type 2 T, Any, sub t1, sub t2)
        | (t0 as Const (@{const_name ord_fun_inst.less_eq_fun}, T), [t1, t2]) =>
          Op2 (Subset, bool_T, Any, sub t1, sub t2)
        | (t0 as Const (x as (s, T)), ts) =>
          if is_constr thy x then
            case num_binder_types T - length ts of
              0 => Construct (map ((fn (s, T) => ConstName (s, T, Any))
                                    o nth_sel_for_constr x)
                                  (~1 upto num_sels_for_constr_type T - 1),
                              body_type T, Any,
                              ts |> map (`(curry fastype_of1 Ts))
                                 |> maps factorize |> map (sub o snd))
            | k => sub (eta_expand Ts t k)
          else if String.isPrefix numeral_prefix s then
            Cst (Num (the (Int.fromString (unprefix numeral_prefix s))), T, Any)
          else
            (case arity_of_built_in_const fast_descrs x of
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

(* scope -> typ -> rep *)
fun rep_for_abs_fun scope T =
  let val (R1, R2) = best_non_opt_symmetric_reps_for_fun_type scope T in
    Func (R1, (card_of_rep R1 <> card_of_rep R2 ? Opt) R2)
  end

(* scope -> nut -> nut list * rep NameTable.table
   -> nut list * rep NameTable.table *)
fun choose_rep_for_free_var scope v (vs, table) =
  let
    val R = best_non_opt_set_rep_for_type scope (type_of v)
    val v = modify_name_rep v R
  in (v :: vs, NameTable.update (v, R) table) end
(* scope -> bool -> nut -> nut list * rep NameTable.table
   -> nut list * rep NameTable.table *)
fun choose_rep_for_const (scope as {ext_ctxt as {thy, ctxt, ...}, datatypes,
                                    ofs, ...}) all_exact v (vs, table) =
  let
    val x as (s, T) = (nickname_of v, type_of v)
    val R = (if is_abs_fun thy x then
               rep_for_abs_fun
             else if is_rep_fun thy x then
               Func oo best_non_opt_symmetric_reps_for_fun_type
             else if all_exact orelse is_skolem_name v
                     orelse member (op =) [@{const_name undefined_fast_The},
                                           @{const_name undefined_fast_Eps},
                                           @{const_name bisim},
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

(* scope -> nut list -> rep NameTable.table -> nut list * rep NameTable.table *)
fun choose_reps_for_free_vars scope vs table =
  fold (choose_rep_for_free_var scope) vs ([], table)
(* scope -> bool -> nut list -> rep NameTable.table
   -> nut list * rep NameTable.table *)
fun choose_reps_for_consts scope all_exact vs table =
  fold (choose_rep_for_const scope all_exact) vs ([], table)

(* scope -> styp -> int -> nut list * rep NameTable.table
   -> nut list * rep NameTable.table *)
fun choose_rep_for_nth_sel_for_constr (scope as {ext_ctxt, ...}) x n
                                      (vs, table) =
  let
    val (s', T') = boxed_nth_sel_for_constr ext_ctxt x n
    val R' = if n = ~1 then best_non_opt_set_rep_for_type scope T'
             else best_opt_set_rep_for_type scope T' |> unopt_rep
    val v = ConstName (s', T', R')
  in (v :: vs, NameTable.update (v, R') table) end
(* scope -> styp -> nut list * rep NameTable.table
   -> nut list * rep NameTable.table *)
fun choose_rep_for_sels_for_constr scope (x as (_, T)) =
  fold_rev (choose_rep_for_nth_sel_for_constr scope x)
           (~1 upto num_sels_for_constr_type T - 1)
(* scope -> dtype_spec -> nut list * rep NameTable.table
   -> nut list * rep NameTable.table *)
fun choose_rep_for_sels_of_datatype _ ({shallow = true, ...} : dtype_spec) = I
  | choose_rep_for_sels_of_datatype scope {constrs, ...} =
    fold_rev (choose_rep_for_sels_for_constr scope o #const) constrs
(* scope -> rep NameTable.table -> nut list * rep NameTable.table *)
fun choose_reps_for_all_sels (scope as {datatypes, ...}) =
  fold (choose_rep_for_sels_of_datatype scope) datatypes o pair []

(* scope -> nut -> rep NameTable.table -> rep NameTable.table *)
fun choose_rep_for_bound_var scope v table =
  let val R = best_one_rep_for_type scope (type_of v) in
    NameTable.update (v, R) table
  end

(* A nut is said to be constructive if whenever it evaluates to unknown in our
   three-valued logic, it would evaluate to a unrepresentable value ("unrep")
   according to the HOL semantics. For example, "Suc n" is constructive if "n"
   is representable or "Unrep", because unknown implies unrep. *)
(* nut -> bool *)
fun is_constructive u =
  is_Cst Unrep u orelse
  (not (is_fun_type (type_of u)) andalso not (is_opt_rep (rep_of u))) orelse
  case u of
    Cst (Num _, _, _) => true
  | Cst (cst, T, _) => cst = Suc orelse (body_type T = nat_T andalso cst = Add)
  | Op2 (Apply, _, _, u1, u2) => forall is_constructive [u1, u2]
  | Op3 (If, _, _, u1, u2, u3) =>
    not (is_opt_rep (rep_of u1)) andalso forall is_constructive [u2, u3]
  | Tuple (_, _, us) => forall is_constructive us
  | Construct (_, _, _, us) => forall is_constructive us
  | _ => false

(* nut -> nut *)
fun optimize_unit u =
  if rep_of u = Unit then Cst (Unity, type_of u, Unit) else u
(* typ -> rep -> nut *)
fun unknown_boolean T R =
  Cst (case R of
         Formula Pos => False
       | Formula Neg => True
       | _ => Unknown, T, R)

(* op1 -> typ -> rep -> nut -> nut *)
fun s_op1 oper T R u1 =
  ((if oper = Not then
      if is_Cst True u1 then Cst (False, T, R)
      else if is_Cst False u1 then Cst (True, T, R)
      else raise SAME ()
    else
      raise SAME ())
   handle SAME () => Op1 (oper, T, R, u1))
  |> optimize_unit
(* op2 -> typ -> rep -> nut -> nut -> nut *)
fun s_op2 oper T R u1 u2 =
  ((case oper of
      Or =>
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
        if is_constructive u1 then
          Cst (Unrep, T, R)
        else if is_boolean_type T then
          if is_FreeName u1 then Cst (False, T, Formula Neut)
          else unknown_boolean T R
        else case u1 of
          Op2 (Apply, _, _, ConstName (@{const_name List.append}, _, _), _) =>
          Cst (Unrep, T, R)
        | _ => raise SAME ()
      else
        raise SAME ()
    | _ => raise SAME ())
   handle SAME () => Op2 (oper, T, R, u1, u2))
  |> optimize_unit
(* op3 -> typ -> rep -> nut -> nut -> nut -> nut *)
fun s_op3 oper T R u1 u2 u3 =
  ((case oper of
      Let =>
      if inline_nut u2 orelse num_occs_in_nut u1 u3 < 2 then
        substitute_in_nut u1 u2 u3
      else
        raise SAME ()
    | _ => raise SAME ())
   handle SAME () => Op3 (oper, T, R, u1, u2, u3))
  |> optimize_unit
(* typ -> rep -> nut list -> nut *)
fun s_tuple T R us =
  (if exists (is_Cst Unrep) us then Cst (Unrep, T, R) else Tuple (T, R, us))
  |> optimize_unit

(* theory -> nut -> nut *)
fun optimize_nut u =
  case u of
    Op1 (oper, T, R, u1) => s_op1 oper T R (optimize_nut u1)
  | Op2 (oper, T, R, u1, u2) =>
    s_op2 oper T R (optimize_nut u1) (optimize_nut u2)
  | Op3 (oper, T, R, u1, u2, u3) =>
    s_op3 oper T R (optimize_nut u1) (optimize_nut u2) (optimize_nut u3)
  | Tuple (T, R, us) => s_tuple T R (map optimize_nut us)
  | Construct (us', T, R, us) => Construct (us', T, R, map optimize_nut us)
  | _ => optimize_unit u

(* (nut -> 'a) -> nut -> 'a list *)
fun untuple f (Tuple (_, _, us)) = maps (untuple f) us
  | untuple f u = if rep_of u = Unit then [] else [f u]

(* scope -> bool -> rep NameTable.table -> bool -> nut -> nut *)
fun choose_reps_in_nut (scope as {ext_ctxt as {thy, ctxt, ...}, card_assigns,
                                  datatypes, ofs, ...}) liberal table def =
  let
    val bool_atom_R = Atom (2, offset_of_type ofs bool_T)
    (* polarity -> bool -> rep *)
    fun bool_rep polar opt =
      if polar = Neut andalso opt then Opt bool_atom_R else Formula polar
    (* nut -> nut -> nut *)
    fun triad u1 u2 = s_op2 Triad (type_of u1) (Opt bool_atom_R) u1 u2
    (* (polarity -> nut) -> nut *)
    fun triad_fn f = triad (f Pos) (f Neg)
    (* rep NameTable.table -> bool -> polarity -> nut -> nut -> nut *)
    fun unrepify_nut_in_nut table def polar needle_u =
      let val needle_T = type_of needle_u in
        substitute_in_nut needle_u (Cst (if is_fun_type needle_T then Unknown
                                         else Unrep, needle_T, Any))
        #> aux table def polar
      end
    (* rep NameTable.table -> bool -> polarity -> nut -> nut *)
    and aux table def polar u =
      let
        (* bool -> polarity -> nut -> nut *)
        val gsub = aux table
        (* nut -> nut *)
        val sub = gsub false Neut
      in
        case u of
          Cst (False, T, _) => Cst (False, T, Formula Neut)
        | Cst (True, T, _) => Cst (True, T, Formula Neut)
        | Cst (Num j, T, _) =>
          (case spec_of_type scope T of
             (1, j0) => if j = 0 then Cst (Unity, T, Unit)
                        else Cst (Unrep, T, Opt (Atom (1, j0)))
           | (k, j0) =>
             let
               val ok = (if T = int_T then atom_for_int (k, j0) j <> ~1
                         else j < k)
             in
               if ok then Cst (Num j, T, Atom (k, j0))
               else Cst (Unrep, T, Opt (Atom (k, j0)))
             end)
        | Cst (Suc, T as Type ("fun", [T1, _]), _) =>
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
            case (is_boolean_type T, polar) of
              (true, Pos) => Cst (False, T, Formula Pos)
            | (true, Neg) => Cst (True, T, Formula Neg)
            | _ => Cst (cst, T, best_opt_set_rep_for_type scope T)
          else if member (op =) [Add, Subtract, Multiply, Divide, Modulo, Gcd,
                                 Lcm] cst then
            let
              val T1 = domain_type T
              val R1 = Atom (spec_of_type scope T1)
              val total =
                T1 = nat_T andalso (cst = Subtract orelse cst = Divide
                                    orelse cst = Modulo orelse cst = Gcd)
            in Cst (cst, T, Func (R1, Func (R1, (not total ? Opt) R1))) end
          else if cst = NatToInt orelse cst = IntToNat then
            let
              val (nat_card, nat_j0) = spec_of_type scope nat_T
              val (int_card, int_j0) = spec_of_type scope int_T
            in
              if cst = NatToInt then
                let val total = (max_int_for_card int_card >= nat_card + 1) in
                  Cst (cst, T,
                       Func (Atom (nat_card, nat_j0),
                             (not total ? Opt) (Atom (int_card, int_j0))))
                end
              else
                let val total = (max_int_for_card int_card < nat_card) in
                  Cst (cst, T, Func (Atom (int_card, int_j0),
                       Atom (nat_card, nat_j0)) |> not total ? Opt)
                end
            end
          else
            Cst (cst, T, best_set_rep_for_type scope T)
        | Op1 (Not, T, _, u1) =>
          (case gsub def (flip_polarity polar) u1 of
             Op2 (Triad, T, R, u11, u12) =>
             triad (s_op1 Not T (Formula Pos) u12)
                   (s_op1 Not T (Formula Neg) u11)
           | u1' => s_op1 Not T (flip_rep_polarity (rep_of u1')) u1')
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
            else if opt andalso polar = Pos andalso
                    not (is_concrete_type datatypes (type_of u1)) then
              Cst (False, T, Formula Pos)
            else
              s_op2 Subset T R u1 u2
          end
        | Op2 (DefEq, T, _, u1, u2) =>
          s_op2 DefEq T (Formula Neut) (sub u1) (sub u2)
        | Op2 (Eq, T, _, u1, u2) =>
          let
            val u1' = sub u1
            val u2' = sub u2
            (* unit -> nut *)
            fun non_opt_case () = s_op2 Eq T (Formula polar) u1' u2'
            (* unit -> nut *)
            fun opt_opt_case () =
              if polar = Neut then
                triad_fn (fn polar => s_op2 Eq T (Formula polar) u1' u2')
              else
                non_opt_case ()
            (* nut -> nut *)
            fun hybrid_case u =
              (* hackish optimization *)
              if is_constructive u then s_op2 Eq T (Formula Neut) u1' u2'
              else opt_opt_case ()
          in
            if liberal orelse polar = Neg
               orelse is_concrete_type datatypes (type_of u1) then
              case (is_opt_rep (rep_of u1'), is_opt_rep (rep_of u2')) of
                (true, true) => opt_opt_case ()
              | (true, false) => hybrid_case u1'
              | (false, true) => hybrid_case u2'
              | (false, false) => non_opt_case ()
            else
              Cst (False, T, Formula Pos)
              |> polar = Neut ? (fn pos_u => triad pos_u (gsub def Neg u))
          end
        | Op2 (Image, T, _, u1, u2) =>
          let
            val u1' = sub u1
            val u2' = sub u2
          in
            (case (rep_of u1', rep_of u2') of
               (Func (R11, R12), Func (R21, Formula Neut)) =>
               if R21 = R11 andalso is_lone_rep R12 then
                 let
                   val R =
                     best_non_opt_set_rep_for_type scope T
                     |> exists (is_opt_rep o rep_of) [u1', u2'] ? opt_rep ofs T
                 in s_op2 Image T R u1' u2' end
               else
                 raise SAME ()
             | _ => raise SAME ())
            handle SAME () =>
                   let
                     val T1 = type_of u1
                     val dom_T = domain_type T1
                     val ran_T = range_type T1
                     val x_u = BoundName (~1, dom_T, Any, "image.x")
                     val y_u = BoundName (~2, ran_T, Any, "image.y")
                   in
                     Op2 (Lambda, T, Any, y_u,
                          Op2 (Exist, bool_T, Any, x_u,
                               Op2 (And, bool_T, Any,
                                    case u2 of
                                      Op2 (Lambda, _, _, u21, u22) =>
                                      if num_occs_in_nut u21 u22 = 0 then
                                        u22
                                      else
                                        Op2 (Apply, bool_T, Any, u2, x_u)
                                    | _ => Op2 (Apply, bool_T, Any, u2, x_u),

                                    Op2 (Eq, bool_T, Any, y_u,
                                         Op2 (Apply, ran_T, Any, u1, x_u)))))
                     |> sub
                   end
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
                smart_range_rep ofs T1 (fn () => card_of_type card_assigns T)
                                (unopt_rep R1)
                |> opt ? opt_rep ofs T
          in s_op2 Apply T ran_R u1 u2 end
        | Op2 (Lambda, T, _, u1, u2) =>
          (case best_set_rep_for_type scope T of
             Unit => Cst (Unity, T, Unit)
           | R as Func (R1, _) =>
             let
               val table' = NameTable.update (u1, R1) table
               val u1' = aux table' false Neut u1
               val u2' = aux table' false Neut u2
               val R =
                 if is_opt_rep (rep_of u2')
                    orelse (range_type T = bool_T andalso
                            not (is_Cst False
                                        (unrepify_nut_in_nut table false Neut
                                                             u1 u2
                                         |> optimize_nut))) then
                   opt_rep ofs T R
                 else
                   unopt_rep R
             in s_op2 Lambda T R u1' u2' end
           | R => raise NUT ("Nitpick_Nut.aux.choose_reps_in_nut", [u]))
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
                  if def
                     orelse (liberal andalso (polar = Pos) = (oper = All))
                     orelse is_complete_type datatypes (type_of u1) then
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
          else if oper = The orelse oper = Eps then
            let
              val u1' = sub u1
              val opt1 = is_opt_rep (rep_of u1')
              val opt = (oper = Eps orelse opt1)
              val unopt_R = best_one_rep_for_type scope T |> optable_rep ofs T
              val R = if is_boolean_type T then bool_rep polar opt
                      else unopt_R |> opt ? opt_rep ofs T
              val u = Op2 (oper, T, R, u1', sub u2)
            in
              if is_complete_type datatypes T orelse not opt1 then
                u
              else
                let
                  val x_u = BoundName (~1, T, unopt_R, "descr.x")
                  val R = R |> opt_rep ofs T
                in
                  Op3 (If, T, R,
                       Op2 (Exist, bool_T, Formula Pos, x_u,
                            s_op2 Apply bool_T (Formula Pos) (gsub false Pos u1)
                                  x_u), u, Cst (Unknown, T, R))
                end
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
            val R = if forall (curry (op =) Unit) Rs then Unit else Struct Rs
            val R' = (exists (is_opt_rep o rep_of) us ? opt_rep ofs T) R
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
            if polar = Neut orelse not (is_boolean_type (type_of u))
               orelse not (is_opt_rep (rep_of u)) then
              u
            else
              s_op1 Cast (type_of u) (Formula polar) u
          end
      end
      |> optimize_unit
  in aux table def Pos end

(* int -> Kodkod.n_ary_index list -> Kodkod.n_ary_index list
   -> int * Kodkod.n_ary_index list *)
fun fresh_n_ary_index n [] ys = (0, (n, 1) :: ys)
  | fresh_n_ary_index n ((m, j) :: xs) ys =
    if m = n then (j, ys @ ((m, j + 1) :: xs))
    else fresh_n_ary_index n xs ((m, j) :: ys)
(* int -> name_pool -> int * name_pool *)
fun fresh_rel n {rels, vars, formula_reg, rel_reg} =
  let val (j, rels') = fresh_n_ary_index n rels [] in
    (j, {rels = rels', vars = vars, formula_reg = formula_reg,
         rel_reg = rel_reg})
  end
(* int -> name_pool -> int * name_pool *)
fun fresh_var n {rels, vars, formula_reg, rel_reg} =
  let val (j, vars') = fresh_n_ary_index n vars [] in
    (j, {rels = rels, vars = vars', formula_reg = formula_reg,
         rel_reg = rel_reg})
  end
(* int -> name_pool -> int * name_pool *)
fun fresh_formula_reg {rels, vars, formula_reg, rel_reg} =
  (formula_reg, {rels = rels, vars = vars, formula_reg = formula_reg + 1,
                 rel_reg = rel_reg})
(* int -> name_pool -> int * name_pool *)
fun fresh_rel_reg {rels, vars, formula_reg, rel_reg} =
  (rel_reg, {rels = rels, vars = vars, formula_reg = formula_reg,
             rel_reg = rel_reg + 1})

(* nut -> nut list * name_pool * nut NameTable.table
   -> nut list * name_pool * nut NameTable.table *)
fun rename_plain_var v (ws, pool, table) =
  let
    val is_formula = (rep_of v = Formula Neut)
    val fresh = if is_formula then fresh_formula_reg else fresh_rel_reg
    val (j, pool) = fresh pool
    val constr = if is_formula then FormulaReg else RelReg
    val w = constr (j, type_of v, rep_of v)
  in (w :: ws, pool, NameTable.update (v, w) table) end

(* typ -> rep -> nut list -> nut *)
fun shape_tuple (T as Type ("*", [T1, T2])) (R as Struct [R1, R2]) us =
    let val arity1 = arity_of_rep R1 in
      Tuple (T, R, [shape_tuple T1 R1 (List.take (us, arity1)),
                    shape_tuple T2 R2 (List.drop (us, arity1))])
    end
  | shape_tuple (T as Type ("fun", [_, T2])) (R as Vect (k, R')) us =
    Tuple (T, R, map (shape_tuple T2 R') (batch_list (length us div k) us))
  | shape_tuple T R [u] =
    if type_of u = T then u else raise NUT ("Nitpick_Nut.shape_tuple", [u])
  | shape_tuple T Unit [] = Cst (Unity, T, Unit)
  | shape_tuple _ _ us = raise NUT ("Nitpick_Nut.shape_tuple", us)

(* bool -> nut -> nut list * name_pool * nut NameTable.table
   -> nut list * name_pool * nut NameTable.table *)
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
        val (j, pool) = fresh arity pool
        val w = constr ((arity, j), T, R, nick)
      in (w :: ws, pool, NameTable.update (v, w) table) end
  end

(* nut list -> name_pool -> nut NameTable.table
  -> nut list * name_pool * nut NameTable.table *)
fun rename_free_vars vs pool table =
  let
    val vs = filter (not_equal Unit o rep_of) vs
    val (vs, pool, table) = fold (rename_n_ary_var true) vs ([], pool, table)
  in (rev vs, pool, table) end

(* name_pool -> nut NameTable.table -> nut -> nut *)
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
    if rep_of u2 = Unit orelse inline_nut u2 then
      let
        val u2 = rename_vars_in_nut pool table u2
        val table = NameTable.update (u1, u2) table
      in rename_vars_in_nut pool table u3 end
    else
      let
        val bs = untuple I u1
        val (_, pool, table') = fold rename_plain_var bs ([], pool, table)
        val u11 = rename_vars_in_nut pool table' u1
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
