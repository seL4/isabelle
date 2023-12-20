(*  Title:      Pure/zterm.ML
    Author:     Makarius

Tight representation of types / terms / proof terms, notably for proof recording.
*)

(*** global ***)

(* types and terms *)

datatype ztyp =
    ZTVar of indexname * sort      (*free: index ~1*)
  | ZFun of ztyp * ztyp
  | ZProp
  | ZItself of ztyp
  | ZType0 of string               (*type constant*)
  | ZType1 of string * ztyp        (*type constructor: 1 argument*)
  | ZType of string * ztyp list    (*type constructor: >= 2 arguments*)

datatype zterm =
    ZVar of indexname * ztyp       (*free: index ~1*)
  | ZBound of int
  | ZConst0 of string              (*monomorphic constant*)
  | ZConst1 of string * ztyp       (*polymorphic constant: 1 type argument*)
  | ZConst of string * ztyp list   (*polymorphic constant: >= 2 type arguments*)
  | ZAbs of string * ztyp * zterm
  | ZApp of zterm * zterm
  | ZClass of ztyp * class         (*OFCLASS proposition*)

structure ZTerm =
struct

(* fold *)

fun fold_tvars f (ZTVar v) = f v
  | fold_tvars f (ZFun (T, U)) = fold_tvars f T #> fold_tvars f U
  | fold_tvars f (ZItself T) = fold_tvars f T
  | fold_tvars f (ZType1 (_, T)) = fold_tvars f T
  | fold_tvars f (ZType (_, Ts)) = fold (fold_tvars f) Ts
  | fold_tvars _ _ = I;

fun fold_aterms f (ZApp (t, u)) = fold_aterms f t #> fold_aterms f u
  | fold_aterms f (ZAbs (_, _, t)) = fold_aterms f t
  | fold_aterms f a = f a;

fun fold_types f (ZVar (_, T)) = f T
  | fold_types f (ZConst1 (_, T)) = f T
  | fold_types f (ZConst (_, As)) = fold f As
  | fold_types f (ZAbs (_, T, b)) = f T #> fold_types f b
  | fold_types f (ZApp (t, u)) = fold_types f t #> fold_types f u
  | fold_types f (ZClass (T, _)) = f T
  | fold_types _ _ = I;


(* type ordering *)

local

fun cons_nr (ZTVar _) = 0
  | cons_nr (ZFun _) = 1
  | cons_nr ZProp = 2
  | cons_nr (ZItself _) = 3
  | cons_nr (ZType0 _) = 4
  | cons_nr (ZType1 _) = 5
  | cons_nr (ZType _) = 6;

val fast_indexname_ord = Term_Ord.fast_indexname_ord;
val sort_ord = Term_Ord.sort_ord;

in

fun ztyp_ord TU =
  if pointer_eq TU then EQUAL
  else
    (case TU of
      (ZTVar (a, A), ZTVar (b, B)) =>
        (case fast_indexname_ord (a, b) of EQUAL => sort_ord (A, B) | ord => ord)
    | (ZFun (T, T'), ZFun (U, U')) =>
        (case ztyp_ord (T, U) of EQUAL => ztyp_ord (T', U') | ord => ord)
    | (ZProp, ZProp) => EQUAL
    | (ZItself T, ZItself U) => ztyp_ord (T, U)
    | (ZType0 a, ZType0 b) => fast_string_ord (a, b)
    | (ZType1 (a, T), ZType1 (b, U)) =>
        (case fast_string_ord (a, b) of EQUAL => ztyp_ord (T, U) | ord => ord)
    | (ZType (a, Ts), ZType (b, Us)) =>
        (case fast_string_ord (a, b) of EQUAL => dict_ord ztyp_ord (Ts, Us) | ord => ord)
    | (T, U) => int_ord (cons_nr T, cons_nr U));

end;


(* term ordering and alpha-conversion *)

local

fun cons_nr (ZVar _) = 0
  | cons_nr (ZBound _) = 1
  | cons_nr (ZConst0 _) = 2
  | cons_nr (ZConst1 _) = 3
  | cons_nr (ZConst _) = 4
  | cons_nr (ZAbs _) = 5
  | cons_nr (ZApp _) = 6
  | cons_nr (ZClass _) = 7;

fun struct_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (ZAbs (_, _, t), ZAbs (_, _, u)) => struct_ord (t, u)
    | (ZApp (t1, t2), ZApp (u1, u2)) =>
        (case struct_ord (t1, u1) of EQUAL => struct_ord (t2, u2) | ord => ord)
    | (t, u) => int_ord (cons_nr t, cons_nr u));

fun atoms_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (ZAbs (_, _, t), ZAbs (_, _, u)) => atoms_ord (t, u)
    | (ZApp (t1, t2), ZApp (u1, u2)) =>
        (case atoms_ord (t1, u1) of EQUAL => atoms_ord (t2, u2) | ord => ord)
    | (ZConst0 a, ZConst0 b) => fast_string_ord (a, b)
    | (ZConst1 (a, _), ZConst1 (b, _)) => fast_string_ord (a, b)
    | (ZConst (a, _), ZConst (b, _)) => fast_string_ord (a, b)
    | (ZVar (xi, _), ZVar (yj, _)) => Term_Ord.fast_indexname_ord (xi, yj)
    | (ZBound i, ZBound j) => int_ord (i, j)
    | (ZClass (_, a), ZClass (_, b)) => fast_string_ord (a, b)
    | _ => EQUAL);

fun types_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (ZAbs (_, T, t), ZAbs (_, U, u)) =>
        (case ztyp_ord (T, U) of EQUAL => types_ord (t, u) | ord => ord)
    | (ZApp (t1, t2), ZApp (u1, u2)) =>
        (case types_ord (t1, u1) of EQUAL => types_ord (t2, u2) | ord => ord)
    | (ZConst1 (_, T), ZConst1 (_, U)) => ztyp_ord (T, U)
    | (ZConst (_, Ts), ZConst (_, Us)) => dict_ord ztyp_ord (Ts, Us)
    | (ZVar (_, T), ZVar (_, U)) => ztyp_ord (T, U)
    | (ZClass (T, _), ZClass (U, _)) => ztyp_ord (T, U)
    | _ => EQUAL);

in

val fast_zterm_ord = struct_ord ||| atoms_ord ||| types_ord;

end;

fun aconv_zterm (tm1, tm2) =
  pointer_eq (tm1, tm2) orelse
    (case (tm1, tm2) of
      (ZApp (t1, u1), ZApp (t2, u2)) => aconv_zterm (t1, t2) andalso aconv_zterm (u1, u2)
    | (ZAbs (_, T1, t1), ZAbs (_, T2, t2)) => aconv_zterm (t1, t2) andalso T1 = T2
    | (a1, a2) => a1 = a2);

end;


(* tables and term items *)

structure ZTypes = Table(type key = ztyp val ord = ZTerm.ztyp_ord);
structure ZTerms = Table(type key = zterm val ord = ZTerm.fast_zterm_ord);

structure ZTVars:
sig
  include TERM_ITEMS
  val add_tvarsT: ztyp -> set -> set
  val add_tvars: zterm -> set -> set
end =
struct
  open TVars;
  val add_tvarsT = ZTerm.fold_tvars add_set;
  val add_tvars = ZTerm.fold_types add_tvarsT;
end;

structure ZVars:
sig
  include TERM_ITEMS
  val add_vars: zterm -> set -> set
end =
struct

structure Term_Items = Term_Items
(
  type key = indexname * ztyp;
  val ord = pointer_eq_ord (prod_ord Term_Ord.fast_indexname_ord ZTerm.ztyp_ord);
);
open Term_Items;

val add_vars = ZTerm.fold_aterms (fn ZVar v => add_set v | _ => I);

end;


(* proofs *)

datatype zproof_name =
    ZAxiom of string
  | ZOracle of string
  | ZBox of serial
  | ZThm of serial;

datatype zproof =
    ZDummy                         (*dummy proof*)
  | ZConstp of zproof_name * zterm * ztyp ZTVars.table * zterm ZVars.table
  | ZBoundp of int
  | ZHyp of zterm
  | ZAbst of string * ztyp * zproof
  | ZAbsp of string * zterm * zproof
  | ZAppt of zproof * zterm
  | ZAppp of zproof * zproof
  | ZClassp of ztyp * class;       (*OFCLASS proof from sorts algebra*)



(*** local ***)

signature ZTERM =
sig
  datatype ztyp = datatype ztyp
  datatype zterm = datatype zterm
  datatype zproof = datatype zproof
  exception ZTERM of string * ztyp list * zterm list * zproof list
  type zproof_const = zproof_name * zterm * ztyp ZTVars.table * zterm ZVars.table
  val fold_tvars: (indexname * sort -> 'a -> 'a) -> ztyp -> 'a -> 'a
  val fold_aterms: (zterm -> 'a -> 'a) -> zterm -> 'a -> 'a
  val fold_types: (ztyp -> 'a -> 'a) -> zterm -> 'a -> 'a
  val ztyp_ord: ztyp ord
  val fast_zterm_ord: zterm ord
  val aconv_zterm: zterm * zterm -> bool
  val ZAbsts: (string * ztyp) list -> zproof -> zproof
  val ZAbsps: zterm list -> zproof -> zproof
  val ZAppts: zproof * zterm list -> zproof
  val ZAppps: zproof * zproof list -> zproof
  val incr_bv_same: int -> int -> zterm Same.operation
  val incr_proof_bv_same: int -> int -> int -> int -> zproof Same.operation
  val incr_bv: int -> int -> zterm -> zterm
  val incr_boundvars: int -> zterm -> zterm
  val incr_proof_bv: int -> int -> int -> int -> zproof -> zproof
  val incr_proof_boundvars: int -> int -> zproof -> zproof
  val subst_term_bound_same: zterm -> int -> zterm Same.operation
  val subst_proof_bound_same: zterm -> int -> zproof Same.operation
  val subst_proof_boundp_same: zproof -> int -> int -> zproof Same.operation
  val subst_term_bound: zterm -> zterm -> zterm
  val subst_proof_bound: zterm -> zproof -> zproof
  val subst_proof_boundp: zproof -> zproof -> zproof
  val map_proof: ztyp Same.operation -> zterm Same.operation -> zproof -> zproof
  val map_proof_types: ztyp Same.operation -> zproof -> zproof
  val ztyp_of: typ -> ztyp
  val zterm_cache: theory -> {zterm: term -> zterm, ztyp: typ -> ztyp}
  val zterm_of: theory -> term -> zterm
  val typ_of: ztyp -> typ
  val term_of: theory -> zterm -> term
  val beta_norm_term_same: zterm Same.operation
  val beta_norm_proof_same: zproof Same.operation
  val beta_norm_prooft_same: zproof -> zproof
  val beta_norm_term: zterm -> zterm
  val beta_norm_proof: zproof -> zproof
  val beta_norm_prooft: zproof -> zproof
  val norm_type: Type.tyenv -> ztyp -> ztyp
  val norm_term: theory -> Envir.env -> zterm -> zterm
  val norm_proof: theory -> Envir.env -> term list -> zproof -> zproof
  type zbox = serial * (zterm * zproof)
  val zbox_ord: zbox ord
  type zboxes = zbox Ord_List.T
  val union_zboxes: zboxes -> zboxes -> zboxes
  val unions_zboxes: zboxes list -> zboxes
  val add_box_proof: theory -> term list -> term -> zboxes * zproof -> zboxes * zproof
  val thm_proof: theory -> term list -> term -> zproof -> zbox * zproof
  val axiom_proof:  theory -> string -> term -> zproof
  val oracle_proof:  theory -> string -> term -> zproof
  val assume_proof: theory -> term -> zproof
  val trivial_proof: theory -> term -> zproof
  val implies_intr_proof: theory -> term -> zproof -> zproof
  val forall_intr_proof: theory -> typ -> string * term -> zproof -> zproof
  val forall_elim_proof: theory -> term -> zproof -> zproof
  val of_class_proof: typ * class -> zproof
  val reflexive_proof: theory -> typ -> term -> zproof
  val symmetric_proof: theory -> typ -> term -> term -> zproof -> zproof
  val transitive_proof: theory -> typ -> term -> term -> term -> zproof -> zproof -> zproof
  val equal_intr_proof: theory -> term -> term -> zproof -> zproof -> zproof
  val equal_elim_proof: theory -> term -> term -> zproof -> zproof -> zproof
  val abstract_rule_proof: theory -> typ -> typ -> string * term -> term -> term -> zproof -> zproof
  val combination_proof: theory -> typ -> typ -> term -> term -> term -> term ->
    zproof -> zproof -> zproof
  val generalize_proof: Names.set * Names.set -> int -> zproof -> zproof
  val instantiate_proof: theory ->
    ((indexname * sort) * typ) list * ((indexname * typ) * term) list -> zproof -> zproof
  val varifyT_proof: ((string * sort) * (indexname * sort)) list -> zproof -> zproof
  val legacy_freezeT_proof: term -> zproof -> zproof
  val rotate_proof: theory -> term list -> term -> (string * typ) list ->
    term list -> int -> zproof -> zproof
  val permute_prems_proof: theory -> term list -> int -> int -> zproof -> zproof
  val incr_indexes_proof: int -> zproof -> zproof
  val lift_proof: theory -> term -> int -> term list -> zproof -> zproof
  val assumption_proof: theory -> Envir.env -> term list -> term -> int -> term list ->
    zproof -> zproof
  val bicompose_proof: theory -> Envir.env -> int -> bool -> term list -> term list ->
    term option -> term list -> int -> int -> term list -> zproof -> zproof -> zproof
end;

structure ZTerm: ZTERM =
struct

datatype ztyp = datatype ztyp;
datatype zterm = datatype zterm;
datatype zproof = datatype zproof;

exception ZTERM of string * ztyp list * zterm list * zproof list;

open ZTerm;


(* derived operations *)

val ZFuns = Library.foldr ZFun;

val ZAbsts = fold_rev (fn (x, T) => fn prf => ZAbst (x, T, prf));
val ZAbsps = fold_rev (fn t => fn prf => ZAbsp ("H", t, prf));

val ZAppts = Library.foldl ZAppt;
val ZAppps = Library.foldl ZAppp;

fun combound (t, n, k) =
  if k > 0 then ZApp (combound (t, n + 1, k - 1), ZBound n) else t;


(* increment bound variables *)

fun incr_bv_same inc =
  if inc = 0 then fn _ => Same.same
  else
    let
      fun term lev (ZBound i) =
            if i >= lev then ZBound (i + inc) else raise Same.SAME
        | term lev (ZAbs (a, T, t)) = ZAbs (a, T, term (lev + 1) t)
        | term lev (ZApp (t, u)) =
            (ZApp (term lev t, Same.commit (term lev) u)
              handle Same.SAME => ZApp (t, term lev u))
        | term _ _ = raise Same.SAME;
    in term end;

fun incr_proof_bv_same incp inct =
  if incp = 0 andalso inct = 0 then fn _ => fn _ => Same.same
  else
    let
      val term = incr_bv_same inct;

      fun proof plev _ (ZBoundp i) =
            if i >= plev then ZBoundp (i + incp) else raise Same.SAME
        | proof plev tlev (ZAbsp (a, t, p)) =
            (ZAbsp (a, term tlev t, Same.commit (proof (plev + 1) tlev) p)
              handle Same.SAME => ZAbsp (a, t, proof (plev + 1) tlev p))
        | proof plev tlev (ZAbst (a, T, p)) = ZAbst (a, T, proof plev (tlev + 1) p)
        | proof plev tlev (ZAppp (p, q)) =
            (ZAppp (proof plev tlev p, Same.commit (proof plev tlev) q)
              handle Same.SAME => ZAppp (p, proof plev tlev q))
        | proof plev tlev (ZAppt (p, t)) =
            (ZAppt (proof plev tlev p, Same.commit (term tlev) t)
              handle Same.SAME => ZAppt (p, term tlev t))
        | proof _ _ _ = raise Same.SAME;
    in proof end;

fun incr_bv inc lev = Same.commit (incr_bv_same inc lev);
fun incr_boundvars inc = incr_bv inc 0;

fun incr_proof_bv incp inct plev tlev = Same.commit (incr_proof_bv_same incp inct plev tlev);
fun incr_proof_boundvars incp inct = incr_proof_bv incp inct 0 0;


(* substitution of bound variables *)

fun subst_term_bound_same arg =
  let
    fun term lev (ZBound i) =
          if i < lev then raise Same.SAME   (*var is locally bound*)
          else if i = lev then incr_boundvars lev arg
          else ZBound (i - 1)   (*loose: change it*)
      | term lev (ZAbs (a, T, t)) = ZAbs (a, T, term (lev + 1) t)
      | term lev (ZApp (t, u)) =
          (ZApp (term lev t, Same.commit (term lev) u)
            handle Same.SAME => ZApp (t, term lev u))
      | term _ _ = raise Same.SAME;
  in term end;

fun subst_proof_bound_same arg =
  let
    val term = subst_term_bound_same arg;

    fun proof lev (ZAbsp (a, t, p)) =
          (ZAbsp (a, term lev t, Same.commit (proof lev) p)
            handle Same.SAME => ZAbsp (a, t, proof lev p))
      | proof lev (ZAbst (a, T, p)) = ZAbst (a, T, proof (lev + 1) p)
      | proof lev (ZAppp (p, q)) =
          (ZAppp (proof lev p, Same.commit (proof lev) q)
            handle Same.SAME => ZAppp (p, proof lev q))
      | proof lev (ZAppt (p, t)) =
          (ZAppt (proof lev p, Same.commit (term lev) t)
            handle Same.SAME => ZAppt (p, term lev t))
      | proof _ _ = raise Same.SAME;
  in proof end;

fun subst_proof_boundp_same arg =
  let
    fun proof plev tlev (ZBoundp i) =
          if i < plev then raise Same.SAME   (*var is locally bound*)
          else if i = plev then incr_proof_boundvars plev tlev arg
          else ZBoundp (i - 1)   (*loose: change it*)
      | proof plev tlev (ZAbsp (a, t, p)) = ZAbsp (a, t, proof (plev + 1) tlev p)
      | proof plev tlev (ZAbst (a, T, p)) = ZAbst (a, T, proof plev (tlev + 1) p)
      | proof plev tlev (ZAppp (p, q)) =
          (ZAppp (proof plev tlev p, Same.commit (proof plev tlev) q)
            handle Same.SAME => ZAppp (p, proof plev tlev q))
      | proof plev tlev (ZAppt (p, t)) = ZAppt (proof plev tlev p, t)
      | proof _ _ _ = raise Same.SAME;
  in proof end;

fun subst_term_bound arg body = Same.commit (subst_term_bound_same arg 0) body;
fun subst_proof_bound arg body = Same.commit (subst_proof_bound_same arg 0) body;
fun subst_proof_boundp arg body = Same.commit (subst_proof_boundp_same arg 0 0) body;


(* substitution of free or schematic variables *)

fun subst_type_same tvar =
  let
    fun typ (ZTVar x) = tvar x
      | typ (ZFun (T, U)) = (ZFun (typ T, Same.commit typ U) handle Same.SAME => ZFun (T, typ U))
      | typ ZProp = raise Same.SAME
      | typ (ZItself T) = ZItself (typ T)
      | typ (ZType0 _) = raise Same.SAME
      | typ (ZType1 (a, T)) = ZType1 (a, typ T)
      | typ (ZType (a, Ts)) = ZType (a, Same.map typ Ts);
  in typ end;

fun subst_term_same typ var =
  let
    fun term (ZVar (x, T)) =
          let val (T', same) = Same.commit_id typ T in
            (case Same.catch var (x, T') of
              NONE => if same then raise Same.SAME else ZVar (x, T')
            | SOME t' => t')
          end
      | term (ZBound _) = raise Same.SAME
      | term (ZConst0 _) = raise Same.SAME
      | term (ZConst1 (a, T)) = ZConst1 (a, typ T)
      | term (ZConst (a, Ts)) = ZConst (a, Same.map typ Ts)
      | term (ZAbs (a, T, t)) =
          (ZAbs (a, typ T, Same.commit term t) handle Same.SAME => ZAbs (a, T, term t))
      | term (ZApp (t, u)) =
          (ZApp (term t, Same.commit term u) handle Same.SAME => ZApp (t, term u))
      | term (ZClass (T, c)) = ZClass (typ T, c);
  in term end;

fun instantiate_type_same instT =
  if ZTVars.is_empty instT then Same.same
  else ZTypes.unsynchronized_cache (subst_type_same (Same.function (ZTVars.lookup instT)));

fun instantiate_term_same typ inst =
  subst_term_same typ (Same.function (ZVars.lookup inst));


(* map types/terms within proof *)

fun map_insts_same typ term (instT, inst) =
  let
    val changed = Unsynchronized.ref false;
    fun apply f x =
      (case Same.catch f x of
        NONE => NONE
      | some => (changed := true; some));

    val instT' =
      (instT, instT) |-> ZTVars.fold (fn (v, T) =>
        (case apply typ T of
          NONE => I
        | SOME T' => ZTVars.update (v, T')));

    val vars' =
      (inst, ZVars.empty) |-> ZVars.fold (fn ((v, T), _) =>
        (case apply typ T of
          NONE => I
        | SOME T' => ZVars.add ((v, T), (v, T'))));

    val inst' =
      if ZVars.is_empty vars' then
        (inst, inst) |-> ZVars.fold (fn (v, t) =>
          (case apply term t of
            NONE => I
          | SOME t' => ZVars.update (v, t')))
      else
        ZVars.dest inst
        |> map (fn (v, t) => (the_default v (ZVars.lookup vars' v), the_default t (apply term t)))
        |> ZVars.make_strict;
  in if ! changed then (instT', inst') else raise Same.SAME end;

fun map_proof_same typ term =
  let
    fun proof ZDummy = raise Same.SAME
      | proof (ZConstp (a, A, instT, inst)) =
          let val (instT', inst') = map_insts_same typ term (instT, inst)
          in ZConstp (a, A, instT', inst') end
      | proof (ZBoundp _) = raise Same.SAME
      | proof (ZHyp _) = raise Same.SAME
      | proof (ZAbst (a, T, p)) =
          (ZAbst (a, typ T, Same.commit proof p) handle Same.SAME => ZAbst (a, T, proof p))
      | proof (ZAbsp (a, t, p)) =
          (ZAbsp (a, term t, Same.commit proof p) handle Same.SAME => ZAbsp (a, t, proof p))
      | proof (ZAppt (p, t)) =
          (ZAppt (proof p, Same.commit term t) handle Same.SAME => ZAppt (p, term t))
      | proof (ZAppp (p, q)) =
          (ZAppp (proof p, Same.commit proof q) handle Same.SAME => ZAppp (p, proof q))
      | proof (ZClassp (T, c)) = ZClassp (typ T, c);
  in proof end;

fun map_proof typ term = Same.commit (map_proof_same typ term);
fun map_proof_types typ = map_proof typ (subst_term_same typ Same.same);


(* convert ztyp / zterm vs. regular typ / term *)

fun ztyp_of (TFree (a, S)) = ZTVar ((a, ~1), S)
  | ztyp_of (TVar v) = ZTVar v
  | ztyp_of (Type ("fun", [T, U])) = ZFun (ztyp_of T, ztyp_of U)
  | ztyp_of (Type (c, [])) = if c = "prop" then ZProp else ZType0 c
  | ztyp_of (Type (c, [T])) = if c = "itself" then ZItself (ztyp_of T) else ZType1 (c, ztyp_of T)
  | ztyp_of (Type (c, ts)) = ZType (c, map ztyp_of ts);

fun ztyp_cache () = Typtab.unsynchronized_cache ztyp_of;

fun zterm_cache thy =
  let
    val typargs = Consts.typargs (Sign.consts_of thy);

    val ztyp = ztyp_cache ();

    fun zterm (Free (x, T)) = ZVar ((x, ~1), ztyp T)
      | zterm (Var (xi, T)) = ZVar (xi, ztyp T)
      | zterm (Bound i) = ZBound i
      | zterm (Const (c, T)) =
          (case typargs (c, T) of
            [] => ZConst0 c
          | [T] => ZConst1 (c, ztyp T)
          | Ts => ZConst (c, map ztyp Ts))
      | zterm (Abs (a, T, b)) = ZAbs (a, ztyp T, zterm b)
      | zterm ((t as Const (c, _)) $ (u as Const ("Pure.type", _))) =
          if String.isSuffix Logic.class_suffix c then
            ZClass (ztyp (Logic.dest_type u), Logic.class_of_const c)
          else ZApp (zterm t, zterm u)
      | zterm (t $ u) = ZApp (zterm t, zterm u);
  in {ztyp = ztyp, zterm = zterm} end;

val zterm_of = #zterm o zterm_cache;

fun typ_of (ZTVar ((a, ~1), S)) = TFree (a, S)
  | typ_of (ZTVar v) = TVar v
  | typ_of (ZFun (T, U)) = typ_of T --> typ_of U
  | typ_of ZProp = propT
  | typ_of (ZItself T) = Term.itselfT (typ_of T)
  | typ_of (ZType0 c) = Type (c, [])
  | typ_of (ZType1 (c, T)) = Type (c, [typ_of T])
  | typ_of (ZType (c, Ts)) = Type (c, map typ_of Ts);

fun typ_cache () = ZTypes.unsynchronized_cache typ_of;

fun term_of thy =
  let
    val instance = Consts.instance (Sign.consts_of thy);

    fun const (c, Ts) = Const (c, instance (c, Ts));

    fun term (ZVar ((x, ~1), T)) = Free (x, typ_of T)
      | term (ZVar (xi, T)) = Var (xi, typ_of T)
      | term (ZBound i) = Bound i
      | term (ZConst0 c) = const (c, [])
      | term (ZConst1 (c, T)) = const (c, [typ_of T])
      | term (ZConst (c, Ts)) = const (c, map typ_of Ts)
      | term (ZAbs (a, T, b)) = Abs (a, typ_of T, term b)
      | term (ZApp (t, u)) = term t $ term u
      | term (ZClass (T, c)) = Logic.mk_of_class (typ_of T, c);
  in term end;


(* beta contraction *)

val beta_norm_term_same =
  let
    fun norm (ZAbs (a, T, t)) = ZAbs (a, T, Same.commit norm t)
      | norm (ZApp (ZAbs (_, _, body), t)) = Same.commit norm (subst_term_bound t body)
      | norm (ZApp (f, t)) =
          ((case norm f of
             ZAbs (_, _, body) => Same.commit norm (subst_term_bound t body)
           | nf => ZApp (nf, Same.commit norm t))
          handle Same.SAME => ZApp (f, norm t))
      | norm _ = raise Same.SAME;
  in norm end;

val beta_norm_prooft_same =
  let
    val term = beta_norm_term_same;

    fun norm (ZAbst (a, T, p)) = ZAbst (a, T, norm p)
      | norm (ZAppt (ZAbst (_, _, body), t)) = Same.commit norm (subst_proof_bound t body)
      | norm (ZAppt (f, t)) =
          ((case norm f of
             ZAbst (_, _, body) => Same.commit norm (subst_proof_bound t body)
           | nf => ZAppt (nf, Same.commit term t))
          handle Same.SAME => ZAppt (f, term t))
      | norm _ = raise Same.SAME;
  in norm end;

val beta_norm_proof_same =
  let
    val term = beta_norm_term_same;

    fun norm (ZAbst (a, T, p)) = ZAbst (a, T, norm p)
      | norm (ZAbsp (a, t, p)) =
          (ZAbsp (a, term t, Same.commit norm p)
            handle Same.SAME => ZAbsp (a, t, norm p))
      | norm (ZAppt (ZAbst (_, _, body), t)) = Same.commit norm (subst_proof_bound t body)
      | norm (ZAppp (ZAbsp (_, _, body), p)) = Same.commit norm (subst_proof_boundp p body)
      | norm (ZAppt (f, t)) =
          ((case norm f of
             ZAbst (_, _, body) => Same.commit norm (subst_proof_bound t body)
           | nf => ZAppt (nf, Same.commit term t))
          handle Same.SAME => ZAppt (f, term t))
      | norm (ZAppp (f, p)) =
          ((case norm f of
             ZAbsp (_, _, body) => Same.commit norm (subst_proof_boundp p body)
           | nf => ZAppp (nf, Same.commit norm p))
          handle Same.SAME => ZAppp (f, norm p))
      | norm _ = raise Same.SAME;
  in norm end;

val beta_norm_term = Same.commit beta_norm_term_same;
val beta_norm_proof = Same.commit beta_norm_proof_same;
val beta_norm_prooft = Same.commit beta_norm_prooft_same;


(* normalization wrt. environment and beta contraction *)

fun norm_type_same ztyp tyenv =
  if Vartab.is_empty tyenv then Same.same
  else
    let
      fun norm (ZTVar v) =
            (case Type.lookup tyenv v of
              SOME U => Same.commit norm (ztyp U)
            | NONE => raise Same.SAME)
        | norm (ZFun (T, U)) =
            (ZFun (norm T, Same.commit norm U)
              handle Same.SAME => ZFun (T, norm U))
        | norm ZProp = raise Same.SAME
        | norm (ZItself T) = ZItself (norm T)
        | norm (ZType0 _) = raise Same.SAME
        | norm (ZType1 (a, T)) = ZType1 (a, norm T)
        | norm (ZType (a, Ts)) = ZType (a, Same.map norm Ts);
    in norm end;

fun norm_term_same {ztyp, zterm, typ} (envir as Envir.Envir {tyenv, tenv, ...}) =
  let
    val lookup =
      if Vartab.is_empty tenv then K NONE
      else ZVars.unsynchronized_cache (apsnd typ #> Envir.lookup envir #> Option.map zterm);

    val normT = norm_type_same ztyp tyenv;

    fun norm (ZVar (xi, T)) =
          (case lookup (xi, T) of
            SOME u => Same.commit norm u
          | NONE => ZVar (xi, normT T))
      | norm (ZBound _) = raise Same.SAME
      | norm (ZConst0 _) = raise Same.SAME
      | norm (ZConst1 (a, T)) = ZConst1 (a, normT T)
      | norm (ZConst (a, Ts)) = ZConst (a, Same.map normT Ts)
      | norm (ZAbs (a, T, t)) =
          (ZAbs (a, normT T, Same.commit norm t)
            handle Same.SAME => ZAbs (a, T, norm t))
      | norm (ZApp (ZAbs (_, _, body), t)) = Same.commit norm (subst_term_bound t body)
      | norm (ZApp (f, t)) =
          ((case norm f of
             ZAbs (_, _, body) => Same.commit norm (subst_term_bound t body)
           | nf => ZApp (nf, Same.commit norm t))
          handle Same.SAME => ZApp (f, norm t))
      | norm _ = raise Same.SAME;
  in fn t => if Envir.is_empty envir then beta_norm_term_same t else norm t end;

fun norm_proof_cache (cache as {ztyp, ...}) (envir as Envir.Envir {tyenv, ...}) =
  let
    val norm_tvar = ZTVar #> Same.commit (norm_type_same ztyp tyenv);
    val norm_var = ZVar #> Same.commit (norm_term_same cache envir);
  in
    fn visible => fn prf =>
      if Envir.is_empty envir orelse null visible then beta_norm_prooft prf
      else
        let
          fun add_tvar v tab =
            if ZTVars.defined tab v then tab else ZTVars.update (v, norm_tvar v) tab;

          val inst_typ =
            if Vartab.is_empty tyenv then Same.same
            else
              ZTVars.build (visible |> (fold o Term.fold_types o Term.fold_atyps)
                (fn TVar v => add_tvar v | _ => I))
              |> instantiate_type_same;

          fun add_var (a, T) tab =
            let val v = (a, Same.commit inst_typ (ztyp T))
            in if ZVars.defined tab v then tab else ZVars.update (v, norm_var v) tab end;

          val inst_term =
            ZVars.build (visible |> (fold o Term.fold_aterms) (fn Var v => add_var v | _ => I))
            |> instantiate_term_same inst_typ;

          val norm_term = Same.compose beta_norm_term_same inst_term;
        in beta_norm_prooft (map_proof inst_typ norm_term prf) end
  end;

fun norm_cache thy =
  let
    val {ztyp, zterm} = zterm_cache thy;
    val typ = typ_cache ();
  in {ztyp = ztyp, zterm = zterm, typ = typ} end;

fun norm_type tyenv = Same.commit (norm_type_same (ztyp_cache ()) tyenv);
fun norm_term thy envir = Same.commit (norm_term_same (norm_cache thy) envir);
fun norm_proof thy envir = norm_proof_cache (norm_cache thy) envir;



(** proof construction **)

(* constants *)

type zproof_const = zproof_name * zterm * ztyp ZTVars.table * zterm ZVars.table;

fun zproof_const a A : zproof_const =
  let
    val instT =
      ZTVars.build (A |> (fold_types o fold_tvars) (fn v => fn tab =>
        if ZTVars.defined tab v then tab else ZTVars.update (v, ZTVar v) tab));
    val inst =
      ZVars.build (A |> fold_aterms (fn t => fn tab =>
        (case t of
          ZVar v => if ZVars.defined tab v then tab else ZVars.update (v, t) tab
        | _ => tab)));
  in (a, A, instT, inst) end;

fun make_const_proof (f, g) (a, A, instT, inst) =
  let
    val instT' = ZTVars.map (fn ((x, _), _) => fn y => the_default y (try f x)) instT;
    val inst' = ZVars.map (fn ((x, _), _) => fn y => the_default y (try g x)) inst;
  in ZConstp (a, A, instT', inst') end;


(* closed proof boxes *)

type zbox = serial * (zterm * zproof);
val zbox_ord: zbox ord = fn ((i, _), (j, _)) => int_ord (j, i);

type zboxes = zbox Ord_List.T;
val union_zboxes = Ord_List.union zbox_ord;
val unions_zboxes = Ord_List.unions zbox_ord;
val add_zboxes = Ord_List.insert zbox_ord;

local

fun close_prop hyps concl =
  fold_rev (fn A => fn B => ZApp (ZApp (ZConst0 "Pure.imp", A), B)) hyps concl;

fun close_proof hyps prf =
  let
    val m = length hyps - 1;
    val bounds = ZTerms.build (hyps |> fold_index (fn (i, h) => ZTerms.update (h, m - i)));

    fun proof lev (ZHyp t) =
          (case ZTerms.lookup bounds t of
            SOME i => ZBoundp (lev + i)
          | NONE => raise ZTERM ("Unbound proof hypothesis", [], [t], []))
      | proof lev (ZAbst (x, T, p)) = ZAbst (x, T, proof lev p)
      | proof lev (ZAbsp (x, t, p)) = ZAbsp (x, t, proof (lev + 1) p)
      | proof lev (ZAppt (p, t)) = ZAppt (proof lev p, t)
      | proof lev (ZAppp (p, q)) =
          (ZAppp (proof lev p, Same.commit (proof lev) q) handle Same.SAME =>
            ZAppp (p, proof lev q))
      | proof _ _ = raise Same.SAME;
  in ZAbsps hyps (Same.commit (proof 0) prf) end;

fun box_proof zproof_name thy hyps concl prf =
  let
    val {zterm, ...} = zterm_cache thy;
    val hyps' = map zterm hyps;
    val concl' = zterm concl;

    val prop' = beta_norm_term (close_prop hyps' concl');
    val prf' = beta_norm_prooft (close_proof hyps' prf);

    val i = serial ();
    val zbox: zbox = (i, (prop', prf'));
    val zbox_prf = ZAppts (ZConstp (zproof_const (zproof_name i) prop'), hyps');
  in (zbox, zbox_prf) end;

in

val thm_proof = box_proof ZThm;

fun add_box_proof thy hyps concl (zboxes, prf) =
  let val (zbox, zbox_prf) = box_proof ZBox thy hyps concl prf
  in (add_zboxes zbox zboxes, zbox_prf) end;

end;


(* basic logic *)

fun axiom_proof thy name A =
  ZConstp (zproof_const (ZAxiom name) (zterm_of thy A));

fun oracle_proof thy name A =
  ZConstp (zproof_const (ZOracle name) (zterm_of thy A));

fun assume_proof thy A =
  ZHyp (zterm_of thy A);

fun trivial_proof thy A =
  ZAbsp ("H", zterm_of thy A, ZBoundp 0);

fun implies_intr_proof thy A prf =
  let
    val h = zterm_of thy A;
    fun proof lev (ZHyp t) = if aconv_zterm (h, t) then ZBoundp lev else raise Same.SAME
      | proof lev (ZAbst (x, T, p)) = ZAbst (x, T, proof lev p)
      | proof lev (ZAbsp (x, t, p)) = ZAbsp (x, t, proof (lev + 1) p)
      | proof lev (ZAppt (p, t)) = ZAppt (proof lev p, t)
      | proof lev (ZAppp (p, q)) =
          (ZAppp (proof lev p, Same.commit (proof lev) q) handle Same.SAME =>
            ZAppp (p, proof lev q))
      | proof _ _ = raise Same.SAME;
  in ZAbsp ("H", h, Same.commit (proof 0) prf) end;

fun forall_intr_proof thy T (a, x) prf =
  let
    val {ztyp, zterm} = zterm_cache thy;
    val Z = ztyp T;
    val z = zterm x;

    fun term i b =
      if aconv_zterm (b, z) then ZBound i
      else
        (case b of
          ZAbs (x, T, t) => ZAbs (x, T, term (i + 1) t)
        | ZApp (t, u) =>
            (ZApp (term i t, Same.commit (term i) u) handle Same.SAME =>
              ZApp (t, term i u))
        | _ => raise Same.SAME);

    fun proof i (ZAbst (x, T, prf)) = ZAbst (x, T, proof (i + 1) prf)
      | proof i (ZAbsp (x, t, prf)) =
          (ZAbsp (x, term i t, Same.commit (proof i) prf) handle Same.SAME =>
            ZAbsp (x, t, proof i prf))
      | proof i (ZAppt (p, t)) =
          (ZAppt (proof i p, Same.commit (term i) t) handle Same.SAME =>
            ZAppt (p, term i t))
      | proof i (ZAppp (p, q)) =
          (ZAppp (proof i p, Same.commit (proof i) q) handle Same.SAME =>
            ZAppp (p, proof i q))
      | proof _ _ = raise Same.SAME;

  in ZAbst (a, Z, Same.commit (proof 0) prf) end;

fun forall_elim_proof thy t p = ZAppt (p, zterm_of thy t);

fun of_class_proof (T, c) = ZClassp (ztyp_of T, c);


(* equality *)

local

val thy0 =
  Context.the_global_context ()
  |> Sign.add_types_global [(Binding.name "fun", 2, NoSyn), (Binding.name "prop", 0, NoSyn)]
  |> Sign.local_path
  |> Sign.add_consts
   [(Binding.name "all", (Term.aT [] --> propT) --> propT, NoSyn),
    (Binding.name "imp", propT --> propT --> propT, NoSyn),
    (Binding.name "eq", Term.aT [] --> Term.aT [] --> propT, NoSyn)];

val [reflexive_axiom, symmetric_axiom, transitive_axiom, equal_intr_axiom, equal_elim_axiom,
  abstract_rule_axiom, combination_axiom] =
    Theory.equality_axioms |> map (fn (b, t) =>
      let val ZConstp c = axiom_proof thy0 (Sign.full_name thy0 b) t in c end);

in

val is_reflexive_proof =
  fn ZConstp (ZAxiom "Pure.reflexive", _, _, _) => true | _ => false;

fun reflexive_proof thy T t =
  let
    val {ztyp, zterm} = zterm_cache thy;
    val A = ztyp T;
    val x = zterm t;
  in make_const_proof (fn "'a" => A, fn "x" => x) reflexive_axiom end;

fun symmetric_proof thy T t u prf =
  if is_reflexive_proof prf then prf
  else
    let
      val {ztyp, zterm} = zterm_cache thy;
      val A = ztyp T;
      val x = zterm t;
      val y = zterm u;
      val ax = make_const_proof (fn "'a" => A, fn "x" => x | "y" => y) symmetric_axiom;
    in ZAppp (ax, prf) end;

fun transitive_proof thy T t u v prf1 prf2 =
  if is_reflexive_proof prf1 then prf2
  else if is_reflexive_proof prf2 then prf1
  else
    let
      val {ztyp, zterm} = zterm_cache thy;
      val A = ztyp T;
      val x = zterm t;
      val y = zterm u;
      val z = zterm v;
      val ax = make_const_proof (fn "'a" => A, fn "x" => x | "y" => y | "z" => z) transitive_axiom;
    in ZAppp (ZAppp (ax, prf1), prf2) end;

fun equal_intr_proof thy t u prf1 prf2 =
  let
    val {zterm, ...} = zterm_cache thy;
    val A = zterm t;
    val B = zterm u;
    val ax = make_const_proof (undefined, fn "A" => A | "B" => B) equal_intr_axiom;
  in ZAppp (ZAppp (ax, prf1), prf2) end;

fun equal_elim_proof thy t u prf1 prf2 =
  let
    val {zterm, ...} = zterm_cache thy;
    val A = zterm t;
    val B = zterm u;
    val ax = make_const_proof (undefined, fn "A" => A | "B" => B) equal_elim_axiom;
  in ZAppp (ZAppp (ax, prf1), prf2) end;

fun abstract_rule_proof thy T U x t u prf =
  let
    val {ztyp, zterm} = zterm_cache thy;
    val A = ztyp T;
    val B = ztyp U;
    val f = zterm t;
    val g = zterm u;
    val ax =
      make_const_proof (fn "'a" => A | "'b" => B, fn "f" => f | "g" => g)
        abstract_rule_axiom;
  in ZAppp (ax, forall_intr_proof thy T x prf) end;

fun combination_proof thy T U f g t u prf1 prf2 =
  let
    val {ztyp, zterm} = zterm_cache thy;
    val A = ztyp T;
    val B = ztyp U;
    val f' = zterm f;
    val g' = zterm g;
    val x = zterm t;
    val y = zterm u;
    val ax =
      make_const_proof (fn "'a" => A | "'b" => B, fn "f" => f' | "g" => g' | "x" => x | "y" => y)
        combination_axiom;
  in ZAppp (ZAppp (ax, prf1), prf2) end;

end;


(* substitution *)

fun generalize_proof (tfrees, frees) idx prf =
  let
    val typ =
      if Names.is_empty tfrees then Same.same else
        ZTypes.unsynchronized_cache
          (subst_type_same (fn ((a, i), S) =>
            if i = ~1 andalso Names.defined tfrees a then ZTVar ((a, idx), S)
            else raise Same.SAME));
    val term =
      subst_term_same typ (fn ((x, i), T) =>
        if i = ~1 andalso Names.defined frees x then ZVar ((x, idx), T)
        else raise Same.SAME);
  in map_proof typ term prf end;

fun instantiate_proof thy (Ts, ts) prf =
  let
    val {ztyp, zterm} = zterm_cache thy;
    val instT = ZTVars.build (Ts |> fold (fn (v, T) => ZTVars.add (v, ztyp T)));
    val inst = ZVars.build (ts |> fold (fn ((v, T), t) => ZVars.add ((v, ztyp T), zterm t)));
    val typ = instantiate_type_same instT;
    val term = instantiate_term_same typ inst;
  in map_proof typ term prf end;

fun varifyT_proof names prf =
  if null names then prf
  else
    let
      val tab = ZTVars.build (names |> fold (fn ((a, S), b) => ZTVars.add (((a, ~1), S), b)));
      val typ =
        ZTypes.unsynchronized_cache (subst_type_same (fn v =>
          (case ZTVars.lookup tab v of
            NONE => raise Same.SAME
          | SOME w => ZTVar w)));
    in map_proof_types typ prf end;

fun legacy_freezeT_proof t prf =
  (case Type.legacy_freezeT t of
    NONE => prf
  | SOME f =>
      let
        val tvar = ztyp_of o Same.function f;
        val typ = ZTypes.unsynchronized_cache (subst_type_same tvar);
      in map_proof_types typ prf end);


(* permutations *)

fun rotate_proof thy Bs Bi' params asms m prf =
  let
    val {ztyp, zterm} = zterm_cache thy;
    val i = length asms;
    val j = length Bs;
  in
    ZAbsps (map zterm Bs @ [zterm Bi']) (ZAppps (prf, map ZBoundp
      (j downto 1) @ [ZAbsts (map (apsnd ztyp) params) (ZAbsps (map zterm asms)
        (ZAppps (ZAppts (ZBoundp i, map ZBound ((length params - 1) downto 0)),
          map ZBoundp (((i-m-1) downto 0) @ ((i-1) downto (i-m))))))]))
  end;

fun permute_prems_proof thy prems' j k prf =
  let
    val {zterm, ...} = zterm_cache thy;
    val n = length prems';
  in
    ZAbsps (map zterm prems')
      (ZAppps (prf, map ZBoundp ((n-1 downto n-j) @ (k-1 downto 0) @ (n-j-1 downto k))))
  end;


(* lifting *)

fun incr_tvar_same inc =
  if inc = 0 then Same.same
  else
    let fun tvar ((a, i), S) = if i >= 0 then ZTVar ((a, i + inc), S) else raise Same.SAME
    in ZTypes.unsynchronized_cache (subst_type_same tvar) end;

fun incr_indexes_proof inc prf =
  let
    val typ = incr_tvar_same inc;
    fun var ((x, i), T) = if i >= 0 then ZVar ((x, i + inc), T) else raise Same.SAME;
    val term = subst_term_same typ var;
  in map_proof typ term prf end;

fun lift_proof thy gprop inc prems prf =
  let
    val {ztyp, zterm} = zterm_cache thy;

    val typ = incr_tvar_same inc;

    fun term Ts lev =
      if null Ts andalso inc = 0 then Same.same
      else
        let
          val n = length Ts;
          fun incr lev (ZVar ((x, i), T)) =
                if i >= 0 then combound (ZVar ((x, i + inc), ZFuns (Ts, Same.commit typ T)), lev, n)
                else raise Same.SAME
            | incr _ (ZBound _) = raise Same.SAME
            | incr _ (ZConst0 _) = raise Same.SAME
            | incr _ (ZConst1 (c, T)) = ZConst1 (c, typ T)
            | incr _ (ZConst (c, Ts)) = ZConst (c, Same.map typ Ts)
            | incr lev (ZAbs (x, T, t)) =
                (ZAbs (x, typ T, Same.commit (incr (lev + 1)) t)
                  handle Same.SAME => ZAbs (x, T, incr (lev + 1) t))
            | incr lev (ZApp (t, u)) =
                (ZApp (incr lev t, Same.commit (incr lev) u)
                  handle Same.SAME => ZApp (t, incr lev u))
            | incr _ (ZClass (T, c)) = ZClass (typ T, c);
        in incr lev end;

    fun proof Ts lev (ZAbst (a, T, p)) =
          (ZAbst (a, typ T, Same.commit (proof Ts (lev + 1)) p)
            handle Same.SAME => ZAbst (a, T, proof Ts (lev + 1) p))
      | proof Ts lev (ZAbsp (a, t, p)) =
          (ZAbsp (a, term Ts lev t, Same.commit (proof Ts lev) p)
            handle Same.SAME => ZAbsp (a, t, proof Ts lev p))
      | proof Ts lev (ZAppt (p, t)) =
          (ZAppt (proof Ts lev p, Same.commit (term Ts lev) t)
            handle Same.SAME => ZAppt (p, term Ts lev t))
      | proof Ts lev (ZAppp (p, q)) =
          (ZAppp (proof Ts lev p, Same.commit (proof Ts lev) q)
            handle Same.SAME => ZAppp (p, proof Ts lev q))
      | proof Ts lev (ZConstp (a, A, instT, inst)) =
          let val (instT', insts') = map_insts_same typ (term Ts lev) (instT, inst)
          in ZConstp (a, A, instT', insts') end
      | proof _ _ (ZClassp (T, c)) = ZClassp (typ T, c)
      | proof _ _ _ = raise Same.SAME;

    val k = length prems;

    fun mk_app b (i, j, p) =
      if b then (i - 1, j, ZAppp (p, ZBoundp i)) else (i, j - 1, ZAppt (p, ZBound j));

    fun lift Ts bs i j (Const ("Pure.imp", _) $ A $ B) =
          ZAbsp ("H", Same.commit (term Ts 0) (zterm A), lift Ts (true :: bs) (i + 1) j B)
      | lift Ts bs i j (Const ("Pure.all", _) $ Abs (a, T, t)) =
          let val T' = ztyp T
          in ZAbst (a, T', lift (T' :: Ts) (false :: bs) i (j + 1) t) end
      | lift Ts bs i j _ =
          ZAppps (Same.commit (proof (rev Ts) 0) prf,
            map (fn k => (#3 (fold_rev mk_app bs (i - 1, j - 1, ZBoundp k)))) (i + k - 1 downto i));
  in ZAbsps (map zterm prems) (lift [] [] 0 0 gprop) end;


(* higher-order resolution *)

fun mk_asm_prf C i m =
  let
    fun imp _ i 0 = ZBoundp i
      | imp (ZApp (ZApp (ZConst0 "Pure.imp", A), B)) i m = ZAbsp ("H", A, imp B (i + 1) (m - 1))
      | imp _ i _ = ZBoundp i;
    fun all (ZApp (ZConst1 ("Pure.all", _), ZAbs (a, T, t))) = ZAbst (a, T, all t)
      | all t = imp t (~ i) m
  in all C end;

fun assumption_proof thy envir Bs Bi n visible prf =
  let
    val cache as {zterm, ...} = norm_cache thy;
    val normt = zterm #> Same.commit (norm_term_same cache envir);
  in
    ZAbsps (map normt Bs)
      (ZAppps (prf, map ZBoundp (length Bs - 1 downto 0) @ [mk_asm_prf (normt Bi) n ~1]))
    |> norm_proof_cache cache envir visible
  end;

fun flatten_params_proof i j n (ZApp (ZApp (ZConst0 "Pure.imp", A), B), k) =
      ZAbsp ("H", A, flatten_params_proof (i + 1) j n (B, k))
  | flatten_params_proof i j n (ZApp (ZConst1 ("Pure.all", _), ZAbs (a, T, t)), k) =
      ZAbst (a, T, flatten_params_proof i (j + 1) n (t, k))
  | flatten_params_proof i j n (_, k) =
      ZAppps (ZAppts (ZBoundp (k + i),
        map ZBound (j - 1 downto 0)), map ZBoundp (remove (op =) (i - n) (i - 1 downto 0)));

fun bicompose_proof thy env smax flatten Bs As A oldAs n m visible rprf sprf =
  let
    val cache as {zterm, ...} = norm_cache thy;
    val normt = zterm #> Same.commit (norm_term_same cache env);
    val normp = norm_proof_cache cache env visible;

    val lb = length Bs;
    val la = length As;

    fun proof p q =
      ZAbsps (map normt (Bs @ As))
        (ZAppp (ZAppps (q, map ZBoundp (lb + la - 1 downto la)),
          ZAppps (p, (if n > 0 then [mk_asm_prf (normt (the A)) n m] else []) @
            map (if flatten then flatten_params_proof 0 0 n else ZBoundp o snd)
              (map normt oldAs ~~ (la - 1 downto 0)))));
  in
    if Envir.is_empty env then proof rprf sprf
    else proof (normp rprf) (if Envir.above env smax then sprf else normp sprf)
  end;

end;
