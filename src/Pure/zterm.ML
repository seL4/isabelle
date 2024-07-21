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
  | OFCLASS of ztyp * class

structure ZTerm =
struct

(* fold *)

fun fold_tvars f (ZTVar v) = f v
  | fold_tvars f (ZFun (T, U)) = fold_tvars f T #> fold_tvars f U
  | fold_tvars f (ZType1 (_, T)) = fold_tvars f T
  | fold_tvars f (ZType (_, Ts)) = fold (fold_tvars f) Ts
  | fold_tvars _ _ = I;

fun fold_aterms f (ZApp (t, u)) = fold_aterms f t #> fold_aterms f u
  | fold_aterms f (ZAbs (_, _, t)) = fold_aterms f t
  | fold_aterms f a = f a;

fun fold_vars f = fold_aterms (fn ZVar v => f v | _ => I);

fun fold_types f (ZVar (_, T)) = f T
  | fold_types f (ZConst1 (_, T)) = f T
  | fold_types f (ZConst (_, As)) = fold f As
  | fold_types f (ZAbs (_, T, b)) = f T #> fold_types f b
  | fold_types f (ZApp (t, u)) = fold_types f t #> fold_types f u
  | fold_types f (OFCLASS (T, _)) = f T
  | fold_types _ _ = I;


(* map *)

fun map_tvars_same f =
  let
    fun typ (ZTVar v) = f v
      | typ (ZFun (T, U)) =
          (ZFun (typ T, Same.commit typ U)
            handle Same.SAME => ZFun (T, typ U))
      | typ ZProp = raise Same.SAME
      | typ (ZType0 _) = raise Same.SAME
      | typ (ZType1 (a, T)) = ZType1 (a, typ T)
      | typ (ZType (a, Ts)) = ZType (a, Same.map typ Ts);
  in typ end;

fun map_aterms_same f =
  let
    fun term (ZAbs (x, T, t)) = ZAbs (x, T, term t)
      | term (ZApp (t, u)) =
          (ZApp (term t, Same.commit term u)
            handle Same.SAME => ZApp (t, term u))
      | term a = f a;
  in term end;

fun map_vars_same f = map_aterms_same (fn ZVar v => f v | _ => raise Same.SAME);

fun map_types_same f =
  let
    fun term (ZVar (xi, T)) = ZVar (xi, f T)
      | term (ZBound _) = raise Same.SAME
      | term (ZConst0 _) = raise Same.SAME
      | term (ZConst1 (c, T)) = ZConst1 (c, f T)
      | term (ZConst (c, Ts)) = ZConst (c, Same.map f Ts)
      | term (ZAbs (x, T, t)) =
          (ZAbs (x, f T, Same.commit term t)
            handle Same.SAME => ZAbs (x, T, term t))
      | term (ZApp (t, u)) =
          (ZApp (term t, Same.commit term u)
            handle Same.SAME => ZApp (t, term u))
      | term (OFCLASS (T, c)) = OFCLASS (f T, c);
  in term end;

val map_tvars = Same.commit o map_tvars_same;
val map_aterms = Same.commit o map_aterms_same;
val map_vars = Same.commit o map_vars_same;
val map_types = Same.commit o map_types_same;


(* type ordering *)

local

fun cons_nr (ZTVar _) = 0
  | cons_nr (ZFun _) = 1
  | cons_nr ZProp = 2
  | cons_nr (ZType0 _) = 3
  | cons_nr (ZType1 _) = 4
  | cons_nr (ZType _) = 5;

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
  | cons_nr (OFCLASS _) = 7;

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
    | (OFCLASS (_, a), OFCLASS (_, b)) => fast_string_ord (a, b)
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
    | (OFCLASS (T, _), OFCLASS (U, _)) => ztyp_ord (T, U)
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

val add_vars = ZTerm.fold_vars add_set;

end;


(* proofs *)

datatype zproof_name =
    ZAxiom of string
  | ZOracle of string
  | ZThm of {theory_name: string, thm_name: Thm_Name.P, serial: serial};

type zproof_const = (zproof_name * zterm) * (ztyp ZTVars.table * zterm ZVars.table);

datatype zproof =
    ZNop
  | ZConstp of zproof_const
  | ZBoundp of int
  | ZAbst of string * ztyp * zproof
  | ZAbsp of string * zterm * zproof
  | ZAppt of zproof * zterm
  | ZAppp of zproof * zproof
  | ZHyp of zterm
  | OFCLASSp of ztyp * class;      (*OFCLASS proof from sorts algebra*)



(*** local ***)

signature ZTERM =
sig
  datatype ztyp = datatype ztyp
  datatype zterm = datatype zterm
  datatype zproof = datatype zproof
  exception ZTERM of string * ztyp list * zterm list * zproof list
  val fold_tvars: (indexname * sort -> 'a -> 'a) -> ztyp -> 'a -> 'a
  val fold_aterms: (zterm -> 'a -> 'a) -> zterm -> 'a -> 'a
  val fold_vars: (indexname * ztyp -> 'a -> 'a) -> zterm -> 'a -> 'a
  val fold_types: (ztyp -> 'a -> 'a) -> zterm -> 'a -> 'a
  val map_tvars: (indexname * sort -> ztyp) -> ztyp -> ztyp
  val map_aterms: (zterm -> zterm) -> zterm -> zterm
  val map_vars: (indexname * ztyp -> zterm) -> zterm -> zterm
  val map_types: (ztyp -> ztyp) -> zterm -> zterm
  val ztyp_ord: ztyp ord
  val fast_zterm_ord: zterm ord
  val aconv_zterm: zterm * zterm -> bool
  val ZAbsts: (string * ztyp) list -> zproof -> zproof
  val ZAbsps: zterm list -> zproof -> zproof
  val ZAppts: zproof * zterm list -> zproof
  val ZAppps: zproof * zproof list -> zproof
  val strip_sortsT: ztyp -> ztyp
  val strip_sorts: zterm -> zterm
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
  val subst_type_same: (indexname * sort, ztyp) Same.function -> ztyp Same.operation
  val subst_term_same:
    ztyp Same.operation -> (indexname * ztyp, zterm) Same.function -> zterm Same.operation
  exception BAD_INST of ((indexname * ztyp) * zterm) list
  val fold_proof: {hyps: bool} -> (ztyp -> 'a -> 'a) -> (zterm -> 'a -> 'a) -> zproof -> 'a -> 'a
  val fold_proof_types: {hyps: bool} -> (ztyp -> 'a -> 'a) -> zproof -> 'a -> 'a
  val map_proof: {hyps: bool} -> ztyp Same.operation -> zterm Same.operation -> zproof -> zproof
  val map_proof_types: {hyps: bool} -> ztyp Same.operation -> zproof -> zproof
  val map_class_proof: (ztyp * class, zproof) Same.function -> zproof -> zproof
  val maxidx_type: ztyp -> int -> int
  val maxidx_term: zterm -> int -> int
  val maxidx_proof: zproof -> int -> int
  val ztyp_of: typ -> ztyp
  val ztyp_dummy: ztyp
  val typ_of_tvar: indexname * sort -> typ
  val typ_of: ztyp -> typ
  val reset_cache: theory -> theory
  val check_cache: theory -> {ztyp: int, typ: int} option
  val ztyp_cache: theory -> typ -> ztyp
  val typ_cache: theory -> ztyp -> typ
  val zterm_cache: theory -> {zterm: term -> zterm, ztyp: typ -> ztyp}
  val zterm_of: theory -> term -> zterm
  val term_of: theory -> zterm -> term
  val beta_norm_term_same: zterm Same.operation
  val beta_norm_proof_same: zproof Same.operation
  val beta_norm_prooft_same: zproof -> zproof
  val beta_norm_term: zterm -> zterm
  val beta_norm_proof: zproof -> zproof
  val beta_norm_prooft: zproof -> zproof
  val norm_type: theory -> Type.tyenv -> ztyp -> ztyp
  val norm_term: theory -> Envir.env -> zterm -> zterm
  val norm_proof: theory -> Envir.env -> term list -> zproof -> zproof
  val zproof_const_typargs: zproof_const -> ((indexname * sort) * ztyp) list
  val zproof_const_args: zproof_const -> ((indexname * ztyp) * zterm) list
  type zbox = serial * (zterm * zproof)
  val zbox_ord: zbox ord
  type zboxes = zbox Ord_List.T
  val union_zboxes: zboxes -> zboxes -> zboxes
  val unions_zboxes: zboxes list -> zboxes
  val add_box_proof: {unconstrain: bool} -> theory ->
    term list -> term -> zproof -> zboxes -> zproof * zboxes
  val thm_proof: theory -> Thm_Name.P -> term list -> term -> zproof -> zbox * zproof
  val axiom_proof:  theory -> string -> term -> zproof
  val oracle_proof:  theory -> string -> term -> zproof
  val assume_proof: theory -> term -> zproof
  val trivial_proof: theory -> term -> zproof
  val implies_intr_proof': zterm -> zproof -> zproof
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
  type sorts_proof = (class * class -> zproof) * (string * class list list * class -> zproof)
  val of_sort_proof: Sorts.algebra -> sorts_proof -> (typ * class -> zproof) ->
    typ * sort -> zproof list
  val unconstrainT_proof: theory -> sorts_proof -> Logic.unconstrain_context -> zproof -> zproof
  val encode_ztyp: ztyp XML.Encode.T
  val encode_zterm: {typed_vars: bool} -> zterm XML.Encode.T
  val encode_zproof: {typed_vars: bool} -> zproof XML.Encode.T
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

val strip_sortsT_same = map_tvars_same (fn (_, []) => raise Same.SAME | (a, _) => ZTVar (a, []));
val strip_sorts_same = map_types_same strip_sortsT_same;

val strip_sortsT = Same.commit strip_sortsT_same;
val strip_sorts = Same.commit strip_sorts_same;


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
      | typ (ZFun (T, U)) =
          (ZFun (typ T, Same.commit typ U)
            handle Same.SAME => ZFun (T, typ U))
      | typ ZProp = raise Same.SAME
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
          (ZAbs (a, typ T, Same.commit term t)
            handle Same.SAME => ZAbs (a, T, term t))
      | term (ZApp (t, u)) =
          (ZApp (term t, Same.commit term u)
            handle Same.SAME => ZApp (t, term u))
      | term (OFCLASS (T, c)) = OFCLASS (typ T, c);
  in term end;

fun instantiate_type_same instT =
  if ZTVars.is_empty instT then Same.same
  else #apply (ZTypes.unsynchronized_cache (subst_type_same (Same.function (ZTVars.lookup instT))));

fun instantiate_term_same typ inst =
  subst_term_same typ (Same.function (ZVars.lookup inst));


(* fold types/terms within proof *)

fun fold_proof {hyps} typ term =
  let
    fun proof ZNop = I
      | proof (ZConstp (_, (instT, inst))) =
          ZTVars.fold (typ o #2) instT #> ZVars.fold (term o #2) inst
      | proof (ZBoundp _) = I
      | proof (ZAbst (_, T, p)) = typ T #> proof p
      | proof (ZAbsp (_, t, p)) = term t #> proof p
      | proof (ZAppt (p, t)) = proof p #> term t
      | proof (ZAppp (p, q)) = proof p #> proof q
      | proof (ZHyp h) = hyps ? term h
      | proof (OFCLASSp (T, _)) = hyps ? typ T;
  in proof end;

fun fold_proof_types hyps typ =
  fold_proof hyps typ (fold_types typ);


(* map types/terms within proof *)

exception BAD_INST of ((indexname * ztyp) * zterm) list

fun make_inst inst =
  ZVars.build (inst |> fold (ZVars.insert (op aconv_zterm)))
    handle ZVars.DUP _ => raise BAD_INST inst;

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
        build (inst |> ZVars.fold_rev (fn (v, t) =>
          cons (the_default v (ZVars.lookup vars' v), the_default t (apply term t))))
        |> make_inst;
  in if ! changed then (instT', inst') else raise Same.SAME end;

fun map_proof_same {hyps} typ term =
  let
    fun proof ZNop = raise Same.SAME
      | proof (ZConstp (a, (instT, inst))) =
          ZConstp (a, map_insts_same typ term (instT, inst))
      | proof (ZBoundp _) = raise Same.SAME
      | proof (ZAbst (a, T, p)) =
          (ZAbst (a, typ T, Same.commit proof p)
            handle Same.SAME => ZAbst (a, T, proof p))
      | proof (ZAbsp (a, t, p)) =
          (ZAbsp (a, term t, Same.commit proof p)
            handle Same.SAME => ZAbsp (a, t, proof p))
      | proof (ZAppt (p, t)) =
          (ZAppt (proof p, Same.commit term t)
            handle Same.SAME => ZAppt (p, term t))
      | proof (ZAppp (p, q)) =
          (ZAppp (proof p, Same.commit proof q)
            handle Same.SAME => ZAppp (p, proof q))
      | proof (ZHyp h) = if hyps then ZHyp (term h) else raise Same.SAME
      | proof (OFCLASSp (T, c)) = if hyps then OFCLASSp (typ T, c) else raise Same.SAME;
  in proof end;

fun map_proof hyps typ term = Same.commit (map_proof_same hyps typ term);
fun map_proof_types hyps typ = map_proof hyps typ (subst_term_same typ Same.same);


(* map class proofs *)

fun map_class_proof class =
  let
    fun proof (OFCLASSp C) = class C
      | proof (ZAbst (a, T, p)) = ZAbst (a, T, proof p)
      | proof (ZAbsp (a, t, p)) = ZAbsp (a, t, proof p)
      | proof (ZAppt (p, t)) = ZAppt (proof p, t)
      | proof (ZAppp (p, q)) =
          (ZAppp (proof p, Same.commit proof q)
            handle Same.SAME => ZAppp (p, proof q))
      | proof _ = raise Same.SAME;
  in Same.commit proof end;


(* maximum index of variables *)

val maxidx_type = fold_tvars (fn ((_, i), _) => Integer.max i);

fun maxidx_term t =
  fold_types maxidx_type t #>
  fold_aterms (fn ZVar ((_, i), _) => Integer.max i | _ => I) t;

val maxidx_proof = fold_proof {hyps = false} maxidx_type maxidx_term;


(* convert ztyp vs. regular typ *)

fun ztyp_of (TFree (a, S)) = ZTVar ((a, ~1), S)
  | ztyp_of (TVar v) = ZTVar v
  | ztyp_of (Type ("fun", [T, U])) = ZFun (ztyp_of T, ztyp_of U)
  | ztyp_of (Type ("prop", [])) = ZProp
  | ztyp_of (Type (c, [])) = ZType0 c
  | ztyp_of (Type (c, [T])) = ZType1 (c, ztyp_of T)
  | ztyp_of (Type (c, ts)) = ZType (c, map ztyp_of ts);

val ztyp_dummy = ztyp_of dummyT;

fun typ_of_tvar ((a, ~1), S) = TFree (a, S)
  | typ_of_tvar v = TVar v;

fun typ_of (ZTVar v) = typ_of_tvar v
  | typ_of (ZFun (T, U)) = typ_of T --> typ_of U
  | typ_of ZProp = propT
  | typ_of (ZType0 c) = Type (c, [])
  | typ_of (ZType1 (c, T)) = Type (c, [typ_of T])
  | typ_of (ZType (c, Ts)) = Type (c, map typ_of Ts);


(* cache within theory context *)

local

structure Data = Theory_Data
(
  type T = (ztyp Typtab.cache_ops * typ ZTypes.cache_ops) option;
  val empty = NONE;
  val merge = K NONE;
);

fun make_ztyp_cache () = Typtab.unsynchronized_cache ztyp_of;
fun make_typ_cache () = ZTypes.unsynchronized_cache typ_of;

fun init_cache thy =
  if is_some (Data.get thy) then NONE
  else SOME (Data.put (SOME (make_ztyp_cache (), make_typ_cache ())) thy);

fun exit_cache thy =
  (case Data.get thy of
    SOME (cache1, cache2) => (#reset cache1 (); #reset cache2 (); SOME (Data.put NONE thy))
  | NONE => NONE);

in

val _ = Theory.setup (Theory.at_begin init_cache #> Theory.at_end exit_cache);

fun reset_cache thy =
  (case Data.get thy of
    SOME (cache1, cache2) => (#reset cache1 (); #reset cache2 (); thy)
  | NONE => thy);

fun check_cache thy =
  Data.get thy
  |> Option.map (fn (cache1, cache2) => {ztyp = #size cache1 (), typ = #size cache2 ()});

fun ztyp_cache thy =
  (case Data.get thy of
    SOME (cache, _) => cache
  | NONE => make_ztyp_cache ()) |> #apply;

fun typ_cache thy =
  (case Data.get thy of
    SOME (_, cache) => cache
  | NONE => make_typ_cache ()) |> #apply;

end;


(* convert zterm vs. regular term *)

fun zterm_cache thy =
  let
    val typargs = Consts.typargs (Sign.consts_of thy);

    val ztyp = ztyp_cache thy;

    fun zterm (Free (x, T)) = ZVar ((x, ~1), ztyp T)
      | zterm (Var (xi, T)) = ZVar (xi, ztyp T)
      | zterm (Bound i) = ZBound i
      | zterm (Const (c, T)) =
          (case typargs (c, T) of
            [] => ZConst0 c
          | [T] => ZConst1 (c, ztyp T)
          | Ts => ZConst (c, map ztyp Ts))
      | zterm (Abs (a, T, b)) = ZAbs (a, ztyp T, zterm b)
      | zterm (tm as t $ u) =
          (case try Logic.match_of_class tm of
            SOME (T, c) => OFCLASS (ztyp T, c)
          | NONE => ZApp (zterm t, zterm u));
  in {ztyp = ztyp, zterm = zterm} end;

val zterm_of = #zterm o zterm_cache;

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
      | term (OFCLASS (T, c)) = Logic.mk_of_class (typ_of T, c);
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
        | norm (ZType0 _) = raise Same.SAME
        | norm (ZType1 (a, T)) = ZType1 (a, norm T)
        | norm (ZType (a, Ts)) = ZType (a, Same.map norm Ts);
    in norm end;

fun norm_term_same {ztyp, zterm} (envir as Envir.Envir {tyenv, tenv, ...}) =
  let
    val lookup =
      if Vartab.is_empty tenv then K NONE
      else
        #apply (ZVars.unsynchronized_cache
          (apsnd typ_of #> Envir.lookup envir #> Option.map zterm));

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
        in beta_norm_prooft (map_proof {hyps = false} inst_typ norm_term prf) end
  end;

fun norm_type thy tyenv = Same.commit (norm_type_same (ztyp_cache thy) tyenv);
fun norm_term thy envir = Same.commit (norm_term_same (zterm_cache thy) envir);
fun norm_proof thy envir = norm_proof_cache (zterm_cache thy) envir;



(** proof construction **)

(* constants *)

fun zproof_const (a, A) : zproof_const =
  let
    val instT =
      ZTVars.build (A |> (fold_types o fold_tvars) (fn v => fn tab =>
        if ZTVars.defined tab v then tab else ZTVars.update (v, ZTVar v) tab));
    val inst =
      ZVars.build (A |> fold_vars (fn v => fn tab =>
        if ZVars.defined tab v then tab else ZVars.update (v, ZVar v) tab));
  in ((a, A), (instT, inst)) end;

fun zproof_const_typargs (((_, A), (instT, _)): zproof_const) =
  ZTVars.build (A |> ZTVars.add_tvars) |> ZTVars.list_set
  |> map (fn v => (v, the_default (ZTVar v) (ZTVars.lookup instT v)));

fun zproof_const_args (((_, A), (_, inst)): zproof_const) =
  ZVars.build (A |> ZVars.add_vars) |> ZVars.list_set
  |> map (fn v => (v, the_default (ZVar v) (ZVars.lookup inst v)));

fun make_const_proof (f, g) ((a, insts): zproof_const) =
  let
    val typ = subst_type_same (Same.function (fn ((x, _), _) => try f x));
    val term = Same.function (fn ZVar ((x, _), _) => try g x | _ => NONE);
  in ZConstp (a, Same.commit (map_insts_same typ term) insts) end;


(* closed proof boxes *)

type zbox = serial * (zterm * zproof);
val zbox_ord: zbox ord = fn ((i, _), (j, _)) => int_ord (j, i);

type zboxes = zbox Ord_List.T;
val union_zboxes = Ord_List.union zbox_ord;
val unions_zboxes = Ord_List.unions zbox_ord;
val add_zboxes = Ord_List.insert zbox_ord;

local

fun close_prop prems prop =
  fold_rev (fn A => fn B => ZApp (ZApp (ZConst0 "Pure.imp", A), B)) prems prop;

fun close_proof prems prf =
  let
    val m = length prems - 1;
    val bounds = ZTerms.build (prems |> fold_index (fn (i, h) => ZTerms.update (h, m - i)));
    fun get_bound lev t = ZTerms.lookup bounds t |> Option.map (fn i => ZBoundp (lev + i));

    fun proof lev (ZHyp t) =
          (case get_bound lev t of
            SOME p => p
          | NONE => raise ZTERM ("Loose bound in proof term", [], [t], [prf]))
      | proof lev (OFCLASSp C) =
          (case get_bound lev (OFCLASS C) of
            SOME p => p
          | NONE => raise Same.SAME)
      | proof lev (ZAbst (x, T, p)) = ZAbst (x, T, proof lev p)
      | proof lev (ZAbsp (x, t, p)) = ZAbsp (x, t, proof (lev + 1) p)
      | proof lev (ZAppt (p, t)) = ZAppt (proof lev p, t)
      | proof lev (ZAppp (p, q)) =
          (ZAppp (proof lev p, Same.commit (proof lev) q)
            handle Same.SAME => ZAppp (p, proof lev q))
      | proof _ _ = raise Same.SAME;
  in ZAbsps prems (Same.commit (proof 0) prf) end;

fun box_proof {unconstrain} thy thm_name hyps concl prf =
  let
    val {zterm, ...} = zterm_cache thy;

    val present_set_prf =
      ZTVars.build ((fold_proof_types {hyps = true} o fold_tvars) ZTVars.add_set prf);
    val present_set =
      Types.build (Types.add_atyps concl #> fold Types.add_atyps hyps #>
        ZTVars.fold (Types.add_set o typ_of_tvar o #1) present_set_prf);
    val ucontext as {constraints, outer_constraints, ...} =
      Logic.unconstrain_context [] present_set;

    val typ_operation = #typ_operation ucontext {strip_sorts = true};
    val unconstrain_typ = Same.commit typ_operation;
    val unconstrain_ztyp =
      #apply (ZTypes.unsynchronized_cache
        (Same.function_eq (op =) (typ_of #> unconstrain_typ #> ztyp_of)));
    val unconstrain_zterm = zterm o Term.map_types typ_operation;
    val unconstrain_proof = Same.commit (map_proof_types {hyps = true} unconstrain_ztyp);

    val constrain_instT =
      if unconstrain then ZTVars.empty
      else
        ZTVars.build (present_set |> Types.fold (fn (T, _) =>
          let
            val ZTVar v = ztyp_of (unconstrain_typ T) and U = ztyp_of T;
            val equal = (case U of ZTVar u => u = v | _ => false);
          in not equal ? ZTVars.add (v, U) end));
    val constrain_proof =
      if ZTVars.is_empty constrain_instT then I
      else
        map_proof_types {hyps = true}
          (subst_type_same (Same.function (ZTVars.lookup constrain_instT)));

    val hyps' = map unconstrain_zterm hyps;
    val prems = map (zterm o #2) constraints @ hyps';
    val prop' = beta_norm_term (close_prop prems (unconstrain_zterm concl));
    val prf' = beta_norm_prooft (close_proof prems (unconstrain_proof prf));

    val i = serial ();
    val zbox: zbox = (i, (prop', prf'));

    val proof_name =
      ZThm {theory_name = Context.theory_long_name thy, thm_name = thm_name, serial = i};

    val const = constrain_proof (ZConstp (zproof_const (proof_name, prop')));
    val args1 =
      outer_constraints |> map (fn (T, c) =>
        OFCLASSp (ztyp_of (if unconstrain then unconstrain_typ T else T), c));
    val args2 = if unconstrain then map ZHyp hyps' else map (ZHyp o zterm) hyps;
  in (zbox, ZAppps (ZAppps (const, args1), args2)) end;

in

val thm_proof = box_proof {unconstrain = false};

fun add_box_proof unconstrain thy hyps concl prf zboxes =
  let
    val (zbox, prf') = box_proof unconstrain thy Thm_Name.none hyps concl prf;
    val zboxes' = add_zboxes zbox zboxes;
  in (prf', zboxes') end;

end;


(* basic logic *)

fun zproof_axiom thy name A = zproof_const (ZAxiom name, zterm_of thy A);
val axiom_proof = ZConstp ooo zproof_axiom;

fun oracle_proof thy name A =
  ZConstp (zproof_const (ZOracle name, zterm_of thy A));

fun assume_proof thy A =
  ZHyp (zterm_of thy A);

fun trivial_proof thy A =
  ZAbsp ("H", zterm_of thy A, ZBoundp 0);

fun implies_intr_proof' h prf =
  let
    fun proof lev (ZHyp t) = if aconv_zterm (h, t) then ZBoundp lev else raise Same.SAME
      | proof lev (ZAbst (x, T, p)) = ZAbst (x, T, proof lev p)
      | proof lev (ZAbsp (x, t, p)) = ZAbsp (x, t, proof (lev + 1) p)
      | proof lev (ZAppt (p, t)) = ZAppt (proof lev p, t)
      | proof lev (ZAppp (p, q)) =
          (ZAppp (proof lev p, Same.commit (proof lev) q)
            handle Same.SAME => ZAppp (p, proof lev q))
      | proof _ _ = raise Same.SAME;
  in ZAbsp ("H", h, Same.commit (proof 0) prf) end;

fun implies_intr_proof thy = implies_intr_proof' o zterm_of thy;

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
            (ZApp (term i t, Same.commit (term i) u)
              handle Same.SAME => ZApp (t, term i u))
        | _ => raise Same.SAME);

    fun proof i (ZAbst (x, T, prf)) = ZAbst (x, T, proof (i + 1) prf)
      | proof i (ZAbsp (x, t, prf)) =
          (ZAbsp (x, term i t, Same.commit (proof i) prf)
            handle Same.SAME => ZAbsp (x, t, proof i prf))
      | proof i (ZAppt (p, t)) =
          (ZAppt (proof i p, Same.commit (term i) t)
            handle Same.SAME => ZAppt (p, term i t))
      | proof i (ZAppp (p, q)) =
          (ZAppp (proof i p, Same.commit (proof i) q)
            handle Same.SAME => ZAppp (p, proof i q))
      | proof _ _ = raise Same.SAME;

  in ZAbst (a, Z, Same.commit (proof 0) prf) end;

fun forall_elim_proof thy t p = ZAppt (p, zterm_of thy t);

fun of_class_proof (T, c) = OFCLASSp (ztyp_of T, c);


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
    Theory.equality_axioms |> map (fn (b, t) => zproof_axiom thy0 (Sign.full_name thy0 b) t);

in

val is_reflexive_proof =
  fn ZConstp ((ZAxiom "Pure.reflexive", _), _) => true | _ => false;

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
      if Names.is_empty tfrees then Same.same
      else
        #apply (ZTypes.unsynchronized_cache
          (subst_type_same (fn ((a, i), S) =>
            if i = ~1 andalso Names.defined tfrees a then ZTVar ((a, idx), S)
            else raise Same.SAME)));
    val term =
      subst_term_same typ (fn ((x, i), T) =>
        if i = ~1 andalso Names.defined frees x then ZVar ((x, idx), T)
        else raise Same.SAME);
  in map_proof {hyps = false} typ term prf end;

fun instantiate_proof thy (Ts, ts) prf =
  let
    val {ztyp, zterm} = zterm_cache thy;
    val instT = ZTVars.build (Ts |> fold (fn (v, T) => ZTVars.add (v, ztyp T)));
    val inst = ZVars.build (ts |> fold (fn ((v, T), t) => ZVars.add ((v, ztyp T), zterm t)));
    val typ = instantiate_type_same instT;
    val term = instantiate_term_same typ inst;
  in map_proof {hyps = false} typ term prf end;

fun varifyT_proof names prf =
  if null names then prf
  else
    let
      val tab = ZTVars.build (names |> fold (fn ((a, S), b) => ZTVars.add (((a, ~1), S), b)));
      val typ =
        #apply (ZTypes.unsynchronized_cache (subst_type_same (fn v =>
          (case ZTVars.lookup tab v of
            NONE => raise Same.SAME
          | SOME w => ZTVar w))));
    in map_proof_types {hyps = false} typ prf end;

fun legacy_freezeT_proof t prf =
  (case Type.legacy_freezeT t of
    NONE => prf
  | SOME f =>
      let
        val tvar = ztyp_of o Same.function f;
        val typ = #apply (ZTypes.unsynchronized_cache (subst_type_same tvar));
      in map_proof_types {hyps = false} typ prf end);


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
          map ZBoundp (((i - m - 1) downto 0) @ ((i - 1) downto (i - m))))))]))
  end;

fun permute_prems_proof thy prems' j k prf =
  let
    val {zterm, ...} = zterm_cache thy;
    val n = length prems';
  in
    ZAbsps (map zterm prems')
      (ZAppps (prf, map ZBoundp ((n - 1 downto n - j) @ (k - 1 downto 0) @ (n - j - 1 downto k))))
  end;


(* lifting *)

fun incr_tvar_same inc =
  if inc = 0 then Same.same
  else
    let fun tvar ((a, i), S) = if i >= 0 then ZTVar ((a, i + inc), S) else raise Same.SAME
    in #apply (ZTypes.unsynchronized_cache (subst_type_same tvar)) end;

fun incr_indexes_proof inc prf =
  let
    val typ = incr_tvar_same inc;
    fun var ((x, i), T) = if i >= 0 then ZVar ((x, i + inc), T) else raise Same.SAME;
    val term = subst_term_same typ var;
  in map_proof {hyps = false} typ term prf end;

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
            | incr _ (OFCLASS (T, c)) = OFCLASS (typ T, c);
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
      | proof Ts lev (ZConstp (a, insts)) =
          ZConstp (a, map_insts_same typ (term Ts lev) insts)
      | proof _ _ (OFCLASSp (T, c)) = OFCLASSp (typ T, c)
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
    val cache as {zterm, ...} = zterm_cache thy;
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
    val cache as {zterm, ...} = zterm_cache thy;
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


(* sort constraints within the logic *)

type sorts_proof = (class * class -> zproof) * (string * class list list * class -> zproof);

fun of_sort_proof algebra (classrel_proof, arity_proof) hyps =
  Sorts.of_sort_derivation algebra
   {class_relation = fn _ => fn _ => fn (prf, c1) => fn c2 =>
      if c1 = c2 then prf else ZAppp (classrel_proof (c1, c2), prf),
    type_constructor = fn (a, _) => fn dom => fn c =>
      let val Ss = map (map snd) dom and prfs = maps (map fst) dom
      in ZAppps (arity_proof (a, Ss, c), prfs) end,
    type_variable = fn typ => map (fn c => (hyps (typ, c), c)) (Type.sort_of_atyp typ)};

fun unconstrainT_proof thy sorts_proof (ucontext: Logic.unconstrain_context) =
  let
    val algebra = Sign.classes_of thy;

    val cache = zterm_cache thy;
    val typ_cache = typ_cache thy;

    val typ =
      #apply (ZTypes.unsynchronized_cache
        (typ_of #> #typ_operation ucontext {strip_sorts = true} #> ztyp_of));

    val typ_sort = #typ_operation ucontext {strip_sorts = false};

    fun hyps T =
      (case AList.lookup (op =) (#constraints ucontext) T of
        SOME t => ZHyp (#zterm cache t)
      | NONE => raise Fail "unconstrainT_proof: missing constraint");

    fun class (T, c) =
      let val T' = Same.commit typ_sort (typ_cache T)
      in the_single (of_sort_proof algebra sorts_proof hyps (T', [c])) end;
  in
    map_proof_types {hyps = false} typ #> map_class_proof class #> beta_norm_prooft
    #> fold_rev (implies_intr_proof' o #zterm cache o #2) (#constraints ucontext)
  end;



(** XML data representation **)

(* encode *)

local

open XML.Encode Term_XML.Encode;

fun ztyp T = T |> variant
 [fn ZFun args => (["fun"], pair ztyp ztyp args)
   | ZProp => (["prop"], [])
   | ZType0 a => ([a], [])
   | ZType1 (a, b) => ([a], list ztyp [b])
   | ZType (a, b) => ([a], list ztyp b),
  fn ZTVar ((a, ~1), b) => ([a], sort b),
  fn ZTVar (a, b) => (indexname a, sort b)];

fun zvar_type {typed_vars} T =
  if typed_vars andalso T <> ztyp_dummy then ztyp T else [];

fun zterm flag t = t |> variant
 [fn ZConst0 a => ([a], [])
   | ZConst1 (a, b) => ([a], list ztyp [b])
   | ZConst (a, b) => ([a], list ztyp b),
  fn ZVar ((a, ~1), b) => ([a], zvar_type flag b),
  fn ZVar (a, b) => (indexname a, zvar_type flag b),
  fn ZBound a => ([], int a),
  fn ZAbs (a, b, c) => ([a], pair ztyp (zterm flag) (b, c)),
  fn ZApp a => ([], pair (zterm flag) (zterm flag) a),
  fn OFCLASS (a, b) => ([b], ztyp a)];

fun zproof flag prf = prf |> variant
 [fn ZNop => ([], []),
  fn ZBoundp a => ([], int a),
  fn ZAbst (a, b, c) => ([a], pair ztyp (zproof flag) (b, c)),
  fn ZAbsp (a, b, c) => ([a], pair (zterm flag) (zproof flag) (b, c)),
  fn ZAppt a => ([], pair (zproof flag) (zterm flag) a),
  fn ZAppp a => ([], pair (zproof flag) (zproof flag) a),
  fn ZHyp a => ([], zterm flag a),
  fn ZConstp (c as ((ZAxiom a, b), _)) => ([a], list (ztyp o #2) (zproof_const_typargs c)),
  fn OFCLASSp (a, b) => ([b], ztyp a),
  fn ZConstp (c as ((ZOracle a, b), _)) => ([a], list (ztyp o #2) (zproof_const_typargs c)),
  fn ZConstp (c as ((ZThm {theory_name, thm_name = (name, _), serial}, b), _)) =>
    ([int_atom serial, theory_name, #1 name, int_atom (#2 name)],
      list (ztyp o #2) (zproof_const_typargs c))];

in

val encode_ztyp = ztyp;
val encode_zterm = zterm;
val encode_zproof = zproof;

end;

end;
