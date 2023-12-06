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


(* ordering *)

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

end;


(* term items *)

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
  | ZBox of serial;

datatype zproof =
    ZDummy                         (*dummy proof*)
  | ZConstP of zproof_name * zterm * ztyp ZTVars.table * zterm ZVars.table
  | ZBoundP of int
  | ZHyp of zterm
  | ZAbst of string * ztyp * zproof
  | ZAbsP of string * zterm * zproof
  | ZAppt of zproof * zterm
  | ZAppP of zproof * zproof
  | ZClassP of ztyp * class;       (*OFCLASS proof from sorts algebra*)



(*** local ***)

signature ZTERM =
sig
  datatype ztyp = datatype ztyp
  datatype zterm = datatype zterm
  datatype zproof = datatype zproof
  val fold_tvars: (indexname * sort -> 'a -> 'a) -> ztyp -> 'a -> 'a
  val fold_aterms: (zterm -> 'a -> 'a) -> zterm -> 'a -> 'a
  val fold_types: (ztyp -> 'a -> 'a) -> zterm -> 'a -> 'a
  val ztyp_ord: ztyp * ztyp -> order
  val aconv_zterm: zterm * zterm -> bool
  val ztyp_of: typ -> ztyp
  val typ_of: ztyp -> typ
  val zterm_of: Consts.T -> term -> zterm
  val term_of: Consts.T -> zterm -> term
  val global_zterm_of: theory -> term -> zterm
  val global_term_of: theory -> zterm -> term
  val dummy_proof: 'a -> zproof
  val todo_proof: 'a -> zproof
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
  val varifyT_proof: ((string * sort) * (indexname * sort)) list -> zproof -> zproof
end;

structure ZTerm: ZTERM =
struct

datatype ztyp = datatype ztyp;
datatype zterm = datatype zterm;
datatype zproof = datatype zproof;

open ZTerm;

fun aconv_zterm (tm1, tm2) =
  pointer_eq (tm1, tm2) orelse
    (case (tm1, tm2) of
      (ZApp (t1, u1), ZApp (t2, u2)) => aconv_zterm (t1, t2) andalso aconv_zterm (u1, u2)
    | (ZAbs (_, T1, t1), ZAbs (_, T2, t2)) => aconv_zterm (t1, t2) andalso T1 = T2
    | (a1, a2) => a1 = a2);


(* map structure *)

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
      | proof (ZConstP (a, A, instT, inst)) =
          (case Same.catch (map_insts_same typ term) (instT, inst) of
            NONE => ZConstP (a, term A, instT, inst)
          | SOME (instT', inst') => ZConstP (a, Same.commit term A, instT', inst'))
      | proof (ZBoundP _) = raise Same.SAME
      | proof (ZHyp h) = ZHyp (term h)
      | proof (ZAbst (a, T, p)) =
          (ZAbst (a, typ T, Same.commit proof p) handle Same.SAME => ZAbst (a, T, proof p))
      | proof (ZAbsP (a, t, p)) =
          (ZAbsP (a, term t, Same.commit proof p) handle Same.SAME => ZAbsP (a, t, proof p))
      | proof (ZAppt (p, t)) =
          (ZAppt (proof p, Same.commit term t) handle Same.SAME => ZAppt (p, term t))
      | proof (ZAppP (p, q)) =
          (ZAppP (proof p, Same.commit proof q) handle Same.SAME => ZAppP (p, proof q))
      | proof (ZClassP (T, c)) = ZClassP (typ T, c);
  in proof end;

fun map_proof_types_same typ =
  map_proof_same typ (subst_term_same typ Same.same);


(* instantiation *)

fun init_instT t = ZTVars.build (ZTVars.add_tvars t) |> ZTVars.map (fn v => fn _ => ZTVar v);
fun init_inst t = ZVars.build (ZVars.add_vars t) |> ZVars.map (fn v => fn _ => ZVar v);

fun map_const_proof (f, g) prf =
  (case prf of
    ZConstP (a, A, instT, inst) =>
      let
        val instT' = ZTVars.map (fn ((x, _), _) => fn y => the_default y (try f x)) instT;
        val inst' = ZVars.map (fn ((x, _), _) => fn y => the_default y (try g x)) inst;
      in ZConstP (a, A, instT', inst') end
  | _ => prf);


(* convert ztyp / zterm vs. regular typ / term *)

fun ztyp_of (TFree (a, S)) = ZTVar ((a, ~1), S)
  | ztyp_of (TVar v) = ZTVar v
  | ztyp_of (Type ("fun", [T, U])) = ZFun (ztyp_of T, ztyp_of U)
  | ztyp_of (Type (c, [])) = if c = "prop" then ZProp else ZType0 c
  | ztyp_of (Type (c, [T])) = if c = "itself" then ZItself (ztyp_of T) else ZType1 (c, ztyp_of T)
  | ztyp_of (Type (c, ts)) = ZType (c, map ztyp_of ts);

fun typ_of (ZTVar ((a, ~1), S)) = TFree (a, S)
  | typ_of (ZTVar v) = TVar v
  | typ_of (ZFun (T, U)) = typ_of T --> typ_of U
  | typ_of ZProp = propT
  | typ_of (ZItself T) = Term.itselfT (typ_of T)
  | typ_of (ZType0 c) = Type (c, [])
  | typ_of (ZType1 (c, T)) = Type (c, [typ_of T])
  | typ_of (ZType (c, Ts)) = Type (c, map typ_of Ts);

fun zterm_of consts =
  let
    val typargs = Consts.typargs consts;
    fun zterm (Free (x, T)) = ZVar ((x, ~1), ztyp_of T)
      | zterm (Var (xi, T)) = ZVar (xi, ztyp_of T)
      | zterm (Bound i) = ZBound i
      | zterm (Const (c, T)) =
          (case typargs (c, T) of
            [] => ZConst0 c
          | [T] => ZConst1 (c, ztyp_of T)
          | Ts => ZConst (c, map ztyp_of Ts))
      | zterm (Abs (a, T, b)) = ZAbs (a, ztyp_of T, zterm b)
      | zterm ((t as Const (c, _)) $ (u as Const ("Pure.type", _))) =
          if String.isSuffix Logic.class_suffix c then
            ZClass (ztyp_of (Logic.dest_type u), Logic.class_of_const c)
          else ZApp (zterm t, zterm u)
      | zterm (t $ u) = ZApp (zterm t, zterm u);
  in zterm end;

fun term_of consts =
  let
    val instance = Consts.instance consts;
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

val global_zterm_of = zterm_of o Sign.consts_of;
val global_term_of = term_of o Sign.consts_of;



(** proof construction **)

fun dummy_proof _ = ZDummy;
val todo_proof = dummy_proof;


(* basic logic *)

fun const_proof thy a A =
  let
    val t = global_zterm_of thy A;
    val instT = init_instT t;
    val inst = init_inst t;
  in ZConstP (a, t, instT, inst) end;

fun axiom_proof thy name = const_proof thy (ZAxiom name);
fun oracle_proof thy name = const_proof thy (ZOracle name);

fun assume_proof thy A =
  ZHyp (global_zterm_of thy A);

fun trivial_proof thy A =
  ZAbsP ("H", global_zterm_of thy A, ZBoundP 0);

fun implies_intr_proof thy A prf =
  let
    val h = global_zterm_of thy A;
    fun abs_hyp i (p as ZHyp t) = if aconv_zterm (h, t) then ZBoundP i else p
      | abs_hyp i (ZAbst (x, T, p)) = ZAbst (x, T, abs_hyp i p)
      | abs_hyp i (ZAbsP (x, t, p)) = ZAbsP (x, t, abs_hyp (i + 1) p)
      | abs_hyp i (ZAppt (p, t)) = ZAppt (abs_hyp i p, t)
      | abs_hyp i (ZAppP (p, q)) = ZAppP (abs_hyp i p, abs_hyp i q)
      | abs_hyp _ p = p;
  in ZAbsP ("H", h, abs_hyp 0 prf) end;

fun forall_intr_proof thy T (a, x) prf =
  let
    val Z = ztyp_of T;
    val z = global_zterm_of thy x;

    fun abs_term i b =
      if aconv_zterm (b, z) then ZBound i
      else
        (case b of
          ZAbs (x, T, t) => ZAbs (x, T, abs_term (i + 1) t)
        | ZApp (t, u) => ZApp (abs_term i t, abs_term i u)
        | _ => b);

    fun abs_proof i (ZAbst (x, T, prf)) = ZAbst (x, T, abs_proof (i + 1) prf)
      | abs_proof i (ZAbsP (x, t, prf)) = ZAbsP (x, abs_term i t, abs_proof i prf)
      | abs_proof i (ZAppt (p, t)) = ZAppt (abs_proof i p, abs_term i t)
      | abs_proof i (ZAppP (p, q)) = ZAppP (abs_proof i p, abs_proof i q)
      | abs_proof _ p = p;

  in ZAbst (a, Z, abs_proof 0 prf) end;

fun forall_elim_proof thy t p = ZAppt (p, global_zterm_of thy t);

fun of_class_proof (T, c) = ZClassP (ztyp_of T, c);


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
    Theory.equality_axioms |> map (fn (b, t) => axiom_proof thy0 (Sign.full_name thy0 b) t);

in

val is_reflexive_proof =
  fn ZConstP (ZAxiom "Pure.reflexive", _, _, _) => true | _ => false;

fun reflexive_proof thy T t =
  let
    val A = ztyp_of T;
    val x = global_zterm_of thy t;
  in map_const_proof (fn "'a" => A, fn "x" => x) reflexive_axiom end;

fun symmetric_proof thy T t u prf =
  if is_reflexive_proof prf then prf
  else
    let
      val A = ztyp_of T;
      val x = global_zterm_of thy t;
      val y = global_zterm_of thy u;
      val ax = map_const_proof (fn "'a" => A, fn "x" => x | "y" => y) symmetric_axiom;
    in ZAppP (ax, prf) end;

fun transitive_proof thy T t u v prf1 prf2 =
  if is_reflexive_proof prf1 then prf2
  else if is_reflexive_proof prf2 then prf1
  else
    let
      val A = ztyp_of T;
      val x = global_zterm_of thy t;
      val y = global_zterm_of thy u;
      val z = global_zterm_of thy v;
      val ax = map_const_proof (fn "'a" => A, fn "x" => x | "y" => y | "z" => z) transitive_axiom;
    in ZAppP (ZAppP (ax, prf1), prf2) end;

fun equal_intr_proof thy t u prf1 prf2 =
  let
    val A = global_zterm_of thy t;
    val B = global_zterm_of thy u;
    val ax = map_const_proof (undefined, fn "A" => A | "B" => B) equal_intr_axiom;
  in ZAppP (ZAppP (ax, prf1), prf2) end;

fun equal_elim_proof thy t u prf1 prf2 =
  let
    val A = global_zterm_of thy t;
    val B = global_zterm_of thy u;
    val ax = map_const_proof (undefined, fn "A" => A | "B" => B) equal_elim_axiom;
  in ZAppP (ZAppP (ax, prf1), prf2) end;

fun abstract_rule_proof thy T U x t u prf =
  let
    val A = ztyp_of T;
    val B = ztyp_of U;
    val f = global_zterm_of thy t;
    val g = global_zterm_of thy u;
    val ax =
      map_const_proof (fn "'a" => A | "'b" => B, fn "f" => f | "g" => g)
        abstract_rule_axiom;
  in ZAppP (ax, forall_intr_proof thy T x prf) end;

fun combination_proof thy T U f g t u prf1 prf2 =
  let
    val A = ztyp_of T;
    val B = ztyp_of U;
    val f' = global_zterm_of thy f;
    val g' = global_zterm_of thy g;
    val x = global_zterm_of thy t;
    val y = global_zterm_of thy u;
    val ax =
      map_const_proof (fn "'a" => A | "'b" => B, fn "f" => f' | "g" => g' | "x" => x | "y" => y)
        combination_axiom;
  in ZAppP (ZAppP (ax, prf1), prf2) end;

end;


(* substitution *)

fun generalize_proof (tfrees, frees) idx prf =
  let
    val typ =
      if Names.is_empty tfrees then Same.same else
        subst_type_same (fn ((a, i), S) =>
          if i = ~1 andalso Names.defined tfrees a then ZTVar ((a, idx), S)
          else raise Same.SAME);
    val term =
      subst_term_same typ (fn ((x, i), T) =>
        if i = ~1 andalso Names.defined frees x then ZVar ((x, idx), T)
        else raise Same.SAME);
  in Same.commit (map_proof_same typ term) prf end;

fun varifyT_proof names prf =
  if null names then prf
  else
    let
      val tab = ZTVars.build (names |> fold (fn ((a, S), b) => ZTVars.add (((a, ~1), S), b)));
      val typ =
        subst_type_same (fn v =>
          (case ZTVars.lookup tab v of
            NONE => raise Same.SAME
          | SOME w => ZTVar w));
    in Same.commit (map_proof_types_same typ) prf end;

end;
