(*  Title:      Pure/term_subst.ML
    Author:     Makarius

Efficient type/term substitution.
*)

signature INST_TABLE =
sig
  include TABLE
  val add: key * 'a -> 'a table -> 'a table
  val table: (key * 'a) list -> 'a table
end;

functor Inst_Table(Key: KEY): INST_TABLE =
struct

structure Tab = Table(Key);

fun add entry = Tab.insert (K true) entry;
fun table entries = fold add entries Tab.empty;

open Tab;

end;

signature TERM_SUBST =
sig
  structure TFrees: INST_TABLE
  structure TVars: INST_TABLE
  structure Frees: INST_TABLE
  structure Vars: INST_TABLE
  val map_atypsT_same: typ Same.operation -> typ Same.operation
  val map_types_same: typ Same.operation -> term Same.operation
  val map_aterms_same: term Same.operation -> term Same.operation
  val generalizeT_same: Symtab.set -> int -> typ Same.operation
  val generalize_same: Symtab.set * Symtab.set -> int -> term Same.operation
  val generalizeT: Symtab.set -> int -> typ -> typ
  val generalize: Symtab.set * Symtab.set -> int -> term -> term
  val instantiateT_maxidx: (typ * int) TVars.table -> typ -> int -> typ * int
  val instantiate_maxidx: (typ * int) TVars.table * (term * int) Vars.table ->
    term -> int -> term * int
  val instantiateT_frees_same: typ TFrees.table -> typ Same.operation
  val instantiate_frees_same: typ TFrees.table * term Frees.table -> term Same.operation
  val instantiateT_frees: typ TFrees.table -> typ -> typ
  val instantiate_frees: typ TFrees.table * term Frees.table -> term -> term
  val instantiateT_same: typ TVars.table -> typ Same.operation
  val instantiate_same: typ TVars.table * term Vars.table -> term Same.operation
  val instantiateT: typ TVars.table -> typ -> typ
  val instantiate: typ TVars.table * term Vars.table -> term -> term
  val zero_var_indexes_inst: Name.context -> term list -> typ TVars.table * term Vars.table
  val zero_var_indexes: term -> term
  val zero_var_indexes_list: term list -> term list
end;

structure Term_Subst: TERM_SUBST =
struct

(* instantiation as table *)

structure TFrees = Inst_Table(
  type key = string * sort
  val ord = pointer_eq_ord (prod_ord fast_string_ord Term_Ord.sort_ord)
);

structure TVars = Inst_Table(
  type key = indexname * sort
  val ord = pointer_eq_ord (prod_ord Term_Ord.fast_indexname_ord Term_Ord.sort_ord)
);

structure Frees = Inst_Table(
  type key = string * typ
  val ord = pointer_eq_ord (prod_ord fast_string_ord Term_Ord.typ_ord)
);

structure Vars = Inst_Table(
  type key = indexname * typ
  val ord = pointer_eq_ord (prod_ord Term_Ord.fast_indexname_ord Term_Ord.typ_ord)
);


(* generic mapping *)

fun map_atypsT_same f =
  let
    fun typ (Type (a, Ts)) = Type (a, Same.map typ Ts)
      | typ T = f T;
  in typ end;

fun map_types_same f =
  let
    fun term (Const (a, T)) = Const (a, f T)
      | term (Free (a, T)) = Free (a, f T)
      | term (Var (v, T)) = Var (v, f T)
      | term (Bound _) = raise Same.SAME
      | term (Abs (x, T, t)) =
          (Abs (x, f T, Same.commit term t)
            handle Same.SAME => Abs (x, T, term t))
      | term (t $ u) = (term t $ Same.commit term u handle Same.SAME => t $ term u);
  in term end;

fun map_aterms_same f =
  let
    fun term (Abs (x, T, t)) = Abs (x, T, term t)
      | term (t $ u) = (term t $ Same.commit term u handle Same.SAME => t $ term u)
      | term a = f a;
  in term end;


(* generalization of fixed variables *)

fun generalizeT_same tfrees idx ty =
  if Symtab.is_empty tfrees then raise Same.SAME
  else
    let
      fun gen (Type (a, Ts)) = Type (a, Same.map gen Ts)
        | gen (TFree (a, S)) =
            if Symtab.defined tfrees a then TVar ((a, idx), S)
            else raise Same.SAME
        | gen _ = raise Same.SAME;
    in gen ty end;

fun generalize_same (tfrees, frees) idx tm =
  if Symtab.is_empty tfrees andalso Symtab.is_empty frees then raise Same.SAME
  else
    let
      val genT = generalizeT_same tfrees idx;
      fun gen (Free (x, T)) =
            if Symtab.defined frees x then
              Var (Name.clean_index (x, idx), Same.commit genT T)
            else Free (x, genT T)
        | gen (Var (xi, T)) = Var (xi, genT T)
        | gen (Const (c, T)) = Const (c, genT T)
        | gen (Bound _) = raise Same.SAME
        | gen (Abs (x, T, t)) =
            (Abs (x, genT T, Same.commit gen t)
              handle Same.SAME => Abs (x, T, gen t))
        | gen (t $ u) = (gen t $ Same.commit gen u handle Same.SAME => t $ gen u);
    in gen tm end;

fun generalizeT names i ty = Same.commit (generalizeT_same names i) ty;
fun generalize names i tm = Same.commit (generalize_same names i) tm;


(* instantiation of free variables (types before terms) *)

fun instantiateT_frees_same instT ty =
  if TFrees.is_empty instT then raise Same.SAME
  else
    let
      fun subst (Type (a, Ts)) = Type (a, Same.map subst Ts)
        | subst (TFree v) =
            (case TFrees.lookup instT v of
              SOME T => T
            | NONE => raise Same.SAME)
        | subst _ = raise Same.SAME;
    in subst ty end;

fun instantiate_frees_same (instT, inst) tm =
  if TFrees.is_empty instT andalso Frees.is_empty inst then raise Same.SAME
  else
    let
      val substT = instantiateT_frees_same instT;
      fun subst (Const (c, T)) = Const (c, substT T)
        | subst (Free (x, T)) =
            let val (T', same) = (substT T, false) handle Same.SAME => (T, true) in
              (case Frees.lookup inst (x, T') of
                 SOME t => t
               | NONE => if same then raise Same.SAME else Free (x, T'))
            end
        | subst (Var (xi, T)) = Var (xi, substT T)
        | subst (Bound _) = raise Same.SAME
        | subst (Abs (x, T, t)) =
            (Abs (x, substT T, Same.commit subst t)
              handle Same.SAME => Abs (x, T, subst t))
        | subst (t $ u) = (subst t $ Same.commit subst u handle Same.SAME => t $ subst u);
    in subst tm end;

fun instantiateT_frees instT ty = Same.commit (instantiateT_frees_same instT) ty;
fun instantiate_frees inst tm = Same.commit (instantiate_frees_same inst) tm;


(* instantiation of schematic variables (types before terms) -- recomputes maxidx *)

local

fun no_indexesT instT = TVars.map (fn _ => rpair ~1) instT;
fun no_indexes inst = Vars.map (fn _ => rpair ~1) inst;

fun instT_same maxidx instT ty =
  let
    fun maxify i = if i > ! maxidx then maxidx := i else ();

    fun subst_typ (Type (a, Ts)) = Type (a, subst_typs Ts)
      | subst_typ (TVar ((a, i), S)) =
          (case TVars.lookup instT ((a, i), S) of
            SOME (T, j) => (maxify j; T)
          | NONE => (maxify i; raise Same.SAME))
      | subst_typ _ = raise Same.SAME
    and subst_typs (T :: Ts) =
        (subst_typ T :: Same.commit subst_typs Ts
          handle Same.SAME => T :: subst_typs Ts)
      | subst_typs [] = raise Same.SAME;
  in subst_typ ty end;

fun inst_same maxidx (instT, inst) tm =
  let
    fun maxify i = if i > ! maxidx then maxidx := i else ();

    val substT = instT_same maxidx instT;
    fun subst (Const (c, T)) = Const (c, substT T)
      | subst (Free (x, T)) = Free (x, substT T)
      | subst (Var ((x, i), T)) =
          let val (T', same) = (substT T, false) handle Same.SAME => (T, true) in
            (case Vars.lookup inst ((x, i), T') of
               SOME (t, j) => (maxify j; t)
             | NONE => (maxify i; if same then raise Same.SAME else Var ((x, i), T')))
          end
      | subst (Bound _) = raise Same.SAME
      | subst (Abs (x, T, t)) =
          (Abs (x, substT T, Same.commit subst t)
            handle Same.SAME => Abs (x, T, subst t))
      | subst (t $ u) = (subst t $ Same.commit subst u handle Same.SAME => t $ subst u);
  in subst tm end;

in

fun instantiateT_maxidx instT ty i =
  let val maxidx = Unsynchronized.ref i
  in (Same.commit (instT_same maxidx instT) ty, ! maxidx) end;

fun instantiate_maxidx insts tm i =
  let val maxidx = Unsynchronized.ref i
  in (Same.commit (inst_same maxidx insts) tm, ! maxidx) end;

fun instantiateT_same instT ty =
  if TVars.is_empty instT then raise Same.SAME
  else instT_same (Unsynchronized.ref ~1) (no_indexesT instT) ty;

fun instantiate_same (instT, inst) tm =
  if TVars.is_empty instT andalso Vars.is_empty inst then raise Same.SAME
  else inst_same (Unsynchronized.ref ~1) (no_indexesT instT, no_indexes inst) tm;

fun instantiateT instT ty = Same.commit (instantiateT_same instT) ty;
fun instantiate inst tm = Same.commit (instantiate_same inst) tm;

end;


(* zero var indexes *)

fun zero_var_inst ins mk (v as ((x, i), X)) (inst, used) =
  let val (x', used') = Name.variant (if Name.is_bound x then "u" else x) used
  in if x = x' andalso i = 0 then (inst, used') else (ins (v, mk ((x', 0), X)) inst, used') end;

fun zero_var_indexes_inst used ts =
  let
    val (instT, _) =
      (TVars.empty, used) |> TVars.fold (zero_var_inst TVars.add TVar o #1)
        ((fold o fold_types o fold_atyps) (fn TVar v =>
          TVars.add (v, ()) | _ => I) ts TVars.empty);
    val (inst, _) =
      (Vars.empty, used) |> Vars.fold (zero_var_inst Vars.add Var o #1)
        ((fold o fold_aterms) (fn Var (xi, T) =>
          Vars.add ((xi, instantiateT instT T), ()) | _ => I) ts Vars.empty);
  in (instT, inst) end;

fun zero_var_indexes_list ts = map (instantiate (zero_var_indexes_inst Name.context ts)) ts;
val zero_var_indexes = singleton zero_var_indexes_list;

end;
