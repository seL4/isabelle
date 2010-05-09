(*  Title:      Pure/term_subst.ML
    Author:     Makarius

Efficient type/term substitution.
*)

signature TERM_SUBST =
sig
  val map_atypsT_same: typ Same.operation -> typ Same.operation
  val map_types_same: typ Same.operation -> term Same.operation
  val map_aterms_same: term Same.operation -> term Same.operation
  val generalizeT_same: string list -> int -> typ Same.operation
  val generalize_same: string list * string list -> int -> term Same.operation
  val generalize: string list * string list -> int -> term -> term
  val generalizeT: string list -> int -> typ -> typ
  val instantiateT_maxidx: ((indexname * sort) * (typ * int)) list -> typ -> int -> typ * int
  val instantiate_maxidx:
    ((indexname * sort) * (typ * int)) list * ((indexname * typ) * (term * int)) list ->
    term -> int -> term * int
  val instantiateT: ((indexname * sort) * typ) list -> typ -> typ
  val instantiate: ((indexname * sort) * typ) list * ((indexname * typ) * term) list ->
    term -> term
  val instantiateT_same: ((indexname * sort) * typ) list -> typ Same.operation
  val instantiate_same: ((indexname * sort) * typ) list * ((indexname * typ) * term) list ->
    term Same.operation
  val zero_var_indexes: term -> term
  val zero_var_indexes_inst: term list ->
    ((indexname * sort) * typ) list * ((indexname * typ) * term) list
end;

structure Term_Subst: TERM_SUBST =
struct

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

fun generalizeT_same [] _ _ = raise Same.SAME
  | generalizeT_same tfrees idx ty =
      let
        fun gen (Type (a, Ts)) = Type (a, Same.map gen Ts)
          | gen (TFree (a, S)) =
              if member (op =) tfrees a then TVar ((a, idx), S)
              else raise Same.SAME
          | gen _ = raise Same.SAME;
      in gen ty end;

fun generalize_same ([], []) _ _ = raise Same.SAME
  | generalize_same (tfrees, frees) idx tm =
      let
        val genT = generalizeT_same tfrees idx;
        fun gen (Free (x, T)) =
              if member (op =) frees x then
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

fun generalize names i tm = Same.commit (generalize_same names i) tm;
fun generalizeT names i ty = Same.commit (generalizeT_same names i) ty;


(* instantiation of schematic variables (types before terms) -- recomputes maxidx *)

local

fun no_index (x, y) = (x, (y, ~1));
fun no_indexes1 inst = map no_index inst;
fun no_indexes2 (inst1, inst2) = (map no_index inst1, map no_index inst2);

fun instT_same maxidx instT ty =
  let
    fun maxify i = if i > ! maxidx then maxidx := i else ();

    fun subst_typ (Type (a, Ts)) = Type (a, subst_typs Ts)
      | subst_typ (TVar ((a, i), S)) =
          (case AList.lookup Term.eq_tvar instT ((a, i), S) of
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
            (case AList.lookup Term.eq_var inst ((x, i), T') of
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

fun instantiateT [] ty = ty
  | instantiateT instT ty = Same.commit (instT_same (Unsynchronized.ref ~1) (no_indexes1 instT)) ty;

fun instantiate ([], []) tm = tm
  | instantiate insts tm = Same.commit (inst_same (Unsynchronized.ref ~1) (no_indexes2 insts)) tm;

fun instantiateT_same [] _ = raise Same.SAME
  | instantiateT_same instT ty = instT_same (Unsynchronized.ref ~1) (no_indexes1 instT) ty;

fun instantiate_same ([], []) _ = raise Same.SAME
  | instantiate_same insts tm = inst_same (Unsynchronized.ref ~1) (no_indexes2 insts) tm;

end;


(* zero var indexes *)

fun zero_var_inst vars =
  fold (fn v as ((x, i), X) => fn (inst, used) =>
    let
      val ([x'], used') = Name.variants [if Name.is_bound x then "u" else x] used;
    in if x = x' andalso i = 0 then (inst, used') else ((v, ((x', 0), X)) :: inst, used') end)
  vars ([], Name.context) |> #1;

fun zero_var_indexes_inst ts =
  let
    val tvars = sort Term_Ord.tvar_ord (fold Term.add_tvars ts []);
    val instT = map (apsnd TVar) (zero_var_inst tvars);
    val vars = sort Term_Ord.var_ord (map (apsnd (instantiateT instT)) (fold Term.add_vars ts []));
    val inst = map (apsnd Var) (zero_var_inst vars);
  in (instT, inst) end;

fun zero_var_indexes t = instantiate (zero_var_indexes_inst [t]) t;

end;
