(*  Title:      Pure/term_subst.ML
    Author:     Makarius

Efficient term substitution -- avoids copying.
*)

signature TERM_SUBST =
sig
  val generalize: string list * string list -> int -> term -> term
  val generalizeT: string list -> int -> typ -> typ
  val generalize_option: string list * string list -> int -> term -> term option
  val generalizeT_option: string list -> int -> typ -> typ option
  val instantiateT_maxidx: ((indexname * sort) * (typ * int)) list -> typ -> int -> typ * int
  val instantiate_maxidx:
    ((indexname * sort) * (typ * int)) list * ((indexname * typ) * (term * int)) list ->
    term -> int -> term * int
  val instantiate: ((indexname * sort) * typ) list * ((indexname * typ) * term) list ->
    term -> term
  val instantiateT: ((indexname * sort) * typ) list -> typ -> typ
  val instantiate_option: ((indexname * sort) * typ) list * ((indexname * typ) * term) list ->
    term -> term option
  val instantiateT_option: ((indexname * sort) * typ) list -> typ -> typ option
  val zero_var_indexes: term -> term
  val zero_var_indexes_inst: term list ->
    ((indexname * sort) * typ) list * ((indexname * typ) * term) list
end;

structure Term_Subst: TERM_SUBST =
struct

(* generalization of fixed variables *)

local

exception SAME;

fun generalizeT_same [] _ _ = raise SAME
  | generalizeT_same tfrees idx ty =
      let
        fun gen_typ (Type (a, Ts)) = Type (a, gen_typs Ts)
          | gen_typ (TFree (a, S)) =
              if member (op =) tfrees a then TVar ((a, idx), S)
              else raise SAME
          | gen_typ _ = raise SAME
        and gen_typs (T :: Ts) =
            (gen_typ T :: (gen_typs Ts handle SAME => Ts)
              handle SAME => T :: gen_typs Ts)
          | gen_typs [] = raise SAME;
      in gen_typ ty end;

fun generalize_same ([], []) _ _ = raise SAME
  | generalize_same (tfrees, frees) idx tm =
      let
        val genT = generalizeT_same tfrees idx;
        fun gen (Free (x, T)) =
              if member (op =) frees x then
                Var (Name.clean_index (x, idx), genT T handle SAME => T)
              else Free (x, genT T)
          | gen (Var (xi, T)) = Var (xi, genT T)
          | gen (Const (c, T)) = Const (c, genT T)
          | gen (Bound _) = raise SAME
          | gen (Abs (x, T, t)) =
              (Abs (x, genT T, gen t handle SAME => t)
                handle SAME => Abs (x, T, gen t))
          | gen (t $ u) = (gen t $ (gen u handle SAME => u) handle SAME => t $ gen u);
      in gen tm end;

in

fun generalize names i tm = generalize_same names i tm handle SAME => tm;
fun generalizeT names i ty = generalizeT_same names i ty handle SAME => ty;

fun generalize_option names i tm = SOME (generalize_same names i tm) handle SAME => NONE;
fun generalizeT_option names i ty = SOME (generalizeT_same names i ty) handle SAME => NONE;

end;


(* instantiation of schematic variables (types before terms) -- recomputes maxidx *)

local

fun no_index (x, y) = (x, (y, ~1));
fun no_indexes1 inst = map no_index inst;
fun no_indexes2 (inst1, inst2) = (map no_index inst1, map no_index inst2);

exception SAME;

fun instantiateT_same maxidx instT ty =
  let
    fun maxify i = if i > ! maxidx then maxidx := i else ();

    fun subst_typ (Type (a, Ts)) = Type (a, subst_typs Ts)
      | subst_typ (TVar ((a, i), S)) =
          (case AList.lookup Term.eq_tvar instT ((a, i), S) of
            SOME (T, j) => (maxify j; T)
          | NONE => (maxify i; raise SAME))
      | subst_typ _ = raise SAME
    and subst_typs (T :: Ts) =
        (subst_typ T :: (subst_typs Ts handle SAME => Ts)
          handle SAME => T :: subst_typs Ts)
      | subst_typs [] = raise SAME;
  in subst_typ ty end;

fun instantiate_same maxidx (instT, inst) tm =
  let
    fun maxify i = if i > ! maxidx then maxidx := i else ();

    val substT = instantiateT_same maxidx instT;
    fun subst (Const (c, T)) = Const (c, substT T)
      | subst (Free (x, T)) = Free (x, substT T)
      | subst (Var ((x, i), T)) =
          let val (T', same) = (substT T, false) handle SAME => (T, true) in
            (case AList.lookup Term.eq_var inst ((x, i), T') of
               SOME (t, j) => (maxify j; t)
             | NONE => (maxify i; if same then raise SAME else Var ((x, i), T')))
          end
      | subst (Bound _) = raise SAME
      | subst (Abs (x, T, t)) =
          (Abs (x, substT T, subst t handle SAME => t)
            handle SAME => Abs (x, T, subst t))
      | subst (t $ u) = (subst t $ (subst u handle SAME => u) handle SAME => t $ subst u);
  in subst tm end;

in

fun instantiateT_maxidx instT ty i =
  let val maxidx = ref i
  in (instantiateT_same maxidx instT ty handle SAME => ty, ! maxidx) end;

fun instantiate_maxidx insts tm i =
  let val maxidx = ref i
  in (instantiate_same maxidx insts tm handle SAME => tm, ! maxidx) end;

fun instantiateT [] ty = ty
  | instantiateT instT ty =
      (instantiateT_same (ref ~1) (no_indexes1 instT) ty handle SAME => ty);

fun instantiate ([], []) tm = tm
  | instantiate insts tm =
      (instantiate_same (ref ~1) (no_indexes2 insts) tm handle SAME => tm);

fun instantiateT_option [] _ = NONE
  | instantiateT_option instT ty =
      (SOME (instantiateT_same (ref ~1) (no_indexes1 instT) ty) handle SAME => NONE);

fun instantiate_option ([], []) _ = NONE
  | instantiate_option insts tm =
      (SOME (instantiate_same (ref ~1) (no_indexes2 insts) tm) handle SAME => NONE);

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
    val tvars = sort TermOrd.tvar_ord (fold Term.add_tvars ts []);
    val instT = map (apsnd TVar) (zero_var_inst tvars);
    val vars = sort TermOrd.var_ord (map (apsnd (instantiateT instT)) (fold Term.add_vars ts []));
    val inst = map (apsnd Var) (zero_var_inst vars);
  in (instT, inst) end;

fun zero_var_indexes t = instantiate (zero_var_indexes_inst [t]) t;

end;
