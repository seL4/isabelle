(*  Title:      HOL/Tools/SMT2/smt2_datatypes.ML
    Author:     Sascha Boehme, TU Muenchen

Collector functions for common type declarations and their representation
as algebraic datatypes.
*)

signature SMT2_DATATYPES =
sig
  val add_decls: typ ->
    (typ * (term * term list) list) list list * Proof.context ->
    (typ * (term * term list) list) list list * Proof.context
end;

structure SMT2_Datatypes: SMT2_DATATYPES =
struct

fun mk_selectors T Ts =
  Variable.variant_fixes (replicate (length Ts) "select")
  #>> map2 (fn U => fn n => Free (n, T --> U)) Ts


(* free constructor type declarations *)

fun get_ctr_sugar_decl ({ctrs, ...} : Ctr_Sugar.ctr_sugar) T Ts ctxt =
  let
    fun mk_constr ctr0 =
      let val ctr = Ctr_Sugar.mk_ctr Ts ctr0 in
        mk_selectors T (binder_types (fastype_of ctr)) #>> pair ctr
      end
  in
    fold_map mk_constr ctrs ctxt
    |>> (pair T #> single)
  end


(* typedef declarations *)

fun get_typedef_decl (({Abs_name, Rep_name, abs_type, rep_type, ...}, {Abs_inverse, ...})
    : Typedef.info) T Ts =
  if can (curry (op RS) @{thm UNIV_I}) Abs_inverse then
    let
      val env = snd (Term.dest_Type abs_type) ~~ Ts
      val instT = Term.map_atyps (perhaps (AList.lookup (op =) env))

      val constr = Const (Abs_name, instT (rep_type --> abs_type))
      val select = Const (Rep_name, instT (abs_type --> rep_type))
    in [(T, [(constr, [select])])] end
  else
    []


(* collection of declarations *)

fun declared declss T = exists (exists (equal T o fst)) declss
fun declared' dss T = exists (exists (equal T o fst) o snd) dss

fun get_decls T n Ts ctxt =
  (case Ctr_Sugar.ctr_sugar_of ctxt n of
    SOME ctr_sugar => get_ctr_sugar_decl ctr_sugar T Ts ctxt
  | NONE =>
      (case Typedef.get_info ctxt n of
        [] => ([], ctxt)
      | info :: _ => (get_typedef_decl info T Ts, ctxt)))

fun add_decls T (declss, ctxt) =
  let
    fun depends Ts ds = exists (member (op =) (map fst ds)) Ts

    fun add (TFree _) = I
      | add (TVar _) = I
      | add (T as Type (@{type_name fun}, _)) =
          fold add (Term.body_type T :: Term.binder_types T)
      | add @{typ bool} = I
      | add (T as Type (n, Ts)) = (fn (dss, ctxt1) =>
          if declared declss T orelse declared' dss T then (dss, ctxt1)
          else if SMT2_Builtin.is_builtin_typ_ext ctxt1 T then (dss, ctxt1)
          else
            (case get_decls T n Ts ctxt1 of
              ([], _) => (dss, ctxt1)
            | (ds, ctxt2) =>
                let
                  val constrTs = maps (map (snd o Term.dest_Const o fst) o snd) ds
                  val Us = fold (union (op =) o Term.binder_types) constrTs []

                  fun ins [] = [(Us, ds)]
                    | ins ((Uds as (Us', _)) :: Udss) =
                        if depends Us' ds then (Us, ds) :: Uds :: Udss
                        else Uds :: ins Udss
            in fold add Us (ins dss, ctxt2) end))
  in add T ([], ctxt) |>> append declss o map snd end

end;
