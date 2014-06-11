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
end

structure SMT2_Datatypes: SMT2_DATATYPES =
struct

val lhs_head_of = Term.head_of o fst o Logic.dest_equals o Thm.prop_of

fun mk_selectors T Ts ctxt =
  let
    val (sels, ctxt') = Variable.variant_fixes (replicate (length Ts) "select") ctxt
  in (map2 (fn n => fn U => Free (n, T --> U)) sels Ts, ctxt') end


(* datatype declarations *)

fun get_datatype_decl ({descr, ...} : Datatype.info) n Ts ctxt =
  let
    fun get_vars (_, (m, vs, _)) = if m = n then SOME vs else NONE
    val vars = the (get_first get_vars descr) ~~ Ts
    val lookup_var = the o AList.lookup (op =) vars

    fun typ_of (dt as Datatype.DtTFree _) = lookup_var dt
      | typ_of (Datatype.DtType (m, dts)) = Type (m, map typ_of dts)
      | typ_of (Datatype.DtRec i) =
          the (AList.lookup (op =) descr i)
          |> (fn (m, dts, _) => Type (m, map typ_of dts))

    fun mk_constr T (m, dts) ctxt =
      let
        val Ts = map typ_of dts
        val constr = Const (m, Ts ---> T)
        val (selects, ctxt') = mk_selectors T Ts ctxt
      in ((constr, selects), ctxt') end

    fun mk_decl (i, (_, _, constrs)) ctxt =
      let
        val T = typ_of (Datatype.DtRec i)
        val (css, ctxt') = fold_map (mk_constr T) constrs ctxt
      in ((T, css), ctxt') end

  in fold_map mk_decl descr ctxt end


(* record declarations *)

val record_name_of = Long_Name.implode o fst o split_last o Long_Name.explode

fun get_record_decl ({ext_def, ...} : Record.info) T ctxt =
  let
    val (con, _) = Term.dest_Const (lhs_head_of ext_def)
    val (fields, more) = Record.get_extT_fields (Proof_Context.theory_of ctxt) T
    val fieldTs = map snd fields @ [snd more]

    val constr = Const (con, fieldTs ---> T)
    val (selects, ctxt') = mk_selectors T fieldTs ctxt
  in ((T, [(constr, selects)]), ctxt') end


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
  let val thy = Proof_Context.theory_of ctxt
  in
    (case Datatype.get_info thy n of
      SOME info => get_datatype_decl info n Ts ctxt
    | NONE =>
        (case Record.get_info thy (record_name_of n) of
          SOME info => get_record_decl info T ctxt |>> single
        | NONE =>
            (case Typedef.get_info ctxt n of
              [] => ([], ctxt)
            | info :: _ => (get_typedef_decl info T Ts, ctxt))))
  end

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
                  val constrTs =
                    maps (map (snd o Term.dest_Const o fst) o snd) ds
                  val Us = fold (union (op =) o Term.binder_types) constrTs []

                  fun ins [] = [(Us, ds)]
                    | ins ((Uds as (Us', _)) :: Udss) =
                        if depends Us' ds then (Us, ds) :: Uds :: Udss
                        else Uds :: ins Udss
            in fold add Us (ins dss, ctxt2) end))
  in add T ([], ctxt) |>> append declss o map snd end

end
