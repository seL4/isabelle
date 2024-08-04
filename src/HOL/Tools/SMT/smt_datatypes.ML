(*  Title:      HOL/Tools/SMT/smt_datatypes.ML
    Author:     Sascha Boehme, TU Muenchen

Collector functions for common type declarations and their representation
as (co)algebraic datatypes.
*)

signature SMT_DATATYPES =
sig
  val add_decls: BNF_Util.fp_kind list -> typ ->
    (BNF_Util.fp_kind * (typ * (term * term list) list)) list list * Proof.context ->
    (BNF_Util.fp_kind * (typ * (term * term list) list)) list list * Proof.context
end;

structure SMT_Datatypes: SMT_DATATYPES =
struct

fun mk_selectors T Ts sels =
  if null sels then
    Variable.variant_fixes (replicate (length Ts) "select")
    #>> map2 (fn U => fn n => Free (n, T --> U)) Ts
  else
    pair sels


(* free constructor type declarations *)

fun get_ctr_sugar_decl ({ctrs = ctrs0, selss = selss0, ...} : Ctr_Sugar.ctr_sugar) T Ts ctxt =
  let
    val selss = map (map (Ctr_Sugar.mk_disc_or_sel Ts)) selss0
    val ctrs = map (Ctr_Sugar.mk_ctr Ts) ctrs0

    fun mk_constr ctr sels =
      mk_selectors T (binder_types (fastype_of ctr)) sels #>> pair ctr

    val selss' =
      (if has_duplicates (op aconv) (flat selss) orelse
          exists (exists (can (dest_funT o range_type o fastype_of))) selss then
         []
       else
         selss)
      |> Ctr_Sugar_Util.pad_list [] (length ctrs)
  in
    @{fold_map 2} mk_constr ctrs selss' ctxt
    |>> (pair T #> single)
  end


(* typedef declarations *)

fun get_typedef_decl (({Abs_name, Rep_name, abs_type, rep_type, ...}, {Abs_inverse, ...})
    : Typedef.info) T Ts =
  if can (curry (op RS) @{thm UNIV_I}) Abs_inverse then
    let
      val env = Term.dest_Type_args abs_type ~~ Ts
      val instT = Term.map_atyps (perhaps (AList.lookup (op =) env))

      val constr = Const (Abs_name, instT (rep_type --> abs_type))
      val select = Const (Rep_name, instT (abs_type --> rep_type))
    in [(T, [(constr, [select])])] end
  else
    []


(* collection of declarations *)

val extN = "_ext" (* cf. "HOL/Tools/typedef.ML" *)

fun get_decls fps T n Ts ctxt =
  let
    fun maybe_typedef () =
      (case Typedef.get_info ctxt n of
        [] => ([], ctxt)
      | info :: _ => (map (pair (hd fps)) (get_typedef_decl info T Ts), ctxt))
  in
    (case BNF_FP_Def_Sugar.fp_sugar_of ctxt n of
      SOME {fp, fp_res = {Ts = fp_Ts, ...}, fp_ctr_sugar = {ctr_sugar, ...}, ...} =>
      if member (op =) fps fp then
        let
          val ns = map dest_Type_name fp_Ts
          val mutual_fp_sugars = map_filter (BNF_FP_Def_Sugar.fp_sugar_of ctxt) ns
          val Xs = map #X mutual_fp_sugars
          val ctrXs_Tsss = map (#ctrXs_Tss o #fp_ctr_sugar) mutual_fp_sugars

          (* Datatypes nested through datatypes and codatatypes nested through codatatypes are
             allowed. So are mutually (co)recursive (co)datatypes. *)
          fun is_same_fp s =
            (case BNF_FP_Def_Sugar.fp_sugar_of ctxt s of
              SOME {fp = fp', ...} => fp' = fp
            | NONE => false)
          fun is_homogenously_nested_co_recursive (Type (s, Ts)) =
              forall (if is_same_fp s then is_homogenously_nested_co_recursive
                else not o BNF_FP_Rec_Sugar_Util.exists_subtype_in Xs) Ts
            | is_homogenously_nested_co_recursive _ = true

          val Type (_, As) :: _ = fp_Ts
          val substAs = Term.typ_subst_atomic (As ~~ Ts);
        in
          (* TODO/FIXME: The "bool" check is there to work around a CVC4 bug
             (http://church.cims.nyu.edu/bugzilla3/show_bug.cgi?id=597). It should be removed once
             the bug is fixed. *)
          if forall (forall (forall (is_homogenously_nested_co_recursive))) ctrXs_Tsss andalso
             forall (forall (forall (curry (op <>) \<^typ>\<open>bool\<close>)))
               (map (map (map substAs)) ctrXs_Tsss) then
            get_ctr_sugar_decl ctr_sugar T Ts ctxt |>> map (pair fp)
          else
            maybe_typedef ()
        end
      else
        ([], ctxt)
    | NONE =>
      if String.isSuffix extN n then
        (* for records (FIXME: hack) *)
        (case Ctr_Sugar.ctr_sugar_of ctxt n of
          SOME ctr_sugar =>
          get_ctr_sugar_decl ctr_sugar T Ts ctxt |>> map (pair (hd fps))
        | NONE => maybe_typedef ())
      else
        maybe_typedef ())
  end

fun add_decls fps T (declss, ctxt) =
  let
    fun declared T = exists (exists (equal T o fst o snd))
    fun declared' T = exists (exists (equal T o fst o snd) o snd)
    fun depends ds = exists (member (op =) (map (fst o snd) ds))

    fun add (TFree _) = I
      | add (TVar _) = I
      | add (T as Type (\<^type_name>\<open>fun\<close>, _)) =
          fold add (Term.body_type T :: Term.binder_types T)
      | add \<^typ>\<open>bool\<close> = I
      | add (T as Type (n, Ts)) = (fn (dss, ctxt1) =>
          if declared T declss orelse declared' T dss then
            (dss, ctxt1)
          else if SMT_Builtin.is_builtin_typ_ext ctxt1 T then
            (dss, ctxt1)
          else
            (case get_decls fps T n Ts ctxt1 of
              ([], _) => (dss, ctxt1)
            | (ds, ctxt2) =>
                let
                  val constrTs = maps (map (snd o Term.dest_Const o fst) o snd o snd) ds
                  val Us = fold (union (op =) o Term.binder_types) constrTs []

                  fun ins [] = [(Us, ds)]
                    | ins ((Uds as (Us', _)) :: Udss) =
                        if depends ds Us' then (Us, ds) :: Uds :: Udss else Uds :: ins Udss
            in fold add Us (ins dss, ctxt2) end))
  in add T ([], ctxt) |>> append declss o map snd end

end;
