signature DATATYPE_RECORDS = sig
  type ctr_options = string -> bool
  type ctr_options_cmd = Proof.context -> string -> bool

  val default_ctr_options: ctr_options
  val default_ctr_options_cmd: ctr_options_cmd

  val mk_update_defs: string -> local_theory -> local_theory

  val record: binding -> ctr_options -> (binding option * (typ * sort)) list ->
    (binding * typ) list -> local_theory -> local_theory

  val record_cmd: binding -> ctr_options_cmd ->
    (binding option * (string * string option)) list -> (binding * string) list -> local_theory ->
    local_theory

  val setup: theory -> theory
end

structure Datatype_Records : DATATYPE_RECORDS = struct

type ctr_options = string -> bool
type ctr_options_cmd = Proof.context -> string -> bool

val default_ctr_options = Plugin_Name.default_filter
val default_ctr_options_cmd = K Plugin_Name.default_filter

type data = string Symtab.table

structure Data = Theory_Data
(
  type T = data
  val empty = Symtab.empty
  val merge = Symtab.merge op =
  val extend = I
)

fun mk_eq_dummy (lhs, rhs) =
  Const (\<^const_name>\<open>HOL.eq\<close>, dummyT --> dummyT --> \<^typ>\<open>bool\<close>) $ lhs $ rhs

val dummify = map_types (K dummyT)
fun repeat_split_tac ctxt thm = REPEAT_ALL_NEW (CHANGED o Splitter.split_tac ctxt [thm])

fun mk_update_defs typ_name lthy =
  let
    val short_name = Long_Name.base_name typ_name
    val {ctrs, casex, selss, split, sel_thmss, injects, ...} =
      the (Ctr_Sugar.ctr_sugar_of lthy typ_name)
    val ctr = case ctrs of [ctr] => ctr | _ => error "Datatype_Records.mk_update_defs: expected only single constructor"
    val sels = case selss of [sels] => sels | _ => error "Datatype_Records.mk_update_defs: expected selectors"
    val sels_dummy = map dummify sels
    val ctr_dummy = dummify ctr
    val casex_dummy = dummify casex
    val len = length sels

    val simp_thms = flat sel_thmss @ injects

    fun mk_name sel =
      Binding.name ("update_" ^ Long_Name.base_name (fst (dest_Const sel)))

    val thms_binding = (Binding.name "record_simps", @{attributes [simp]})

    fun mk_t idx =
      let
        val body =
          fold_rev (fn pos => fn t => t $ (if len - pos = idx + 1 then Bound len $ Bound pos else Bound pos)) (0 upto len - 1) ctr_dummy
          |> fold_rev (fn idx => fn t => Abs ("x" ^ Value.print_int idx, dummyT, t)) (1 upto len)
      in
        Abs ("f", dummyT, casex_dummy $ body)
      end

    fun simp_only_tac ctxt =
      REPEAT_ALL_NEW (resolve_tac ctxt @{thms impI allI}) THEN'
        asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps simp_thms)

    fun prove ctxt defs ts n =
      let
        val t = nth ts n

        val sel_dummy = nth sels_dummy n
        val t_dummy = dummify t
        fun tac {context = ctxt, ...} =
          Goal.conjunction_tac 1 THEN
            Local_Defs.unfold_tac ctxt defs THEN
            PARALLEL_ALLGOALS (repeat_split_tac ctxt split THEN' simp_only_tac ctxt)

        val sel_upd_same_thm =
          let
            val ([f, x], ctxt') = Variable.add_fixes ["f", "x"] ctxt
            val f = Free (f, dummyT)
            val x = Free (x, dummyT)

            val lhs = sel_dummy $ (t_dummy $ f $ x)
            val rhs = f $ (sel_dummy $ x)
            val prop = Syntax.check_term ctxt' (HOLogic.mk_Trueprop (mk_eq_dummy (lhs, rhs)))
          in
            [Goal.prove_future ctxt' [] [] prop tac]
            |> Variable.export ctxt' ctxt
          end

        val sel_upd_diff_thms =
          let
            val ([f, x], ctxt') = Variable.add_fixes ["f", "x"] ctxt
            val f = Free (f, dummyT)
            val x = Free (x, dummyT)

            fun lhs sel = sel $ (t_dummy $ f $ x)
            fun rhs sel = sel $ x
            fun eq sel = (lhs sel, rhs sel)
            fun is_n i = i = n
            val props =
              sels_dummy ~~ (0 upto len - 1)
              |> filter_out (is_n o snd)
              |> map (HOLogic.mk_Trueprop o mk_eq_dummy o eq o fst)
              |> Syntax.check_terms ctxt'
          in
            if length props > 0 then
              Goal.prove_common ctxt' (SOME ~1) [] [] props tac
              |> Variable.export ctxt' ctxt
            else
              []
          end

        val upd_comp_thm =
          let
            val ([f, g, x], ctxt') = Variable.add_fixes ["f", "g", "x"] ctxt
            val f = Free (f, dummyT)
            val g = Free (g, dummyT)
            val x = Free (x, dummyT)

            val lhs = t_dummy $ f $ (t_dummy $ g $ x)
            val rhs = t_dummy $ Abs ("a", dummyT, f $ (g $ Bound 0)) $ x
            val prop = Syntax.check_term ctxt' (HOLogic.mk_Trueprop (mk_eq_dummy (lhs, rhs)))
          in
            [Goal.prove_future ctxt' [] [] prop tac]
            |> Variable.export ctxt' ctxt
          end

        val upd_comm_thms =
          let
            fun prop i ctxt =
              let
                val ([f, g, x], ctxt') = Variable.variant_fixes ["f", "g", "x"] ctxt
                val self = t_dummy $ Free (f, dummyT)
                val other = dummify (nth ts i) $ Free (g, dummyT)
                val lhs = other $ (self $ Free (x, dummyT))
                val rhs = self $ (other $ Free (x, dummyT))
              in
                (HOLogic.mk_Trueprop (mk_eq_dummy (lhs, rhs)), ctxt')
              end
            val (props, ctxt') = fold_map prop (0 upto n - 1) ctxt
            val props = Syntax.check_terms ctxt' props
          in
            if length props > 0 then
              Goal.prove_common ctxt' (SOME ~1) [] [] props tac
              |> Variable.export ctxt' ctxt
            else
              []
          end

        val upd_sel_thm =
          let
            val ([x], ctxt') = Variable.add_fixes ["x"] ctxt

            val lhs = t_dummy $ Abs("_", dummyT, (sel_dummy $ Free(x, dummyT))) $ Free (x, dummyT)
            val rhs = Free (x, dummyT)
            val prop = Syntax.check_term ctxt (HOLogic.mk_Trueprop (mk_eq_dummy (lhs, rhs)))
          in
            [Goal.prove_future ctxt [] [] prop tac]
            |> Variable.export ctxt' ctxt
          end
      in
        sel_upd_same_thm @ sel_upd_diff_thms @ upd_comp_thm @ upd_comm_thms @ upd_sel_thm
      end

    fun define name t =
      Local_Theory.define ((name, NoSyn), ((Binding.empty, @{attributes [datatype_record_update, code]}),t))
      #> apfst (apsnd snd)

    val (updates, (lthy'', lthy')) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> Local_Theory.map_background_naming (Name_Space.qualified_path false (Binding.name short_name))
      |> @{fold_map 2} define (map mk_name sels) (Syntax.check_terms lthy (map mk_t (0 upto len - 1)))
      ||> `Local_Theory.end_nested

    val phi = Proof_Context.export_morphism lthy' lthy''

    val (update_ts, update_defs) =
      split_list updates
      |>> map (Morphism.term phi)
      ||> map (Morphism.thm phi)

    val thms = flat (map (prove lthy'' update_defs update_ts) (0 upto len-1))

    fun insert sel =
      Symtab.insert op = (fst (dest_Const sel), Local_Theory.full_name lthy' (mk_name sel))
  in
    lthy''
    |> Local_Theory.map_background_naming (Name_Space.mandatory_path short_name)
    |> Local_Theory.note (thms_binding, thms)
    |> snd
    |> Local_Theory.restore_background_naming lthy
    |> Local_Theory.background_theory (Data.map (fold insert sels))
  end

fun record binding opts tyargs args lthy =
  let
    val constructor =
      (((Binding.empty, Binding.map_name (fn c => "make_" ^ c) binding), args), NoSyn)

    val datatyp =
      ((tyargs, binding), NoSyn)

    val dtspec =
      ((opts, false),
       [(((datatyp, [constructor]), (Binding.empty, Binding.empty, Binding.empty)), [])])

    val lthy' =
      BNF_FP_Def_Sugar.co_datatypes BNF_Util.Least_FP BNF_LFP.construct_lfp dtspec lthy
      |> mk_update_defs (Local_Theory.full_name lthy binding)
  in
    lthy'
  end

fun record_cmd binding opts tyargs args lthy =
  record binding (opts lthy)
    (map (apsnd (apfst (Syntax.parse_typ lthy) o apsnd (Typedecl.read_constraint lthy))) tyargs)
    (map (apsnd (Syntax.parse_typ lthy)) args) lthy

(* syntax *)
(* copied and adapted from record.ML *)

val read_const =
  dest_Const oo Proof_Context.read_const {proper = true, strict = true}

fun field_tr ((Const (\<^syntax_const>\<open>_datatype_field\<close>, _) $ Const (name, _) $ arg)) = (name, arg)
  | field_tr t = raise TERM ("field_tr", [t]);

fun fields_tr (Const (\<^syntax_const>\<open>_datatype_fields\<close>, _) $ t $ u) = field_tr t :: fields_tr u
  | fields_tr t = [field_tr t];

fun record_fields_tr ctxt t =
  let
    val assns = map (apfst (read_const ctxt)) (fields_tr t)

    val typ_name =
      snd (fst (hd assns))
      |> domain_type
      |> dest_Type
      |> fst

    val assns' = map (apfst fst) assns

    val {ctrs, selss, ...} = the (Ctr_Sugar.ctr_sugar_of ctxt typ_name)
    val ctr = case ctrs of [ctr] => ctr | _ => error "BNF_Record.record_fields_tr: expected only single constructor"
    val sels = case selss of [sels] => sels | _ => error "BNF_Record.record_fields_tr: expected selectors"
    val ctr_dummy = Const (fst (dest_Const ctr), dummyT)

    fun mk_arg name =
      case AList.lookup op = assns' name of
        NONE => error ("BNF_Record.record_fields_tr: missing field " ^ name)
      | SOME t => t
  in
    if length assns = length sels then
      list_comb (ctr_dummy, map (mk_arg o fst o dest_Const) sels)
    else
      error ("BNF_Record.record_fields_tr: expected " ^ Value.print_int (length sels) ^ " field(s)")
  end

fun field_update_tr ctxt (Const (\<^syntax_const>\<open>_datatype_field_update\<close>, _) $ Const (name, _) $ arg) =
      let
        val thy = Proof_Context.theory_of ctxt
        val (name, _) = read_const ctxt name
      in
        case Symtab.lookup (Data.get thy) name of
          NONE => raise Fail ("not a valid record field: " ^ name)
        | SOME s => Const (s, dummyT) $ Abs (Name.uu_, dummyT, arg)
      end
  | field_update_tr _ t = raise TERM ("field_update_tr", [t]);

fun field_updates_tr ctxt (Const (\<^syntax_const>\<open>_datatype_field_updates\<close>, _) $ t $ u) =
      field_update_tr ctxt t :: field_updates_tr ctxt u
  | field_updates_tr ctxt t = [field_update_tr ctxt t];

fun record_tr ctxt [t] = record_fields_tr ctxt t
  | record_tr _ ts = raise TERM ("record_tr", ts);

fun record_update_tr ctxt [t, u] = fold (curry op $) (field_updates_tr ctxt u) t
  | record_update_tr _ ts = raise TERM ("record_update_tr", ts);

val parse_ctr_options =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.list1 (Plugin_Name.parse_filter >> K) --| \<^keyword>\<open>)\<close> >>
    (fn fs => fold I fs default_ctr_options_cmd)) default_ctr_options_cmd

val parser =
  (parse_ctr_options -- BNF_Util.parse_type_args_named_constrained -- Parse.binding) --
    (\<^keyword>\<open>=\<close> |-- Scan.repeat1 (Parse.binding -- (\<^keyword>\<open>::\<close> |-- Parse.!!! Parse.typ)))

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>datatype_record\<close>
    "Defines a record based on the BNF/datatype machinery"
    (parser >> (fn (((ctr_options, tyargs), binding), args) =>
      record_cmd binding ctr_options tyargs args))

val setup =
   (Sign.parse_translation
     [(\<^syntax_const>\<open>_datatype_record_update\<close>, record_update_tr),
      (\<^syntax_const>\<open>_datatype_record\<close>, record_tr)]);

end