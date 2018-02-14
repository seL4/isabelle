signature DATATYPE_RECORDS = sig
  type ctr_options = string -> bool
  type ctr_options_cmd = Proof.context -> string -> bool

  val default_ctr_options: ctr_options
  val default_ctr_options_cmd: ctr_options_cmd

  val mk_update_defs: string -> local_theory -> local_theory

  val bnf_record: binding -> ctr_options -> (binding option * (typ * sort)) list ->
    (binding * typ) list -> local_theory -> local_theory

  val bnf_record_cmd: binding -> ctr_options_cmd ->
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

fun mk_update_defs typ_name lthy =
  let
    val short_name = Long_Name.base_name typ_name

    val {ctrs, casex, selss, ...} = the (Ctr_Sugar.ctr_sugar_of lthy typ_name)
    val ctr = case ctrs of [ctr] => ctr | _ => error "BNF_Record.mk_update_defs: expected only single constructor"
    val sels = case selss of [sels] => sels | _ => error "BNF_Record.mk_update_defs: expected selectors"
    val ctr_dummy = Const (fst (dest_Const ctr), dummyT)
    val casex_dummy = Const (fst (dest_Const casex), dummyT)

    val len = length sels

    fun mk_name sel =
      Binding.name ("update_" ^ Long_Name.base_name (fst (dest_Const sel)))

    fun mk_t idx =
      let
        val body =
          fold_rev (fn pos => fn t => t $ (if len - pos = idx + 1 then Bound len $ Bound pos else Bound pos)) (0 upto len - 1) ctr_dummy
          |> fold_rev (fn idx => fn t => Abs ("x" ^ Value.print_int idx, dummyT, t)) (1 upto len)
      in
        Abs ("f", dummyT, casex_dummy $ body)
      end

    fun define name t =
      Local_Theory.define ((name, NoSyn), ((Binding.empty, @{attributes [datatype_record_update, code]}), t)) #> snd

    val lthy' =
      Local_Theory.map_background_naming (Name_Space.qualified_path false (Binding.name short_name)) lthy

    fun insert sel =
      Symtab.insert op = (fst (dest_Const sel), Local_Theory.full_name lthy' (mk_name sel))
  in
    lthy'
    |> @{fold 2} define (map mk_name sels) (Syntax.check_terms lthy (map mk_t (0 upto len - 1)))
    |> Local_Theory.background_theory (Data.map (fold insert sels))
    |> Local_Theory.restore_background_naming lthy
  end

fun bnf_record binding opts tyargs args lthy =
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

fun bnf_record_cmd binding opts tyargs args lthy =
  bnf_record binding (opts lthy)
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
  | field_update_tr _ t = raise TERM ("field_update_tr", [@{print} t]);

fun field_updates_tr ctxt (Const (\<^syntax_const>\<open>_datatype_field_updates\<close>, _) $ t $ u) =
      field_update_tr ctxt t :: field_updates_tr ctxt u
  | field_updates_tr ctxt t = [field_update_tr ctxt t];

fun record_tr ctxt [t] = record_fields_tr ctxt t
  | record_tr _ ts = raise TERM ("record_tr", ts);

fun record_update_tr ctxt [t, u] = fold (curry op $) (field_updates_tr ctxt u) t
  | record_update_tr _ ts = raise TERM ("record_update_tr", ts);

val parse_ctr_options =
  Scan.optional (@{keyword "("} |-- Parse.list1 (Plugin_Name.parse_filter >> K) --| @{keyword ")"} >>
    (fn fs => fold I fs default_ctr_options_cmd)) default_ctr_options_cmd

val parser =
  (parse_ctr_options -- BNF_Util.parse_type_args_named_constrained -- Parse.binding) --
    (\<^keyword>\<open>=\<close> |-- Scan.repeat1 (Parse.binding -- (Parse.$$$ "::" |-- Parse.!!! Parse.typ)))

val _ =
  Outer_Syntax.local_theory
    @{command_keyword datatype_record}
    "Defines a record based on the BNF/datatype machinery"
    (parser >> (fn (((ctr_options, tyargs), binding), args) =>
      bnf_record_cmd binding ctr_options tyargs args))

val setup =
   (Sign.parse_translation
     [(\<^syntax_const>\<open>_datatype_record_update\<close>, record_update_tr),
      (\<^syntax_const>\<open>_datatype_record\<close>, record_tr)]);

end