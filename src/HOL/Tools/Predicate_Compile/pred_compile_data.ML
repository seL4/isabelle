(* Author: Lukas Bulwahn, TU Muenchen

Book-keeping datastructure for the predicate compiler

*)
signature PREDICATE_COMPILE_DATA =
sig
  type specification_table;
  val make_const_spec_table : theory -> specification_table
  val get_specification :  specification_table -> string -> thm list
  val obtain_specification_graph : theory -> specification_table -> string -> thm list Graph.T
  val normalize_equation : theory -> thm -> thm
end;

structure Predicate_Compile_Data : PREDICATE_COMPILE_DATA =
struct

open Predicate_Compile_Aux;

structure Data = TheoryDataFun
(
  type T =
    {const_spec_table : thm list Symtab.table};
  val empty =
    {const_spec_table = Symtab.empty};
  val copy = I;
  val extend = I;
  fun merge _
    ({const_spec_table = const_spec_table1},
     {const_spec_table = const_spec_table2}) =
     {const_spec_table = Symtab.merge (K true) (const_spec_table1, const_spec_table2)}
);

fun mk_data c = {const_spec_table = c}
fun map_data f {const_spec_table = c} = mk_data (f c)

type specification_table = thm list Symtab.table

fun defining_const_of_introrule_term t =
  let
    val _ $ u = Logic.strip_imp_concl t
    val (pred, all_args) = strip_comb u
  in case pred of
    Const (c, T) => c
    | _ => raise TERM ("defining_const_of_introrule_term failed: Not a constant", [t])
  end

val defining_const_of_introrule = defining_const_of_introrule_term o prop_of

(*TODO*)
fun is_introlike_term t = true

val is_introlike = is_introlike_term o prop_of

fun check_equation_format_term (t as (Const ("==", _) $ u $ v)) =
  (case strip_comb u of
    (Const (c, T), args) =>
      if (length (binder_types T) = length args) then
        true
      else
        raise TERM ("check_equation_format_term failed: Number of arguments mismatch", [t])
  | _ => raise TERM ("check_equation_format_term failed: Not a constant", [t]))
  | check_equation_format_term t =
    raise TERM ("check_equation_format_term failed: Not an equation", [t])

val check_equation_format = check_equation_format_term o prop_of

fun defining_const_of_equation_term (t as (Const ("==", _) $ u $ v)) =
  (case fst (strip_comb u) of
    Const (c, _) => c
  | _ => raise TERM ("defining_const_of_equation_term failed: Not a constant", [t]))
  | defining_const_of_equation_term t =
    raise TERM ("defining_const_of_equation_term failed: Not an equation", [t])

val defining_const_of_equation = defining_const_of_equation_term o prop_of

(* Normalizing equations *)

fun mk_meta_equation th =
  case prop_of th of
    Const ("Trueprop", _) $ (Const ("op =", _) $ _ $ _) => th RS @{thm eq_reflection}
  | _ => th

val meta_fun_cong = @{lemma "f == g ==> f x == g x" by simp}

fun full_fun_cong_expand th =
  let
    val (f, args) = strip_comb (fst (Logic.dest_equals (prop_of th)))
    val i = length (binder_types (fastype_of f)) - length args
  in funpow i (fn th => th RS meta_fun_cong) th end;

fun declare_names s xs ctxt =
  let
    val res = Name.names ctxt s xs
  in (res, fold Name.declare (map fst res) ctxt) end
  
fun split_all_pairs thy th =
  let
    val ctxt = ProofContext.init thy
    val ((_, [th']), ctxt') = Variable.import true [th] ctxt
    val t = prop_of th'
    val frees = Term.add_frees t [] 
    val freenames = Term.add_free_names t []
    val nctxt = Name.make_context freenames
    fun mk_tuple_rewrites (x, T) nctxt =
      let
        val Ts = HOLogic.flatten_tupleT T
        val (xTs, nctxt') = declare_names x Ts nctxt
        val paths = HOLogic.flat_tupleT_paths T
      in ((Free (x, T), HOLogic.mk_ptuple paths T (map Free xTs)), nctxt') end
    val (rewr, _) = fold_map mk_tuple_rewrites frees nctxt 
    val t' = Pattern.rewrite_term thy rewr [] t
    val tac = Skip_Proof.cheat_tac thy
    val th'' = Goal.prove ctxt (Term.add_free_names t' []) [] t' (fn {...} => tac)
    val th''' = LocalDefs.unfold ctxt [@{thm split_conv}] th''
  in
    th'''
  end;

fun normalize_equation thy th =
  mk_meta_equation th
  |> Predicate_Compile_Set.unfold_set_notation
  |> full_fun_cong_expand
  |> split_all_pairs thy
  |> tap check_equation_format

fun inline_equations thy th = Conv.fconv_rule (Simplifier.rewrite
((Simplifier.theory_context thy Simplifier.empty_ss) addsimps (Predicate_Compile_Inline_Defs.get (ProofContext.init thy)))) th

fun store_thm_in_table ignore_consts thy th=
  let
    val th = th
      |> inline_equations thy
      |> Predicate_Compile_Set.unfold_set_notation
      |> AxClass.unoverload thy
    val (const, th) =
      if is_equationlike th then
        let
          val eq = normalize_equation thy th
        in
          (defining_const_of_equation eq, eq)
        end
      else if (is_introlike th) then (defining_const_of_introrule th, th)
      else error "store_thm: unexpected definition format"
  in
    if not (member (op =) ignore_consts const) then
      Symtab.cons_list (const, th)
    else I
  end

fun make_const_spec_table thy =
  let
    fun store ignore_const f = fold (store_thm_in_table ignore_const thy) (map (Thm.transfer thy) (f (ProofContext.init thy)))
    val table = Symtab.empty
      |> store [] Predicate_Compile_Alternative_Defs.get
    val ignore_consts = Symtab.keys table
  in
    table
    |> store ignore_consts Predicate_Compile_Preproc_Const_Defs.get
    |> store ignore_consts Nitpick_Simps.get
    |> store ignore_consts Nitpick_Intros.get
  end

fun get_specification table constname =
  case Symtab.lookup table constname of
    SOME thms => thms
  | NONE => error ("get_specification: lookup of constant " ^ quote constname ^ " failed")

val logic_operator_names =
  [@{const_name "=="}, @{const_name "op ="}, @{const_name "op -->"}, @{const_name "All"}, @{const_name "Ex"}, 
   @{const_name "op &"}]

val special_cases = member (op =) [
    @{const_name "False"},
    @{const_name "Suc"}, @{const_name Nat.zero_nat_inst.zero_nat},
    @{const_name Nat.one_nat_inst.one_nat},
@{const_name "HOL.ord_class.less"}, @{const_name "HOL.ord_class.less_eq"}, @{const_name "HOL.zero_class.zero"},
@{const_name "HOL.one_class.one"},  @{const_name HOL.plus_class.plus},
@{const_name Nat.ord_nat_inst.less_eq_nat},
@{const_name number_nat_inst.number_of_nat},
  @{const_name Int.Bit0},
  @{const_name Int.Bit1},
  @{const_name Int.Pls},
@{const_name "Int.zero_int_inst.zero_int"},
@{const_name "List.filter"}]

fun case_consts thy s = is_some (Datatype.info_of_case thy s)

fun obtain_specification_graph thy table constname =
  let
    fun is_nondefining_constname c = member (op =) logic_operator_names c
    val is_defining_constname = member (op =) (Symtab.keys table)
    fun has_code_pred_intros c = is_some (try (Predicate_Compile_Core.intros_of thy) c)
    fun defiants_of specs =
      fold (Term.add_const_names o prop_of) specs []
      |> filter is_defining_constname
      |> filter_out is_nondefining_constname
      |> filter_out has_code_pred_intros
      |> filter_out (case_consts thy)
      |> filter_out special_cases
    fun extend constname =
      let
        val specs = get_specification table constname
      in (specs, defiants_of specs) end;
  in
    Graph.extend extend constname Graph.empty
  end;
  
  
end;
