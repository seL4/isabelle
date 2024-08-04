(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_data.ML
    Author:     Lukas Bulwahn, TU Muenchen

Book-keeping datastructure for the predicate compiler.
*)

signature PREDICATE_COMPILE_DATA =
sig
  val ignore_consts : string list -> theory -> theory
  val keep_functions : string list -> theory -> theory
  val keep_function : theory -> string -> bool
  val processed_specs : theory -> string -> (string * thm list) list option
  val store_processed_specs : (string * (string * thm list) list) -> theory -> theory

  val get_specification : Predicate_Compile_Aux.options -> theory -> term -> thm list
  val obtain_specification_graph :
    Predicate_Compile_Aux.options -> theory -> term -> thm list Term_Graph.T

  val normalize_equation : theory -> thm -> thm
end;

structure Predicate_Compile_Data : PREDICATE_COMPILE_DATA =
struct

open Predicate_Compile_Aux;

structure Data = Theory_Data
(
  type T =
    {ignore_consts : Symset.T,
     keep_functions : Symset.T,
     processed_specs : ((string * thm list) list) Symtab.table};
  val empty =
    {ignore_consts = Symset.empty,
     keep_functions = Symset.empty,
     processed_specs =  Symtab.empty};
  fun merge
    ({ignore_consts = c1, keep_functions = k1, processed_specs = s1},
     {ignore_consts = c2, keep_functions = k2, processed_specs = s2}) =
     {ignore_consts = Symset.merge (c1, c2),
      keep_functions = Symset.merge (k1, k2),
      processed_specs = Symtab.merge (K true) (s1, s2)}
);



fun mk_data (c, k, s) = {ignore_consts = c, keep_functions = k, processed_specs = s}
fun map_data f {ignore_consts = c, keep_functions = k, processed_specs = s} = mk_data (f (c, k, s))

fun ignore_consts cs =
  Data.map (map_data (@{apply 3(1)} (fold Symset.insert cs)))

fun keep_functions cs =
  Data.map (map_data (@{apply 3(2)} (fold Symset.insert cs)))

fun keep_function thy = Symset.member (#keep_functions (Data.get thy))

fun processed_specs thy = Symtab.lookup (#processed_specs (Data.get thy))

fun store_processed_specs (constname, specs) =
  Data.map (map_data (@{apply 3(3)} (Symtab.update_new (constname, specs))))


fun defining_term_of_introrule_term t =
  let
    val _ $ u = Logic.strip_imp_concl t
  in fst (strip_comb u) end
(*
  in case pred of
    Const (c, T) => c
    | _ => raise TERM ("defining_const_of_introrule_term failed: Not a constant", [t])
  end
*)
val defining_term_of_introrule = defining_term_of_introrule_term o Thm.prop_of

fun defining_const_of_introrule th =
  (case defining_term_of_introrule th of
    Const (c, _) => c
  | _ => raise TERM ("defining_const_of_introrule failed: Not a constant", [Thm.prop_of th]))

(*TODO*)
fun is_introlike_term _ = true

val is_introlike = is_introlike_term o Thm.prop_of

fun check_equation_format_term (t as (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ u $ _)) =
      (case strip_comb u of
        (Const (_, T), args) =>
          if (length (binder_types T) = length args) then
            true
          else
            raise TERM ("check_equation_format_term failed: Number of arguments mismatch", [t])
      | _ => raise TERM ("check_equation_format_term failed: Not a constant", [t]))
  | check_equation_format_term t =
      raise TERM ("check_equation_format_term failed: Not an equation", [t])

val check_equation_format = check_equation_format_term o Thm.prop_of


fun defining_term_of_equation_term (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ u $ _) = fst (strip_comb u)
  | defining_term_of_equation_term t =
      raise TERM ("defining_const_of_equation_term failed: Not an equation", [t])

val defining_term_of_equation = defining_term_of_equation_term o Thm.prop_of

fun defining_const_of_equation th =
  (case defining_term_of_equation th of
    Const (c, _) => c
  | _ => raise TERM ("defining_const_of_equation failed: Not a constant", [Thm.prop_of th]))




(* Normalizing equations *)

fun mk_meta_equation th =
  (case Thm.prop_of th of
    Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _) =>
      th RS @{thm eq_reflection}
  | _ => th)

val meta_fun_cong = @{lemma "\<And>f :: 'a::{} \<Rightarrow> 'b::{}.f == g ==> f x == g x" by simp}

fun full_fun_cong_expand th =
  let
    val (f, args) = strip_comb (fst (Logic.dest_equals (Thm.prop_of th)))
    val i = length (binder_types (fastype_of f)) - length args
  in funpow i (fn th => th RS meta_fun_cong) th end;

fun declare_names s xs ctxt =
  let
    val res = Name.invent_names ctxt s xs
  in (res, fold Name.declare (map fst res) ctxt) end

fun split_all_pairs thy th =
  let
    val ctxt = Proof_Context.init_global thy  (* FIXME proper context!? *)
    val ((_, [th']), _) = Variable.import true [th] ctxt
    val t = Thm.prop_of th'
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
    val th'' =
      Goal.prove ctxt (Term.add_free_names t' []) [] t'
        (fn _ => ALLGOALS (Skip_Proof.cheat_tac ctxt))
    val th''' = Local_Defs.unfold0 ctxt [@{thm split_conv}, @{thm fst_conv}, @{thm snd_conv}] th''
  in
    th'''
  end;


fun inline_equations thy th =
  let
    val ctxt = Proof_Context.init_global thy
    val inline_defs = Named_Theorems.get ctxt \<^named_theorems>\<open>code_pred_inline\<close>
    val th' = Simplifier.full_simplify (put_simpset HOL_basic_ss ctxt addsimps inline_defs) th
    (*val _ = print_step options
      ("Inlining " ^ (Syntax.string_of_term_global thy (prop_of th))
       ^ "with " ^ (commas (map ((Syntax.string_of_term_global thy) o prop_of) inline_defs))
       ^" to " ^ (Syntax.string_of_term_global thy (prop_of th')))*)
  in
    th'
  end

fun normalize_equation thy th =
  mk_meta_equation th
  |> full_fun_cong_expand
  |> split_all_pairs thy
  |> tap check_equation_format
  |> inline_equations thy

fun normalize_intros thy th =
  split_all_pairs thy th
  |> inline_equations thy

fun normalize thy th =
  if is_equationlike th then
    normalize_equation thy th
  else
    normalize_intros thy th

fun get_specification options thy t =
  let
    (*val (c, T) = dest_Const t
    val t = Const (Axclass.unoverload_const thy (c, T), T)*)
    val _ = if show_steps options then
        tracing ("getting specification of " ^ Syntax.string_of_term_global thy t ^
          " with type " ^ Syntax.string_of_typ_global thy (fastype_of t))
      else ()
    val ctxt = Proof_Context.init_global thy
    fun filtering th =
      if is_equationlike th andalso
        defining_const_of_equation (normalize_equation thy th) = dest_Const_name t then
        SOME (normalize_equation thy th)
      else
        if is_introlike th andalso defining_const_of_introrule th = dest_Const_name t then
          SOME th
        else
          NONE
    fun filter_defs ths = map_filter filtering (map (normalize thy o Thm.transfer thy) ths)
    val spec =
      (case filter_defs (Named_Theorems.get ctxt \<^named_theorems>\<open>code_pred_def\<close>) of
        [] =>
          (case Spec_Rules.retrieve ctxt t of
            [] => error ("No specification for " ^ Syntax.string_of_term_global thy t)
          | ({rules = ths, ...} :: _) => filter_defs ths)
      | ths => ths)
    val _ =
      if show_intermediate_results options then
        tracing ("Specification for " ^ (Syntax.string_of_term_global thy t) ^ ":\n" ^
          commas (map (Thm.string_of_thm_global thy) spec))
      else ()
  in
    spec
  end

val logic_operator_names =
  [\<^const_name>\<open>Pure.eq\<close>,
   \<^const_name>\<open>Pure.imp\<close>,
   \<^const_name>\<open>Trueprop\<close>,
   \<^const_name>\<open>Not\<close>,
   \<^const_name>\<open>HOL.eq\<close>,
   \<^const_name>\<open>HOL.implies\<close>,
   \<^const_name>\<open>All\<close>,
   \<^const_name>\<open>Ex\<close>,
   \<^const_name>\<open>HOL.conj\<close>,
   \<^const_name>\<open>HOL.disj\<close>]

fun special_cases (c, _) =
  member (op =)
   [\<^const_name>\<open>Product_Type.Unity\<close>,
    \<^const_name>\<open>False\<close>,
    \<^const_name>\<open>Suc\<close>, \<^const_name>\<open>Nat.zero_nat_inst.zero_nat\<close>,
    \<^const_name>\<open>Nat.one_nat_inst.one_nat\<close>,
    \<^const_name>\<open>Orderings.less\<close>, \<^const_name>\<open>Orderings.less_eq\<close>,
    \<^const_name>\<open>Groups.zero\<close>,
    \<^const_name>\<open>Groups.one\<close>,  \<^const_name>\<open>Groups.plus\<close>,
    \<^const_name>\<open>Nat.ord_nat_inst.less_eq_nat\<close>,
    \<^const_name>\<open>Nat.ord_nat_inst.less_nat\<close>,
  (* FIXME
    @{const_name number_nat_inst.number_of_nat},
  *)
    \<^const_name>\<open>Num.Bit0\<close>,
    \<^const_name>\<open>Num.Bit1\<close>,
    \<^const_name>\<open>Num.One\<close>,
    \<^const_name>\<open>Int.zero_int_inst.zero_int\<close>,
    \<^const_name>\<open>List.filter\<close>,
    \<^const_name>\<open>HOL.If\<close>,
    \<^const_name>\<open>Groups.minus\<close>] c


fun obtain_specification_graph options thy t =
  let
    val ctxt = Proof_Context.init_global thy
    fun is_nondefining_const (c, _) = member (op =) logic_operator_names c
    fun has_code_pred_intros (c, _) = can (Core_Data.intros_of ctxt) c
    fun case_consts (c, _) = is_some (Ctr_Sugar.ctr_sugar_of_case ctxt c)
    fun is_datatype_constructor (x as (_, T)) =
      (case body_type T of
        Type (Tcon, _) => can (Ctr_Sugar.dest_ctr ctxt Tcon) (Const x)
      | _ => false)
    fun defiants_of specs =
      fold (Term.add_consts o Thm.prop_of) specs []
      |> filter_out is_datatype_constructor
      |> filter_out is_nondefining_const
      |> filter_out has_code_pred_intros
      |> filter_out case_consts
      |> filter_out special_cases
      |> filter_out (fn (c, _) => Symset.member (#ignore_consts (Data.get thy)) c)
      |> map (fn (c, _) => (c, Sign.the_const_constraint thy c))
      |> map Const
      (*
      |> filter is_defining_constname*)
    fun extend t gr =
      if can (Term_Graph.get_node gr) t then gr
      else
        let
          val specs = get_specification options thy t
          (*val _ = print_specification options thy constname specs*)
          val us = defiants_of specs
        in
          gr
          |> Term_Graph.new_node (t, specs)
          |> fold extend us
          |> fold (fn u => Term_Graph.add_edge (t, u)) us
        end
  in
    extend t Term_Graph.empty
  end;

end
