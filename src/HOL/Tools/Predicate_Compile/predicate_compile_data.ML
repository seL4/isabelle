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
    
  val present_graph : thm list Term_Graph.T -> unit
  val normalize_equation : theory -> thm -> thm
end;

structure Predicate_Compile_Data : PREDICATE_COMPILE_DATA =
struct

open Predicate_Compile_Aux;

structure Data = Theory_Data
(
  type T =
    {ignore_consts : unit Symtab.table,
     keep_functions : unit Symtab.table,
     processed_specs : ((string * thm list) list) Symtab.table};
  val empty =
    {ignore_consts = Symtab.empty,
     keep_functions = Symtab.empty,
     processed_specs =  Symtab.empty};
  val extend = I;
  fun merge
    ({ignore_consts = c1, keep_functions = k1, processed_specs = s1},
     {ignore_consts = c2, keep_functions = k2, processed_specs = s2}) =
     {ignore_consts = Symtab.merge (K true) (c1, c2),
      keep_functions = Symtab.merge (K true) (k1, k2),
      processed_specs = Symtab.merge (K true) (s1, s2)}
);



fun mk_data (c, k, s) = {ignore_consts = c, keep_functions = k, processed_specs = s}
fun map_data f {ignore_consts = c, keep_functions = k, processed_specs = s} = mk_data (f (c, k, s))

fun ignore_consts cs = Data.map (map_data (apfst3 (fold (fn c => Symtab.insert (op =) (c, ())) cs)))

fun keep_functions cs = Data.map (map_data (apsnd3 (fold (fn c => Symtab.insert (op =) (c, ())) cs)))

fun keep_function thy = Symtab.defined (#keep_functions (Data.get thy))

fun processed_specs thy = Symtab.lookup (#processed_specs (Data.get thy))

fun store_processed_specs (constname, specs) =
  Data.map (map_data (aptrd3 (Symtab.update_new (constname, specs))))
(* *)


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
val defining_term_of_introrule = defining_term_of_introrule_term o prop_of

fun defining_const_of_introrule th =
  case defining_term_of_introrule th
   of Const (c, _) => c
    | _ => raise TERM ("defining_const_of_introrule failed: Not a constant", [prop_of th])

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


fun defining_term_of_equation_term (t as (Const ("==", _) $ u $ v)) = fst (strip_comb u)
  | defining_term_of_equation_term t =
    raise TERM ("defining_const_of_equation_term failed: Not an equation", [t])

val defining_term_of_equation = defining_term_of_equation_term o prop_of

fun defining_const_of_equation th =
  case defining_term_of_equation th
   of Const (c, _) => c
    | _ => raise TERM ("defining_const_of_equation failed: Not a constant", [prop_of th])




(* Normalizing equations *)

fun mk_meta_equation th =
  case prop_of th of
    Const (@{const_name Trueprop}, _) $ (Const (@{const_name HOL.eq}, _) $ _ $ _) => th RS @{thm eq_reflection}
  | _ => th

val meta_fun_cong = @{lemma "f == g ==> f x == g x" by simp}

fun full_fun_cong_expand th =
  let
    val (f, args) = strip_comb (fst (Logic.dest_equals (prop_of th)))
    val i = length (binder_types (fastype_of f)) - length args
  in funpow i (fn th => th RS meta_fun_cong) th end;

fun declare_names s xs ctxt =
  let
    val res = Name.invent_names ctxt s xs
  in (res, fold Name.declare (map fst res) ctxt) end
  
fun split_all_pairs thy th =
  let
    val ctxt = Proof_Context.init_global thy
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
    val th'' = Goal.prove ctxt (Term.add_free_names t' []) [] t' (fn _ => tac)
    val th''' = Local_Defs.unfold ctxt [@{thm split_conv}, @{thm fst_conv}, @{thm snd_conv}] th''
  in
    th'''
  end;


fun inline_equations thy th =
  let
    val inline_defs = Predicate_Compile_Inline_Defs.get (Proof_Context.init_global thy)
    val th' = (Simplifier.full_simplify (HOL_basic_ss addsimps inline_defs)) th
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
    val t = Const (AxClass.unoverload_const thy (c, T), T)*)
    val _ = if show_steps options then
        tracing ("getting specification of " ^ Syntax.string_of_term_global thy t ^
          " with type " ^ Syntax.string_of_typ_global thy (fastype_of t))
      else ()
    val ctxt = Proof_Context.init_global thy
    fun filtering th =
      if is_equationlike th andalso
        defining_const_of_equation (normalize_equation thy th) = fst (dest_Const t) then
        SOME (normalize_equation thy th)
      else
        if is_introlike th andalso defining_const_of_introrule th = fst (dest_Const t) then
          SOME th
        else
          NONE
    fun filter_defs ths = map_filter filtering (map (normalize thy o Thm.transfer thy) ths)
    val spec = case filter_defs (Predicate_Compile_Alternative_Defs.get ctxt) of
      [] => (case Spec_Rules.retrieve ctxt t of
          [] => error ("No specification for " ^ (Syntax.string_of_term_global thy t))
        | ((_, (_, ths)) :: _) => filter_defs ths)
    | ths => rev ths
    val _ =
      if show_intermediate_results options then
        tracing ("Specification for " ^ (Syntax.string_of_term_global thy t) ^ ":\n" ^
          commas (map (Display.string_of_thm_global thy) spec))
      else ()
  in
    spec
  end

val logic_operator_names =
  [@{const_name "=="}, 
   @{const_name "==>"},
   @{const_name Trueprop},
   @{const_name Not},
   @{const_name HOL.eq},
   @{const_name HOL.implies},
   @{const_name All},
   @{const_name Ex}, 
   @{const_name HOL.conj},
   @{const_name HOL.disj}]

fun special_cases (c, T) = member (op =) [
  @{const_name Product_Type.Unity},
  @{const_name False},
  @{const_name Suc}, @{const_name Nat.zero_nat_inst.zero_nat},
  @{const_name Nat.one_nat_inst.one_nat},
  @{const_name Orderings.less}, @{const_name Orderings.less_eq},
  @{const_name Groups.zero},
  @{const_name Groups.one},  @{const_name Groups.plus},
  @{const_name Nat.ord_nat_inst.less_eq_nat},
  @{const_name Nat.ord_nat_inst.less_nat},
(* FIXME
  @{const_name number_nat_inst.number_of_nat},
*)
  @{const_name Num.Bit0},
  @{const_name Num.Bit1},
  @{const_name Num.One},
  @{const_name Int.zero_int_inst.zero_int},
  @{const_name List.filter},
  @{const_name HOL.If},
  @{const_name Groups.minus}
  ] c


fun print_specification options thy constname specs = 
  if show_intermediate_results options then
    tracing ("Specification of " ^ constname ^ ":\n" ^
      cat_lines (map (Display.string_of_thm_global thy) specs))
  else ()

fun obtain_specification_graph options thy t =
  let
    val ctxt = Proof_Context.init_global thy
    fun is_nondefining_const (c, T) = member (op =) logic_operator_names c
    fun has_code_pred_intros (c, T) = can (Core_Data.intros_of ctxt) c
    fun case_consts (c, T) = is_some (Datatype.info_of_case thy c)
    fun is_datatype_constructor (c, T) = is_some (Datatype.info_of_constr thy (c, T))
    fun defiants_of specs =
      fold (Term.add_consts o prop_of) specs []
      |> filter_out is_datatype_constructor
      |> filter_out is_nondefining_const
      |> filter_out has_code_pred_intros
      |> filter_out case_consts
      |> filter_out special_cases
      |> filter_out (fn (c, _) => Symtab.defined (#ignore_consts (Data.get thy)) c)
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


fun present_graph gr =
  let
    fun eq_cname (Const (c1, _), Const (c2, _)) = (c1 = c2)
    fun string_of_const (Const (c, _)) = c
      | string_of_const _ = error "string_of_const: unexpected term"
    val constss = Term_Graph.strong_conn gr;
    val mapping = Termtab.empty |> fold (fn consts => fold (fn const =>
      Termtab.update (const, consts)) consts) constss;
    fun succs consts = consts
      |> maps (Term_Graph.immediate_succs gr)
      |> subtract eq_cname consts
      |> map (the o Termtab.lookup mapping)
      |> distinct (eq_list eq_cname);
    val conn = [] |> fold (fn consts => cons (consts, succs consts)) constss;
    
    fun namify consts = map string_of_const consts
      |> commas;
    val prgr = map (fn (consts, constss) =>
      { name = namify consts, ID = namify consts, dir = "", unfold = true,
        path = "", parents = map namify constss }) conn;
  in Present.display_graph prgr end;


end;
