
structure Core_Data =
struct

open Predicate_Compile_Aux;

(* book-keeping *)

datatype predfun_data = PredfunData of {
  definition : thm,
  intro : thm,
  elim : thm,
  neg_intro : thm option
};

fun rep_predfun_data (PredfunData data) = data;

fun mk_predfun_data (definition, ((intro, elim), neg_intro)) =
  PredfunData {definition = definition, intro = intro, elim = elim, neg_intro = neg_intro}

datatype pred_data = PredData of {
  intros : (string option * thm) list,
  elim : thm option,
  preprocessed : bool,
  function_names : (compilation * (mode * string) list) list,
  predfun_data : (mode * predfun_data) list,
  needs_random : mode list
};

fun rep_pred_data (PredData data) = data;

fun mk_pred_data (((intros, elim), preprocessed), (function_names, (predfun_data, needs_random))) =
  PredData {intros = intros, elim = elim, preprocessed = preprocessed,
    function_names = function_names, predfun_data = predfun_data, needs_random = needs_random}

fun map_pred_data f (PredData {intros, elim, preprocessed, function_names, predfun_data, needs_random}) =
  mk_pred_data (f (((intros, elim), preprocessed), (function_names, (predfun_data, needs_random))))

fun eq_option eq (NONE, NONE) = true
  | eq_option eq (SOME x, SOME y) = eq (x, y)
  | eq_option eq _ = false

fun eq_pred_data (PredData d1, PredData d2) = 
  eq_list (eq_pair (op =) Thm.eq_thm) (#intros d1, #intros d2) andalso
  eq_option Thm.eq_thm (#elim d1, #elim d2)

structure PredData = Theory_Data
(
  type T = pred_data Graph.T;
  val empty = Graph.empty;
  val extend = I;
  val merge = Graph.merge eq_pred_data;
);

(* queries *)

fun lookup_pred_data ctxt name =
  Option.map rep_pred_data (try (Graph.get_node (PredData.get (ProofContext.theory_of ctxt))) name)

fun the_pred_data ctxt name = case lookup_pred_data ctxt name
 of NONE => error ("No such predicate " ^ quote name)  
  | SOME data => data;

val is_registered = is_some oo lookup_pred_data

val all_preds_of = Graph.keys o PredData.get o ProofContext.theory_of

val intros_of = map snd o #intros oo the_pred_data

val names_of = map fst o #intros oo the_pred_data

fun the_elim_of ctxt name = case #elim (the_pred_data ctxt name)
 of NONE => error ("No elimination rule for predicate " ^ quote name)
  | SOME thm => thm
  
val has_elim = is_some o #elim oo the_pred_data

fun function_names_of compilation ctxt name =
  case AList.lookup (op =) (#function_names (the_pred_data ctxt name)) compilation of
    NONE => error ("No " ^ string_of_compilation compilation
      ^ " functions defined for predicate " ^ quote name)
  | SOME fun_names => fun_names

fun function_name_of compilation ctxt name mode =
  case AList.lookup eq_mode
    (function_names_of compilation ctxt name) mode of
    NONE => error ("No " ^ string_of_compilation compilation
      ^ " function defined for mode " ^ string_of_mode mode ^ " of predicate " ^ quote name)
  | SOME function_name => function_name

fun modes_of compilation ctxt name = map fst (function_names_of compilation ctxt name)

fun all_modes_of compilation ctxt =
  map_filter (fn name => Option.map (pair name) (try (modes_of compilation ctxt) name))
    (all_preds_of ctxt)

val all_random_modes_of = all_modes_of Random

fun defined_functions compilation ctxt name = case lookup_pred_data ctxt name of
    NONE => false
  | SOME data => AList.defined (op =) (#function_names data) compilation

fun needs_random ctxt s m =
  member (op =) (#needs_random (the_pred_data ctxt s)) m

fun lookup_predfun_data ctxt name mode =
  Option.map rep_predfun_data
    (AList.lookup (op =) (#predfun_data (the_pred_data ctxt name)) mode)

fun the_predfun_data ctxt name mode =
  case lookup_predfun_data ctxt name mode of
    NONE => error ("No function defined for mode " ^ string_of_mode mode ^
      " of predicate " ^ name)
  | SOME data => data;

val predfun_definition_of = #definition ooo the_predfun_data

val predfun_intro_of = #intro ooo the_predfun_data

val predfun_elim_of = #elim ooo the_predfun_data

val predfun_neg_intro_of = #neg_intro ooo the_predfun_data

val intros_graph_of =
  Graph.map (K (map snd o #intros o rep_pred_data)) o PredData.get o ProofContext.theory_of

(* registration of alternative function names *)

structure Alt_Compilations_Data = Theory_Data
(
  type T = (mode * (compilation_funs -> typ -> term)) list Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

fun alternative_compilation_of_global thy pred_name mode =
  AList.lookup eq_mode (Symtab.lookup_list (Alt_Compilations_Data.get thy) pred_name) mode

fun alternative_compilation_of ctxt pred_name mode =
  AList.lookup eq_mode
    (Symtab.lookup_list (Alt_Compilations_Data.get (ProofContext.theory_of ctxt)) pred_name) mode

fun force_modes_and_compilations pred_name compilations =
  let
    (* thm refl is a dummy thm *)
    val modes = map fst compilations
    val (needs_random, non_random_modes) = pairself (map fst)
      (List.partition (fn (m, (fun_name, random)) => random) compilations)
    val non_random_dummys = map (rpair "dummy") non_random_modes
    val all_dummys = map (rpair "dummy") modes
    val dummy_function_names = map (rpair all_dummys) Predicate_Compile_Aux.random_compilations
      @ map (rpair non_random_dummys) Predicate_Compile_Aux.non_random_compilations
    val alt_compilations = map (apsnd fst) compilations
  in
    PredData.map (Graph.new_node
      (pred_name, mk_pred_data ((([], SOME @{thm refl}), true), (dummy_function_names, ([], needs_random)))))
    #> Alt_Compilations_Data.map (Symtab.insert (K false) (pred_name, alt_compilations))
  end

fun functional_compilation fun_name mode compfuns T =
  let
    val (inpTs, outpTs) = split_map_modeT (fn _ => fn T => (SOME T, NONE))
      mode (binder_types T)
    val bs = map (pair "x") inpTs
    val bounds = map Bound (rev (0 upto (length bs) - 1))
    val f = Const (fun_name, inpTs ---> HOLogic.mk_tupleT outpTs)
  in list_abs (bs, mk_single compfuns (list_comb (f, bounds))) end

fun register_alternative_function pred_name mode fun_name =
  Alt_Compilations_Data.map (Symtab.insert_list (eq_pair eq_mode (K false))
    (pred_name, (mode, functional_compilation fun_name mode)))

fun force_modes_and_functions pred_name fun_names =
  force_modes_and_compilations pred_name
    (map (fn (mode, (fun_name, random)) => (mode, (functional_compilation fun_name mode, random)))
    fun_names)

end;