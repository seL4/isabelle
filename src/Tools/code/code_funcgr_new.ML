(*  Title:      Tools/code/code_funcgr.ML
    Author:     Florian Haftmann, TU Muenchen

Retrieving, well-sorting and structuring code equations in graph
with explicit dependencies -- the waisenhaus algorithm.
*)

signature CODE_FUNCGR =
sig
  type T
  val eqns: T -> string -> (thm * bool) list
  val typ: T -> string -> (string * sort) list * typ
  val all: T -> string list
  val pretty: theory -> T -> Pretty.T
  val make: theory -> string list
    -> ((sort -> sort) * Sorts.algebra) * T
  val eval_conv: theory
    -> (term -> term * (((sort -> sort) * Sorts.algebra) -> T -> thm)) -> cterm -> thm
  val eval_term: theory
    -> (term -> term * (((sort -> sort) * Sorts.algebra) -> T -> 'a)) -> term -> 'a
end

structure Code_Funcgr : CODE_FUNCGR =
struct

(** the graph type **)

type T = (((string * sort) list * typ) * (thm * bool) list) Graph.T;

fun eqns funcgr = these o Option.map snd o try (Graph.get_node funcgr);
fun typ funcgr = fst o Graph.get_node funcgr;
fun all funcgr = Graph.keys funcgr;

fun pretty thy funcgr =
  AList.make (snd o Graph.get_node funcgr) (Graph.keys funcgr)
  |> (map o apfst) (Code_Unit.string_of_const thy)
  |> sort (string_ord o pairself fst)
  |> map (fn (s, thms) =>
       (Pretty.block o Pretty.fbreaks) (
         Pretty.str s
         :: map (Display.pretty_thm o fst) thms
       ))
  |> Pretty.chunks;


(** graph algorithm **)

(* generic *)

fun tracing s = (if ! Toplevel.debug then Output.tracing s else ());

fun complete_proper_sort thy =
  Sign.complete_sort thy #> filter (can (AxClass.get_info thy));

fun inst_params thy tyco class =
  map (fn (c, _) => AxClass.param_of_inst thy (c, tyco))
    ((#params o AxClass.get_info thy) class);

fun consts_of thy eqns = [] |> (fold o fold o fold_aterms)
  (fn Const (c, ty) => insert (op =) (c, Sign.const_typargs thy (c, Logic.unvarifyT ty)) | _ => I)
    (map (op :: o swap o apfst (snd o strip_comb) o Logic.dest_equals o Thm.plain_prop_of o fst) eqns);

fun lhs_rhss_of thy c =
  let
    val eqns = Code.these_eqns thy c
      |> burrow_fst (Code_Unit.norm_args thy)
      |> burrow_fst (Code_Unit.norm_varnames thy Code_Name.purify_tvar Code_Name.purify_var);
    val (lhs, _) = case eqns of [] => Code.default_typscheme thy c
      | ((thm, _) :: _) => (snd o Code_Unit.head_eqn thy) thm;
    val rhss = consts_of thy eqns;
  in (lhs, rhss) end;


(* data structures *)

datatype const = Fun of string | Inst of class * string;

fun const_ord (Fun c1, Fun c2) = fast_string_ord (c1, c2)
  | const_ord (Inst class_tyco1, Inst class_tyco2) =
      prod_ord fast_string_ord fast_string_ord (class_tyco1, class_tyco2)
  | const_ord (Fun _, Inst _) = LESS
  | const_ord (Inst _, Fun _) = GREATER;

type var = const * int;

structure Vargraph =
  GraphFun(type key = var val ord = prod_ord const_ord int_ord);

datatype styp = Tyco of string * styp list | Var of var;

type vardeps = const list * ((string * styp list) list * class list) Vargraph.T;


(* computing instantiations -- FIXME does not consider existing things *)

fun add_classes thy c_k new_classes vardeps =
  let
    val _ = tracing "add_classes";
    val (styps, old_classes) = Vargraph.get_node (snd vardeps) c_k;
    val diff_classes = new_classes |> subtract (op =) old_classes;
  in if null diff_classes then vardeps
  else let
    val c_ks = Vargraph.imm_succs (snd vardeps) c_k |> insert (op =) c_k;
  in
    vardeps
    |> (apsnd o Vargraph.map_node c_k o apsnd) (append diff_classes)
    |> fold (fn styp => fold (add_typmatch_inst thy styp) new_classes) styps
    |> fold (fn c_k => add_classes thy c_k diff_classes) c_ks
  end end
and add_styp thy c_k tyco_styps vardeps =
  let
    val _ = tracing "add_styp";
    val (old_styps, classes) = Vargraph.get_node (snd vardeps) c_k;
  in if member (op =) old_styps tyco_styps then vardeps
  else
    vardeps
    |> (apsnd o Vargraph.map_node c_k o apfst) (cons tyco_styps)
    |> fold (add_typmatch_inst thy tyco_styps) classes
  end
and add_dep thy c_k c_k' vardeps =
  let
    val _ = tracing ("add_dep " ^ makestring c_k ^ " -> " ^ makestring c_k');
    val (_, classes) = Vargraph.get_node (snd vardeps) c_k;
  in
    vardeps
    |> add_classes thy c_k' classes
    |> apsnd (Vargraph.add_edge (c_k, c_k'))
  end
and add_typmatch_inst thy (tyco, styps) class vardeps = if can (Sign.arity_sorts thy tyco) [class]
  then vardeps
    |> tap (fn _ => tracing "add_typmatch_inst")
    |> assert thy (Inst (class, tyco))
    |> fold_index (fn (k, styp) =>
         add_typmatch thy styp (Inst (class, tyco), k)) styps
  else vardeps (*permissive!*)
and add_typmatch thy (Var c_k') c_k vardeps =
      vardeps
      |> tap (fn _ => tracing "add_typmatch (Inst)")
      |> add_dep thy c_k c_k'
  | add_typmatch thy (Tyco tyco_styps) c_k vardeps =
      vardeps
      |> tap (fn _ => tracing "add_typmatch (Tyco)")
      |> add_styp thy c_k tyco_styps
and add_inst thy (class, tyco) vardeps =
  let
    val _ = tracing ("add_inst " ^ tyco ^ "::" ^ class);
    val superclasses = complete_proper_sort thy
      (Sign.super_classes thy class);
    val classess = map (complete_proper_sort thy)
      (Sign.arity_sorts thy tyco [class]);
    val inst_params = inst_params thy tyco class;
    (*FIXME also consider existing things here*)
  in
    vardeps
    |> fold (fn superclass => assert thy (Inst (superclass, tyco))) superclasses
    |> fold (assert thy o Fun) inst_params
    |> fold_index (fn (k, classes) =>
         apsnd (Vargraph.default_node ((Inst (class, tyco), k), ([] ,[])))
         #> add_classes thy (Inst (class, tyco), k) classes
         #> fold (fn superclass =>
             add_dep thy (Inst (superclass, tyco), k)
             (Inst (class, tyco), k)) superclasses
         #> fold (fn inst_param =>
             add_dep thy (Fun inst_param, k)
             (Inst (class, tyco), k)
             ) inst_params
         ) classess
  end
and add_const thy c vardeps =
  let
    val _ = tracing "add_const";
    val (lhs, rhss) = lhs_rhss_of thy c;
    (*FIXME build lhs_rhss_of such that it points to existing graph if possible*)
    fun styp_of (Type (tyco, tys)) = Tyco (tyco, map styp_of tys)
      | styp_of (TFree (v, _)) = Var (Fun c, find_index (fn (v', _) => v = v') lhs);
    val rhss' = (map o apsnd o map) styp_of rhss;
  in
    vardeps
    |> fold_index (fn (k, (_, sort)) =>
         apsnd (Vargraph.default_node ((Fun c, k), ([] ,[])))
         #> add_classes thy (Fun c, k) (complete_proper_sort thy sort)) lhs
    |> fold (assert thy o Fun o fst) rhss'
    |> fold (fn (c', styps) => fold_index (fn (k', styp) =>
         add_typmatch thy styp (Fun c', k')) styps) rhss'
  end
and assert thy c (vardeps as (asserted, _)) =
  if member (op =) asserted c then vardeps
  else case c
   of Fun const => vardeps |> apfst (cons c) |> add_const thy const
    | Inst inst => vardeps |> apfst (cons c) |> add_inst thy inst;


(* applying instantiations *)

fun dicts_of thy (proj_sort, algebra) (T, sort) =
  let
    fun class_relation (x, _) _ = x;
    fun type_constructor tyco xs class =
      inst_params thy tyco class @ (maps o maps) fst xs;
    fun type_variable (TFree (_, sort)) = map (pair []) (proj_sort sort);
  in
    flat (Sorts.of_sort_derivation (Syntax.pp_global thy) algebra
      { class_relation = class_relation, type_constructor = type_constructor,
        type_variable = type_variable } (T, proj_sort sort)
       handle Sorts.CLASS_ERROR _ => [] (*permissive!*))
  end;

fun algebra_of thy vardeps =
  let
    val pp = Syntax.pp_global thy;
    val thy_algebra = Sign.classes_of thy;
    val is_proper = can (AxClass.get_info thy);
    val classrels = Sorts.classrels_of thy_algebra
      |> filter (is_proper o fst)
      |> (map o apsnd) (filter is_proper);
    val instances = Sorts.instances_of thy_algebra
      |> filter (is_proper o snd);
    fun add_class (class, superclasses) algebra =
      Sorts.add_class pp (class, Sorts.minimize_sort algebra superclasses) algebra;
    val arity_constraints = Vargraph.fold (fn ((Fun _, _), _) => I
      | ((Inst (class, tyco), k), ((_, classes), _)) =>
          AList.map_default (op =)
            ((tyco, class), replicate (Sign.arity_number thy tyco) [])
              (nth_map k (K classes))) vardeps [];
    fun add_arity (tyco, class) algebra =
      case AList.lookup (op =) arity_constraints (tyco, class)
       of SOME sorts => (tracing (Pretty.output (Syntax.pretty_arity (ProofContext.init thy)
              (tyco, sorts, [class])));
            Sorts.add_arities pp
              (tyco, [(class, map (Sorts.minimize_sort algebra) sorts)]) algebra)
        | NONE => if Sign.arity_number thy tyco = 0
            then Sorts.add_arities pp (tyco, [(class, [])]) algebra
            else algebra;
  in
    Sorts.empty_algebra
    |> fold add_class classrels
    |> fold add_arity instances
  end;

fun add_eqs thy (proj_sort, algebra) vardeps c gr =
  let
    val eqns = Code.these_eqns thy c
      |> burrow_fst (Code_Unit.norm_args thy)
      |> burrow_fst (Code_Unit.norm_varnames thy Code_Name.purify_tvar Code_Name.purify_var);
    val (vs, _) = case eqns of [] => Code.default_typscheme thy c
      | ((thm, _) :: _) => (snd o Code_Unit.head_eqn thy) thm;
    val inst = Vartab.empty |> fold_index (fn (k, (v, _)) =>
      Vartab.update ((v, 0), snd (Vargraph.get_node vardeps (Fun c, k)))) vs;
    val eqns' = eqns
      |> (map o apfst) (Code_Unit.inst_thm thy inst);
    val tyscm = case eqns' of [] => Code.default_typscheme thy c
      | ((thm, _) :: _) => (snd o Code_Unit.head_eqn thy) thm;
    val _ = tracing ("tyscm " ^ makestring (map snd (fst tyscm)));
    val rhss = consts_of thy eqns';
  in
    gr
    |> Graph.new_node (c, (tyscm, eqns'))
    |> fold (fn (c', Ts) => ensure_eqs_dep thy (proj_sort, algebra) vardeps c c'
        #-> (fn (vs, _) =>
          fold2 (ensure_match thy (proj_sort, algebra) vardeps c) Ts (map snd vs))) rhss
    |> pair tyscm
  end
and ensure_match thy (proj_sort, algebra) vardeps c T sort gr =
  gr
  |> fold (fn c' => ensure_eqs_dep thy (proj_sort, algebra) vardeps c c' #> snd)
       (dicts_of thy (proj_sort, algebra) (T, proj_sort sort))
and ensure_eqs_dep thy (proj_sort, algebra) vardeps c c' gr =
  gr
  |> ensure_eqs thy (proj_sort, algebra) vardeps c'
  ||> Graph.add_edge (c, c')
and ensure_eqs thy (proj_sort, algebra) vardeps c gr =
  case try (Graph.get_node gr) c
   of SOME (tyscm, _) => (tyscm, gr)
    | NONE => add_eqs thy (proj_sort, algebra) vardeps c gr;

fun extend_graph thy cs gr =
  let
    val _ = tracing ("extending with " ^ commas cs);
    val _ = tracing "obtaining instantiations";
    val (_, vardeps) = fold (assert thy o Fun) cs ([], Vargraph.empty)
    val _ = tracing "obtaining algebra";
    val algebra = algebra_of thy vardeps;
    val _ = tracing "obtaining equations";
    val proj_sort = complete_proper_sort thy #> Sorts.minimize_sort algebra;
    val (_, gr') = fold_map (ensure_eqs thy (proj_sort, algebra) vardeps) cs gr;
    val _ = tracing "sort projection";
  in ((proj_sort, algebra), gr') end;


(** retrieval interfaces **)

fun proto_eval thy cterm_of evaluator_lift evaluator proto_ct funcgr =
  let
    val ct = cterm_of proto_ct;
    val _ = Sign.no_vars (Syntax.pp_global thy) (Thm.term_of ct);
    val _ = Term.fold_types (Type.no_tvars #> K I) (Thm.term_of ct) ();
    fun consts_of t =
      fold_aterms (fn Const c_ty => cons c_ty | _ => I) t [];
    val thm = Code.preprocess_conv thy ct;
    val ct' = Thm.rhs_of thm;
    val t' = Thm.term_of ct';
    val consts = map fst (consts_of t');
    val (algebra', funcgr') = extend_graph thy consts funcgr;
    val (t'', evaluator_funcgr) = evaluator t';
    val consts' = consts_of t'';
    val const_matches = fold (fn (c, ty) =>
      insert (op =) (Sign.const_typargs thy (c, Logic.unvarifyT ty), c)) consts' [];
    val typ_matches = maps (fn (tys, c) => tys ~~ map snd (fst (fst (Graph.get_node funcgr' c))))
      const_matches;
    val dicts = maps (dicts_of thy algebra') typ_matches;
    val (algebra'', funcgr'') = extend_graph thy dicts funcgr';
  in (evaluator_lift (evaluator_funcgr algebra'') thm funcgr'', funcgr'') end;

fun proto_eval_conv thy =
  let
    fun evaluator_lift evaluator thm1 funcgr =
      let
        val thm2 = evaluator funcgr;
        val thm3 = Code.postprocess_conv thy (Thm.rhs_of thm2);
      in
        Thm.transitive thm1 (Thm.transitive thm2 thm3) handle THM _ =>
          error ("could not construct evaluation proof:\n"
          ^ (cat_lines o map Display.string_of_thm) [thm1, thm2, thm3])
      end;
  in proto_eval thy I evaluator_lift end;

fun proto_eval_term thy =
  let
    fun evaluator_lift evaluator _ funcgr = evaluator funcgr;
  in proto_eval thy (Thm.cterm_of thy) evaluator_lift end;

structure Funcgr = CodeDataFun
(
  type T = T;
  val empty = Graph.empty;
  fun purge _ cs funcgr =
    Graph.del_nodes ((Graph.all_preds funcgr 
      o filter (can (Graph.get_node funcgr))) cs) funcgr;
);

fun make thy = Funcgr.change_yield thy o extend_graph thy;

fun eval_conv thy f =
  fst o Funcgr.change_yield thy o proto_eval_conv thy f;

fun eval_term thy f =
  fst o Funcgr.change_yield thy o proto_eval_term thy f;


(** diagnostic commands **)

fun code_depgr thy consts =
  let
    val (_, gr) = make thy consts;
    val select = Graph.all_succs gr consts;
  in
    gr
    |> not (null consts) ? Graph.subgraph (member (op =) select) 
    |> Graph.map_nodes ((apsnd o map o apfst) (AxClass.overload thy))
  end;

fun code_thms thy = Pretty.writeln o pretty thy o code_depgr thy;

fun code_deps thy consts =
  let
    val gr = code_depgr thy consts;
    fun mk_entry (const, (_, (_, parents))) =
      let
        val name = Code_Unit.string_of_const thy const;
        val nameparents = map (Code_Unit.string_of_const thy) parents;
      in { name = name, ID = name, dir = "", unfold = true,
        path = "", parents = nameparents }
      end;
    val prgr = Graph.fold ((fn x => fn xs => xs @ [x]) o mk_entry) gr [];
  in Present.display_graph prgr end;

local

structure P = OuterParse
and K = OuterKeyword

fun code_thms_cmd thy = code_thms thy o op @ o Code_Name.read_const_exprs thy;
fun code_deps_cmd thy = code_deps thy o op @ o Code_Name.read_const_exprs thy;

in

val _ =
  OuterSyntax.improper_command "code_thms" "print system of defining equations for code" OuterKeyword.diag
    (Scan.repeat P.term_group
      >> (fn cs => Toplevel.no_timing o Toplevel.unknown_theory
        o Toplevel.keep ((fn thy => code_thms_cmd thy cs) o Toplevel.theory_of)));

val _ =
  OuterSyntax.improper_command "code_deps" "visualize dependencies of defining equations for code" OuterKeyword.diag
    (Scan.repeat P.term_group
      >> (fn cs => Toplevel.no_timing o Toplevel.unknown_theory
        o Toplevel.keep ((fn thy => code_deps_cmd thy cs) o Toplevel.theory_of)));

end;

end; (*struct*)
