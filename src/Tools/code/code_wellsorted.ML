(*  Title:      Tools/code/code_wellsorted.ML
    Author:     Florian Haftmann, TU Muenchen

Retrieving, well-sorting and structuring code equations in graph
with explicit dependencies -- the Waisenhaus algorithm.
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

(** the equation graph type **)

type T = (((string * sort) list * typ) * (thm * bool) list) Graph.T;

fun eqns eqngr = these o Option.map snd o try (Graph.get_node eqngr);
fun typ eqngr = fst o Graph.get_node eqngr;
fun all eqngr = Graph.keys eqngr;

fun pretty thy eqngr =
  AList.make (snd o Graph.get_node eqngr) (Graph.keys eqngr)
  |> (map o apfst) (Code_Unit.string_of_const thy)
  |> sort (string_ord o pairself fst)
  |> map (fn (s, thms) =>
       (Pretty.block o Pretty.fbreaks) (
         Pretty.str s
         :: map (Display.pretty_thm o fst) thms
       ))
  |> Pretty.chunks;


(** the Waisenhaus algorithm **)

(* auxiliary *)

fun complete_proper_sort thy =
  Sign.complete_sort thy #> filter (can (AxClass.get_info thy));

fun inst_params thy tyco class =
  map (fn (c, _) => AxClass.param_of_inst thy (c, tyco))
    ((#params o AxClass.get_info thy) class);

fun consts_of thy eqns = [] |> (fold o fold o fold_aterms)
  (fn Const (c, ty) => insert (op =) (c, Sign.const_typargs thy (c, Logic.unvarifyT ty)) | _ => I)
    (map (op :: o swap o apfst (snd o strip_comb) o Logic.dest_equals o Thm.plain_prop_of o fst) eqns);

fun tyscm_rhss_of thy c eqns =
  let
    val tyscm = case eqns of [] => Code.default_typscheme thy c
      | ((thm, _) :: _) => (snd o Code_Unit.head_eqn thy) thm;
    val rhss = consts_of thy eqns;
  in (tyscm, rhss) end;


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


(* computing instantiations *)

fun obtain_eqns thy eqngr c =
  case try (Graph.get_node eqngr) c
   of SOME ((lhs, _), eqns) => ((lhs, []), eqns)
    | NONE => let
        val eqns = Code.these_eqns thy c
          |> burrow_fst (Code_Unit.norm_args thy)
          |> burrow_fst (Code_Unit.norm_varnames thy Code_Name.purify_tvar Code_Name.purify_var);
        val ((lhs, _), rhss) = tyscm_rhss_of thy c eqns;
      in ((lhs, rhss), eqns) end;

fun obtain_instance thy arities (inst as (class, tyco)) =
  case AList.lookup (op =) arities inst
   of SOME classess => (classess, ([], []))
    | NONE => let
        val classess = map (complete_proper_sort thy)
          (Sign.arity_sorts thy tyco [class]);
        val superclasses = [class]
          |> complete_proper_sort thy
          |> remove (op =) class;
        val inst_params = inst_params thy tyco class;
      in (classess, (superclasses, inst_params)) end;

fun add_classes thy arities eqngr c_k new_classes vardeps_data =
  let
    val (styps, old_classes) = Vargraph.get_node (fst vardeps_data) c_k;
    val diff_classes = new_classes |> subtract (op =) old_classes;
  in if null diff_classes then vardeps_data
  else let
    val c_ks = Vargraph.imm_succs (fst vardeps_data) c_k |> insert (op =) c_k;
  in
    vardeps_data
    |> (apfst o Vargraph.map_node c_k o apsnd) (append diff_classes)
    |> fold (fn styp => fold (add_typmatch_inst thy arities eqngr styp) new_classes) styps
    |> fold (fn c_k => add_classes thy arities eqngr c_k diff_classes) c_ks
  end end
and add_styp thy arities eqngr c_k tyco_styps vardeps_data =
  let
    val (old_styps, classes) = Vargraph.get_node (fst vardeps_data) c_k;
  in if member (op =) old_styps tyco_styps then vardeps_data
  else
    vardeps_data
    |> (apfst o Vargraph.map_node c_k o apfst) (cons tyco_styps)
    |> fold (add_typmatch_inst thy arities eqngr tyco_styps) classes
  end
and add_dep thy arities eqngr c_k c_k' vardeps_data =
  let
    val (_, classes) = Vargraph.get_node (fst vardeps_data) c_k;
  in
    vardeps_data
    |> add_classes thy arities eqngr c_k' classes
    |> apfst (Vargraph.add_edge (c_k, c_k'))
  end
and add_typmatch_inst thy arities eqngr (tyco, styps) class vardeps_data =
  if can (Sign.arity_sorts thy tyco) [class]
  then vardeps_data
    |> assert thy arities eqngr (Inst (class, tyco))
    |> fold_index (fn (k, styp) =>
         add_typmatch thy arities eqngr styp (Inst (class, tyco), k)) styps
  else vardeps_data (*permissive!*)
and add_typmatch thy arities eqngr (Var c_k') c_k vardeps_data =
      vardeps_data
      |> add_dep thy arities eqngr c_k c_k'
  | add_typmatch thy arities eqngr (Tyco tyco_styps) c_k vardeps_data =
      vardeps_data
      |> add_styp thy arities eqngr c_k tyco_styps
and add_inst thy arities eqngr (inst as (class, tyco)) vardeps_data =
  let
    val (classess, (superclasses, inst_params)) =
      obtain_instance thy arities inst;
  in
    vardeps_data
    |> fold (fn superclass => assert thy arities eqngr (Inst (superclass, tyco))) superclasses
    |> fold (assert thy arities eqngr o Fun) inst_params
    |> fold_index (fn (k, classes) =>
         apfst (Vargraph.new_node ((Inst (class, tyco), k), ([] ,[])))
         #> add_classes thy arities eqngr (Inst (class, tyco), k) classes
         #> fold (fn superclass =>
             add_dep thy arities eqngr (Inst (superclass, tyco), k)
             (Inst (class, tyco), k)) superclasses
         #> fold (fn inst_param =>
             add_dep thy arities eqngr (Fun inst_param, k)
             (Inst (class, tyco), k)
             ) inst_params
         ) classess
  end
and add_const thy arities eqngr c vardeps_data =
  let
    val ((lhs, rhss), eqns) = obtain_eqns thy eqngr c;
    fun styp_of (Type (tyco, tys)) = Tyco (tyco, map styp_of tys)
      | styp_of (TFree (v, _)) = Var (Fun c, find_index (fn (v', _) => v = v') lhs);
    val rhss' = (map o apsnd o map) styp_of rhss;
  in
    vardeps_data
    |> (apsnd o apsnd) (Symtab.update_new (c, (lhs, eqns)))
    |> fold_index (fn (k, (_, sort)) =>
         apfst (Vargraph.new_node ((Fun c, k), ([] ,[])))
         #> add_classes thy arities eqngr (Fun c, k) (complete_proper_sort thy sort)) lhs
    |> fold (assert thy arities eqngr o Fun o fst) rhss'
    |> fold (fn (c', styps) => fold_index (fn (k', styp) =>
         add_typmatch thy arities eqngr styp (Fun c', k')) styps) rhss'
  end
and assert thy arities eqngr c vardeps_data =
  if member (op =) ((fst o snd) vardeps_data) c then vardeps_data
  else case c
   of Fun const => vardeps_data |> (apsnd o apfst) (cons c) |> add_const thy arities eqngr const
    | Inst inst => vardeps_data |> (apsnd o apfst) (cons c) |> add_inst thy arities eqngr inst;


(* applying instantiations *)

fun build_algebra thy arities =
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
    fun add_arity (tyco, class) algebra =
      case AList.lookup (op =) arities (tyco, class)
       of SOME sorts => Sorts.add_arities pp
            (tyco, [(class, map (Sorts.minimize_sort algebra) sorts)]) algebra
        | NONE => if Sign.arity_number thy tyco = 0
            then Sorts.add_arities pp (tyco, [(class, [])]) algebra
            else algebra;
  in
    Sorts.empty_algebra
    |> fold add_class classrels
    |> fold add_arity instances
  end;

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

fun add_arities thy vardeps = Vargraph.fold (fn ((Fun _, _), _) => I
  | ((Inst (class, tyco), k), ((_, classes), _)) =>
      AList.map_default (op =)
        ((tyco, class), replicate (Sign.arity_number thy tyco) [])
          (nth_map k (K classes))) vardeps;

fun add_eqs thy (proj_sort, algebra) eqntab vardeps c gr =
  let
    val (proto_lhs, proto_eqns) = (the o Symtab.lookup eqntab) c;
    val lhs = map_index (fn (k, (v, _)) =>
      (v, snd (Vargraph.get_node vardeps (Fun c, k)))) proto_lhs;
    val inst_tab = Vartab.empty |> fold (fn (v, sort) =>
      Vartab.update ((v, 0), sort)) lhs;
    val eqns = proto_eqns
      |> (map o apfst) (Code_Unit.inst_thm thy inst_tab);
    val (tyscm, rhss) = tyscm_rhss_of thy c eqns;
  in
    gr
    |> Graph.new_node (c, (tyscm, eqns))
    |> fold (fn (c', Ts) => ensure_eqs_dep thy (proj_sort, algebra) eqntab vardeps c c'
        #-> (fn (vs, _) =>
          fold2 (ensure_match thy (proj_sort, algebra) eqntab vardeps c) Ts (map snd vs))) rhss
    |> pair tyscm
  end
and ensure_match thy (proj_sort, algebra) eqntab vardeps c T sort gr =
  gr
  |> fold (fn c' => ensure_eqs_dep thy (proj_sort, algebra) eqntab vardeps c c' #> snd)
       (dicts_of thy (proj_sort, algebra) (T, proj_sort sort))
and ensure_eqs_dep thy (proj_sort, algebra) eqntab vardeps c c' gr =
  gr
  |> ensure_eqs thy (proj_sort, algebra) eqntab vardeps c'
  ||> Graph.add_edge (c, c')
and ensure_eqs thy (proj_sort, algebra) eqntab vardeps c gr =
  case try (Graph.get_node gr) c
   of SOME (tyscm, _) => (tyscm, gr)
    | NONE => add_eqs thy (proj_sort, algebra) eqntab vardeps c gr;

fun extend_arities_eqngr thy cs (arities, eqngr) =
  let
    val (vardeps, (_, eqntab)) = fold (assert thy arities eqngr o Fun)
      cs (Vargraph.empty, ([], Symtab.empty));
    val arities' = add_arities thy vardeps arities;
    val algebra = build_algebra thy arities';
    val proj_sort = complete_proper_sort thy #> Sorts.minimize_sort algebra;
    val (_, eqngr') = fold_map (ensure_eqs thy (proj_sort, algebra) eqntab vardeps) cs eqngr;
  in ((proj_sort, algebra), (arities', eqngr')) end;


(** retrieval interfaces **)

fun proto_eval thy cterm_of evaluator_lift evaluator proto_ct arities_eqngr =
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
    val (algebra', arities_eqngr') = extend_arities_eqngr thy consts arities_eqngr;
    val (t'', evaluator_eqngr) = evaluator t';
    val consts' = consts_of t'';
    val const_matches = fold (fn (c, ty) =>
      insert (op =) (Sign.const_typargs thy (c, Logic.unvarifyT ty), c)) consts' [];
    val typ_matches = maps (fn (tys, c) =>
      tys ~~ map snd (fst (fst (Graph.get_node (snd arities_eqngr') c))))
      const_matches;
    val dicts = maps (dicts_of thy algebra') typ_matches;
    val (algebra'', arities_eqngr'') = extend_arities_eqngr thy dicts arities_eqngr';
  in (evaluator_lift (evaluator_eqngr algebra'') thm (snd arities_eqngr''), arities_eqngr'') end;

fun proto_eval_conv thy =
  let
    fun evaluator_lift evaluator thm1 eqngr =
      let
        val thm2 = evaluator eqngr;
        val thm3 = Code.postprocess_conv thy (Thm.rhs_of thm2);
      in
        Thm.transitive thm1 (Thm.transitive thm2 thm3) handle THM _ =>
          error ("could not construct evaluation proof:\n"
          ^ (cat_lines o map Display.string_of_thm) [thm1, thm2, thm3])
      end;
  in proto_eval thy I evaluator_lift end;

fun proto_eval_term thy =
  let
    fun evaluator_lift evaluator _ eqngr = evaluator eqngr;
  in proto_eval thy (Thm.cterm_of thy) evaluator_lift end;

structure Wellsorted = CodeDataFun
(
  type T = ((string * class) * sort list) list * T;
  val empty = ([], Graph.empty);
  fun purge thy cs (arities, eqngr) =
    let
      val del_cs = ((Graph.all_preds eqngr
        o filter (can (Graph.get_node eqngr))) cs);
      val del_arities =
        map_filter (AxClass.inst_of_param thy) del_cs;
      val arities' = fold (AList.delete (op =)) del_arities arities;
      val eqngr' = Graph.del_nodes del_cs eqngr;
    in (arities', eqngr') end;
);

fun make thy = apsnd snd
  o Wellsorted.change_yield thy o extend_arities_eqngr thy;

fun eval_conv thy f =
  fst o Wellsorted.change_yield thy o proto_eval_conv thy f;

fun eval_term thy f =
  fst o Wellsorted.change_yield thy o proto_eval_term thy f;


(** diagnostic commands **)

fun code_depgr thy consts =
  let
    val (_, eqngr) = make thy consts;
    val select = Graph.all_succs eqngr consts;
  in
    eqngr
    |> not (null consts) ? Graph.subgraph (member (op =) select) 
    |> Graph.map_nodes ((apsnd o map o apfst) (AxClass.overload thy))
  end;

fun code_thms thy = Pretty.writeln o pretty thy o code_depgr thy;

fun code_deps thy consts =
  let
    val eqngr = code_depgr thy consts;
    fun mk_entry (const, (_, (_, parents))) =
      let
        val name = Code_Unit.string_of_const thy const;
        val nameparents = map (Code_Unit.string_of_const thy) parents;
      in { name = name, ID = name, dir = "", unfold = true,
        path = "", parents = nameparents }
      end;
    val prgr = Graph.fold ((fn x => fn xs => xs @ [x]) o mk_entry) eqngr [];
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
