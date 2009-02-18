(*  Title:      Tools/code/code_funcgr.ML
    Author:     Florian Haftmann, TU Muenchen

Retrieving, normalizing and structuring code equations in graph
with explicit dependencies.
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
  val timing: bool ref
end

structure Code_Funcgr : CODE_FUNCGR =
struct

(** the graph type **)

type T = (((string * sort) list * typ) * (thm * bool) list) Graph.T;

fun eqns funcgr =
  these o Option.map snd o try (Graph.get_node funcgr);

fun typ funcgr =
  fst o Graph.get_node funcgr;

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


(** generic combinators **)

fun fold_consts f thms =
  thms
  |> maps (op :: o swap o apfst (snd o strip_comb) o Logic.dest_equals o Thm.plain_prop_of)
  |> (fold o fold_aterms) (fn Const c => f c | _ => I);

fun consts_of (const, []) = []
  | consts_of (const, thms as _ :: _) = 
      let
        fun the_const (c, _) = if c = const then I else insert (op =) c
      in fold_consts the_const (map fst thms) [] end;

fun insts_of thy algebra tys sorts =
  let
    fun class_relation (x, _) _ = x;
    fun type_constructor tyco xs class =
      (tyco, class) :: (maps o maps) fst xs;
    fun type_variable (TVar (_, sort)) = map (pair []) sort
      | type_variable (TFree (_, sort)) = map (pair []) sort;
    fun of_sort_deriv ty sort =
      Sorts.of_sort_derivation (Syntax.pp_global thy) algebra
        { class_relation = class_relation, type_constructor = type_constructor,
          type_variable = type_variable }
        (ty, sort) handle Sorts.CLASS_ERROR _ => [] (*permissive!*)
  in (flat o flat) (map2 of_sort_deriv tys sorts) end;

fun meets_of thy algebra =
  let
    fun meet_of ty sort tab =
      Sorts.meet_sort algebra (ty, sort) tab
        handle Sorts.CLASS_ERROR _ => tab (*permissive!*);
  in fold2 meet_of end;


(** graph algorithm **)

val timing = ref false;

local

fun resort_thms thy algebra typ_of thms =
  let
    val cs = fold_consts (insert (op =)) thms [];
    fun meets (c, ty) = case typ_of c
       of SOME (vs, _) =>
            meets_of thy algebra (Sign.const_typargs thy (c, ty)) (map snd vs)
        | NONE => I;
    val tab = fold meets cs Vartab.empty;
  in map (Code_Unit.inst_thm thy tab) thms end;

fun resort_eqnss thy algebra funcgr =
  let
    val typ_funcgr = try (fst o Graph.get_node funcgr);
    val resort_dep = (apsnd o burrow_fst) (resort_thms thy algebra typ_funcgr);
    fun resort_rec typ_of (c, []) = (true, (c, []))
      | resort_rec typ_of (c, thms as (thm, _) :: _) = if is_some (AxClass.inst_of_param thy c)
          then (true, (c, thms))
          else let
            val (_, (vs, ty)) = Code_Unit.head_eqn thy thm;
            val thms' as (thm', _) :: _ = burrow_fst (resort_thms thy algebra typ_of) thms
            val (_, (vs', ty')) = Code_Unit.head_eqn thy thm'; (*FIXME simplify check*)
          in (Sign.typ_equiv thy (ty, ty'), (c, thms')) end;
    fun resort_recs eqnss =
      let
        fun typ_of c = case these (AList.lookup (op =) eqnss c)
         of (thm, _) :: _ => (SOME o snd o Code_Unit.head_eqn thy) thm
          | [] => NONE;
        val (unchangeds, eqnss') = split_list (map (resort_rec typ_of) eqnss);
        val unchanged = fold (fn x => fn y => x andalso y) unchangeds true;
      in (unchanged, eqnss') end;
    fun resort_rec_until eqnss =
      let
        val (unchanged, eqnss') = resort_recs eqnss;
      in if unchanged then eqnss' else resort_rec_until eqnss' end;
  in map resort_dep #> resort_rec_until end;

fun instances_of thy algebra insts =
  let
    val thy_classes = (#classes o Sorts.rep_algebra o Sign.classes_of) thy;
    fun all_classparams tyco class =
      these (try (#params o AxClass.get_info thy) class)
      |> map_filter (fn (c, _) => try (AxClass.param_of_inst thy) (c, tyco))
  in
    Symtab.empty
    |> fold (fn (tyco, class) =>
        Symtab.map_default (tyco, []) (insert (op =) class)) insts
    |> (fn tab => Symtab.fold (fn (tyco, classes) => append (maps (all_classparams tyco)
         (Graph.all_succs thy_classes classes))) tab [])
  end;

fun instances_of_consts thy algebra funcgr consts =
  let
    fun inst (cexpr as (c, ty)) = insts_of thy algebra
      (Sign.const_typargs thy (c, ty)) ((map snd o fst) (typ funcgr c));
  in
    []
    |> fold (fold (insert (op =)) o inst) consts
    |> instances_of thy algebra
  end;

fun ensure_const' thy algebra funcgr const auxgr =
  if can (Graph.get_node funcgr) const
    then (NONE, auxgr)
  else if can (Graph.get_node auxgr) const
    then (SOME const, auxgr)
  else if is_some (Code.get_datatype_of_constr thy const) then
    auxgr
    |> Graph.new_node (const, [])
    |> pair (SOME const)
  else let
    val thms = Code.these_eqns thy const
      |> burrow_fst (Code_Unit.norm_args thy)
      |> burrow_fst (Code_Unit.norm_varnames thy Code_Name.purify_tvar Code_Name.purify_var);
    val rhs = consts_of (const, thms);
  in
    auxgr
    |> Graph.new_node (const, thms)
    |> fold_map (ensure_const thy algebra funcgr) rhs
    |-> (fn rhs' => fold (fn SOME const' => Graph.add_edge (const, const')
                           | NONE => I) rhs')
    |> pair (SOME const)
  end
and ensure_const thy algebra funcgr const =
  let
    val timeap = if !timing
      then Output.timeap_msg ("time for " ^ Code_Unit.string_of_const thy const)
      else I;
  in timeap (ensure_const' thy algebra funcgr const) end;

fun merge_eqnss thy algebra raw_eqnss funcgr =
  let
    val eqnss = raw_eqnss
      |> resort_eqnss thy algebra funcgr
      |> filter_out (can (Graph.get_node funcgr) o fst);
    fun typ_eqn c [] = Code.default_typscheme thy c
      | typ_eqn c (thms as (thm, _) :: _) = (snd o Code_Unit.head_eqn thy) thm;
    fun add_eqns (const, thms) =
      Graph.new_node (const, (typ_eqn const thms, thms));
    fun add_deps (eqns as (const, thms)) funcgr =
      let
        val deps = consts_of eqns;
        val insts = instances_of_consts thy algebra funcgr
          (fold_consts (insert (op =)) (map fst thms) []);
      in
        funcgr
        |> ensure_consts thy algebra insts
        |> fold (curry Graph.add_edge const) deps
        |> fold (curry Graph.add_edge const) insts
       end;
  in
    funcgr
    |> fold add_eqns eqnss
    |> fold add_deps eqnss
  end
and ensure_consts thy algebra cs funcgr =
  let
    val auxgr = Graph.empty
      |> fold (snd oo ensure_const thy algebra funcgr) cs;
  in
    funcgr
    |> fold (merge_eqnss thy algebra)
         (map (AList.make (Graph.get_node auxgr))
         (rev (Graph.strong_conn auxgr)))
  end;

in

(** retrieval interfaces **)

val ensure_consts = ensure_consts;

fun proto_eval thy cterm_of evaluator_lift evaluator proto_ct funcgr =
  let
    val ct = cterm_of proto_ct;
    val _ = Sign.no_vars (Syntax.pp_global thy) (Thm.term_of ct);
    val _ = Term.fold_types (Type.no_tvars #> K I) (Thm.term_of ct) ();
    fun consts_of t =
      fold_aterms (fn Const c_ty => cons c_ty | _ => I) t [];
    val algebra = Code.coregular_algebra thy;
    val thm = Code.preprocess_conv thy ct;
    val ct' = Thm.rhs_of thm;
    val t' = Thm.term_of ct';
    val consts = map fst (consts_of t');
    val funcgr' = ensure_consts thy algebra consts funcgr;
    val (t'', evaluator_funcgr) = evaluator t';
    val consts' = consts_of t'';
    val dicts = instances_of_consts thy algebra funcgr' consts';
    val funcgr'' = ensure_consts thy algebra dicts funcgr';
  in (evaluator_lift (evaluator_funcgr (Code.operational_algebra thy)) thm funcgr'', funcgr'') end;

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

end; (*local*)

structure Funcgr = CodeDataFun
(
  type T = T;
  val empty = Graph.empty;
  fun purge _ cs funcgr =
    Graph.del_nodes ((Graph.all_preds funcgr 
      o filter (can (Graph.get_node funcgr))) cs) funcgr;
);

fun make thy =
  pair (Code.operational_algebra thy)
  o Funcgr.change thy o ensure_consts thy (Code.coregular_algebra thy);

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
