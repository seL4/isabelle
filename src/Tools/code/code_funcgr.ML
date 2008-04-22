(*  Title:      Tools/code/code_funcgr.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Retrieving, normalizing and structuring defining equations in graph
with explicit dependencies.
*)

signature CODE_FUNCGR =
sig
  type T
  val timing: bool ref
  val funcs: T -> string -> thm list
  val typ: T -> string -> typ
  val all: T -> string list
  val pretty: theory -> T -> Pretty.T
  val make: theory -> string list -> T
  val make_consts: theory -> string list -> string list * T
  val eval_conv: theory -> (term -> term * (T -> term -> thm)) -> cterm -> thm
  val eval_term: theory -> (term -> term * (T -> term -> 'a)) -> term -> 'a
end

structure CodeFuncgr : CODE_FUNCGR =
struct

(** the graph type **)

type T = (typ * thm list) Graph.T;

fun funcs funcgr =
  these o Option.map snd o try (Graph.get_node funcgr);

fun typ funcgr =
  fst o Graph.get_node funcgr;

fun all funcgr = Graph.keys funcgr;

fun pretty thy funcgr =
  AList.make (snd o Graph.get_node funcgr) (Graph.keys funcgr)
  |> (map o apfst) (CodeUnit.string_of_const thy)
  |> sort (string_ord o pairself fst)
  |> map (fn (s, thms) =>
       (Pretty.block o Pretty.fbreaks) (
         Pretty.str s
         :: map Display.pretty_thm thms
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
      in fold_consts the_const thms [] end;

fun insts_of thy algebra c ty_decl ty =
  let
    val tys_decl = Sign.const_typargs thy (c, ty_decl);
    val tys = Sign.const_typargs thy (c, ty);
    fun class_relation (x, _) _ = x;
    fun type_constructor tyco xs class =
      (tyco, class) :: maps (maps fst) xs;
    fun type_variable (TVar (_, sort)) = map (pair []) sort
      | type_variable (TFree (_, sort)) = map (pair []) sort;
    fun mk_inst ty (TVar (_, sort)) = cons (ty, sort)
      | mk_inst ty (TFree (_, sort)) = cons (ty, sort)
      | mk_inst (Type (_, tys1)) (Type (_, tys2)) = fold2 mk_inst tys1 tys2;
    fun of_sort_deriv (ty, sort) =
      Sorts.of_sort_derivation (Sign.pp thy) algebra
        { class_relation = class_relation, type_constructor = type_constructor,
          type_variable = type_variable }
        (ty, sort) handle Sorts.CLASS_ERROR _ => [] (*permissive!*)
  in
    flat (maps of_sort_deriv (fold2 mk_inst tys tys_decl []))
  end;

fun drop_classes thy tfrees thm =
  let
    val (_, thm') = Thm.varifyT' [] thm;
    val tvars = Term.add_tvars (Thm.prop_of thm') [];
    val unconstr = map (Thm.ctyp_of thy o TVar) tvars;
    val instmap = map2 (fn (v_i, _) => fn (v, sort) => pairself (Thm.ctyp_of thy)
      (TVar (v_i, []), TFree (v, sort))) tvars tfrees;
  in
    thm'
    |> fold Thm.unconstrainT unconstr
    |> Thm.instantiate (instmap, [])
    |> Tactic.rule_by_tactic ((REPEAT o CHANGED o ALLGOALS o Tactic.resolve_tac) (AxClass.class_intros thy))
  end;


(** graph algorithm **)

val timing = ref false;

local

exception CLASS_ERROR of string list * string;

fun resort_thms algebra tap_typ [] = []
  | resort_thms algebra tap_typ (thms as thm :: _) =
      let
        val thy = Thm.theory_of_thm thm;
        val pp = Sign.pp thy;
        val cs = fold_consts (insert (op =)) thms [];
        fun match_const c (ty, ty_decl) =
          let
            val tys = Sign.const_typargs thy (c, ty);
            val sorts = map (snd o dest_TVar) (Sign.const_typargs thy (c, ty_decl));
          in fn tab => fold2 (curry (Sorts.meet_sort algebra)) tys sorts tab
            handle Sorts.CLASS_ERROR e => raise CLASS_ERROR ([c], Sorts.class_error pp e ^ ",\n"
              ^ "for constant " ^ CodeUnit.string_of_const thy c
              ^ "\nin defining equations(s)\n"
              ^ (cat_lines o map string_of_thm) thms)
            (*handle Sorts.CLASS_ERROR _ => tab (*permissive!*)*)
          end;
        fun match (c, ty) = case tap_typ c
           of SOME ty_decl => match_const c (ty, ty_decl)
            | NONE => I;
        val tvars = fold match cs Vartab.empty;
      in map (CodeUnit.inst_thm tvars) thms end;

fun resort_funcss thy algebra funcgr =
  let
    val typ_funcgr = try (fst o Graph.get_node funcgr);
    val resort_dep = apsnd (resort_thms algebra typ_funcgr);
    fun resort_rec tap_typ (const, []) = (true, (const, []))
      | resort_rec tap_typ (const, thms as thm :: _) =
          let
            val (_, ty) = CodeUnit.head_func thm;
            val thms' as thm' :: _ = resort_thms algebra tap_typ thms
            val (_, ty') = CodeUnit.head_func thm';
          in (Sign.typ_equiv thy (ty, ty'), (const, thms')) end;
    fun resort_recs funcss =
      let
        fun tap_typ c =
          AList.lookup (op =) funcss c
          |> these
          |> try hd
          |> Option.map (snd o CodeUnit.head_func);
        val (unchangeds, funcss') = split_list (map (resort_rec tap_typ) funcss);
        val unchanged = fold (fn x => fn y => x andalso y) unchangeds true;
      in (unchanged, funcss') end;
    fun resort_rec_until funcss =
      let
        val (unchanged, funcss') = resort_recs funcss;
      in if unchanged then funcss' else resort_rec_until funcss' end;
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
    fun inst (cexpr as (c, ty)) = insts_of thy algebra c
      ((fst o Graph.get_node funcgr) c) ty;
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
    val thms = Code.these_funcs thy const
      |> CodeUnit.norm_args
      |> CodeUnit.norm_varnames CodeName.purify_tvar CodeName.purify_var;
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
      then Output.timeap_msg ("time for " ^ CodeUnit.string_of_const thy const)
      else I;
  in timeap (ensure_const' thy algebra funcgr const) end;

fun merge_funcss thy algebra raw_funcss funcgr =
  let
    val funcss = raw_funcss
      |> resort_funcss thy algebra funcgr
      |> filter_out (can (Graph.get_node funcgr) o fst);
    fun typ_func c [] = Code.default_typ thy c
      | typ_func c (thms as thm :: _) = case AxClass.inst_of_param thy c
         of SOME (c', tyco) => 
              let
                val (_, ty) = CodeUnit.head_func thm;
                val SOME class = AxClass.class_of_param thy c';
                val sorts_decl = Sorts.mg_domain algebra tyco [class];
                val tys = Sign.const_typargs thy (c, ty);
                val sorts = map (snd o dest_TVar) tys;
              in if sorts = sorts_decl then ty
                else raise CLASS_ERROR ([c], "Illegal instantation for class operation "
                  ^ CodeUnit.string_of_const thy c
                  ^ "\nin defining equations\n"
                  ^ (cat_lines o map (string_of_thm o AxClass.overload thy)) thms)
              end
          | NONE => (snd o CodeUnit.head_func) thm;
    fun add_funcs (const, thms) =
      Graph.new_node (const, (typ_func const thms, thms));
    fun add_deps (funcs as (const, thms)) funcgr =
      let
        val deps = consts_of funcs;
        val insts = instances_of_consts thy algebra funcgr
          (fold_consts (insert (op =)) thms []);
      in
        funcgr
        |> ensure_consts' thy algebra insts
        |> fold (curry Graph.add_edge const) deps
        |> fold (curry Graph.add_edge const) insts
       end;
  in
    funcgr
    |> fold add_funcs funcss
    |> fold add_deps funcss
  end
and ensure_consts' thy algebra cs funcgr =
  let
    val auxgr = Graph.empty
      |> fold (snd oo ensure_const thy algebra funcgr) cs;
  in
    funcgr
    |> fold (merge_funcss thy algebra)
         (map (AList.make (Graph.get_node auxgr))
         (rev (Graph.strong_conn auxgr)))
  end handle CLASS_ERROR (cs', msg)
    => raise CLASS_ERROR (fold (insert (op =)) cs' cs, msg);

in

(** retrieval interfaces **)

fun ensure_consts thy algebra consts funcgr =
  ensure_consts' thy algebra consts funcgr
    handle CLASS_ERROR (cs', msg) => error (msg ^ ",\nwhile preprocessing equations for constant(s) "
    ^ commas (map (CodeUnit.string_of_const thy) cs'));

fun check_consts thy consts funcgr =
  let
    val algebra = Code.coregular_algebra thy;
    fun try_const const funcgr =
      (SOME const, ensure_consts' thy algebra [const] funcgr)
      handle CLASS_ERROR (cs', msg) => (NONE, funcgr);
    val (consts', funcgr') = fold_map try_const consts funcgr;
  in (map_filter I consts', funcgr') end;

fun proto_eval thy cterm_of evaluator_fr evaluator proto_ct funcgr =
  let
    val ct = cterm_of proto_ct;
    val _ = Sign.no_vars (Sign.pp thy) (Thm.term_of ct);
    val _ = Term.fold_types (Type.no_tvars #> K I) (Thm.term_of ct) ();
    fun consts_of t = fold_aterms (fn Const c_ty => cons c_ty | _ => I)
      t [];
    val algebra = Code.coregular_algebra thy;
    val thm = Code.preprocess_conv ct;
    val ct' = Thm.rhs_of thm;
    val t' = Thm.term_of ct';
    val consts = map fst (consts_of t');
    val funcgr' = ensure_consts thy algebra consts funcgr;
    val (t'', evaluator') = apsnd evaluator_fr (evaluator t');
    val consts' = consts_of t'';
    val dicts = instances_of_consts thy algebra funcgr' consts';
    val funcgr'' = ensure_consts thy algebra dicts funcgr';
  in (evaluator' thm funcgr'' t'', funcgr'') end;

fun proto_eval_conv thy =
  let
    fun evaluator evaluator' thm1 funcgr t =
      let
        val thm2 = evaluator' funcgr t;
        val thm3 = Code.postprocess_conv (Thm.rhs_of thm2);
      in
        Thm.transitive thm1 (Thm.transitive thm2 thm3) handle THM _ =>
          error ("could not construct evaluation proof (probably due to wellsortedness problem):\n"
          ^ (cat_lines o map string_of_thm) [thm1, thm2, thm3])
      end;
  in proto_eval thy I evaluator end;

fun proto_eval_term thy =
  let
    fun evaluator evaluator' _ funcgr t = evaluator' funcgr t;
  in proto_eval thy (Thm.cterm_of thy) evaluator end;

end; (*local*)

structure Funcgr = CodeDataFun
(
  type T = T;
  val empty = Graph.empty;
  fun merge _ _ = Graph.empty;
  fun purge _ NONE _ = Graph.empty
    | purge _ (SOME cs) funcgr =
        Graph.del_nodes ((Graph.all_preds funcgr 
          o filter (can (Graph.get_node funcgr))) cs) funcgr;
);

fun make thy =
  Funcgr.change thy o ensure_consts thy (Code.coregular_algebra thy);

fun make_consts thy =
  Funcgr.change_yield thy o check_consts thy;

fun eval_conv thy f =
  fst o Funcgr.change_yield thy o proto_eval_conv thy f;

fun eval_term thy f =
  fst o Funcgr.change_yield thy o proto_eval_term thy f;

end; (*struct*)
