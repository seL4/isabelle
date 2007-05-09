(*  Title:      Pure/Tools/codegen_funcgr.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Retrieving, normalizing and structuring defining equations
in graph with explicit dependencies.
*)

signature CODEGEN_FUNCGR =
sig
  type T
  val timing: bool ref
  val funcs: T -> CodegenConsts.const -> thm list
  val typ: T -> CodegenConsts.const -> typ
  val deps: T -> CodegenConsts.const list -> CodegenConsts.const list list
  val all: T -> CodegenConsts.const list
  val pretty: theory -> T -> Pretty.T
  structure Constgraph : GRAPH
end

signature CODEGEN_FUNCGR_RETRIEVAL =
sig
  type T (* = CODEGEN_FUNCGR.T *)
  val make: theory -> CodegenConsts.const list -> T
  val make_consts: theory -> CodegenConsts.const list -> CodegenConsts.const list * T
  val make_term: theory -> (T -> (thm -> thm) -> cterm -> thm -> 'a) -> cterm -> 'a * T
  val init: theory -> theory
end;

structure CodegenFuncgr = (*signature is added later*)
struct

(** the graph type **)

structure Constgraph = GraphFun (
  type key = CodegenConsts.const;
  val ord = CodegenConsts.const_ord;
);

type T = (typ * thm list) Constgraph.T;

fun funcs funcgr =
  these o Option.map snd o try (Constgraph.get_node funcgr);

fun typ funcgr =
  fst o Constgraph.get_node funcgr;

fun deps funcgr cs =
  let
    val conn = Constgraph.strong_conn funcgr;
    val order = rev conn;
  in
    (map o filter) (member (op =) (Constgraph.all_succs funcgr cs)) order
    |> filter_out null
  end;

fun all funcgr = Constgraph.keys funcgr;

fun pretty thy funcgr =
  AList.make (snd o Constgraph.get_node funcgr) (Constgraph.keys funcgr)
  |> (map o apfst) (CodegenConsts.string_of_const thy)
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
  | consts_of (const, thms as thm :: _) = 
      let
        val thy = Thm.theory_of_thm thm;
        val is_refl = curry CodegenConsts.eq_const const;
        fun the_const c = case try (CodegenConsts.const_of_cexpr thy) c
         of SOME const => if is_refl const then I else insert CodegenConsts.eq_const const
          | NONE => I
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
        (ty, sort)
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

exception INVALID of CodegenConsts.const list * string;

fun resort_thms algebra tap_typ [] = []
  | resort_thms algebra tap_typ (thms as thm :: _) =
      let
        val thy = Thm.theory_of_thm thm;
        val cs = fold_consts (insert (op =)) thms [];
        fun match_const c (ty, ty_decl) =
          let
            val tys = CodegenConsts.typargs thy (c, ty);
            val sorts = map (snd o dest_TVar) (CodegenConsts.typargs thy (c, ty_decl));
          in fold2 (curry (CodegenConsts.typ_sort_inst algebra)) tys sorts end;
        fun match (c_ty as (c, ty)) =
          case tap_typ c_ty
           of SOME ty_decl => match_const c (ty, ty_decl)
            | NONE => I;
        val tvars = fold match cs Vartab.empty;
      in map (CodegenFunc.inst_thm tvars) thms end;

fun resort_funcss thy algebra funcgr =
  let
    val typ_funcgr = try (fst o Constgraph.get_node funcgr o CodegenConsts.const_of_cexpr thy);
    fun resort_dep (const, thms) = (const, resort_thms algebra typ_funcgr thms)
      handle Sorts.CLASS_ERROR e => raise INVALID ([const], Sorts.msg_class_error (Sign.pp thy) e
                    ^ ",\nfor constant " ^ CodegenConsts.string_of_const thy const
                    ^ "\nin defining equations\n"
                    ^ (cat_lines o map string_of_thm) thms)
    fun resort_rec tap_typ (const, []) = (true, (const, []))
      | resort_rec tap_typ (const, thms as thm :: _) =
          let
            val (_, ty) = CodegenFunc.head_func thm;
            val thms' as thm' :: _ = resort_thms algebra tap_typ thms
            val (_, ty') = CodegenFunc.head_func thm';
          in (Sign.typ_equiv thy (ty, ty'), (const, thms')) end;
    fun resort_recs funcss =
      let
        fun tap_typ c_ty = case try (CodegenConsts.const_of_cexpr thy) c_ty
         of SOME const => AList.lookup (CodegenConsts.eq_const) funcss const
              |> these
              |> try hd
              |> Option.map (snd o CodegenFunc.head_func)
          | NONE => NONE;
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
    fun all_classops tyco class =
      try (AxClass.params_of_class thy) class
      |> Option.map snd
      |> these
      |> map (fn (c, _) => (c, SOME tyco))
  in
    Symtab.empty
    |> fold (fn (tyco, class) =>
        Symtab.map_default (tyco, []) (insert (op =) class)) insts
    |> (fn tab => Symtab.fold (fn (tyco, classes) => append (maps (all_classops tyco)
         (Graph.all_succs thy_classes classes))) tab [])
  end;

fun instances_of_consts thy algebra funcgr consts =
  let
    fun inst (cexpr as (c, ty)) = insts_of thy algebra c
      ((fst o Constgraph.get_node funcgr o CodegenConsts.const_of_cexpr thy) cexpr)
      ty handle CLASS_ERROR => [];
  in
    []
    |> fold (fold (insert (op =)) o inst) consts
    |> instances_of thy algebra
  end;

fun ensure_const' rewrites thy algebra funcgr const auxgr =
  if can (Constgraph.get_node funcgr) const
    then (NONE, auxgr)
  else if can (Constgraph.get_node auxgr) const
    then (SOME const, auxgr)
  else if is_some (CodegenData.get_datatype_of_constr thy const) then
    auxgr
    |> Constgraph.new_node (const, [])
    |> pair (SOME const)
  else let
    val thms = CodegenData.these_funcs thy const
      |> map (CodegenFunc.rewrite_func (rewrites thy))
      |> CodegenFunc.norm_args
      |> CodegenFunc.norm_varnames CodegenNames.purify_tvar CodegenNames.purify_var;
    val rhs = consts_of (const, thms);
  in
    auxgr
    |> Constgraph.new_node (const, thms)
    |> fold_map (ensure_const rewrites thy algebra funcgr) rhs
    |-> (fn rhs' => fold (fn SOME const' => Constgraph.add_edge (const, const')
                           | NONE => I) rhs')
    |> pair (SOME const)
  end
and ensure_const rewrites thy algebra funcgr const =
  let
    val timeap = if !timing
      then Output.timeap_msg ("time for " ^ CodegenConsts.string_of_const thy const)
      else I;
  in timeap (ensure_const' rewrites thy algebra funcgr const) end;

fun merge_funcss rewrites thy algebra raw_funcss funcgr =
  let
    val funcss = raw_funcss
      |> resort_funcss thy algebra funcgr
      |> filter_out (can (Constgraph.get_node funcgr) o fst);
    fun typ_func const [] = CodegenData.default_typ thy const
      | typ_func (_, NONE) (thm :: _) = (snd o CodegenFunc.head_func) thm
      | typ_func (const as (c, SOME tyco)) (thms as (thm :: _)) =
          let
            val (_, ty) = CodegenFunc.head_func thm;
            val SOME class = AxClass.class_of_param thy c;
            val sorts_decl = Sorts.mg_domain algebra tyco [class];
            val tys = CodegenConsts.typargs thy (c, ty);
            val sorts = map (snd o dest_TVar) tys;
          in if sorts = sorts_decl then ty
            else raise INVALID ([const], "Illegal instantation for class operation "
              ^ CodegenConsts.string_of_const thy const
              ^ "\nin defining equations\n"
              ^ (cat_lines o map string_of_thm) thms)
          end;
    fun add_funcs (const, thms) =
      Constgraph.new_node (const, (typ_func const thms, thms));
    fun add_deps (funcs as (const, thms)) funcgr =
      let
        val deps = consts_of funcs;
        val insts = instances_of_consts thy algebra funcgr
          (fold_consts (insert (op =)) thms []);
      in
        funcgr
        |> ensure_consts' rewrites thy algebra insts
        |> fold (curry Constgraph.add_edge const) deps
        |> fold (curry Constgraph.add_edge const) insts
       end;
  in
    funcgr
    |> fold add_funcs funcss
    |> fold add_deps funcss
  end
and ensure_consts' rewrites thy algebra cs funcgr =
  let
    val auxgr = Constgraph.empty
      |> fold (snd oo ensure_const rewrites thy algebra funcgr) cs;
  in
    funcgr
    |> fold (merge_funcss rewrites thy algebra)
         (map (AList.make (Constgraph.get_node auxgr))
         (rev (Constgraph.strong_conn auxgr)))
  end handle INVALID (cs', msg)
    => raise INVALID (fold (insert CodegenConsts.eq_const) cs' cs, msg);

fun ensure_consts rewrites thy consts funcgr =
  let
    val algebra = CodegenData.coregular_algebra thy
  in ensure_consts' rewrites thy algebra consts funcgr
    handle INVALID (cs', msg) => error (msg ^ ",\nwhile preprocessing equations for constant(s) "
    ^ commas (map (CodegenConsts.string_of_const thy) cs'))
  end;

in

(** retrieval interfaces **)

val ensure_consts = ensure_consts;

fun check_consts rewrites thy consts funcgr =
  let
    val algebra = CodegenData.coregular_algebra thy;
    fun try_const const funcgr =
      (SOME const, ensure_consts' rewrites thy algebra [const] funcgr)
      handle INVALID (cs', msg) => (NONE, funcgr);
    val (consts', funcgr') = fold_map try_const consts funcgr;
  in (map_filter I consts', funcgr') end;

fun ensure_consts_term rewrites thy f ct funcgr =
  let
    fun consts_of thy t =
      fold_aterms (fn Const c => cons (CodegenConsts.const_of_cexpr thy c) | _ => I) t []
    fun rhs_conv conv thm =
      let
        val thm' = (conv o Thm.rhs_of) thm;
      in Thm.transitive thm thm' end
    val _ = Sign.no_vars (Sign.pp thy) (Thm.term_of ct);
    val _ = Term.fold_types (Type.no_tvars #> K I) (Thm.term_of ct) ();
    val thm1 = CodegenData.preprocess_cterm ct
      |> fold (rhs_conv o MetaSimplifier.rewrite false o single) (rewrites thy);
    val ct' = Thm.rhs_of thm1;
    val consts = consts_of thy (Thm.term_of ct');
    val funcgr' = ensure_consts rewrites thy consts funcgr;
    val algebra = CodegenData.coregular_algebra thy;
    val (_, thm2) = Thm.varifyT' [] thm1;
    val thm3 = Thm.reflexive (Thm.rhs_of thm2);
    val typ_funcgr = try (fst o Constgraph.get_node funcgr' o CodegenConsts.const_of_cexpr thy);
    val [thm4] = resort_thms algebra typ_funcgr [thm3];
    val tfrees = Term.add_tfrees (Thm.prop_of thm1) [];
    fun inst thm =
      let
        val tvars = Term.add_tvars (Thm.prop_of thm) [];
        val instmap = map2 (fn (v_i, sort) => fn (v, _) => pairself (Thm.ctyp_of thy)
          (TVar (v_i, sort), TFree (v, sort))) tvars tfrees;
      in Thm.instantiate (instmap, []) thm end;
    val thm5 = inst thm2;
    val thm6 = inst thm4;
    val ct'' = Thm.rhs_of thm6;
    val cs = fold_aterms (fn Const c => cons c | _ => I) (Thm.term_of ct'') [];
    val drop = drop_classes thy tfrees;
    val instdefs = instances_of_consts thy algebra funcgr' cs;
    val funcgr'' = ensure_consts rewrites thy instdefs funcgr';
  in (f funcgr'' drop ct'' thm5, funcgr'') end;

end; (*local*)

end; (*struct*)

functor CodegenFuncgrRetrieval (val name: string; val rewrites: theory -> thm list) : CODEGEN_FUNCGR_RETRIEVAL =
struct

(** code data **)

type T = CodegenFuncgr.T;

structure Funcgr = CodeDataFun
(struct
  val name = name;
  type T = T;
  val empty = CodegenFuncgr.Constgraph.empty;
  fun merge _ _ = CodegenFuncgr.Constgraph.empty;
  fun purge _ NONE _ = CodegenFuncgr.Constgraph.empty
    | purge _ (SOME cs) funcgr =
        CodegenFuncgr.Constgraph.del_nodes ((CodegenFuncgr.Constgraph.all_preds funcgr 
          o filter (can (CodegenFuncgr.Constgraph.get_node funcgr))) cs) funcgr;
end);

fun make thy =
  Funcgr.change thy o CodegenFuncgr.ensure_consts rewrites thy;

fun make_consts thy =
  Funcgr.change_yield thy o CodegenFuncgr.check_consts rewrites thy;

fun make_term thy f =
  Funcgr.change_yield thy o CodegenFuncgr.ensure_consts_term rewrites thy f;

val init = Funcgr.init;

end; (*functor*)

structure CodegenFuncgr : CODEGEN_FUNCGR =
struct

open CodegenFuncgr;

end; (*struct*)
