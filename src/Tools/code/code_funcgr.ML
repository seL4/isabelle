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
  val funcs: T -> CodeUnit.const -> thm list
  val typ: T -> CodeUnit.const -> typ
  val all: T -> CodeUnit.const list
  val pretty: theory -> T -> Pretty.T
  val make: theory -> CodeUnit.const list -> T
  val make_consts: theory -> CodeUnit.const list -> CodeUnit.const list * T
  val eval_conv: theory -> (T -> cterm -> thm) -> cterm -> thm
  val eval_term: theory -> (T -> cterm -> 'a) -> cterm -> 'a
  val intervene: theory -> T -> T
    (*FIXME drop intervene as soon as possible*)
  structure Constgraph : GRAPH
end

structure CodeFuncgr : CODE_FUNCGR =
struct

(** the graph type **)

structure Constgraph = GraphFun (
  type key = CodeUnit.const;
  val ord = CodeUnit.const_ord;
);

type T = (typ * thm list) Constgraph.T;

fun funcs funcgr =
  these o Option.map snd o try (Constgraph.get_node funcgr);

fun typ funcgr =
  fst o Constgraph.get_node funcgr;

fun all funcgr = Constgraph.keys funcgr;

fun pretty thy funcgr =
  AList.make (snd o Constgraph.get_node funcgr) (Constgraph.keys funcgr)
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
  | consts_of (const, thms as thm :: _) = 
      let
        val thy = Thm.theory_of_thm thm;
        val is_refl = curry CodeUnit.eq_const const;
        fun the_const c = case try (CodeUnit.const_of_cexpr thy) c
         of SOME const => if is_refl const then I else insert CodeUnit.eq_const const
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

exception INVALID of CodeUnit.const list * string;

fun resort_thms algebra tap_typ [] = []
  | resort_thms algebra tap_typ (thms as thm :: _) =
      let
        val thy = Thm.theory_of_thm thm;
        val cs = fold_consts (insert (op =)) thms [];
        fun match_const c (ty, ty_decl) =
          let
            val tys = CodeUnit.typargs thy (c, ty);
            val sorts = map (snd o dest_TVar) (CodeUnit.typargs thy (c, ty_decl));
          in fold2 (curry (CodeUnit.typ_sort_inst algebra)) tys sorts end;
        fun match (c_ty as (c, ty)) =
          case tap_typ c_ty
           of SOME ty_decl => match_const c (ty, ty_decl)
            | NONE => I;
        val tvars = fold match cs Vartab.empty;
      in map (CodeUnit.inst_thm tvars) thms end;

fun resort_funcss thy algebra funcgr =
  let
    val typ_funcgr = try (fst o Constgraph.get_node funcgr o CodeUnit.const_of_cexpr thy);
    fun resort_dep (const, thms) = (const, resort_thms algebra typ_funcgr thms)
      handle Sorts.CLASS_ERROR e => raise INVALID ([const], Sorts.msg_class_error (Sign.pp thy) e
                    ^ ",\nfor constant " ^ CodeUnit.string_of_const thy const
                    ^ "\nin defining equations\n"
                    ^ (cat_lines o map string_of_thm) thms)
    fun resort_rec tap_typ (const, []) = (true, (const, []))
      | resort_rec tap_typ (const, thms as thm :: _) =
          let
            val (_, ty) = CodeUnit.head_func thm;
            val thms' as thm' :: _ = resort_thms algebra tap_typ thms
            val (_, ty') = CodeUnit.head_func thm';
          in (Sign.typ_equiv thy (ty, ty'), (const, thms')) end;
    fun resort_recs funcss =
      let
        fun tap_typ c_ty = case try (CodeUnit.const_of_cexpr thy) c_ty
         of SOME const => AList.lookup (CodeUnit.eq_const) funcss const
              |> these
              |> try hd
              |> Option.map (snd o CodeUnit.head_func)
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
      ((fst o Constgraph.get_node funcgr o CodeUnit.const_of_cexpr thy) cexpr)
      ty handle CLASS_ERROR => [];
  in
    []
    |> fold (fold (insert (op =)) o inst) consts
    |> instances_of thy algebra
  end;

fun ensure_const' thy algebra funcgr const auxgr =
  if can (Constgraph.get_node funcgr) const
    then (NONE, auxgr)
  else if can (Constgraph.get_node auxgr) const
    then (SOME const, auxgr)
  else if is_some (Code.get_datatype_of_constr thy const) then
    auxgr
    |> Constgraph.new_node (const, [])
    |> pair (SOME const)
  else let
    val thms = Code.these_funcs thy const
      |> CodeUnit.norm_args
      |> CodeUnit.norm_varnames CodeName.purify_tvar CodeName.purify_var;
    val rhs = consts_of (const, thms);
  in
    auxgr
    |> Constgraph.new_node (const, thms)
    |> fold_map (ensure_const thy algebra funcgr) rhs
    |-> (fn rhs' => fold (fn SOME const' => Constgraph.add_edge (const, const')
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
      |> filter_out (can (Constgraph.get_node funcgr) o fst);
    fun typ_func const [] = Code.default_typ thy const
      | typ_func (_, NONE) (thm :: _) = (snd o CodeUnit.head_func) thm
      | typ_func (const as (c, SOME tyco)) (thms as (thm :: _)) =
          let
            val (_, ty) = CodeUnit.head_func thm;
            val SOME class = AxClass.class_of_param thy c;
            val sorts_decl = Sorts.mg_domain algebra tyco [class];
            val tys = CodeUnit.typargs thy (c, ty);
            val sorts = map (snd o dest_TVar) tys;
          in if sorts = sorts_decl then ty
            else raise INVALID ([const], "Illegal instantation for class operation "
              ^ CodeUnit.string_of_const thy const
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
        |> ensure_consts' thy algebra insts
        |> fold (curry Constgraph.add_edge const) deps
        |> fold (curry Constgraph.add_edge const) insts
       end;
  in
    funcgr
    |> fold add_funcs funcss
    |> fold add_deps funcss
  end
and ensure_consts' thy algebra cs funcgr =
  let
    val auxgr = Constgraph.empty
      |> fold (snd oo ensure_const thy algebra funcgr) cs;
  in
    funcgr
    |> fold (merge_funcss thy algebra)
         (map (AList.make (Constgraph.get_node auxgr))
         (rev (Constgraph.strong_conn auxgr)))
  end handle INVALID (cs', msg)
    => raise INVALID (fold (insert CodeUnit.eq_const) cs' cs, msg);

fun ensure_consts thy consts funcgr =
  let
    val algebra = Code.coregular_algebra thy
  in ensure_consts' thy algebra consts funcgr
    handle INVALID (cs', msg) => error (msg ^ ",\nwhile preprocessing equations for constant(s) "
    ^ commas (map (CodeUnit.string_of_const thy) cs'))
  end;

in

(** retrieval interfaces **)

val ensure_consts = ensure_consts;

fun check_consts thy consts funcgr =
  let
    val algebra = Code.coregular_algebra thy;
    fun try_const const funcgr =
      (SOME const, ensure_consts' thy algebra [const] funcgr)
      handle INVALID (cs', msg) => (NONE, funcgr);
    val (consts', funcgr') = fold_map try_const consts funcgr;
  in (map_filter I consts', funcgr') end;

fun ensure_consts_term_proto thy f ct funcgr =
  let
    fun consts_of thy t =
      fold_aterms (fn Const c => cons (CodeUnit.const_of_cexpr thy c) | _ => I) t []
    fun rhs_conv conv thm =
      let
        val thm' = (conv o Thm.rhs_of) thm;
      in Thm.transitive thm thm' end
    val _ = Sign.no_vars (Sign.pp thy) (Thm.term_of ct);
    val _ = Term.fold_types (Type.no_tvars #> K I) (Thm.term_of ct) ();
    val thm1 = Code.preprocess_conv ct;
    val ct' = Thm.rhs_of thm1;
    val consts = consts_of thy (Thm.term_of ct');
    val funcgr' = ensure_consts thy consts funcgr;
    val algebra = Code.coregular_algebra thy;
    val (_, thm2) = Thm.varifyT' [] thm1;
    val thm3 = Thm.reflexive (Thm.rhs_of thm2);
    val typ_funcgr = try (fst o Constgraph.get_node funcgr' o CodeUnit.const_of_cexpr thy);
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
    val funcgr'' = ensure_consts thy instdefs funcgr';
  in (f funcgr'' drop ct'' thm5, funcgr'') end;

fun ensure_consts_eval thy conv =
  let
    fun conv' funcgr drop_classes ct thm1 =
      let
        val thm2 = conv funcgr ct;
        val thm3 = Code.postprocess_conv (Thm.rhs_of thm2);
        val thm23 = drop_classes (Thm.transitive thm2 thm3);
      in
        Thm.transitive thm1 thm23 handle THM _ =>
          error ("eval_conv - could not construct proof:\n"
          ^ (cat_lines o map string_of_thm) [thm1, thm2, thm3])
      end;
  in ensure_consts_term_proto thy conv' end;

fun ensure_consts_term thy f =
  let
    fun f' funcgr drop_classes ct thm1 = f funcgr ct;
  in ensure_consts_term_proto thy f' end;

end; (*local*)

structure Funcgr = CodeDataFun
(struct
  type T = T;
  val empty = Constgraph.empty;
  fun merge _ _ = Constgraph.empty;
  fun purge _ NONE _ = Constgraph.empty
    | purge _ (SOME cs) funcgr =
        Constgraph.del_nodes ((Constgraph.all_preds funcgr 
          o filter (can (Constgraph.get_node funcgr))) cs) funcgr;
end);

fun make thy =
  Funcgr.change thy o ensure_consts thy;

fun make_consts thy =
  Funcgr.change_yield thy o check_consts thy;

fun eval_conv thy f =
  fst o Funcgr.change_yield thy o ensure_consts_eval thy f;

fun eval_term thy f =
  fst o Funcgr.change_yield thy o ensure_consts_term thy f;

fun intervene thy funcgr = Funcgr.change thy (K funcgr);

end; (*struct*)
