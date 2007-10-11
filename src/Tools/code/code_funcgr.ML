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
  val eval_conv: theory -> (T -> cterm -> thm) -> cterm -> thm
  val eval_term: theory -> (T -> term -> 'a) -> term -> 'a
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

exception INVALID of string list * string;

fun resort_thms algebra tap_typ [] = []
  | resort_thms algebra tap_typ (thms as thm :: _) =
      let
        val thy = Thm.theory_of_thm thm;
        val cs = fold_consts (insert (op =)) thms [];
        fun match_const c (ty, ty_decl) =
          let
            val tys = Sign.const_typargs thy (c, ty);
            val sorts = map (snd o dest_TVar) (Sign.const_typargs thy (c, ty_decl));
          in fold2 (curry (CodeUnit.typ_sort_inst algebra)) tys sorts end;
        fun match (c, ty) =
          case tap_typ c
           of SOME ty_decl => match_const c (ty, ty_decl)
            | NONE => I;
        val tvars = fold match cs Vartab.empty;
      in map (CodeUnit.inst_thm tvars) thms end;

fun resort_funcss thy algebra funcgr =
  let
    val typ_funcgr = try (fst o Graph.get_node funcgr);
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
      |> map (fn (c, _) => Class.inst_const thy (c, tyco))
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
      ((fst o Graph.get_node funcgr) c) ty handle CLASS_ERROR => [];
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
      | typ_func c (thms as thm :: _) = case Class.param_const thy c
         of SOME (c', tyco) => 
              let
                val (_, ty) = CodeUnit.head_func thm;
                val SOME class = AxClass.class_of_param thy c';
                val sorts_decl = Sorts.mg_domain algebra tyco [class];
                val tys = Sign.const_typargs thy (c, ty);
                val sorts = map (snd o dest_TVar) tys;
              in if sorts = sorts_decl then ty
                else raise INVALID ([c], "Illegal instantation for class operation "
                  ^ CodeUnit.string_of_const thy c
                  ^ "\nin defining equations\n"
                  ^ (cat_lines o map string_of_thm) thms)
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
  end handle INVALID (cs', msg)
    => raise INVALID (fold (insert (op =)) cs' cs, msg);

in

(** retrieval interfaces **)

fun ensure_consts thy algebra consts funcgr =
  ensure_consts' thy algebra consts funcgr
    handle INVALID (cs', msg) => error (msg ^ ",\nwhile preprocessing equations for constant(s) "
    ^ commas (map (CodeUnit.string_of_const thy) cs'));

fun check_consts thy consts funcgr =
  let
    val algebra = Code.coregular_algebra thy;
    fun try_const const funcgr =
      (SOME const, ensure_consts' thy algebra [const] funcgr)
      handle INVALID (cs', msg) => (NONE, funcgr);
    val (consts', funcgr') = fold_map try_const consts funcgr;
  in (map_filter I consts', funcgr') end;

fun raw_eval thy f ct funcgr =
  let
    val algebra = Code.coregular_algebra thy;
    fun consts_of ct = fold_aterms (fn Const c_ty => cons c_ty | _ => I)
      (Thm.term_of ct) [];
    val _ = Sign.no_vars (Sign.pp thy) (Thm.term_of ct);
    val _ = Term.fold_types (Type.no_tvars #> K I) (Thm.term_of ct) ();
    val thm1 = Code.preprocess_conv ct;
    val ct' = Thm.rhs_of thm1;
    val cs = map fst (consts_of ct');
    val funcgr' = ensure_consts thy algebra cs funcgr;
    val (_, thm2) = Thm.varifyT' [] thm1;
    val thm3 = Thm.reflexive (Thm.rhs_of thm2);
    val [thm4] = resort_thms algebra (try (fst o Graph.get_node funcgr')) [thm3];
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
    val c_exprs = consts_of ct'';
    val drop = drop_classes thy tfrees;
    val instdefs = instances_of_consts thy algebra funcgr' c_exprs;
    val funcgr'' = ensure_consts thy algebra instdefs funcgr';
  in (f drop thm5 funcgr'' ct'' , funcgr'') end;

fun raw_eval_conv thy conv =
  let
    fun conv' drop_classes thm1 funcgr ct =
      let
        val thm2 = conv funcgr ct;
        val thm3 = Code.postprocess_conv (Thm.rhs_of thm2);
        val thm23 = drop_classes (Thm.transitive thm2 thm3);
      in
        Thm.transitive thm1 thm23 handle THM _ =>
          error ("could not construct proof:\n"
          ^ (cat_lines o map string_of_thm) [thm1, thm2, thm3])
      end;
  in raw_eval thy conv' end;

fun raw_eval_term thy f t =
  let
    fun f' _ _ funcgr ct = f funcgr (Thm.term_of ct);
  in raw_eval thy f' (Thm.cterm_of thy t) end;

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
  fst o Funcgr.change_yield thy o raw_eval_conv thy f;

fun eval_term thy f =
  fst o Funcgr.change_yield thy o raw_eval_term thy f;

end; (*struct*)
