(*  Title:      Pure/Tools/codegen_funcgr.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Retrieving, normalizing and structuring defining equations
in graph with explicit dependencies.
*)

signature CODEGEN_FUNCGR =
sig
  type T;
  val make: theory -> CodegenConsts.const list -> T
  val make_consts: theory -> CodegenConsts.const list -> CodegenConsts.const list * T
  val make_term: theory -> ((thm -> thm) -> cterm -> thm -> 'a) -> cterm -> 'a * T
  val funcs: T -> CodegenConsts.const -> thm list
  val typ: T -> CodegenConsts.const -> typ
  val deps: T -> CodegenConsts.const list -> CodegenConsts.const list list
  val all: T -> CodegenConsts.const list
  val norm_varnames: thm list -> thm list
  val print_codethms: theory -> CodegenConsts.const list -> unit
  structure Constgraph : GRAPH
  val timing: bool ref
end;

structure CodegenFuncgr: CODEGEN_FUNCGR =
struct

(** code data **)

structure Consttab = CodegenConsts.Consttab;
structure Constgraph = GraphFun (
  type key = CodegenConsts.const;
  val ord = CodegenConsts.const_ord;
);

type T = (typ * thm list) Constgraph.T;

structure Funcgr = CodeDataFun
(struct
  val name = "Pure/codegen_funcgr";
  type T = T;
  val empty = Constgraph.empty;
  fun merge _ _ = Constgraph.empty;
  fun purge _ NONE _ = Constgraph.empty
    | purge _ (SOME cs) funcgr =
        Constgraph.del_nodes ((Constgraph.all_preds funcgr 
          o filter (can (Constgraph.get_node funcgr))) cs) funcgr;
end);

val _ = Context.add_setup Funcgr.init;


(** retrieval **)

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


(** theorem purification **)

fun norm_args thms =
  let
    val num_args_of = length o snd o strip_comb o fst o Logic.dest_equals;
    val k = fold (curry Int.max o num_args_of o Drule.plain_prop_of) thms 0;
  in
    thms
    |> map (CodegenFunc.expand_eta k)
    |> map (Drule.fconv_rule Drule.beta_eta_conversion)
  end;

fun canonical_tvars thm =
  let
    val ctyp = Thm.ctyp_of (Thm.theory_of_thm thm);
    fun tvars_subst_for thm = (fold_types o fold_atyps)
      (fn TVar (v_i as (v, _), sort) => let
            val v' = CodegenNames.purify_tvar v
          in if v = v' then I
          else insert (op =) (v_i, (v', sort)) end
        | _ => I) (prop_of thm) [];
    fun mk_inst (v_i, (v', sort)) (maxidx, acc) =
      let
        val ty = TVar (v_i, sort)
      in
        (maxidx + 1, (ctyp ty, ctyp (TVar ((v', maxidx), sort))) :: acc)
      end;
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, inst) = fold mk_inst (tvars_subst_for thm) (maxidx + 1, []);
  in Thm.instantiate (inst, []) thm end;

fun canonical_vars thm =
  let
    val cterm = Thm.cterm_of (Thm.theory_of_thm thm);
    fun vars_subst_for thm = fold_aterms
      (fn Var (v_i as (v, _), ty) => let
            val v' = CodegenNames.purify_var v
          in if v = v' then I
          else insert (op =) (v_i, (v', ty)) end
        | _ => I) (prop_of thm) [];
    fun mk_inst (v_i as (v, i), (v', ty)) (maxidx, acc) =
      let
        val t = Var (v_i, ty)
      in
        (maxidx + 1, (cterm t, cterm (Var ((v', maxidx), ty))) :: acc)
      end;
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, inst) = fold mk_inst (vars_subst_for thm) (maxidx + 1, []);
  in Thm.instantiate ([], inst) thm end;

fun canonical_absvars thm =
  let
    val t = Thm.prop_of thm;
    val t' = Term.map_abs_vars CodegenNames.purify_var t;
  in Thm.rename_boundvars t t' thm end;

fun norm_varnames thms =
  let
    fun burrow_thms f [] = []
      | burrow_thms f thms =
          thms
          |> Conjunction.intr_list
          |> f
          |> Conjunction.elim_list;
  in
    thms
    |> norm_args
    |> burrow_thms canonical_tvars
    |> map canonical_vars
    |> map canonical_absvars
    |> map Drule.zero_var_indexes
  end;


(** generic combinators **)

fun fold_consts f thms =
  thms
  |> maps (op :: o swap o apfst (snd o strip_comb) o Logic.dest_equals o Drule.plain_prop_of)
  |> (fold o fold_aterms) (fn Const c => f c | _ => I);

fun consts_of (const, []) = []
  | consts_of (const, thms as thm :: _) = 
      let
        val thy = Thm.theory_of_thm thm;
        val is_refl = curry CodegenConsts.eq_const const;
        fun the_const c = case try (CodegenConsts.norm_of_typ thy) c
         of SOME const => if is_refl const then I else insert CodegenConsts.eq_const const
          | NONE => I
      in fold_consts the_const thms [] end;

fun insts_of thy algebra c ty_decl ty =
  let
    val tys_decl = Sign.const_typargs thy (c, ty_decl);
    val tys = Sign.const_typargs thy (c, ty);
    fun classrel (x, _) _ = x;
    fun constructor tyco xs class =
      (tyco, class) :: maps (maps fst) xs;
    fun variable (TVar (_, sort)) = map (pair []) sort
      | variable (TFree (_, sort)) = map (pair []) sort;
    fun mk_inst ty (TVar (_, sort)) = cons (ty, sort)
      | mk_inst ty (TFree (_, sort)) = cons (ty, sort)
      | mk_inst (Type (tyco1, tys1)) (Type (tyco2, tys2)) =
          if tyco1 <> tyco2 then error "bad instance"
          else fold2 mk_inst tys1 tys2;
    fun of_sort_deriv (ty, sort) =
      Sorts.of_sort_derivation (Sign.pp thy) algebra
        { classrel = classrel, constructor = constructor, variable = variable }
        (ty, sort)
  in
    flat (maps of_sort_deriv (fold2 mk_inst tys tys_decl []))
  end;


(** graph algorithm **)

val timing = ref false;

local

exception INVALID of CodegenConsts.const list * string;

fun specialize_typs' thy funcgr funcss =
  let
    fun max xs = fold (curry Int.max) xs 0;
    fun incr_indices (c, thms) maxidx =
      let
        val thms' = map (Thm.incr_indexes (maxidx + 1)) thms;
        val maxidx' = max (maxidx :: map Thm.maxidx_of thms');
      in ((c, thms'), maxidx') end;
    val (funcss', maxidx) =
      fold_map incr_indices funcss 0;
    fun typ_of_const (c, ty) = case try (CodegenConsts.norm_of_typ thy) (c, ty)
     of SOME const => Option.map fst (try (Constgraph.get_node funcgr) const)
      | NONE => NONE;
    fun unify_const (c, ty) (env, maxidx) =
      case typ_of_const (c, ty)
       of SOME ty_decl => let
            val ty_decl' = Logic.incr_tvar (maxidx + 1) ty_decl;
            val maxidx' = max [maxidx, Term.maxidx_of_typ ty_decl'];
          in Type.unify (Sign.tsig_of thy) (ty_decl', ty) (env, maxidx')
          handle TUNIFY => raise INVALID ([], setmp show_sorts true (setmp show_types true (fn f => f ())) (fn _ => ("Failed to instantiate\n"
            ^ (Sign.string_of_typ thy o Envir.norm_type env) ty_decl' ^ "\nto\n"
            ^ (Sign.string_of_typ thy o Envir.norm_type env) ty
            ^ ",\nfor constant " ^ quote c
            ^ "\nin function theorems\n"
            ^ (cat_lines o maps (map (Sign.string_of_term thy o map_types (Envir.norm_type env) o Thm.prop_of) o snd)) funcss')))
          end
        | NONE => (env, maxidx);
    fun apply_unifier unif (c, []) = (c, [])
      | apply_unifier unif (c, thms as thm :: _) =
          let
            val tvars = Term.add_tvars (Thm.prop_of thm) [];
            fun mk_inst (v_i_sort as (v, _)) =
              let
                val ty = TVar v_i_sort;
              in
                pairself (Thm.ctyp_of thy) (ty,
                  TVar (v, (snd o dest_TVar o Envir.norm_type unif) ty))
              end;
            val instmap = map mk_inst tvars;
            val (thms' as thm' :: _) = map (Drule.zero_var_indexes o Thm.instantiate (instmap, [])) thms;
            val _ = case c of NONE => ()
              | SOME c => (case pairself CodegenFunc.typ_func (thm, thm')
               of (ty, ty') => if (is_none o AxClass.class_of_param thy o fst) c
                  andalso Sign.typ_equiv thy (Type.strip_sorts ty, Type.strip_sorts ty')
                  orelse Sign.typ_equiv thy (ty, ty')
                  then ()
                  else raise INVALID ([], "illegal function type instantiation:\n" ^ Sign.string_of_typ thy (CodegenFunc.typ_func thm)
                    ^ "\nto " ^ Sign.string_of_typ thy (CodegenFunc.typ_func thm')
                    ^ ",\nfor constant " ^ CodegenConsts.string_of_const thy c
                    ^ "\nin function theorems\n"
                    ^ (cat_lines o map string_of_thm) thms))
          in (c, thms') end;
    val (unif, _) =
      fold (fn (_, thms) => fold unify_const (fold_consts (insert (op =)) thms []))
        funcss' (Vartab.empty, maxidx);
    val funcss'' = map (apply_unifier unif) funcss';
  in funcss'' end;

fun specialize_typs thy funcgr =
  (map o apfst) SOME
  #> specialize_typs' thy funcgr
  #> (map o apfst) the;

fun classop_const thy algebra class classop tyco =
  let
    val sorts = Sorts.mg_domain algebra tyco [class]
    val (var, _) = try (AxClass.params_of_class thy) class |> the_default ("'a", []);
    val vs = Name.names (Name.declare var Name.context) "'a" sorts;
    val arity_typ = Type (tyco, map TFree vs);
  in (classop, [arity_typ]) end;

fun instances_of thy algebra insts =
  let
    val thy_classes = (#classes o Sorts.rep_algebra o Sign.classes_of) thy;
    fun all_classops tyco class =
      try (AxClass.params_of_class thy) class
      |> Option.map snd
      |> these
      |> map (fn (c, _) => classop_const thy algebra class c tyco)
      |> map (CodegenConsts.norm thy)
  in
    Symtab.empty
    |> fold (fn (tyco, class) =>
        Symtab.map_default (tyco, []) (insert (op =) class)) insts
    |> (fn tab => Symtab.fold (fn (tyco, classes) => append (maps (all_classops tyco)
         (Graph.all_succs thy_classes classes))) tab [])
  end;

fun instances_of_consts thy algebra funcgr consts =
  let
    fun inst (const as (c, ty)) = case try (CodegenConsts.norm_of_typ thy) const
     of SOME const => insts_of thy algebra c (fst (Constgraph.get_node funcgr const)) ty
      | NONE => [];
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
  else if is_some (CodegenData.get_datatype_of_constr thy const) then
    auxgr
    |> Constgraph.new_node (const, [])
    |> pair (SOME const)
  else let
    val thms = norm_varnames (CodegenData.these_funcs thy const);
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
      then Output.timeap_msg ("time for " ^ CodegenConsts.string_of_const thy const)
      else I;
  in timeap (ensure_const' thy algebra funcgr const) end;

fun merge_funcss thy algebra raw_funcss funcgr =
  let
    val funcss = specialize_typs thy funcgr raw_funcss;
    fun default_typ (const as (c, tys)) = case CodegenData.tap_typ thy const
     of SOME ty => ty
      | NONE => let
          val ty = Sign.the_const_type thy c
        in case AxClass.class_of_param thy c
         of SOME class => let
               val inst = case tys
                of [Type (tyco, _)] => classop_const thy algebra class c tyco
                      |> snd
                      |> the_single
                      |> Logic.varifyT
                 | _ => TVar (("'a", 0), [class]);
              in Term.map_type_tvar (K inst) ty end
          | NONE => ty
        end;
    fun add_funcs (const, thms as thm :: _) =
          Constgraph.new_node (const, (CodegenFunc.typ_func thm, thms))
      | add_funcs (const, []) =
          Constgraph.new_node (const, (default_typ const, []));
    val _ = writeln ("constants " ^ (commas o map (CodegenConsts.string_of_const thy o fst)) funcss);
    val _ = writeln ("funcs " ^ (cat_lines o maps (map string_of_thm o snd)) funcss);
    fun add_deps (funcs as (const, thms)) funcgr =
      let
        val deps = consts_of funcs;
        val _ = writeln ("constant " ^ CodegenConsts.string_of_const thy const);
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
  fold (snd oo ensure_const thy algebra funcgr) cs Constgraph.empty
  |> (fn auxgr => fold (merge_funcss thy algebra)
       (map (AList.make (Constgraph.get_node auxgr))
       (rev (Constgraph.strong_conn auxgr))) funcgr)
  handle INVALID (cs', msg) => raise INVALID (fold (insert CodegenConsts.eq_const) cs' cs, msg);

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

fun ensure_consts thy consts funcgr =
  let
    val algebra = CodegenData.coregular_algebra thy
  in ensure_consts' thy algebra consts funcgr
    handle INVALID (cs', msg) => error (msg ^ ",\nwhile preprocessing equations for constant(s) "
    ^ commas (map (CodegenConsts.string_of_const thy) cs'))
  end;

in


(** graph retrieval **)

fun make thy consts =
  Funcgr.change thy (ensure_consts thy consts);

fun make_consts thy consts =
  let
    val algebra = CodegenData.coregular_algebra thy;
    fun try_const const funcgr =
      (SOME const, ensure_consts' thy algebra [const] funcgr)
      handle INVALID (cs', msg) => (NONE, funcgr);
    val (consts', funcgr) = Funcgr.change_yield thy (fold_map try_const consts);
  in (map_filter I consts', funcgr) end;

fun make_term thy f ct =
  let
    val _ = Sign.no_vars (Sign.pp thy) (Thm.term_of ct);
    val _ = Term.fold_types (Type.no_tvars #> K I) (Thm.term_of ct) ();
    val thm1 = CodegenData.preprocess_cterm ct;
    val ct' = Drule.dest_equals_rhs (Thm.cprop_of thm1);
    val consts = CodegenConsts.consts_of thy (Thm.term_of ct');
    val funcgr = make thy consts;
    val (_, thm2) = Thm.varifyT' [] thm1;
    val thm3 = Thm.reflexive (Drule.dest_equals_rhs (Thm.cprop_of thm2));
    val [(_, [thm4])] = specialize_typs' thy funcgr [(NONE, [thm3])];
    val tfrees = Term.add_tfrees (Thm.prop_of thm1) [];
    fun inst thm =
      let
        val tvars = Term.add_tvars (Thm.prop_of thm) [];
        val instmap = map2 (fn (v_i, sort) => fn (v, _) => pairself (Thm.ctyp_of thy)
          (TVar (v_i, sort), TFree (v, sort))) tvars tfrees;
      in Thm.instantiate (instmap, []) thm end;
    val thm5 = inst thm2;
    val thm6 = inst thm4;
    val ct'' = Drule.dest_equals_rhs (Thm.cprop_of thm6);
    val cs = fold_aterms (fn Const c => cons c | _ => I) (Thm.term_of ct'') [];
    val drop = drop_classes thy tfrees;
    val algebra = CodegenData.coregular_algebra thy;
    val instdefs = instances_of_consts thy algebra funcgr cs;
    val funcgr' = ensure_consts thy instdefs funcgr;
  in (f drop ct'' thm5, Funcgr.change thy (K funcgr')) end;

end; (*local*)


(** diagnostics **)

fun print_funcgr thy funcgr =
  AList.make (snd o Constgraph.get_node funcgr) (Constgraph.keys funcgr)
  |> (map o apfst) (CodegenConsts.string_of_const thy)
  |> sort (string_ord o pairself fst)
  |> map (fn (s, thms) =>
       (Pretty.block o Pretty.fbreaks) (
         Pretty.str s
         :: map Display.pretty_thm thms
       ))
  |> Pretty.chunks
  |> Pretty.writeln;

fun print_codethms thy consts =
  make thy consts |> print_funcgr thy;

fun print_codethms_e thy cs =
  print_codethms thy (map (CodegenConsts.read_const thy) cs);


(** Isar setup **)

structure P = OuterParse;

val print_codethmsK = "print_codethms";

val print_codethmsP =
  OuterSyntax.improper_command print_codethmsK "print code theorems of this theory" OuterKeyword.diag
    (Scan.option (P.$$$ "(" |-- Scan.repeat P.term --| P.$$$ ")")
      >> (fn NONE => CodegenData.print_thms
           | SOME cs => fn thy => print_codethms_e thy cs)
      >> (fn f => Toplevel.no_timing o Toplevel.unknown_theory
      o Toplevel.keep (f o Toplevel.theory_of)));

val _ = OuterSyntax.add_parsers [print_codethmsP];

end; (*struct*)
