(*  Title:      Pure/Tools/codegen_funcgr.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Retrieving, normalizing and structuring code function theorems
in graph with explicit dependencies.
*)

signature CODEGEN_FUNCGR =
sig
  type T;
  val make: theory -> CodegenConsts.const list -> T
  val make_term: theory -> ((thm -> thm) -> cterm -> thm -> 'a) -> cterm -> 'a * T
  val funcs: T -> CodegenConsts.const -> thm list
  val typ: T -> CodegenConsts.const -> typ
  val deps: T -> CodegenConsts.const list -> CodegenConsts.const list list
  val all: T -> CodegenConsts.const list
  val norm_vars: theory -> thm list -> thm list
  val print_codethms: theory -> CodegenConsts.const list -> unit
  structure Constgraph : GRAPH
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


(** theorem purification **)

fun abs_norm thy thm =
  let
    fun eta_expand thm =
      let
        val lhs = (fst o Logic.dest_equals o Drule.plain_prop_of) thm;
        val tys = (fst o strip_type o fastype_of) lhs;
        val ctxt = Name.make_context (map (fst o fst) (Term.add_vars lhs []));
        val vs_ct = map (fn (v, ty) => cterm_of thy (Var ((v, 0), ty)))
          (Name.names ctxt "a" tys);
      in
        fold (fn ct => fn thm => Thm.combination thm (Thm.reflexive ct)) vs_ct thm
      end;
  in
    thm
    |> eta_expand
    |> Drule.fconv_rule Drule.beta_eta_conversion
  end;


fun canonical_tvars thy thm =
  let
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
        (maxidx + 1, (ctyp_of thy ty, ctyp_of thy (TVar ((v', maxidx), sort))) :: acc)
      end;
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, inst) = fold mk_inst (tvars_subst_for thm) (maxidx + 1, []);
  in Thm.instantiate (inst, []) thm end;

fun canonical_vars thy thm =
  let
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
        (maxidx + 1, (cterm_of thy t, cterm_of thy (Var ((v', maxidx), ty))) :: acc)
      end;
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, inst) = fold mk_inst (vars_subst_for thm) (maxidx + 1, []);
  in Thm.instantiate ([], inst) thm end;

fun norm_vars thy thms =
  let
    fun burrow_thms f [] = []
      | burrow_thms f thms =
          thms
          |> Conjunction.intr_list
          |> f
          |> Conjunction.elim_list;
  in
    thms
    |> map (abs_norm thy)
    |> burrow_thms (canonical_tvars thy)
    |> map (canonical_vars thy)
    |> map Drule.zero_var_indexes
  end;



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

local

fun add_things_of thy f (c, thms) =
  (fold o fold_aterms)
     (fn Const c_ty => let
            val c' = CodegenConsts.norm_of_typ thy c_ty
          in if is_some c andalso CodegenConsts.eq_const (the c, c') then I
          else f (c', c_ty) end
       | _ => I) (maps (op :: o swap o apfst (snd o strip_comb)
            o Logic.dest_equals o Drule.plain_prop_of) thms)

fun rhs_of thy (c, thms) =
  Consttab.empty
  |> add_things_of thy (Consttab.update o rpair () o fst) (SOME c, thms)
  |> Consttab.keys;

fun insts_of thy funcgr (c, ty) =
  let
    val tys = Sign.const_typargs thy (c, ty);
    val c' = CodegenConsts.norm thy (c, tys);
    val ty_decl = CodegenConsts.disc_typ_of_const thy
      (fst o Constgraph.get_node funcgr o CodegenConsts.norm thy) (c, tys);
    val tys_decl = Sign.const_typargs thy (c, ty_decl);
    fun constructor tyco xs class =
      (tyco, class) :: maps (maps fst) xs;
    fun variable (TVar (_, sort)) = map (pair []) sort
      | variable (TFree (_, sort)) = map (pair []) sort;
    fun mk_inst ty (TVar (_, sort)) = cons (ty, sort)
      | mk_inst ty (TFree (_, sort)) = cons (ty, sort)
      | mk_inst (Type (tyco1, tys1)) (Type (tyco2, tys2)) =
          if tyco1 <> tyco2 then error "bad instance"
          else fold2 mk_inst tys1 tys2;
    val pp = Sign.pp thy;
    val algebra = Sign.classes_of thy;
    fun classrel (x, _) _ = x;
    fun of_sort_deriv (ty, sort) =
      Sorts.of_sort_derivation pp algebra
        { classrel = classrel, constructor = constructor, variable = variable }
        (ty, sort)
  in
    flat (maps of_sort_deriv (fold2 mk_inst tys tys_decl []))
  end;

fun all_classops thy tyco class =
  try (AxClass.params_of_class thy) class
  |> Option.map snd
  |> these
  |> map (fn (c, _) => (c, CodegenConsts.disc_typ_of_classop thy (c, [Type (tyco, [])])))
  |> map (CodegenConsts.norm_of_typ thy);

fun instdefs_of thy insts =
  let
    val thy_classes = (#classes o Sorts.rep_algebra o Sign.classes_of) thy;
  in
    Symtab.empty
    |> fold (fn (tyco, class) =>
        Symtab.map_default (tyco, []) (insert (op =) class)) insts
    |> (fn tab => Symtab.fold (fn (tyco, classes) => append (maps (all_classops thy tyco)
         (Graph.all_succs thy_classes classes))) tab [])
  end;

fun insts_of_thms thy funcgr (c, thms) =
  let
    val insts = add_things_of thy (fn (_, c_ty) => fold (insert (op =))
      (insts_of thy funcgr c_ty)) (SOME c, thms) [];
  in instdefs_of thy insts end;

fun ensure_const thy funcgr c auxgr =
  if can (Constgraph.get_node funcgr) c
    then (NONE, auxgr)
  else if can (Constgraph.get_node auxgr) c
    then (SOME c, auxgr)
  else if is_some (CodegenData.get_datatype_of_constr thy c) then
    auxgr
    |> Constgraph.new_node (c, [])
    |> pair (SOME c)
  else let
    val thms = norm_vars thy (CodegenData.these_funcs thy c);
    val rhs = rhs_of thy (c, thms);
  in
    auxgr
    |> Constgraph.new_node (c, thms)
    |> fold_map (ensure_const thy funcgr) rhs
    |-> (fn rhs' => fold (fn SOME c' => Constgraph.add_edge (c, c')
                           | NONE => I) rhs')
    |> pair (SOME c)
  end;

exception INVALID of CodegenConsts.const list * string;

fun specialize_typs thy funcgr eqss =
  let
    fun max [] = 0
      | max [l] = l
      | max (k::l::ls) = max ((if k < l then l else k) :: ls);
    fun typscheme_of (c, ty) =
      try (Constgraph.get_node funcgr) (CodegenConsts.norm_of_typ thy (c, ty))
      |> Option.map fst;
    fun incr_indices (c, thms) maxidx =
      let
        val thms' = map (Thm.incr_indexes (maxidx + 1)) thms;
        val maxidx' = max (maxidx :: map Thm.maxidx_of thms');
      in ((c, thms'), maxidx') end;
    val (eqss', maxidx) =
      fold_map incr_indices eqss 0;
    fun unify_const (c, ty) (env, maxidx) =
      case typscheme_of (c, ty)
       of SOME ty_decl => let
            val ty_decl' = Logic.incr_tvar (maxidx + 1) ty_decl;
            val maxidx' = max [maxidx, Term.maxidx_of_typ ty_decl'];
          in Type.unify (Sign.tsig_of thy) (ty_decl', ty) (env, maxidx')
          handle TUNIFY => raise INVALID ([], setmp show_sorts true (setmp show_types true (fn f => f ())) (fn _ => ("Failed to instantiate\n"
            ^ (Sign.string_of_typ thy o Envir.norm_type env) ty_decl' ^ "\nto\n"
            ^ (Sign.string_of_typ thy o Envir.norm_type env) ty
            ^ ",\nfor constant " ^ quote c
            ^ "\nin function theorems\n"
            ^ (cat_lines o maps (map (Sign.string_of_term thy o map_types (Envir.norm_type env) o Thm.prop_of) o snd)) eqss')))
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
            val (ty, ty') = pairself (CodegenData.typ_func thy) (thm, thm');
            val _ = if fst c = ""
              orelse (is_none o AxClass.class_of_param thy o fst) c andalso
                Sign.typ_equiv thy (Type.strip_sorts ty, Type.strip_sorts ty')
              orelse Sign.typ_equiv thy (ty, ty')
              then ()
              else raise INVALID ([], "illegal function type instantiation:\n" ^ Sign.string_of_typ thy (CodegenData.typ_func thy thm)
                ^ "\nto " ^ Sign.string_of_typ thy (CodegenData.typ_func thy thm')
                ^ ",\nfor constant " ^ CodegenConsts.string_of_const thy c
                ^ "\nin function theorems\n"
                ^ (cat_lines o map string_of_thm) thms)
          in (c, thms') end;
    fun rhs_of' thy (("", []), thms as [_]) =
          add_things_of thy (cons o snd) (NONE, thms) []
      | rhs_of' thy (c, thms) =
          add_things_of thy (cons o snd) (SOME c, thms) [];
    val (unif, _) =
      fold (fn (c, thms) => fold unify_const (rhs_of' thy (c, thms)))
        eqss' (Vartab.empty, maxidx);
    val eqss'' =
      map (apply_unifier unif) eqss';
  in eqss'' end;

fun merge_eqsyss thy raw_eqss funcgr =
  let
    val eqss = specialize_typs thy funcgr raw_eqss;
    val tys = map (CodegenData.typ_funcs thy) eqss;
    val rhss = map (rhs_of thy) eqss;
  in
    funcgr
    |> fold2 (fn (c, thms) => fn ty => Constgraph.new_node (c, (ty, thms))) eqss tys
    |> `(fn funcgr => map (insts_of_thms thy funcgr) eqss)
    |-> (fn rhs_insts => fold2 (fn (c, _) => fn rhs_inst =>
          ensure_consts thy rhs_inst #> fold (curry Constgraph.add_edge c) rhs_inst) eqss rhs_insts)
    |> fold2 (fn (c, _) => fn rhs => fold (curry Constgraph.add_edge c) rhs) eqss rhss
  end
and merge_new_eqsyss thy raw_eqss funcgr =
  if exists (member CodegenConsts.eq_const (Constgraph.keys funcgr)) (map fst raw_eqss)
  then funcgr
  else merge_eqsyss thy raw_eqss funcgr
and ensure_consts thy cs funcgr =
  fold (snd oo ensure_const thy funcgr) cs Constgraph.empty
  |> (fn auxgr => fold (merge_new_eqsyss thy)
       (map (AList.make (Constgraph.get_node auxgr))
       (rev (Constgraph.strong_conn auxgr))) funcgr)
  handle INVALID (cs', msg) => raise INVALID (cs @ cs', msg);

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

in

val ensure_consts = (fn thy => fn cs => fn funcgr => ensure_consts thy
  cs funcgr handle INVALID (cs', msg) => error (msg ^ ",\nwhile preprocessing equations for constant(s) "
    ^ commas (map (CodegenConsts.string_of_const thy) cs')));

fun make thy consts =
  Funcgr.change thy (ensure_consts thy consts);

fun make_term thy f ct =
  let
    val _ = Sign.no_vars (Sign.pp thy) (Thm.term_of ct);
    val _ = Term.fold_types (Type.no_tvars #> K I) (Thm.term_of ct) ();
    val thm1 = CodegenData.preprocess_cterm thy ct;
    val ct' = Drule.dest_equals_rhs (Thm.cprop_of thm1);
    val consts = CodegenConsts.consts_of thy (Thm.term_of ct');
    val funcgr = make thy consts;
    val (_, thm2) = Thm.varifyT' [] thm1;
    val thm3 = Thm.reflexive (Drule.dest_equals_rhs (Thm.cprop_of thm2));
    val [(_, [thm4])] = specialize_typs thy funcgr [(("", []), [thm3])];
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
    val funcgr' = ensure_consts thy
      (instdefs_of thy (fold (fold (insert (op =)) o insts_of thy funcgr) cs [])) funcgr
  in (f drop ct'' thm5, Funcgr.change thy (K funcgr')) end;

end; (*local*)

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


(** Isar **)

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
