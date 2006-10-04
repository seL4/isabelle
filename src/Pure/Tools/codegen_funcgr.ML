(*  Title:      Pure/Tools/codegen_funcgr.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Retrieving, normalizing and structuring code function theorems
in graph with explicit dependencies.
*)

signature CODEGEN_FUNCGR =
sig
  type T;
  val mk_funcgr: theory -> CodegenConsts.const list -> (string * typ) list -> T
  val all_deps_of: T -> CodegenConsts.const list -> CodegenConsts.const list list
  val get_funcs: T -> CodegenConsts.const -> thm list
  val get_func_typs: T -> (CodegenConsts.const * typ) list
  val normalize: theory -> thm list -> thm list
  val print_codethms: theory -> CodegenConsts.const list -> unit
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
  fun purge _ _ = Constgraph.empty;
end);

val _ = Context.add_setup Funcgr.init;


(** theorem purification **)

fun abs_norm thy thm =
  let
    fun eta_expand thm =
      let
        val lhs = (fst o Logic.dest_equals o Drule.plain_prop_of) thm;
        val tys = (fst o strip_type o fastype_of) lhs;
        val vs_ct = map (fn (v, ty) => cterm_of thy (Var ((v, 0), ty)))
          (Name.names Name.context "a" tys);
      in
        fold (fn ct => fn thm => Thm.combination thm (Thm.reflexive ct)) vs_ct thm
      end;
    fun beta_norm thm =
      let
        val rhs = (snd o Logic.dest_equals o Drule.plain_prop_of) thm;
        val thm' = Thm.beta_conversion true (cterm_of thy rhs);
      in Thm.transitive thm thm' end;
  in
    thm
    |> eta_expand
    |> beta_norm
  end;

fun canonical_tvars thy thm =
  let
    fun mk_inst (v_i as (v, i), (v', sort)) (s as (maxidx, set, acc)) =
      if v = v' orelse member (op =) set v then s
        else let
          val ty = TVar (v_i, sort)
        in
          (maxidx + 1, v :: set,
            (ctyp_of thy ty, ctyp_of thy (TVar ((v', maxidx), sort))) :: acc)
        end;
    fun tvars_of thm = (fold_types o fold_atyps)
      (fn TVar (v_i as (v, i), sort) => cons (v_i, (CodegenNames.purify_var v, sort))
        | _ => I) (prop_of thm) [];
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, _, inst) = fold mk_inst (tvars_of thm) (maxidx + 1, [], []);
  in Thm.instantiate (inst, []) thm end;

fun canonical_vars thy thm =
  let
    fun mk_inst (v_i as (v, i), (v', ty)) (s as (maxidx, set, acc)) =
      if v = v' orelse member (op =) set v then s
        else let
          val t = if i = ~1 then Free (v, ty) else Var (v_i, ty)
        in
          (maxidx + 1,  v :: set,
            (cterm_of thy t, cterm_of thy (Var ((v', maxidx), ty))) :: acc)
        end;
    fun vars_of thm = fold_aterms
      (fn Var (v_i as (v, i), ty) => cons (v_i, (CodegenNames.purify_var v, ty))
        | _ => I) (prop_of thm) [];
    val maxidx = Thm.maxidx_of thm + 1;
    val (_, _, inst) = fold mk_inst (vars_of thm) (maxidx + 1, [], []);
  in Thm.instantiate ([], inst) thm end;

fun normalize thy thms =
  let
    fun burrow_thms f [] = []
      | burrow_thms f thms =
          thms
          |> Conjunction.intr_list
          |> f
          |> Conjunction.elim_list;
    fun unvarify thms =
      #2 (#1 (Variable.import true thms (ProofContext.init thy)));
  in
    thms
    |> map (abs_norm thy)
    |> burrow_thms (
        canonical_tvars thy
        #> canonical_vars thy
        #> Drule.zero_var_indexes
       )
  end;



(** retrieval **)

fun get_funcs funcgr (c_tys as (c, _)) =
  (these o Option.map snd o try (Constgraph.get_node funcgr)) c_tys;

fun get_func_typs funcgr =
  AList.make (fst o Constgraph.get_node funcgr) (Constgraph.keys funcgr);

fun all_deps_of funcgr cs =
  let
    val conn = Constgraph.strong_conn funcgr;
    val order = rev conn;
  in
    (map o filter) (member (op =) (Constgraph.all_succs funcgr cs)) order
    |> filter_out null
  end;

local

fun add_things_of thy f (c, thms) =
  (fold o fold_aterms)
     (fn Const c_ty => let
            val c' = CodegenConsts.norm_of_typ thy c_ty
          in if CodegenConsts.eq_const (c, c') then I
          else f (c', c_ty) end
       | _ => I) (maps (op :: o swap o apfst (snd o strip_comb)
            o Logic.dest_equals o Drule.plain_prop_of) thms)

fun rhs_of thy (c, thms) =
  Consttab.empty
  |> add_things_of thy (Consttab.update o rpair () o fst) (c, thms)
  |> Consttab.keys;

fun rhs_of' thy (c, thms) =
  add_things_of thy (cons o snd) (c, thms) [];

fun insts_of thy funcgr (c, ty) =
  let
    val tys = Sign.const_typargs thy (c, ty);
    val c' = CodegenConsts.norm thy (c, tys);
    val ty_decl = CodegenConsts.disc_typ_of_const thy
      (fst o Constgraph.get_node funcgr o CodegenConsts.norm thy) (c, tys);
    val tys_decl = Sign.const_typargs thy (c, ty_decl);
    val pp = Sign.pp thy;
    val algebra = Sign.classes_of thy;
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
  in
    flat (maps (Sorts.of_sort_derivation pp algebra
      { classrel = classrel, constructor = constructor, variable = variable })
      (fold2 mk_inst tys tys_decl []))
  end;

fun all_classops thy tyco class =
  maps (AxClass.params_of thy)
      (Graph.all_succs ((#classes o Sorts.rep_algebra o Sign.classes_of) thy) [class])
  |> AList.make (fn c => CodegenConsts.disc_typ_of_classop thy (c, [Type (tyco, [])]))
        (*typ_of_classop is very liberal in its type arguments*)
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

fun insts_of_thms thy funcgr c_thms =
  let
    val insts = add_things_of thy (fn (_, c_ty) => fold (insert (op =))
      (insts_of thy funcgr c_ty)) c_thms [];
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
    val thms = normalize thy (CodegenData.these_funcs thy c);
    val rhs = rhs_of thy (c, thms);
  in
    auxgr
    |> Constgraph.new_node (c, thms)
    |> fold_map (ensure_const thy funcgr) rhs
    |-> (fn rhs' => fold (fn SOME c' => Constgraph.add_edge (c, c')
                           | NONE => I) rhs')
    |> pair (SOME c)
  end;

fun specialize_typs thy funcgr eqss =
  let
    fun max k [] = k
      | max k (l::ls) = max (if k < l then l else k) ls;
    fun typscheme_of (c, ty) =
      try (Constgraph.get_node funcgr) (CodegenConsts.norm_of_typ thy (c, ty))
      |> Option.map fst;
    fun incr_indices (c, thms) maxidx =
      let
        val thms' = map (Thm.incr_indexes maxidx) thms;
        val maxidx' = Int.max
          (maxidx, max ~1 (map Thm.maxidx_of thms') + 1);
      in ((c, thms'), maxidx') end;
    val tsig = Sign.tsig_of thy;
    fun unify_const thms (c, ty) (env, maxidx) =
      case typscheme_of (c, ty)
       of SOME ty_decl => let
            val ty_decl' = Logic.incr_tvar maxidx ty_decl;
            val maxidx' = Int.max (Term.maxidx_of_typ ty_decl' + 1, maxidx);
          in Type.unify tsig (ty_decl', ty) (env, maxidx')
          handle TUNIFY => error ("Failed to instantiate\n"
            ^ (Sign.string_of_typ thy o Envir.norm_type env) ty_decl' ^ "\nto\n"
            ^ (Sign.string_of_typ thy o Envir.norm_type env) ty ^ ",\n"
            ^ "in function theorems\n"
            ^ cat_lines (map string_of_thm thms))
          end
        | NONE => (env, maxidx);
    fun apply_unifier unif (c, []) = (c, [])
      | apply_unifier unif (c, thms as thm :: _) =
          let
            val ty = CodegenData.typ_func thy thm;
            val ty' = Envir.norm_type unif ty;
            val env = Type.typ_match (Sign.tsig_of thy) (ty, ty') Vartab.empty;
            val inst = Thm.instantiate (Vartab.fold (fn (x_i, (sort, ty)) =>
              cons (Thm.ctyp_of thy (TVar (x_i, sort)), Thm.ctyp_of thy ty)) env [], []);
          in (c, map (Drule.zero_var_indexes o inst) thms) end;
    val (eqss', maxidx) =
      fold_map incr_indices eqss 0;
    val (unif, _) =
      fold (fn (c, thms) => fold (unify_const thms) (rhs_of' thy (c, thms)))
        eqss' (Vartab.empty, maxidx);
    val eqss'' =
      map (apply_unifier unif) eqss';
  in eqss'' end;

fun merge_eqsyss thy raw_eqss funcgr =
  let
    val eqss = specialize_typs thy funcgr raw_eqss;
    val tys = map (fn (c as (name, _), []) => (case AxClass.class_of_param thy name
         of SOME class => (case ClassPackage.the_consts_sign thy class of (v, cs) =>
              (Logic.varifyT o map_type_tfree (fn u as (w, _) =>
                if w = v then TFree (v, [class]) else TFree u))
              ((the o AList.lookup (op =) cs) name))
          | NONE => Sign.the_const_type thy name)
                   | (_, eq :: _) => CodegenData.typ_func thy eq) eqss;
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
       (rev (Constgraph.strong_conn auxgr))) funcgr);

in

val ensure_consts = ensure_consts;

fun mk_funcgr thy consts cs =
  Funcgr.change thy (
    ensure_consts thy consts
    #> (fn funcgr => ensure_consts thy
         (instdefs_of thy (fold (fold (insert (op =)) o insts_of thy funcgr) cs [])) funcgr)
  );

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
  mk_funcgr thy consts [] |> print_funcgr thy;

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
