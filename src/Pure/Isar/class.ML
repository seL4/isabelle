(*  Title:      Pure/Isar/class.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Type classes derived from primitive axclasses and locales.
*)

signature CLASS =
sig
  val fork_mixfix: bool -> bool -> mixfix -> mixfix * mixfix

  val axclass_cmd: bstring * xstring list
    -> ((bstring * Attrib.src list) * string list) list
    -> theory -> class * theory
  val classrel_cmd: xstring * xstring -> theory -> Proof.state

  val class: bstring -> class list -> Element.context_i Locale.element list
    -> string list -> theory -> string * Proof.context
  val class_cmd: bstring -> xstring list -> Element.context Locale.element list
    -> xstring list -> theory -> string * Proof.context
  val init: class -> Proof.context -> Proof.context
  val add_const_in_class: string -> (string * mixfix) * (string * term)
    -> theory -> string * theory
  val add_abbrev_in_class: string -> Syntax.mode -> (string * mixfix) * (string * term)
    -> theory -> string * theory
  val remove_constraint: class -> string -> Proof.context -> Proof.context
  val is_class: theory -> class -> bool
  val these_params: theory -> sort -> (string * (string * typ)) list
  val intro_classes_tac: thm list -> tactic
  val default_intro_classes_tac: thm list -> tactic
  val print_classes: theory -> unit
  val uncheck: bool ref

  val instance_arity: (theory -> theory) -> arity list -> theory -> Proof.state
  val instance: arity list -> ((bstring * Attrib.src list) * term) list
    -> (thm list -> theory -> theory)
    -> theory -> Proof.state
  val instance_cmd: (bstring * xstring list * xstring) list
    -> ((bstring * Attrib.src list) * xstring) list
    -> (thm list -> theory -> theory)
    -> theory -> Proof.state
  val prove_instance: tactic -> arity list
    -> ((bstring * Attrib.src list) * term) list
    -> theory -> thm list * theory
  val unoverload: theory -> conv
  val overload: theory -> conv
  val unoverload_const: theory -> string * typ -> string
  val inst_const: theory -> string * string -> string
  val param_const: theory -> string -> (string * string) option
end;

structure Class : CLASS =
struct

(** auxiliary **)

fun fork_mixfix is_locale is_class mx =
  let
    val mx' = Syntax.unlocalize_mixfix mx;
    val mx_global = if not is_locale orelse (is_class andalso not (mx = mx'))
      then mx' else NoSyn;
    val mx_local = if is_locale then mx else NoSyn;
  in (mx_global, mx_local) end;

fun prove_interpretation tac prfx_atts expr inst =
  Locale.interpretation_i I prfx_atts expr inst
  #> Proof.global_terminal_proof
      (Method.Basic (K (Method.SIMPLE_METHOD tac), Position.none), NONE)
  #> ProofContext.theory_of;

fun OF_LAST thm1 thm2 = thm1 RSN (Thm.nprems_of thm2, thm2);

fun strip_all_ofclass thy sort =
  let
    val typ = TVar ((Name.aT, 0), sort);
    fun prem_inclass t =
      case Logic.strip_imp_prems t
       of ofcls :: _ => try Logic.dest_inclass ofcls
        | [] => NONE;
    fun strip_ofclass class thm =
      thm OF (fst o AxClass.of_sort thy (typ, [class])) AxClass.cache;
    fun strip thm = case (prem_inclass o Thm.prop_of) thm
     of SOME (_, class) => thm |> strip_ofclass class |> strip
      | NONE => thm;
  in strip end;

fun get_remove_global_constraint c thy =
  let
    val ty = Sign.the_const_constraint thy c;
  in
    thy
    |> Sign.add_const_constraint (c, NONE)
    |> pair (c, Logic.unvarifyT ty)
  end;


(** axclass command **)

fun axclass_cmd (class, raw_superclasses) raw_specs thy =
  let
    val ctxt = ProofContext.init thy;
    val superclasses = map (Sign.read_class thy) raw_superclasses;
    val name_atts = map ((apsnd o map) (Attrib.attribute thy) o fst)
      raw_specs;
    val axiomss = ProofContext.read_propp (ctxt, map (map (rpair []) o snd)
          raw_specs)
      |> snd
      |> (map o map) fst;
  in
    AxClass.define_class (class, superclasses) []
      (name_atts ~~ axiomss) thy
  end;

local

fun gen_instance mk_prop add_thm after_qed insts thy =
  let
    fun after_qed' results =
      ProofContext.theory ((fold o fold) add_thm results #> after_qed);
  in
    thy
    |> ProofContext.init
    |> Proof.theorem_i NONE after_qed' ((map (fn t => [(t, [])])
        o maps (mk_prop thy)) insts)
  end;

in

val instance_arity =
  gen_instance (Logic.mk_arities oo Sign.cert_arity) AxClass.add_arity;
val classrel =
  gen_instance (single oo (Logic.mk_classrel oo AxClass.cert_classrel))
    AxClass.add_classrel I o single;
val classrel_cmd =
  gen_instance (single oo (Logic.mk_classrel oo AxClass.read_classrel))
    AxClass.add_classrel I o single;

end; (*local*)


(** explicit constants for overloaded definitions **)

structure InstData = TheoryDataFun
(
  type T = (string * thm) Symtab.table Symtab.table * (string * string) Symtab.table;
    (*constant name ~> type constructor ~> (constant name, equation),
        constant name ~> (constant name, type constructor)*)
  val empty = (Symtab.empty, Symtab.empty);
  val copy = I;
  val extend = I;
  fun merge _ ((taba1, tabb1), (taba2, tabb2)) =
    (Symtab.join (K (Symtab.merge (K true))) (taba1, taba2),
      Symtab.merge (K true) (tabb1, tabb2));
);

fun inst_thms thy = (Symtab.fold (Symtab.fold (cons o snd o snd) o snd) o fst)
    (InstData.get thy) [];
fun add_inst (c, tyco) inst = (InstData.map o apfst
      o Symtab.map_default (c, Symtab.empty)) (Symtab.update_new (tyco, inst))
  #> (InstData.map o apsnd) (Symtab.update_new (fst inst, (c, tyco)));

fun unoverload thy = MetaSimplifier.rewrite true (inst_thms thy);
fun overload thy = MetaSimplifier.rewrite true (map Thm.symmetric (inst_thms thy));

fun inst_const thy (c, tyco) =
  (fst o the o Symtab.lookup ((the o Symtab.lookup (fst (InstData.get thy))) c)) tyco;
fun unoverload_const thy (c_ty as (c, _)) =
  case AxClass.class_of_param thy c
   of SOME class => (case Sign.const_typargs thy c_ty
       of [Type (tyco, _)] => (case Symtab.lookup
           ((the o Symtab.lookup (fst (InstData.get thy))) c) tyco
             of SOME (c, _) => c
              | NONE => c)
        | [_] => c)
    | NONE => c;

val param_const = Symtab.lookup o snd o InstData.get;

fun add_inst_def (class, tyco) (c, ty) thy =
  let
    val tyco_base = Sign.base_name tyco;
    val name_inst = Sign.base_name class ^ "_" ^ tyco_base ^ "_inst";
    val c_inst_base = Sign.base_name c ^ "_" ^ tyco_base;
  in
    thy
    |> Sign.sticky_prefix name_inst
    |> Sign.declare_const [] (c_inst_base, ty, NoSyn)
    |-> (fn const as Const (c_inst, _) =>
      PureThy.add_defs_i false
        [((Thm.def_name c_inst_base, Logic.mk_equals (const, Const (c, ty))), [])]
      #-> (fn [thm] => add_inst (c, tyco) (c_inst, Thm.symmetric thm)))
    |> Sign.restore_naming thy
  end;

fun add_inst_def' (class, tyco) (c, ty) thy =
  if case Symtab.lookup (fst (InstData.get thy)) c
   of NONE => true
    | SOME tab => is_none (Symtab.lookup tab tyco)
  then add_inst_def (class, tyco) (c, Logic.unvarifyT ty) thy
  else thy;

fun add_def ((class, tyco), ((name, prop), atts)) thy =
  let
    val ((lhs as Const (c, ty), args), rhs) =
      (apfst Term.strip_comb o Logic.dest_equals) prop;
    fun (*add_inst' def ([], (Const (c_inst, ty))) =
          if forall (fn TFree _ => true | _ => false) (Sign.const_typargs thy (c_inst, ty))
          then add_inst (c, tyco) (c_inst, def)
          else add_inst_def (class, tyco) (c, ty)
      |*) add_inst' _ t = add_inst_def (class, tyco) (c, ty);
  in
    thy
    |> PureThy.add_defs_i true [((name, prop), map (Attrib.attribute_i thy) atts)]
    |-> (fn [def] => add_inst' def (args, rhs) #> pair def)
  end;


(** instances with implicit parameter handling **)

local

fun gen_read_def thy prep_att parse_prop ((raw_name, raw_atts), raw_t) =
  let
    val ctxt = ProofContext.init thy;
    val t = parse_prop ctxt raw_t |> Syntax.check_prop ctxt;
    val ((c, ty), _) = Sign.cert_def ctxt t;
    val atts = map (prep_att thy) raw_atts;
    val insts = Consts.typargs (Sign.consts_of thy) (c, ty);
    val name = case raw_name
     of "" => NONE
      | _ => SOME raw_name;
  in (c, (insts, ((name, t), atts))) end;

fun read_def_cmd thy = gen_read_def thy Attrib.intern_src Syntax.parse_prop;
fun read_def thy = gen_read_def thy (K I) (K I);

fun gen_instance prep_arity read_def do_proof raw_arities raw_defs after_qed theory =
  let
    val arities = map (prep_arity theory) raw_arities;
    val _ = if null arities then error "At least one arity must be given" else ();
    val _ = case (duplicates (op =) o map #1) arities
     of [] => ()
      | dupl_tycos => error ("Type constructors occur more than once in arities: "
          ^ commas_quote dupl_tycos);
    fun get_consts_class tyco ty class =
      let
        val cs = (these o try (#params o AxClass.get_info theory)) class;
        val subst_ty = map_type_tfree (K ty);
      in
        map (fn (c, ty) => (c, ((class, tyco), subst_ty ty))) cs
      end;
    fun get_consts_sort (tyco, asorts, sort) =
      let
        val ty = Type (tyco, map (fn (v, sort) => TVar ((v, 0), sort))
          (Name.names Name.context Name.aT asorts))
      in maps (get_consts_class tyco ty) (Sign.complete_sort theory sort) end;
    val cs = maps get_consts_sort arities;
    fun mk_typnorm thy (ty, ty_sc) =
      case try (Sign.typ_match thy (Logic.varifyT ty_sc, ty)) Vartab.empty
       of SOME env => SOME (Logic.varifyT #> Envir.typ_subst_TVars env #> Logic.unvarifyT)
        | NONE => NONE;
    fun read_defs defs cs thy_read =
      let
        fun read raw_def cs =
          let
            val (c, (inst, ((name_opt, t), atts))) = read_def thy_read raw_def;
            val ty = Consts.instance (Sign.consts_of thy_read) (c, inst);
            val ((class, tyco), ty') = case AList.lookup (op =) cs c
             of NONE => error ("Illegal definition for constant " ^ quote c)
              | SOME class_ty => class_ty;
            val name = case name_opt
             of NONE => Thm.def_name (Logic.name_arity (tyco, [], c))
              | SOME name => name;
            val t' = case mk_typnorm thy_read (ty', ty)
             of NONE => error ("Illegal definition for constant " ^
                  quote (c ^ "::" ^ setmp show_sorts true
                    (Sign.string_of_typ thy_read) ty))
              | SOME norm => map_types norm t
          in (((class, tyco), ((name, t'), atts)), AList.delete (op =) c cs) end;
      in fold_map read defs cs end;
    val (defs, other_cs) = read_defs raw_defs cs
      (fold Sign.primitive_arity arities (Theory.copy theory));
    fun after_qed' cs defs =
      fold Sign.add_const_constraint (map (apsnd SOME) cs)
      #> after_qed defs;
  in
    theory
    |> fold_map get_remove_global_constraint (map fst cs |> distinct (op =))
    ||>> fold_map add_def defs
    ||> fold (fn (c, ((class, tyco), ty)) => add_inst_def' (class, tyco) (c, ty)) other_cs
    |-> (fn (cs, defs) => do_proof (after_qed' cs defs) arities defs)
  end;

fun tactic_proof tac f arities defs =
  fold (fn arity => AxClass.prove_arity arity tac) arities
  #> f
  #> pair defs;

in

val instance = gen_instance Sign.cert_arity read_def
  (fn f => fn arities => fn defs => instance_arity f arities);
val instance_cmd = gen_instance Sign.read_arity read_def_cmd
  (fn f => fn arities => fn defs => instance_arity f arities);
fun prove_instance tac arities defs =
  gen_instance Sign.cert_arity read_def
    (tactic_proof tac) arities defs (K I);

end; (*local*)



(** class data **)

datatype class_data = ClassData of {
  consts: (string * string) list
    (*locale parameter ~> constant name*),
  local_sort: sort,
  inst: (typ option list * term option list) * term Symtab.table
    (*canonical interpretation FIXME*),
  intro: thm,
  defs: thm list,
  operations: (string * (term * (typ * int))) list
    (*constant name ~> (locale term, (constant constraint, instantiaton index of class typ))*),
  operations_rev: (string * string) list
    (*locale operation ~> constant name*)
};

fun rep_class_data (ClassData d) = d;
fun mk_class_data ((consts, local_sort, inst, intro),
    (defs, operations, operations_rev)) =
  ClassData { consts = consts, local_sort = local_sort, inst = inst,
    intro = intro, defs = defs, operations = operations,
    operations_rev = operations_rev };
fun map_class_data f (ClassData { consts, local_sort, inst, intro,
    defs, operations, operations_rev }) =
  mk_class_data (f ((consts, local_sort, inst, intro),
    (defs, operations, operations_rev)));
fun merge_class_data _ (ClassData { consts = consts,
    local_sort = local_sort, inst = inst, intro = intro,
    defs = defs1, operations = operations1, operations_rev = operations_rev1 },
  ClassData { consts = _, local_sort = _, inst = _, intro = _,
    defs = defs2, operations = operations2, operations_rev = operations_rev2 }) =
  mk_class_data ((consts, local_sort, inst, intro),
    (Thm.merge_thms (defs1, defs2),
      AList.merge (op =) (K true) (operations1, operations2),
      AList.merge (op =) (K true) (operations_rev1, operations_rev2)));

structure ClassData = TheoryDataFun
(
  type T = class_data Graph.T
  val empty = Graph.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Graph.join merge_class_data;
);


(* queries *)

val lookup_class_data = Option.map rep_class_data oo try o Graph.get_node o ClassData.get;

fun the_class_data thy class = case lookup_class_data thy class
 of NONE => error ("Undeclared class " ^ quote class)
  | SOME data => data;

val is_class = is_some oo lookup_class_data;

val ancestry = Graph.all_succs o ClassData.get;

fun these_params thy =
  let
    fun params class =
      let
        val const_typs = (#params o AxClass.get_info thy) class;
        val const_names = (#consts o the_class_data thy) class;
      in
        (map o apsnd) (fn c => (c, (the o AList.lookup (op =) const_typs) c)) const_names
      end;
  in maps params o ancestry thy end;

fun these_defs thy = maps (these o Option.map #defs o lookup_class_data thy) o ancestry thy;

fun these_intros thy =
  Graph.fold (fn (_, (data, _)) => insert Thm.eq_thm ((#intro o rep_class_data) data))
    (ClassData.get thy) [];

fun these_operations thy =
  maps (#operations o the_class_data thy) o ancestry thy;

fun these_operations_rev thy =
  maps (#operations_rev o the_class_data thy) o ancestry thy;

fun local_operation thy = AList.lookup (op =) o these_operations thy;

fun global_operation thy = AList.lookup (op =) o these_operations_rev thy;

fun sups_local_sort thy sort =
  let
    val sups = filter (is_some o lookup_class_data thy) sort
      |> Sign.minimize_sort thy;
    val local_sort = case sups
     of sup :: _ => #local_sort (the_class_data thy sup)
      | [] => sort;
  in (sups, local_sort) end;

fun print_classes thy =
  let
    val ctxt = ProofContext.init thy;

    val algebra = Sign.classes_of thy;
    val arities =
      Symtab.empty
      |> Symtab.fold (fn (tyco, arities) => fold (fn (class, _) =>
           Symtab.map_default (class, []) (insert (op =) tyco)) arities)
             ((#arities o Sorts.rep_algebra) algebra);
    val the_arities = these o Symtab.lookup arities;
    fun mk_arity class tyco =
      let
        val Ss = Sorts.mg_domain algebra tyco [class];
      in Syntax.pretty_arity ctxt (tyco, Ss, [class]) end;
    fun mk_param (c, ty) = Pretty.str (Sign.extern_const thy c ^ " :: "
      ^ setmp show_sorts false (Syntax.string_of_typ ctxt o Type.strip_sorts) ty);
    fun mk_entry class = (Pretty.block o Pretty.fbreaks o map_filter I) [
      (SOME o Pretty.str) ("class " ^ class ^ ":"),
      (SOME o Pretty.block) [Pretty.str "supersort: ",
        (Syntax.pretty_sort ctxt o Sign.minimize_sort thy o Sign.super_classes thy) class],
      if is_class thy class then (SOME o Pretty.str) ("locale: " ^ class) else NONE,
      ((fn [] => NONE | ps => (SOME o Pretty.block o Pretty.fbreaks) (Pretty.str "parameters:" :: ps)) o map mk_param
        o these o Option.map #params o try (AxClass.get_info thy)) class,
      (SOME o Pretty.block o Pretty.breaks) [
        Pretty.str "instances:",
        Pretty.list "" "" (map (mk_arity class) (the_arities class))
      ]
    ]
  in
    (Pretty.writeln o Pretty.chunks o separate (Pretty.str "")
      o map mk_entry o Sorts.all_classes) algebra
  end;


(* updaters *)

fun add_class_data ((class, superclasses), (cs, local_sort, inst, intro)) thy =
  let
    (*FIXME*)
    val is_empty = null (fold (fn ((_, ty), _) => fold_atyps cons ty) cs [])
      andalso null ((fold o fold_types o fold_atyps) cons
        (maps snd (Locale.global_asms_of thy class)) []);
    (*FIXME*)
    val inst_params = map
      (SOME o the o Symtab.lookup inst o fst o fst)
        (Locale.parameters_of_expr thy (Locale.Locale class));
    val instT = if is_empty then [] else [SOME (TFree (Name.aT, [class]))];
    val inst' = ((instT, inst_params), inst);
    val operations = map (fn (v_ty, (c, ty)) => (c, (Free v_ty, (ty, 0)))) cs;
    val cs = (map o pairself) fst cs;
    val add_class = Graph.new_node (class,
        mk_class_data ((cs, local_sort, inst', intro), ([], operations, [])))
      #> fold (curry Graph.add_edge class) superclasses;
  in
    ClassData.map add_class thy
  end;

fun register_operation class (entry, some_def) =
  (ClassData.map o Graph.map_node class o map_class_data o apsnd)
    (fn (defs, operations, operations_rev) =>
      (case some_def of NONE => defs | SOME def => def :: defs,
        entry :: operations, (*FIXME*)operations_rev));


(** rule calculation, tactics and methods **)

val class_prefix = Logic.const_of_class o Sign.base_name;

fun class_intro thy class sups =
  let
    fun class_elim class =
      case (#axioms o AxClass.get_info thy) class
       of [thm] => SOME (Drule.unconstrainTs thm)
        | [] => NONE;
    val pred_intro = case Locale.intros thy class
     of ([ax_intro], [intro]) => intro |> OF_LAST ax_intro |> SOME
      | ([intro], []) => SOME intro
      | ([], [intro]) => SOME intro
      | _ => NONE;
    val pred_intro' = pred_intro
      |> Option.map (fn intro => intro OF map_filter class_elim sups);
    val class_intro = (#intro o AxClass.get_info thy) class;
    val raw_intro = case pred_intro'
     of SOME pred_intro => class_intro |> OF_LAST pred_intro
      | NONE => class_intro;
    val sort = Sign.super_classes thy class;
    val typ = TVar ((Name.aT, 0), sort);
    val defs = these_defs thy sups;
  in
    raw_intro
    |> Drule.instantiate' [SOME (Thm.ctyp_of thy typ)] []
    |> strip_all_ofclass thy sort
    |> Thm.strip_shyps
    |> MetaSimplifier.rewrite_rule defs
    |> Drule.unconstrainTs
  end;

fun class_interpretation class facts defs thy =
  let
    val params = these_params thy [class];
    val { inst = ((_, inst), _), ... } = the_class_data thy class;
    (*val _ = tracing ("interpreting with " ^ cat_lines (map (setmp show_sorts true makestring)
      (map_filter I inst)));*)
    val tac = ALLGOALS (ProofContext.fact_tac facts);
    val prfx = class_prefix class;
  in
    thy
    |> fold_map (get_remove_global_constraint o fst o snd) params
    ||> prove_interpretation tac ((false, prfx), []) (Locale.Locale class) (inst, defs)
    |-> (fn cs => fold (Sign.add_const_constraint o apsnd SOME) cs)
  end;

fun intro_classes_tac facts st =
  let
    val thy = Thm.theory_of_thm st;
    val classes = Sign.all_classes thy;
    val class_trivs = map (Thm.class_triv thy) classes;
    val class_intros = these_intros thy;
    val axclass_intros = map_filter (try (#intro o AxClass.get_info thy)) classes;
  in
    (ALLGOALS (Method.insert_tac facts THEN'
      REPEAT_ALL_NEW (resolve_tac (class_trivs @ class_intros @ axclass_intros)))
    THEN Tactic.distinct_subgoals_tac) st
  end;

fun default_intro_classes_tac [] = intro_classes_tac []
  | default_intro_classes_tac _ = no_tac;

fun default_tac rules ctxt facts =
  HEADGOAL (Method.some_rule_tac rules ctxt facts) ORELSE
    default_intro_classes_tac facts;

val _ = Context.add_setup (Method.add_methods
 [("intro_classes", Method.no_args (Method.METHOD intro_classes_tac),
    "back-chain introduction rules of classes"),
  ("default", Method.thms_ctxt_args (Method.METHOD oo default_tac),
    "apply some intro/elim rule")]);


(** classes and class target **)

(* class context syntax *)

fun internal_remove_constraint local_sort (c, (_, (ty, typidx))) ctxt =
  let
    val consts = ProofContext.consts_of ctxt;
    val typargs = Consts.typargs consts (c, ty);
    val typargs' = nth_map typidx (K (TVar ((Name.aT, 0), local_sort))) typargs;
    val ty' = Consts.instance consts (c, typargs');
  in ProofContext.add_const_constraint (c, SOME ty') ctxt end;

fun remove_constraint class c ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val SOME entry = local_operation thy [class] c;
  in
    internal_remove_constraint
      ((#local_sort o the_class_data thy) class) (c, entry) ctxt
  end;

fun sort_term_check sups local_sort ts ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val local_operation = local_operation thy sups;
    val constraints = these_operations thy sups |> (map o apsnd) (fst o snd);
    val consts = ProofContext.consts_of ctxt;
    fun check_typ (c, ty) (t', idx) = case nth (Consts.typargs consts (c, ty)) idx
     of TFree (v, _) => if v = Name.aT
          then apfst (AList.update (op =) ((c, ty), t')) else I
      | TVar (vi, _) => if TypeInfer.is_param vi
          then apfst (AList.update (op =) ((c, ty), t'))
            #> apsnd (insert (op =) vi) else I
      | _ => I;
    fun add_const (Const (c, ty)) = (case local_operation c
         of SOME (t', (_, idx)) => check_typ (c, ty) (t', idx)
          | NONE => I)
      | add_const _ = I;
    val (cs, typarams) = (fold o fold_aterms) add_const ts ([], []);
    val ts' = map (map_aterms
        (fn t as Const (c, ty) => the_default t (AList.lookup (op =) cs (c, ty)) | t => t)
      #> (map_types o map_type_tvar) (fn var as (vi, _) => if member (op =) typarams vi
           then TFree (Name.aT, local_sort) else TVar var)) ts;
    val ctxt' = fold (ProofContext.add_const_constraint o apsnd SOME) constraints ctxt;
  in if eq_list (op aconv) (ts, ts') then NONE else SOME (ts', ctxt') end;

val uncheck = ref false;

fun sort_term_uncheck sups ts ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val global_param = AList.lookup (op =) (these_params thy sups) #> Option.map fst;
    val global_operation = global_operation thy sups;
    fun globalize (t as Free (v, ty)) = (case global_param v
         of SOME c => Const (c, ty)
          | NONE => t)
      | globalize (t as Const (c, ty)) = (case global_operation c
         of SOME c => Const (c, ty)
          | NONE => t)
      | globalize t = t;
    val ts' = if ! uncheck then (map o map_aterms) globalize ts else ts;
  in if eq_list (op aconv) (ts, ts') then NONE else SOME (ts', ctxt) end;

fun init_class_ctxt sups local_sort ctxt =
  let
    val operations = these_operations (ProofContext.theory_of ctxt) sups;
  in
    ctxt
    |> Variable.declare_term
        (Logic.mk_type (TFree (Name.aT, local_sort)))
    |> fold (internal_remove_constraint local_sort) operations
    |> Context.proof_map (Syntax.add_term_check 50 "class"
        (sort_term_check sups local_sort)
        #> Syntax.add_term_uncheck 50 "class"
          (sort_term_uncheck sups))
  end;

fun init class ctxt =
  init_class_ctxt [class]
    ((#local_sort o the_class_data (ProofContext.theory_of ctxt)) class) ctxt;


(* class definition *)

local

fun gen_class_spec prep_class prep_expr process_expr thy raw_supclasses raw_includes_elems =
  let
    val supclasses = map (prep_class thy) raw_supclasses;
    val (sups, local_sort) = sups_local_sort thy supclasses;
    val supsort = Sign.minimize_sort thy supclasses;
    val suplocales = map Locale.Locale sups;
    val (raw_elems, includes) = fold_rev (fn Locale.Elem e => apfst (cons e)
      | Locale.Expr i => apsnd (cons (prep_expr thy i))) raw_includes_elems ([], []);
    val supexpr = Locale.Merge suplocales;
    val supparams = (map fst o Locale.parameters_of_expr thy) supexpr;
    val supconsts = AList.make (the o AList.lookup (op =) (these_params thy sups))
      (map fst supparams);
    val mergeexpr = Locale.Merge (suplocales @ includes);
    val constrain = Element.Constrains ((map o apsnd o map_atyps)
      (fn TFree (_, sort) => TFree (Name.aT, sort)) supparams);
  in
    ProofContext.init thy
    |> Locale.cert_expr supexpr [constrain]
    |> snd
    |> init_class_ctxt sups local_sort
    |> process_expr Locale.empty raw_elems
    |> fst
    |> (fn elems => ((((sups, supconsts), (supsort, local_sort, mergeexpr)),
          (*FIXME*) if null includes then constrain :: elems else elems)))
  end;

val read_class_spec = gen_class_spec Sign.intern_class Locale.intern_expr Locale.read_expr;
val check_class_spec = gen_class_spec (K I) (K I) Locale.cert_expr;

fun define_class_params (name, raw_superclasses) raw_consts raw_dep_axioms other_consts thy =
  let
    val superclasses = map (Sign.certify_class thy) raw_superclasses;
    val consts = (map o apfst o apsnd) (Sign.certify_typ thy) raw_consts;
    fun add_const ((c, ty), syn) = Sign.declare_const [] (c, ty, syn) #>> Term.dest_Const;
    fun mk_axioms cs thy =
      raw_dep_axioms thy cs
      |> (map o apsnd o map) (Sign.cert_prop thy)
      |> rpair thy;
    fun constrain_typs class = (map o apsnd o Term.map_type_tfree)
      (fn (v, _) => TFree (v, [class]))
  in
    thy
    |> Sign.add_path (Logic.const_of_class name)
    |> fold_map add_const consts
    ||> Sign.restore_naming thy
    |-> (fn cs => mk_axioms cs
    #-> (fn axioms_prop => AxClass.define_class (name, superclasses)
           (map fst cs @ other_consts) axioms_prop
    #-> (fn class => `(fn _ => constrain_typs class cs)
    #-> (fn cs' => `(fn thy => AxClass.get_info thy class)
    #-> (fn {axioms, ...} => fold (Sign.add_const_constraint o apsnd SOME) cs'
    #> pair (class, (cs', axioms)))))))
  end;

fun gen_class prep_spec prep_param bname
    raw_supclasses raw_includes_elems raw_other_consts thy =
  let
    val class = Sign.full_name thy bname;
    val (((sups, supconsts), (supsort, local_sort, mergeexpr)), elems) =
      prep_spec thy raw_supclasses raw_includes_elems;
    val other_consts = map (tap (Sign.the_const_type thy) o prep_param thy) raw_other_consts;
    fun mk_inst class param_names cs =
      Symtab.empty
      |> fold2 (fn v => fn (c, ty) => Symtab.update (v, Const
           (c, Term.map_type_tfree (fn (v, _) => TFree (v, [class])) ty))) param_names cs;
    fun extract_params thy =
      let
        val params = Locale.parameters_of thy class;
        val _ = if Sign.subsort thy (supsort, local_sort) then () else error
          ("Sort " ^ Sign.string_of_sort thy local_sort
            ^ " is less general than permitted least general sort "
            ^ Sign.string_of_sort thy supsort);
      in
        (map fst params, params
        |> (map o apfst o apsnd o Term.map_type_tfree) (K (TFree (Name.aT, local_sort)))
        |> (map o apsnd) (fork_mixfix true true #> fst)
        |> chop (length supconsts)
        |> snd)
      end;
    fun extract_assumes params thy cs =
      let
        val consts = supconsts @ (map (fst o fst) params ~~ cs);
        fun subst (Free (c, ty)) =
              Const ((fst o the o AList.lookup (op =) consts) c, ty)
          | subst t = t;
        fun prep_asm ((name, atts), ts) =
          ((Sign.base_name name, map (Attrib.attribute_i thy) atts),
            (map o map_aterms) subst ts);
      in
        Locale.global_asms_of thy class
        |> map prep_asm
      end;
    fun note_intro class_intro =
      PureThy.note_thmss_qualified "" (class_prefix class)
        [(("intro", []), [([class_intro], [])])]
      #> snd
  in
    thy
    |> Locale.add_locale_i (SOME "") bname mergeexpr elems
    |> snd
    |> ProofContext.theory (`extract_params
      #-> (fn (globals, params) =>
        define_class_params (bname, supsort) params
          (extract_assumes params) other_consts
      #-> (fn (_, (consts, axioms)) =>
        `(fn thy => class_intro thy class sups)
      #-> (fn class_intro =>
        add_class_data ((class, sups),
          (map fst params ~~ consts, local_sort,
            mk_inst class (map fst globals) (map snd supconsts @ consts),
              class_intro))
      #> note_intro class_intro
      #> class_interpretation class axioms []
      ))))
    |> pair class
  end;

in

val class_cmd = gen_class read_class_spec ((#1 o Term.dest_Const) oo Sign.read_const);
val class = gen_class check_class_spec (K I);

end; (*local*)


(* definition in class target *)

fun export_fixes thy class =
  let
    val cs = these_params thy [class];
    fun subst_aterm (t as Free (v, ty)) = (case AList.lookup (op =) cs v
         of SOME (c, _) => Const (c, ty)
          | NONE => t)
      | subst_aterm t = t;
  in Term.map_aterms subst_aterm end;

fun mk_operation_entry thy (c, rhs) =
  let
    val ty = Logic.unvarifyT (Sign.the_const_constraint thy c);
    val typargs = Sign.const_typargs thy (c, ty);
    val typidx = find_index (fn TFree (w, _) => Name.aT = w | _ => false) typargs;
  in (c, (rhs, (ty, typidx))) end;

fun add_const_in_class class ((c, mx), (c_loc, rhs)) thy =
  let
    val _ = tracing c_loc;
    val prfx = class_prefix class;
    val thy' = thy |> Sign.add_path prfx;

    val rhs' = export_fixes thy' class rhs;
    val subst_typ = Term.map_type_tfree (fn var as (w, sort) =>
      if w = Name.aT then TFree (w, [class]) else TFree var);
    val ty' = Term.fastype_of rhs';
    val ty'' = subst_typ ty';
    val c' = Sign.full_name thy' c;
    val c'' = NameSpace.full (Sign.naming_of thy' |> NameSpace.add_path prfx) c;
    val def = (c, Logic.mk_equals (Const (c', ty'), rhs'));
    val (mx', _) = fork_mixfix true true mx;
    fun interpret def thy =
      let
        val def' = symmetric def;
        val def_eq = (map_types Logic.unvarifyT o Thm.prop_of) def';
      in
        thy
        |> class_interpretation class [def'] [def_eq]
        |> Sign.add_const_constraint (c', SOME ty'')
        |> `(fn thy => mk_operation_entry thy (c', rhs))
        |-> (fn entry => register_operation class (entry, SOME def'))
      end;
  in
    thy'
    |> Sign.hide_consts_i false [c'']
    |> Sign.declare_const [] (c, ty', mx') |> snd
    |> Sign.parent_path
    |> Sign.sticky_prefix prfx
    |> PureThy.add_defs_i false [(def, [])]
    |-> (fn [def] => interpret def)
    |> Sign.restore_naming thy
    |> pair c'
  end;


(* abbreviation in class target *)

fun add_abbrev_in_class class prmode ((c, mx), (c_loc, rhs)) thy =
  let
    val _ = tracing c_loc;
    val prfx = class_prefix class;
    val naming = Sign.naming_of thy |> NameSpace.add_path prfx |> NameSpace.add_path prfx;
      (*FIXME*)
    val c' = NameSpace.full naming c;
    val rhs' = export_fixes thy class rhs;
    val ty' = Term.fastype_of rhs';
    val entry = mk_operation_entry thy (c', rhs);
  in
    thy
    |> Sign.notation true prmode [(Const (c', ty'), mx)]
    |> register_operation class (entry, NONE)
    |> pair c'
  end;

end;
