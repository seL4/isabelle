(*  Title:      Pure/Isar/class.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Type classes derived from primitive axclasses and locales.
*)

signature CLASS =
sig
  val axclass_cmd: bstring * xstring list
    -> ((bstring * Attrib.src list) * string list) list
    -> theory -> class * theory
  val classrel_cmd: xstring * xstring -> theory -> Proof.state

  val class: bstring -> class list -> Element.context_i Locale.element list
    -> string list -> theory -> string * Proof.context
  val class_cmd: bstring -> xstring list -> Element.context Locale.element list
    -> xstring list -> theory -> string * Proof.context
  val is_class: theory -> class -> bool
  val these_params: theory -> sort -> (string * (string * typ)) list
  val init: class -> Proof.context -> Proof.context
  val add_logical_const: string -> Markup.property list
    -> (string * mixfix) * term -> theory -> string * theory
  val add_syntactic_const: string -> Syntax.mode -> Markup.property list
    -> (string * mixfix) * term -> theory -> string * theory
  val refresh_syntax: class -> Proof.context -> Proof.context
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

val classN = "class";
val introN = "intro";

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
  base_sort: sort,
  inst: term option list
    (*canonical interpretation*),
  morphism: morphism,
    (*partial morphism of canonical interpretation*)
  intro: thm,
  defs: thm list,
  operations: (string * (((term * typ) * (typ * int)) * term)) list
    (*constant name ~> ((locale term & typ,
        (constant constraint, instantiaton index of class typ)), locale term for uncheck)*)
};

fun rep_class_data (ClassData d) = d;
fun mk_class_data ((consts, base_sort, inst, morphism, intro),
    (defs, operations)) =
  ClassData { consts = consts, base_sort = base_sort, inst = inst,
    morphism = morphism, intro = intro, defs = defs,
    operations = operations };
fun map_class_data f (ClassData { consts, base_sort, inst, morphism, intro,
    defs, operations }) =
  mk_class_data (f ((consts, base_sort, inst, morphism, intro),
    (defs, operations)));
fun merge_class_data _ (ClassData { consts = consts,
    base_sort = base_sort, inst = inst, morphism = morphism, intro = intro,
    defs = defs1, operations = operations1 },
  ClassData { consts = _, base_sort = _, inst = _, morphism = _, intro = _,
    defs = defs2, operations = operations2 }) =
  mk_class_data ((consts, base_sort, inst, morphism, intro),
    (Thm.merge_thms (defs1, defs2),
      AList.merge (op =) (K true) (operations1, operations2)));

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

fun morphism thy = #morphism o the_class_data thy;

fun these_intros thy =
  Graph.fold (fn (_, (data, _)) => insert Thm.eq_thm ((#intro o rep_class_data) data))
    (ClassData.get thy) [];

fun these_operations thy =
  maps (#operations o the_class_data thy) o ancestry thy;

fun local_operation thy = AList.lookup (op =) o these_operations thy;

fun sups_base_sort thy sort =
  let
    val sups = filter (is_class thy) sort
      |> Sign.minimize_sort thy;
    val base_sort = case sups
     of _ :: _ => maps (#base_sort o the_class_data thy) sups
          |> Sign.minimize_sort thy
      | [] => sort;
  in (sups, base_sort) end;

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
      (SOME o Pretty.str) ("class " ^ Sign.extern_class thy class ^ ":"),
      (SOME o Pretty.block) [Pretty.str "supersort: ",
        (Syntax.pretty_sort ctxt o Sign.minimize_sort thy o Sign.super_classes thy) class],
      if is_class thy class then (SOME o Pretty.str)
        ("locale: " ^ Locale.extern thy class) else NONE,
      ((fn [] => NONE | ps => (SOME o Pretty.block o Pretty.fbreaks)
          (Pretty.str "parameters:" :: ps)) o map mk_param
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

fun add_class_data ((class, superclasses), (cs, base_sort, insttab, phi, intro)) thy =
  let
    val inst = map
      (SOME o the o Symtab.lookup insttab o fst o fst)
        (Locale.parameters_of_expr thy (Locale.Locale class));
    val operations = map (fn (v_ty as (_, ty'), (c, ty)) =>
      (c, (((Free v_ty, ty'), (Logic.varifyT ty, 0)), Free v_ty))) cs;
    val cs = (map o pairself) fst cs;
    val add_class = Graph.new_node (class,
        mk_class_data ((cs, base_sort, inst, phi, intro), ([], operations)))
      #> fold (curry Graph.add_edge class) superclasses;
  in
    ClassData.map add_class thy
  end;

fun register_operation class ((c, (dict, dict_rev)), some_def) thy =
  let
    val ty = Sign.the_const_constraint thy c;
    val typargs = Sign.const_typargs thy (c, ty);
    val typidx = find_index (fn TVar ((v, _), _) => Name.aT = v | _ => false) typargs;
    val ty' = Term.fastype_of dict;
  in
    thy
    |> (ClassData.map o Graph.map_node class o map_class_data o apsnd)
      (fn (defs, operations) =>
        (fold cons (the_list some_def) defs,
          (c, (((dict, ty'), (ty, typidx)), dict_rev)) :: operations))
  end;


(** rule calculation, tactics and methods **)

val class_prefix = Logic.const_of_class o Sign.base_name;

fun calculate_morphism class cs =
  let
    val subst_typ = Term.map_type_tfree (fn var as (v, sort) =>
      if v = Name.aT then TVar ((v, 0), [class]) else TVar ((v, 0), sort));
    fun subst_aterm (t as Free (v, ty)) = (case AList.lookup (op =) cs v
         of SOME (c, _) => Const (c, ty)
          | NONE => t)
      | subst_aterm t = t;
    val subst_term = map_aterms subst_aterm #> map_types subst_typ;
  in
    Morphism.identity
    $> Morphism.term_morphism subst_term
    $> Morphism.typ_morphism subst_typ
  end;

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
    val inst = (#inst o the_class_data thy) class;
    val tac = ALLGOALS (ProofContext.fact_tac facts);
    val prfx = class_prefix class;
  in
    thy
    |> fold_map (get_remove_global_constraint o fst o snd) params
    ||> prove_interpretation tac ((false, prfx), []) (Locale.Locale class)
          (inst, map (fn def => (("", []), def)) defs)
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

structure ClassSyntax = ProofDataFun(
  type T = {
    constraints: (string * typ) list,
    base_sort: sort,
    local_operation: string * typ -> (typ * term) option,
    rews: (term * term) list,
    passed: bool
  } option;
  fun init _ = NONE;
);

fun synchronize_syntax thy sups base_sort ctxt =
  let
    val operations = these_operations thy sups;

    (* constraints *)
    fun local_constraint (c, ((_, (ty, _)),_ )) =
      let
        val ty' = ty
          |> map_atyps (fn ty as TVar ((v, 0), _) =>
               if v = Name.aT then TVar ((v, 0), base_sort) else ty)
          |> SOME;
      in (c, ty') end
    val constraints = (map o apsnd) (fst o snd o fst) operations;

    (* check phase *)
    val typargs = Consts.typargs (ProofContext.consts_of ctxt);
    fun check_const (c, ty) (((t, _), (_, idx)), _) =
      ((nth (typargs (c, ty)) idx), t);
    fun local_operation (c_ty as (c, _)) = AList.lookup (op =) operations c
      |> Option.map (check_const c_ty);

    (* uncheck phase *)
    val proto_rews = map (fn (c, (((t, ty), _), _)) => (t, Const (c, ty))) operations;
    fun rew_app f (t1 $ t2) = rew_app f t1 $ f t2
      | rew_app f t = t;
    val rews = (map o apfst o rew_app)
      (Pattern.rewrite_term thy proto_rews []) proto_rews;
  in
    ctxt
    |> fold (ProofContext.add_const_constraint o local_constraint) operations
    |> ClassSyntax.map (K (SOME {
        constraints = constraints,
        base_sort = base_sort,
        local_operation = local_operation,
        rews = rews,
        passed = false
      }))
  end;

fun refresh_syntax class ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val base_sort = (#base_sort o the_class_data thy) class;
  in synchronize_syntax thy [class] base_sort ctxt end;

val mark_passed = (ClassSyntax.map o Option.map)
  (fn { constraints, base_sort, local_operation, rews, passed } =>
    { constraints = constraints, base_sort = base_sort,
      local_operation = local_operation, rews = rews, passed = true });

fun sort_term_check ts ctxt =
  let
    val { constraints, base_sort, local_operation, passed, ... } =
      the (ClassSyntax.get ctxt);
    fun check_typ (c, ty) (TFree (v, _), t) = if v = Name.aT
          then apfst (AList.update (op =) ((c, ty), t)) else I
      | check_typ (c, ty) (TVar (vi, _), t) = if TypeInfer.is_param vi
          then apfst (AList.update (op =) ((c, ty), t))
            #> apsnd (insert (op =) vi) else I
      | check_typ _ _ = I;
    fun add_const (Const c_ty) = Option.map (check_typ c_ty) (local_operation c_ty)
          |> the_default I
      | add_const _ = I;
    val (cs, typarams) = (fold o fold_aterms) add_const ts ([], []);
    val subst_typ = map_type_tvar (fn var as (vi, _) =>
      if member (op =) typarams vi then TFree (Name.aT, base_sort) else TVar var);
    val subst_term = map_aterms
        (fn t as Const (c, ty) => the_default t (AList.lookup (op =) cs (c, ty)) | t => t)
          #> map_types subst_typ;
    val ts' = map subst_term ts;
  in if eq_list (op aconv) (ts, ts') andalso passed then NONE
  else
    ctxt
    |> fold (ProofContext.add_const_constraint o apsnd SOME) constraints
    |> mark_passed
    |> pair ts'
    |> SOME
  end;

val uncheck = ref true;

fun sort_term_uncheck ts ctxt =
  let
    (*FIXME abbreviations*)
    val thy = ProofContext.theory_of ctxt;
    val rews = (#rews o the o ClassSyntax.get) ctxt;
    val ts' = if ! uncheck
      then map (Pattern.rewrite_term thy rews []) ts else ts;
  in if eq_list (op aconv) (ts, ts') then NONE else SOME (ts', ctxt) end;

fun init_ctxt thy sups base_sort ctxt =
  ctxt
  |> Variable.declare_term
      (Logic.mk_type (TFree (Name.aT, base_sort)))
  |> synchronize_syntax thy sups base_sort
  |> Context.proof_map (
      Syntax.add_term_check 0 "class" sort_term_check
      #> Syntax.add_term_uncheck (~10) "class" sort_term_uncheck)

fun init class ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
  in
    init_ctxt thy [class] ((#base_sort o the_class_data thy) class) ctxt
  end;


(* class definition *)

local

fun gen_class_spec prep_class prep_expr process_expr thy raw_supclasses raw_includes_elems =
  let
    val supclasses = map (prep_class thy) raw_supclasses;
    val (sups, base_sort) = sups_base_sort thy supclasses;
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
    |> init_ctxt thy sups base_sort
    |> process_expr Locale.empty raw_elems
    |> fst
    |> (fn elems => ((((sups, supconsts), (supsort, base_sort, mergeexpr)),
          (*FIXME*) if null includes then constrain :: elems else elems)))
  end;

val read_class_spec = gen_class_spec Sign.intern_class Locale.intern_expr Locale.read_expr;
val check_class_spec = gen_class_spec (K I) (K I) Locale.cert_expr;

fun define_class_params (name, raw_superclasses) raw_consts raw_dep_axioms other_consts thy =
  let
    val superclasses = map (Sign.certify_class thy) raw_superclasses;
    val consts = (map o apfst o apsnd) (Sign.certify_typ thy) raw_consts;
    fun add_const ((c, ty), syn) =
      Sign.declare_const [] (c, Type.strip_sorts ty, syn) #>> Term.dest_Const;
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
    val (((sups, supconsts), (supsort, base_sort, mergeexpr)), elems_syn) =
      prep_spec thy raw_supclasses raw_includes_elems;
    val other_consts = map (tap (Sign.the_const_type thy) o prep_param thy) raw_other_consts;
    fun mk_inst class param_names cs =
      Symtab.empty
      |> fold2 (fn v => fn (c, ty) => Symtab.update (v, Const
           (c, Term.map_type_tfree (fn (v, _) => TFree (v, [class])) ty))) param_names cs;
    fun fork_syntax (Element.Fixes xs) =
          fold_map (fn (c, ty, syn) => cons (c, syn) #> pair (c, ty, NoSyn)) xs
          #>> Element.Fixes
      | fork_syntax x = pair x;
    val (elems, global_syn) = fold_map fork_syntax elems_syn [];
    fun globalize (c, ty) = 
      ((c, Term.map_type_tfree (K (TFree (Name.aT, base_sort))) ty),
        (the_default NoSyn o AList.lookup (op =) global_syn) c);
    fun extract_params thy =
      let
        val params = map fst (Locale.parameters_of thy class);
      in
        (params, (map globalize o snd o chop (length supconsts)) params)
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
  in
    thy
    |> Locale.add_locale_i (SOME "") bname mergeexpr elems
    |> snd
    |> ProofContext.theory (`extract_params
      #-> (fn (all_params, params) =>
        define_class_params (bname, supsort) params
          (extract_assumes params) other_consts
      #-> (fn (_, (consts, axioms)) =>
        `(fn thy => class_intro thy class sups)
      #-> (fn class_intro =>
        PureThy.note_thmss_qualified "" (NameSpace.append class classN)
          [((introN, []), [([class_intro], [])])]
      #-> (fn [(_, [class_intro])] =>
        add_class_data ((class, sups),
          (map fst params ~~ consts, base_sort,
            mk_inst class (map fst all_params) (map snd supconsts @ consts),
              calculate_morphism class (supconsts @ (map (fst o fst) params ~~ consts)), class_intro))
      #> class_interpretation class axioms []
      )))))
    |> pair class
  end;

in

val class_cmd = gen_class read_class_spec ((#1 o Term.dest_Const) oo Sign.read_const);
val class = gen_class check_class_spec (K I);

end; (*local*)


(* definition in class target *)

fun add_logical_const class pos ((c, mx), dict) thy =
  let
    val prfx = class_prefix class;
    val thy' = thy |> Sign.add_path prfx;
    val phi = morphism thy' class;

    val c' = Sign.full_name thy' c;
    val dict' = (map_types Logic.unvarifyT o Morphism.term phi) dict;
    val ty' = Term.fastype_of dict';
    val ty'' = Type.strip_sorts ty';
    val def_eq = Logic.mk_equals (Const (c', ty'), dict');

    val c'' = NameSpace.full (Sign.naming_of thy' |> NameSpace.add_path prfx) c;
  in
    thy'
    |> Sign.hide_consts_i false [c''] (*FIXME*)
    |> Sign.declare_const pos (c, ty'', mx) |> snd
    |> Sign.parent_path
    |> Sign.sticky_prefix prfx
    |> Thm.add_def false (c, def_eq)
    |>> Thm.symmetric
    |-> (fn def => class_interpretation class [def] [Thm.prop_of def]
          #> register_operation class ((c', (dict, dict')), SOME (Thm.varifyT def)))
    |> Sign.restore_naming thy
    |> Sign.add_const_constraint (c', SOME ty')
    |> pair c'
  end;


(* abbreviation in class target *)

fun expand_aux_abbrev thy class t =
  let
    val rews = map (Logic.dest_equals o Thm.prop_of) (these_defs thy [class]);
    val (head, ts) = strip_comb t;
    val tys = (fst o chop (length ts) o fst o strip_type o Term.fastype_of) head;
    val head' = head
      |> Pattern.eta_long tys
      |> Consts.certify (Sign.pp thy) (Sign.tsig_of thy) true (Sign.consts_of thy);
    val ts' = ts
      |> map (Pattern.rewrite_term thy rews []);
  in Term.betapplys (head', ts') end;

fun add_syntactic_const class prmode pos ((c, mx), dict) thy =
  let
    val prfx = class_prefix class;
    val thy' = thy |> Sign.add_path prfx;
    val phi = morphism thy class;

    val c' = Sign.full_name thy' c;
    val dict' = (expand_aux_abbrev thy' class o Morphism.term phi) dict;
    val dict'' = map_types Logic.unvarifyT dict';
    val ty' = Term.fastype_of dict'';

    val c'' = NameSpace.full (Sign.naming_of thy' |> NameSpace.add_path prfx) c;
    val ty'' = (Type.strip_sorts o Logic.unvarifyT) (Sign.the_const_constraint thy' c'');
  in
    thy'
    |> Sign.add_const_constraint (c'', SOME ty'') (*FIXME*)
    |> Sign.hide_consts_i false [c''] (*FIXME*)
    |> Sign.add_abbrev (#1 prmode) pos (c, map_types Type.strip_sorts dict') |> snd
    |> Sign.add_const_constraint (c', SOME ty')
    |> Sign.notation true prmode [(Const (c', ty'), mx)]
    |> register_operation class ((c', (dict, dict'')), NONE)
    |> Sign.restore_naming thy
    |> pair c'
  end;

end;
