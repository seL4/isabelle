(*  Title:      Pure/Isar/class.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Type classes derived from primitive axclasses and locales.
*)

signature CLASS =
sig
  val fork_mixfix: bool -> string option -> mixfix -> mixfix * mixfix

  val axclass_cmd: bstring * xstring list
    -> ((bstring * Attrib.src list) * string list) list
    -> theory -> class * theory
  val classrel_cmd: xstring * xstring -> theory -> Proof.state
  val class: bstring -> class list -> Element.context_i Locale.element list
    -> string list -> theory -> string * Proof.context
  val class_cmd: bstring -> xstring list -> Element.context Locale.element list
    -> xstring list -> theory -> string * Proof.context
  val add_const_in_class: string -> (string * term) * Syntax.mixfix
    -> theory -> theory
  val interpretation_in_class: class * class -> theory -> Proof.state
  val interpretation_in_class_cmd: xstring * xstring -> theory -> Proof.state
  val prove_interpretation_in_class: tactic -> class * class -> theory -> theory
  val intro_classes_tac: thm list -> tactic
  val default_intro_classes_tac: thm list -> tactic
  val class_of_locale: theory -> string -> class option
  val print_classes: theory -> unit

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
  val params_of_sort: theory -> sort -> (string * (string * typ)) list

  (*experimental*)
  val init_ref: (class -> Proof.context -> (theory -> theory) * Proof.context) ref
  val init: class -> Proof.context -> (theory -> theory) * Proof.context;
  val init_default: class -> Proof.context -> (theory -> theory) * Proof.context;
  val remove_constraints: class -> theory -> (string * typ) list * theory
  val class_term_check: theory -> class -> term list -> Proof.context -> term list * Proof.context
  val local_param: theory -> class -> string -> (term * (class * int)) option
end;

structure Class : CLASS =
struct

(** auxiliary **)

fun fork_mixfix is_loc some_class mx =
  let
    val mx' = Syntax.unlocalize_mixfix mx;
    val mx_global = if is_some some_class orelse (is_loc andalso mx = mx')
      then NoSyn else mx';
    val mx_local = if is_loc then mx else NoSyn;
  in (mx_global, mx_local) end;

fun prove_interpretation tac prfx_atts expr insts =
  Locale.interpretation_i I prfx_atts expr insts
  #> Proof.global_terminal_proof
      (Method.Basic (K (Method.SIMPLE_METHOD tac), Position.none), NONE)
  #> ProofContext.theory_of;

fun prove_interpretation_in tac after_qed (name, expr) =
  Locale.interpretation_in_locale
      (ProofContext.theory after_qed) (name, expr)
  #> Proof.global_terminal_proof
      (Method.Basic (K (Method.SIMPLE_METHOD tac), Position.none), NONE)
  #> ProofContext.theory_of;

fun OF_LAST thm1 thm2 =
  let
    val n = (length o Logic.strip_imp_prems o prop_of) thm2;
  in (thm1 RSN (n, thm2)) end;

fun strip_all_ofclass thy sort =
  let
    val typ = TVar ((AxClass.param_tyvarname, 0), sort);
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

fun get_remove_contraint c thy =
  let
    val ty = Sign.the_const_constraint thy c;
  in
    thy
    |> Sign.add_const_constraint_i (c, NONE)
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

fun inst_thms f thy = (Symtab.fold (Symtab.fold (cons o f o snd o snd) o snd) o fst)
    (InstData.get thy) [];
fun add_inst (c, tyco) inst = (InstData.map o apfst
      o Symtab.map_default (c, Symtab.empty)) (Symtab.update_new (tyco, inst))
  #> (InstData.map o apsnd) (Symtab.update_new (fst inst, (c, tyco)));

fun unoverload thy = MetaSimplifier.rewrite false (inst_thms I thy);
fun overload thy = MetaSimplifier.rewrite false (inst_thms symmetric thy);

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
    val tyco_base = NameSpace.base tyco;
    val name_inst = NameSpace.base class ^ "_" ^ tyco_base ^ "_inst";
    val c_inst_base = NameSpace.base c ^ "_" ^ tyco_base;
  in
    thy
    |> Sign.sticky_prefix name_inst
    |> PureThy.simple_def ("", [])
         (((c_inst_base, ty, Syntax.NoSyn), []), Const (c, ty))
    |-> (fn (c_inst, thm) => add_inst (c, tyco) (c_inst, symmetric thm))
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
    |> PureThy.add_defs_i true [((name, prop), map (Attrib.attribute thy) atts)]
    |-> (fn [def] => add_inst' def (args, rhs) #> pair def)
  end;


(** instances with implicit parameter handling **)

local

fun gen_read_def thy prep_att read_def ((raw_name, raw_atts), raw_t) =
  let
    val (_, t) = read_def thy (raw_name, raw_t);
    val ((c, ty), _) = Sign.cert_def (Sign.pp thy) t;
    val atts = map (prep_att thy) raw_atts;
    val insts = Consts.typargs (Sign.consts_of thy) (c, ty);
    val name = case raw_name
     of "" => NONE
      | _ => SOME raw_name;
  in (c, (insts, ((name, t), atts))) end;

fun read_def_cmd thy = gen_read_def thy Attrib.intern_src Theory.read_axm;
fun read_def thy = gen_read_def thy (K I) (K I);

fun gen_instance prep_arity read_def do_proof raw_arities raw_defs after_qed theory =
  let
    val arities = map (prep_arity theory) raw_arities;
    val _ = if null arities then error "at least one arity must be given" else ();
    val _ = case (duplicates (op =) o map #1) arities
     of [] => ()
      | dupl_tycos => error ("type constructors occur more than once in arities: "
          ^ (commas o map quote) dupl_tycos);
    val super_sort =
      (Graph.all_succs o #classes o Sorts.rep_algebra o Sign.classes_of) theory;
    fun get_consts_class tyco ty class =
      let
        val cs = (these o Option.map snd o try (AxClass.params_of_class theory)) class;
        val subst_ty = map_type_tfree (K ty);
      in
        map (fn (c, ty) => (c, ((class, tyco), subst_ty ty))) cs
      end;
    fun get_consts_sort (tyco, asorts, sort) =
      let
        val ty = Type (tyco, map (fn (v, sort) => TVar ((v, 0), sort))
          (Name.names Name.context "'a" asorts))
      in maps (get_consts_class tyco ty) (super_sort sort) end;
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
             of NONE => error ("illegal definition for constant " ^ quote c)
              | SOME class_ty => class_ty;
            val name = case name_opt
             of NONE => Thm.def_name (Logic.name_arity (tyco, [], c))
              | SOME name => name;
            val t' = case mk_typnorm thy_read (ty', ty)
             of NONE => error ("illegal definition for constant " ^
                  quote (c ^ "::" ^ setmp show_sorts true
                    (Sign.string_of_typ thy_read) ty))
              | SOME norm => map_types norm t
          in (((class, tyco), ((name, t'), atts)), AList.delete (op =) c cs) end;
      in fold_map read defs cs end;
    val (defs, other_cs) = read_defs raw_defs cs
      (fold Sign.primitive_arity arities (Theory.copy theory));
    fun after_qed' cs defs =
      fold Sign.add_const_constraint_i (map (apsnd SOME) cs)
      #> after_qed defs;
  in
    theory
    |> fold_map get_remove_contraint (map fst cs |> distinct (op =))
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
  locale: string,
  consts: (string * string) list
    (*locale parameter ~> theory constant name*),
  v: string,
  inst: typ Symtab.table * term Symtab.table
    (*canonical interpretation*),
  intro: thm,
  defs: thm list,
  localized: (string * (term * (class * int))) list
    (*theory constant name ~> (locale parameter, (class, instantiaton index of class typ))*)
};

fun rep_class_data (ClassData d) = d;
fun mk_class_data ((locale, consts, v, inst, intro), (defs, localized)) =
  ClassData { locale = locale, consts = consts, v = v, inst = inst, intro = intro,
    defs = defs, localized = localized };
fun map_class_data f (ClassData { locale, consts, v, inst, intro, defs, localized }) =
  mk_class_data (f ((locale, consts, v, inst, intro), (defs, localized)))
fun merge_class_data _ (ClassData { locale = locale, consts = consts, v = v, inst = inst,
    intro = intro, defs = defs1, localized = localized1 },
  ClassData { locale = _, consts = _, v = _, inst = _, intro = _,
    defs = defs2, localized = localized2 }) =
  mk_class_data ((locale, consts, v, inst, intro),
    (Thm.merge_thms (defs1, defs2), AList.merge (op =) (K true) (localized1, localized2)));

fun merge_pair f1 f2 ((x1, y1), (x2, y2)) = (f1 (x1, x2), f2 (y1, y2));

structure ClassData = TheoryDataFun
(
  type T = class_data Graph.T * class Symtab.table
    (*locale name ~> class name*);
  val empty = (Graph.empty, Symtab.empty);
  val copy = I;
  val extend = I;
  fun merge _ = merge_pair (Graph.join merge_class_data) (Symtab.merge (K true));
);


(* queries *)

val lookup_class_data = Option.map rep_class_data oo try o Graph.get_node
  o fst o ClassData.get;
fun class_of_locale thy = Symtab.lookup ((snd o ClassData.get) thy);

fun the_class_data thy class = case lookup_class_data thy class
 of NONE => error ("undeclared class " ^ quote class)
  | SOME data => data;

val ancestry = Graph.all_succs o fst o ClassData.get;

fun params_of_sort thy =
  let
    fun params class =
      let
        val const_typs = (#params o AxClass.get_definition thy) class;
        val const_names = (#consts o the_class_data thy) class;
      in
        (map o apsnd) (fn c => (c, (the o AList.lookup (op =) const_typs) c)) const_names
      end;
  in maps params o ancestry thy end;

fun these_defs thy = maps (these o Option.map #defs o lookup_class_data thy) o ancestry thy;

fun these_intros thy =
  Graph.fold (fn (_, (data, _)) => insert Thm.eq_thm ((#intro o rep_class_data) data))
    ((fst o ClassData.get) thy) [];

fun these_localized thy class =
  maps (#localized o the_class_data thy) (ancestry thy [class]);

fun local_param thy = AList.lookup (op =) o these_localized thy;

fun print_classes thy =
  let
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
      in Sign.pretty_arity thy (tyco, Ss, [class]) end;
    fun mk_param (c, ty) = Pretty.str (Sign.extern_const thy c ^ " :: "
      ^ setmp show_sorts false (Sign.string_of_typ thy o Type.strip_sorts) ty);
    fun mk_entry class = (Pretty.block o Pretty.fbreaks o map_filter I) [
      (SOME o Pretty.str) ("class " ^ class ^ ":"),
      (SOME o Pretty.block) [Pretty.str "supersort: ",
        (Sign.pretty_sort thy o Sign.certify_sort thy o Sign.super_classes thy) class],
      Option.map (Pretty.str o prefix "locale: " o #locale) (lookup_class_data thy class),
      ((fn [] => NONE | ps => (SOME o Pretty.block o Pretty.fbreaks) (Pretty.str "parameters:" :: ps)) o map mk_param
        o these o Option.map #params o try (AxClass.get_definition thy)) class,
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

fun add_class_data ((class, superclasses), (locale, consts, v, inst, intro)) =
  ClassData.map (fn (gr, tab) => (
    gr
    |> Graph.new_node (class, mk_class_data ((locale, (map o apfst) fst consts, v, inst, intro),
         ([], map (apsnd (rpair (class, 0) o Free) o swap) consts)))
    |> fold (curry Graph.add_edge class) superclasses,
    tab
    |> Symtab.update (locale, class)
  ));

fun add_class_const_def (class, (entry, def)) =
  (ClassData.map o apfst o Graph.map_node class o map_class_data o apsnd)
    (fn (defs, localized) => (def :: defs, (apsnd o apsnd) (pair class) entry :: localized));


(** rule calculation, tactics and methods **)

fun class_intro thy locale class sups =
  let
    fun class_elim class =
      case (map Drule.unconstrainTs o #axioms o AxClass.get_definition thy) class
       of [thm] => SOME thm
        | [] => NONE;
    val pred_intro = case Locale.intros thy locale
     of ([ax_intro], [intro]) => intro |> OF_LAST ax_intro |> SOME
      | ([intro], []) => SOME intro
      | ([], [intro]) => SOME intro
      | _ => NONE;
    val pred_intro' = pred_intro
      |> Option.map (fn intro => intro OF map_filter class_elim sups);
    val class_intro = (#intro o AxClass.get_definition thy) class;
    val raw_intro = case pred_intro'
     of SOME pred_intro => class_intro |> OF_LAST pred_intro
      | NONE => class_intro;
    val sort = Sign.super_classes thy class;
    val typ = TVar ((AxClass.param_tyvarname, 0), sort);
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
    val { locale, inst, ... } = the_class_data thy class;
    val tac = (ALLGOALS o ProofContext.fact_tac) facts;
    val prfx = Logic.const_of_class (NameSpace.base class);
  in
    prove_interpretation tac ((false, prfx), []) (Locale.Locale locale)
      (inst, defs) thy
  end;

fun interpretation_in_rule thy (class1, class2) =
  let
    fun mk_axioms class =
      let
        val { locale, inst = (_, insttab), ... } = the_class_data thy class;
      in
        Locale.global_asms_of thy locale
        |> maps snd
        |> (map o map_aterms) (fn Free (s, _) => (the o Symtab.lookup insttab) s | t => t)
        |> (map o map_types o map_atyps) (fn TFree _ => TFree ("'a", [class1]) | T => T)
        |> map (ObjectLogic.ensure_propT thy)
      end;
    val (prems, concls) = pairself mk_axioms (class1, class2);
  in
    Goal.prove_global thy [] prems (Logic.mk_conjunction_list concls)
      (Locale.intro_locales_tac true (ProofContext.init thy))
  end;

fun intro_classes_tac facts st =
  let
    val thy = Thm.theory_of_thm st;
    val classes = Sign.all_classes thy;
    val class_trivs = map (Thm.class_triv thy) classes;
    val class_intros = these_intros thy;
    fun add_axclass_intro class =
      case try (AxClass.get_definition thy) class of SOME {intro, ...} => cons intro | _ => I;
    val axclass_intros = fold add_axclass_intro classes [];
  in
    st
    |> ((ALLGOALS (Method.insert_tac facts THEN'
          REPEAT_ALL_NEW (resolve_tac (class_trivs @ class_intros @ axclass_intros))))
            THEN Tactic.distinct_subgoals_tac)
  end;

fun default_intro_classes_tac [] = intro_classes_tac []
  | default_intro_classes_tac _ = Tactical.no_tac;    (*no error message!*)

fun default_tac rules ctxt facts =
  HEADGOAL (Method.some_rule_tac rules ctxt facts) ORELSE
    default_intro_classes_tac facts;

val _ = Context.add_setup (Method.add_methods
 [("intro_classes", Method.no_args (Method.METHOD intro_classes_tac),
    "back-chain introduction rules of classes"),
  ("default", Method.thms_ctxt_args (Method.METHOD oo default_tac),
    "apply some intro/elim rule")]);


(** classes and class target **)

(* class definition *)

local

fun read_param thy raw_t =
  let
    val t = Sign.read_term thy raw_t
  in case try dest_Const t
   of SOME (c, _) => c
    | NONE => error ("Not a constant: " ^ Sign.string_of_term thy t)
  end;

fun gen_class add_locale prep_class prep_param bname
    raw_supclasses raw_elems raw_other_consts thy =
  let
    fun mk_instT class = Symtab.empty
      |> Symtab.update (AxClass.param_tyvarname, TFree (AxClass.param_tyvarname, [class]));
    fun mk_inst class param_names cs =
      Symtab.empty
      |> fold2 (fn v => fn (c, ty) => Symtab.update (v, Const
           (c, Term.map_type_tfree (fn (v, _) => TFree (v, [class])) ty))) param_names cs;
    (*FIXME need proper concept for reading locale statements*)
    fun subst_classtyvar (_, _) =
          TFree (AxClass.param_tyvarname, [])
      | subst_classtyvar (v, sort) =
          error ("Sort constraint illegal in type class, for type variable "
            ^ v ^ "::" ^ Sign.string_of_sort thy sort);
    (*val subst_classtyvars = Element.map_ctxt {name = I, var = I, term = I,
      typ = Term.map_type_tfree subst_classtyvar, fact = I, attrib = I};*)
    val other_consts = map (prep_param thy) raw_other_consts;
    val (elems, includes) = fold_rev (fn Locale.Elem e => apfst (cons e)
      | Locale.Expr i => apsnd (cons i)) raw_elems ([], []);
    val supclasses = map (prep_class thy) raw_supclasses;
    val sups = filter (is_some o lookup_class_data thy) supclasses
      |> Sign.certify_sort thy;
    val supsort = Sign.certify_sort thy supclasses;
    val suplocales = map (Locale.Locale o #locale o the_class_data thy) sups;
    val supexpr = Locale.Merge (suplocales @ includes);
    val supparams = (map fst o Locale.parameters_of_expr thy)
      (Locale.Merge suplocales);
    val supconsts = AList.make (the o AList.lookup (op =) (params_of_sort thy sups))
      (map fst supparams);
    (*val elems_constrains = map
      (Element.Constrains o apsnd (Term.map_type_tfree subst_classtyvar)) supparams;*)
    fun mk_tyvar (_, sort) = TFree (AxClass.param_tyvarname,
      if Sign.subsort thy (supsort, sort) then sort else error
        ("Sort " ^ Sign.string_of_sort thy sort
          ^ " is less general than permitted least general sort "
          ^ Sign.string_of_sort thy supsort));
    fun extract_params thy name_locale =
      let
        val params = Locale.parameters_of thy name_locale;
        val v = case (maps typ_tfrees o map (snd o fst)) params
         of (v, _) :: _ => v
          | [] => AxClass.param_tyvarname;
      in
        (v, (map fst params, params
        |> (map o apfst o apsnd o Term.map_type_tfree) mk_tyvar
        |> (map o apsnd) (fork_mixfix true NONE #> fst)
        |> chop (length supconsts)
        |> snd))
      end;
    fun extract_assumes name_locale params thy cs =
      let
        val consts = supconsts @ (map (fst o fst) params ~~ cs);
        fun subst (Free (c, ty)) =
              Const ((fst o the o AList.lookup (op =) consts) c, ty)
          | subst t = t;
        fun prep_asm ((name, atts), ts) =
          ((NameSpace.base name, map (Attrib.attribute thy) atts),
            (map o map_aterms) subst ts);
      in
        Locale.global_asms_of thy name_locale
        |> map prep_asm
      end;
    fun note_intro name_axclass class_intro =
      PureThy.note_thmss_qualified "" ((Logic.const_of_class o NameSpace.base) name_axclass)
        [(("intro", []), [([class_intro], [])])]
      #> snd
  in
    thy
    |> add_locale (SOME "") bname supexpr ((*elems_constrains @*) elems)
    |-> (fn name_locale => ProofContext.theory_result (
      `(fn thy => extract_params thy name_locale)
      #-> (fn (v, (globals, params)) =>
        AxClass.define_class_params (bname, supsort) params
          (extract_assumes name_locale params) other_consts
      #-> (fn (name_axclass, (consts, axioms)) =>
        `(fn thy => class_intro thy name_locale name_axclass sups)
      #-> (fn class_intro =>
        add_class_data ((name_axclass, sups),
          (name_locale, map fst params ~~ map fst consts, v,
            (mk_instT name_axclass, mk_inst name_axclass (map fst globals)
              (map snd supconsts @ consts)), class_intro))
      #> note_intro name_axclass class_intro
      #> class_interpretation name_axclass axioms []
      #> pair name_axclass
      )))))
  end;

in

val class_cmd = gen_class Locale.add_locale Sign.intern_class read_param;
val class = gen_class Locale.add_locale_i Sign.certify_class (K I);

end; (*local*)


(* class target context *)

fun remove_constraints class thy =
  thy |> fold_map (get_remove_contraint o fst) (these_localized thy class);


(* definition in class target *)

fun export_fixes thy class =
  let
    val consts = params_of_sort thy [class];
    fun subst_aterm (t as Free (v, ty)) = (case AList.lookup (op =) consts v
         of SOME (c, _) => Const (c, ty)
          | NONE => t)
      | subst_aterm t = t;
  in Term.map_aterms subst_aterm end;

fun add_const_in_class class ((c, rhs), syn) thy =
  let
    val prfx = (Logic.const_of_class o NameSpace.base) class;
    fun mk_name c =
      let
        val n1 = Sign.full_name thy c;
        val n2 = NameSpace.qualifier n1;
        val n3 = NameSpace.base n1;
      in NameSpace.implode [n2, prfx, n3] end;
    val v = (#v o the_class_data thy) class;
    val constrain_sort = curry (Sorts.inter_sort (Sign.classes_of thy)) [class];
    val subst_typ = Term.map_type_tfree (fn var as (w, sort) =>
      if w = v then TFree (w, constrain_sort sort) else TFree var);
    val rhs' = export_fixes thy class rhs;
    val ty' = Term.fastype_of rhs';
    val ty'' = subst_typ ty';
    val c' = mk_name c;
    val def = (c, Logic.mk_equals (Const (c', ty'), rhs'));
    val (syn', _) = fork_mixfix true NONE syn;
    fun interpret def thy =
      let
        val def' = symmetric def;
        val def_eq = Thm.prop_of def';
        val typargs = Sign.const_typargs thy (c', fastype_of rhs);
        val typidx = find_index (fn TFree (w, _) => v = w | _ => false) typargs;
      in
        thy
        |> class_interpretation class [def'] [def_eq]
        |> add_class_const_def (class, ((c', (rhs, typidx)), def'))
      end;
  in
    thy
    |> Sign.add_path prfx
    |> Sign.add_consts_authentic [(c, ty', syn')]
    |> Sign.parent_path
    |> Sign.sticky_prefix prfx
    |> PureThy.add_defs_i false [(def, [])]
    |-> (fn [def] => interpret def)
    |> Sign.add_const_constraint_i (c', SOME ty'')
    |> Sign.restore_naming thy
  end;


(* interpretation in class target *)

local

fun gen_interpretation_in_class prep_class do_proof (raw_class, raw_superclass) theory =
  let
    val class = prep_class theory raw_class;
    val superclass = prep_class theory raw_superclass;
    val loc_name = (#locale o the_class_data theory) class;
    val loc_expr = (Locale.Locale o #locale o the_class_data theory) superclass;
    fun prove_classrel (class, superclass) thy =
      let
        val classes = (Graph.all_succs o #classes o Sorts.rep_algebra
              o Sign.classes_of) thy [superclass]
          |> filter_out (fn class' => Sign.subsort thy ([class], [class']));
        fun instance_subclass (class1, class2) thy  =
          let
            val interp = interpretation_in_rule thy (class1, class2);
            val ax = #axioms (AxClass.get_definition thy class1);
            val intro = #intro (AxClass.get_definition thy class2)
              |> Drule.instantiate' [SOME (Thm.ctyp_of thy
                  (TVar ((AxClass.param_tyvarname, 0), [class1])))] [];
            val thm = 
              intro
              |> OF_LAST (interp OF ax)
              |> strip_all_ofclass thy (Sign.super_classes thy class2);
          in
            thy |> AxClass.add_classrel thm
          end;
      in
        thy |> fold_rev (curry instance_subclass class) classes
      end;
  in
    theory
    |> do_proof (prove_classrel (class, superclass)) (loc_name, loc_expr)
  end;

in

val interpretation_in_class = gen_interpretation_in_class Sign.certify_class
  (Locale.interpretation_in_locale o ProofContext.theory);
val interpretation_in_class_cmd = gen_interpretation_in_class Sign.read_class
  (Locale.interpretation_in_locale o ProofContext.theory);
val prove_interpretation_in_class = gen_interpretation_in_class Sign.certify_class
  o prove_interpretation_in;

end; (*local*)

(*experimental*)
fun class_term_check thy class =
  let
    val algebra = Sign.classes_of thy;
    val { v, ... } = the_class_data thy class;
    fun add_constrain_classtyp sort' (ty as TFree (v, _)) =
          AList.map_default (op =) (v, []) (curry (Sorts.inter_sort algebra) sort')
      | add_constrain_classtyp sort' (Type (tyco, tys)) = case Sorts.mg_domain algebra tyco sort'
         of sorts => fold2 add_constrain_classtyp sorts tys;
    fun class_arg c idx ty =
      let
        val typargs = Sign.const_typargs thy (c, ty);
        fun classtyp (t as TFree (w, _)) = if w = v then NONE else SOME t
          | classtyp t = SOME t;
      in classtyp (nth typargs idx) end;
    fun add_inst (c, ty) (terminsts, typinsts) = case local_param thy class c
     of NONE => (terminsts, typinsts)
      | SOME (t, (class', idx)) => (case class_arg c idx ty
         of NONE => (((c, ty), t) :: terminsts, typinsts)
          | SOME ty => (terminsts, add_constrain_classtyp [class'] ty typinsts));
  in pair o (fn ts => let
    val cs = (fold o fold_aterms) (fn Const c_ty => insert (op =) c_ty | _ => I) ts [];
    val (terminsts, typinsts) = fold add_inst cs ([], []);
  in
    ts
    |> (map o map_aterms) (fn t as Const c_ty => the_default t (AList.lookup (op =) terminsts c_ty)
         | t => t)
    |> (map o map_types o map_atyps) (fn t as TFree (v, sort) =>
         case AList.lookup (op =) typinsts v
          of SOME sort' => TFree (v, Sorts.inter_sort algebra (sort, sort'))
           | NONE => t)
  end) end;

val init_ref = ref (K (pair I) : class -> Proof.context -> (theory -> theory) * Proof.context);
fun init class = ! init_ref class;

fun init_default class ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val term_check = class_term_check thy class;
  in
    ctxt
    (*|> ProofContext.theory_result (remove_constraints class)*)
    |> Context.proof_map (Syntax.add_term_check term_check)
    (*|>> fold (fn (c, ty) => Sign.add_const_constraint_i (c, SOME ty))*)
    |> pair I
  end;

end;
