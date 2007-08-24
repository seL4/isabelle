(*  Title:      Pure/Isar/class.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Type classes derived from primitive axclasses and locales.
*)

signature CLASS =
sig
  val fork_mixfix: bool -> string option -> mixfix -> mixfix * mixfix

  val axclass_cmd: bstring * xstring list
    -> ((bstring * Attrib.src list) * string list) list -> theory -> class * theory
  val class: bstring -> class list -> Element.context_i Locale.element list
    -> string list -> theory -> string * Proof.context
  val class_cmd: bstring -> string list -> Element.context Locale.element list
    -> string list -> theory -> string * Proof.context
  val class_of_locale: theory -> string -> class option
  val add_const_in_class: string -> (string * term) * Syntax.mixfix
    -> theory -> theory

  val instance_arity: arity list -> ((bstring * Attrib.src list) * term) list
    -> (thm list -> theory -> theory)
    -> theory -> Proof.state
  val instance_arity_cmd: (bstring * string list * string) list
    -> ((bstring * Attrib.src list) * string) list
    -> (thm list -> theory -> theory)
    -> theory -> Proof.state
  val prove_instance_arity: tactic -> arity list
    -> ((bstring * Attrib.src list) * term) list
    -> theory -> thm list * theory
  val unoverload: theory -> conv
  val overload: theory -> conv
  val unoverload_const: theory -> string * typ -> string
  val inst_const: theory -> string * string -> string
  val param_const: theory -> string -> (string * string) option
  val intro_classes_tac: thm list -> tactic
  val default_intro_classes_tac: thm list -> tactic

  val instance_class: class * class -> theory -> Proof.state
  val instance_class_cmd: string * string -> theory -> Proof.state
  val instance_sort: class * sort -> theory -> Proof.state
  val instance_sort_cmd: string * string -> theory -> Proof.state
  val prove_instance_sort: tactic -> class * sort -> theory -> theory

  val print_classes: theory -> unit
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

fun axclass_cmd (class, raw_superclasses) raw_specs thy =
  let
    val ctxt = ProofContext.init thy;
    val superclasses = map (Sign.read_class thy) raw_superclasses;
    val name_atts = map ((apsnd o map) (Attrib.attribute thy) o fst) raw_specs;
    val axiomss = ProofContext.read_propp (ctxt, map (map (rpair []) o snd) raw_specs)
      |> snd
      |> (map o map) fst;
  in AxClass.define_class (class, superclasses) [] (name_atts ~~ axiomss) thy end;


(** axclasses with implicit parameter handling **)

(* axclass instances *)

local

fun gen_instance mk_prop add_thm after_qed insts thy =
  let
    fun after_qed' results =
      ProofContext.theory ((fold o fold) add_thm results #> after_qed);
  in
    thy
    |> ProofContext.init
    |> Proof.theorem_i NONE after_qed' ((map (fn t => [(t, [])]) o maps (mk_prop thy)) insts)
  end;

in

val axclass_instance_arity =
  gen_instance (Logic.mk_arities oo Sign.cert_arity) AxClass.add_arity;
val axclass_instance_sort =
  gen_instance (single oo (Logic.mk_classrel oo AxClass.cert_classrel))
    AxClass.add_classrel I o single;

end; (*local*)


(* introducing axclasses with implicit parameter handling *)

fun axclass_params (name, raw_superclasses) raw_consts raw_dep_axioms other_consts thy =
  let
    val superclasses = map (Sign.certify_class thy) raw_superclasses;
    val consts = (map o apfst o apsnd) (Sign.certify_typ thy) raw_consts;
    val prefix = Logic.const_of_class name;
    fun mk_const_name c = NameSpace.map_base (NameSpace.append prefix)
      (Sign.full_name thy c);
    fun add_const ((c, ty), syn) =
      Sign.add_consts_authentic [(c, ty, syn)]
      #> pair (mk_const_name c, ty);
    fun mk_axioms cs thy =
      raw_dep_axioms thy cs
      |> (map o apsnd o map) (Sign.cert_prop thy)
      |> rpair thy;
    fun add_constraint class (c, ty) =
      Sign.add_const_constraint_i (c, SOME
        (Term.map_type_tfree (fn (v, _) => TFree (v, [class])) ty));
  in
    thy
    |> Theory.add_path prefix
    |> fold_map add_const consts
    ||> Theory.restore_naming thy
    |-> (fn cs => mk_axioms cs
    #-> (fn axioms_prop => AxClass.define_class (name, superclasses)
           (map fst cs @ other_consts) axioms_prop
    #-> (fn class => `(fn thy => AxClass.get_definition thy class)
    #-> (fn {intro, axioms, ...} => fold (add_constraint class) cs
    #> pair (class, ((intro, (map Thm.prop_of axioms, axioms)), cs))))))
  end;


(* explicit constants for overloaded definitions *)

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

fun inst_thms f thy =
  (Symtab.fold (Symtab.fold (cons o f o snd o snd) o snd) o fst) (InstData.get thy) [];
fun add_inst (c, tyco) inst = (InstData.map o apfst o Symtab.map_default (c, Symtab.empty))
  (Symtab.update_new (tyco, inst))
  #> (InstData.map o apsnd) (Symtab.update_new (fst inst, (c, tyco)));

fun unoverload thy thm = MetaSimplifier.rewrite false (inst_thms I thy) thm;
fun overload thy thm = MetaSimplifier.rewrite false (inst_thms symmetric thy) thm;

fun inst_const thy (c, tyco) =
  (fst o the o Symtab.lookup ((the o Symtab.lookup (fst (InstData.get thy))) c)) tyco;
fun unoverload_const thy (c_ty as (c, _)) =
  case AxClass.class_of_param thy c
   of SOME class => (case Sign.const_typargs thy c_ty
       of [Type (tyco, _)] =>
            (case Symtab.lookup ((the o Symtab.lookup (fst (InstData.get thy))) c) tyco
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
    |> Sign.add_consts_i [(c_inst_base, ty, Syntax.NoSyn)]
    |> `(fn thy => Sign.full_name thy c_inst_base)
    |-> (fn c_inst => PureThy.add_defs_i true
          [((Thm.def_name c_inst_base, Logic.mk_equals (Const (c_inst, ty), Const (c, ty))), [])]
    #-> (fn [def] => add_inst (c, tyco) (c_inst, symmetric def))
    #> Sign.restore_naming thy)
  end;

fun add_inst_def' (class, tyco) (c, ty) thy =
  if case Symtab.lookup (fst (InstData.get thy)) c
   of NONE => true
    | SOME tab => is_none (Symtab.lookup tab tyco)
  then add_inst_def (class, tyco) (c, Logic.unvarifyT ty) thy
  else thy;

fun add_def ((class, tyco), ((name, prop), atts)) thy =
  let
    val ((lhs as Const (c, ty), args), rhs) = (apfst Term.strip_comb o Logic.dest_equals) prop;
    fun add_inst' def ([], (Const (c_inst, ty))) =
          if forall (fn TFree _ => true | _ => false) (Sign.const_typargs thy (c_inst, ty))
          then add_inst (c, tyco) (c_inst, def)
          else add_inst_def (class, tyco) (c, ty)
      | add_inst' _ t = add_inst_def (class, tyco) (c, ty);
  in
    thy
    |> PureThy.add_defs_i true [((name, prop), map (Attrib.attribute thy) atts)]
    |-> (fn [def] => add_inst' def (args, rhs) #> pair def)
  end;


(* instances with implicit parameter handling *)

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

fun gen_instance_arity prep_arity read_def do_proof raw_arities raw_defs after_qed theory =
  let
    val arities = map (prep_arity theory) raw_arities;
    val _ = if null arities then error "at least one arity must be given" else ();
    val _ = case (duplicates (op =) o map #1) arities
     of [] => ()
      | dupl_tycos => error ("type constructors occur more than once in arities: "
          ^ (commas o map quote) dupl_tycos);
    val super_sort = (Graph.all_succs o #classes o Sorts.rep_algebra o Sign.classes_of) theory
    fun get_consts_class tyco ty class =
      let
        val cs = (these o Option.map snd o try (AxClass.params_of_class theory)) class;
        val subst_ty = map_type_tfree (K ty);
      in
        map (fn (c, ty) => (c, ((class, tyco), subst_ty ty))) cs
      end;
    fun get_consts_sort (tyco, asorts, sort) =
      let
        val ty = Type (tyco, map (fn (v, sort) => TVar ((v, 0), sort)) (Name.names Name.context "'a" asorts))
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
    fun get_remove_contraint c thy =
      let
        val ty = Sign.the_const_constraint thy c;
      in
        thy
        |> Sign.add_const_constraint_i (c, NONE)
        |> pair (c, Logic.unvarifyT ty)
      end;
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

fun instance_arity_cmd' do_proof = gen_instance_arity Sign.read_arity read_def_cmd do_proof;
fun instance_arity' do_proof = gen_instance_arity Sign.cert_arity read_def do_proof;
fun tactic_proof tac f arities defs =
  fold (fn arity => AxClass.prove_arity arity tac) arities
  #> f
  #> pair defs;

in

val instance_arity_cmd = instance_arity_cmd'
  (fn f => fn arities => fn defs => axclass_instance_arity f arities);
val instance_arity = instance_arity'
  (fn f => fn arities => fn defs => axclass_instance_arity f arities);
fun prove_instance_arity tac arities defs =
  instance_arity' (tactic_proof tac) arities defs (K I);

end; (*local*)



(** combining locales and axclasses **)

(* theory data *)

datatype class_data = ClassData of {
  locale: string,
  consts: (string * string) list
    (*locale parameter ~> toplevel theory constant*),
  v: string option,
  intro: thm
} * thm list (*derived defs*);

fun rep_classdata (ClassData c) = c;

fun merge_pair f1 f2 ((x1, y1), (x2, y2)) = (f1 (x1, x2), f2 (y1, y2));

structure ClassData = TheoryDataFun
(
  type T = class_data Graph.T * class Symtab.table (*locale name ~> class name*);
  val empty = (Graph.empty, Symtab.empty);
  val copy = I;
  val extend = I;
  fun merge _ = merge_pair (Graph.merge (K true)) (Symtab.merge (K true));
);


(* queries *)

val lookup_class_data = Option.map rep_classdata oo try o Graph.get_node o fst o ClassData.get;
fun class_of_locale thy = Symtab.lookup ((snd o ClassData.get) thy);

fun the_class_data thy class =
  case lookup_class_data thy class
    of NONE => error ("undeclared class " ^ quote class)
     | SOME data => data;

val ancestry = Graph.all_succs o fst o ClassData.get;

fun param_map thy =
  let
    fun params class =
      let
        val const_typs = (#params o AxClass.get_definition thy) class;
        val const_names = (#consts o fst o the_class_data thy) class;
      in
        (map o apsnd) (fn c => (c, (the o AList.lookup (op =) const_typs) c)) const_names
      end;
  in maps params o ancestry thy end;

fun these_defs thy = maps (these o Option.map snd o lookup_class_data thy) o ancestry thy;

fun these_intros thy =
  Graph.fold (fn (_, (data, _)) => insert Thm.eq_thm ((#intro o fst o rep_classdata) data))
    ((fst o ClassData.get) thy) [];

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
      Option.map (Pretty.str o prefix "locale: " o #locale o fst) (lookup_class_data thy class),
      ((fn [] => NONE | ps => (SOME o Pretty.block o Pretty.fbreaks) (Pretty.str "parameters:" :: ps)) o map mk_param
        o these o Option.map #params o try (AxClass.get_definition thy)) class,
      (SOME o Pretty.block o Pretty.breaks) [
        Pretty.str "instances:",
        Pretty.list "" "" (map (mk_arity class) (the_arities class))
      ]
    ]
  in
    (Pretty.writeln o Pretty.chunks o separate (Pretty.str "") o map mk_entry o Sorts.all_classes)
      algebra
  end;


(* updaters *)

fun add_class_data ((class, superclasses), (locale, consts, v, intro)) =
  ClassData.map (fn (gr, tab) => (
    gr
    |> Graph.new_node (class, ClassData ({ locale = locale, consts = consts,
         v = v, intro = intro }, []))
    |> fold (curry Graph.add_edge class) superclasses,
    tab
    |> Symtab.update (locale, class)
  ));

fun add_class_const_thm (class, thm) = (ClassData.map o apfst o Graph.map_node class)
  (fn ClassData (data, thms) => ClassData (data, thm :: thms));

(* tactics and methods *)

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


(* tactical interfaces to locale commands *)

fun prove_interpretation tac prfx_atts expr insts thy =
  thy
  |> Locale.interpretation_i I prfx_atts expr insts
  |> Proof.global_terminal_proof (Method.Basic (K (Method.SIMPLE_METHOD tac), Position.none), NONE)
  |> ProofContext.theory_of;

fun prove_interpretation_in tac after_qed (name, expr) thy =
  thy
  |> Locale.interpretation_in_locale (ProofContext.theory after_qed) (name, expr)
  |> Proof.global_terminal_proof (Method.Basic (K (Method.SIMPLE_METHOD tac), Position.none), NONE)
  |> ProofContext.theory_of;


(* constructing class introduction and other rules from axclass and locale rules *)

fun mk_instT class = Symtab.empty
  |> Symtab.update (AxClass.param_tyvarname, TFree (AxClass.param_tyvarname, [class]));

fun mk_inst class param_names cs =
  Symtab.empty
  |> fold2 (fn v => fn (c, ty) => Symtab.update (v, Const
       (c, Term.map_type_tfree (fn (v, _) => TFree (v, [class])) ty))) param_names cs;

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

fun interpretation_in_rule thy (class1, class2) =
  let
    val (params, consts) = split_list (param_map thy [class1]);
    (*FIXME also remember this at add_class*)
    fun mk_axioms class =
      let
        val name_locale = (#locale o fst o the_class_data thy) class;
        val inst = mk_inst class params consts;
      in
        Locale.global_asms_of thy name_locale
        |> maps snd
        |> (map o map_aterms) (fn Free (s, _) => (the o Symtab.lookup inst) s | t => t)
        |> (map o map_types o map_atyps) (fn TFree _ => TFree ("'a", [class1]) | T => T)
        |> map (ObjectLogic.ensure_propT thy)
      end;
    val (prems, concls) = pairself mk_axioms (class1, class2);
  in
    Goal.prove_global thy [] prems (Logic.mk_conjunction_list concls)
      (Locale.intro_locales_tac true (ProofContext.init thy))
  end;


(* classes *)

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
    (*FIXME need proper concept for reading locale statements*)
    fun subst_classtyvar (_, _) =
          TFree (AxClass.param_tyvarname, [])
      | subst_classtyvar (v, sort) =
          error ("Sort constraint illegal in type class, for type variable " ^ v ^ "::" ^ Sign.string_of_sort thy sort);
    (*val subst_classtyvars = Element.map_ctxt {name = I, var = I, term = I,
      typ = Term.map_type_tfree subst_classtyvar, fact = I, attrib = I};*)
    val other_consts = map (prep_param thy) raw_other_consts;
    val (elems, includes) = fold_rev (fn Locale.Elem e => apfst (cons e)
      | Locale.Expr i => apsnd (cons i)) raw_elems ([], []);
    val supclasses = map (prep_class thy) raw_supclasses;
    val sups = filter (is_some o lookup_class_data thy) supclasses
      |> Sign.certify_sort thy;
    val supsort = Sign.certify_sort thy supclasses;
    val suplocales = map (Locale.Locale o #locale o fst o the_class_data thy) sups;
    val supexpr = Locale.Merge (suplocales @ includes);
    val supparams = (map fst o Locale.parameters_of_expr thy)
      (Locale.Merge suplocales);
    val supconsts = AList.make (the o AList.lookup (op =) (param_map thy sups))
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
         of (v, _) :: _ => SOME v
          | _ => NONE;
      in
        (v, (map (fst o fst) params, params
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
        val super_defs = these_defs thy sups;
        fun prep_asm ((name, atts), ts) =
          ((NameSpace.base name, map (Attrib.attribute thy) atts),
            (map o map_aterms) ((*MetaSimplifier.rewrite_term thy super_defs [] o *)subst) ts);
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
      #-> (fn (v, (param_names, params)) =>
        axclass_params (bname, supsort) params (extract_assumes name_locale params) other_consts
      #-> (fn (name_axclass, ((_, (ax_terms, ax_axioms)), consts)) =>
        `(fn thy => class_intro thy name_locale name_axclass sups)
      #-> (fn class_intro =>
        add_class_data ((name_axclass, sups),
          (name_locale, map (fst o fst) params ~~ map fst consts, v,
            class_intro))
        (*FIXME: class_data should already contain data relevant
          for interpretation; use this later for class target*)
        (*FIXME: general export_fixes which may be parametrized
          with pieces of an emerging class*)
      #> note_intro name_axclass class_intro
      #> prove_interpretation ((ALLGOALS o ProofContext.fact_tac) ax_axioms)
          ((false, Logic.const_of_class bname), []) (Locale.Locale name_locale)
          ((mk_instT name_axclass, mk_inst name_axclass param_names (map snd supconsts @ consts)), [])
      #> pair name_axclass
      )))))
  end;

in

val class_cmd = gen_class Locale.add_locale Sign.intern_class read_param;
val class = gen_class Locale.add_locale_i Sign.certify_class (K I);

end; (*local*)

local

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

fun instance_subsort (class, sort) thy =
  let
    val super_sort = (Graph.all_succs o #classes o Sorts.rep_algebra
      o Sign.classes_of) thy sort;
    val classes = filter_out (fn class' => Sign.subsort thy ([class], [class']))
      (rev super_sort);
  in
    thy |> fold (curry instance_subclass class) classes
  end;

fun instance_sort' do_proof (class, sort) theory =
  let
    val loc_name = (#locale o fst o the_class_data theory) class;
    val loc_expr =
      (Locale.Merge o map (Locale.Locale o #locale o fst o the_class_data theory)) sort;
  in
    theory
    |> do_proof (instance_subsort (class, sort)) (loc_name, loc_expr)
  end;

fun gen_instance_sort prep_class prep_sort (raw_class, raw_sort) theory =
  let
    val class = prep_class theory raw_class;
    val sort = prep_sort theory raw_sort;
  in
    theory
    |> instance_sort' (Locale.interpretation_in_locale o ProofContext.theory) (class, sort)
  end;

fun gen_instance_class prep_class (raw_class, raw_superclass) theory =
  let
    val class = prep_class theory raw_class;
    val superclass = prep_class theory raw_superclass;
  in
    theory
    |> axclass_instance_sort (class, superclass)
  end;

in

val instance_sort_cmd = gen_instance_sort Sign.read_class Syntax.global_read_sort;
val instance_sort = gen_instance_sort Sign.certify_class Sign.certify_sort;
val prove_instance_sort = instance_sort' o prove_interpretation_in;
val instance_class_cmd = gen_instance_class Sign.read_class;
val instance_class = gen_instance_class Sign.certify_class;

end; (*local*)


(** class target **)

fun export_fixes thy class =
  let
    val v = (#v o fst o the_class_data thy) class;
    val constrain_sort = curry (Sorts.inter_sort (Sign.classes_of thy)) [class];
    val subst_typ = Term.map_type_tfree (fn var as (w, sort) =>
      if SOME w = v then TFree (w, constrain_sort sort) else TFree var);
    val consts = param_map thy [class];
    fun subst_aterm (t as Free (v, ty)) = (case AList.lookup (op =) consts v
         of SOME (c, _) => Const (c, ty)
          | NONE => t)
      | subst_aterm t = t;
  in map_types subst_typ #> Term.map_aterms subst_aterm end;

fun add_const_in_class class ((c, rhs), syn) thy =
  let
    val prfx = (Logic.const_of_class o NameSpace.base) class;
    fun mk_name inject c =
      let
        val n1 = Sign.full_name thy c;
        val n2 = NameSpace.qualifier n1;
        val n3 = NameSpace.base n1;
      in NameSpace.implode (n2 :: inject @ [n3]) end;
    val abbr' = mk_name [prfx, prfx] c;
    val rhs' = export_fixes thy class rhs;
    val ty' = Term.fastype_of rhs';
    val def = (c, Logic.mk_equals (Const (mk_name [prfx] c, ty'), rhs'));
    val (syn', _) = fork_mixfix true NONE syn;
    fun interpret def =
      let
        val def' = symmetric def
        val tac = (ALLGOALS o ProofContext.fact_tac) [def'];
        val name_locale = (#locale o fst o the_class_data thy) class;
        val def_eq = Thm.prop_of def';
        val (params, consts) = split_list (param_map thy [class]);
      in
        prove_interpretation tac ((false, prfx), []) (Locale.Locale name_locale)
          ((mk_instT class, mk_inst class params consts), [def_eq])
        #> add_class_const_thm (class, def')
      end;
  in
    thy
    |> Sign.hide_consts_i true [abbr']
    |> Sign.add_path prfx
    |> Sign.add_consts_authentic [(c, ty', syn')]
    |> Sign.parent_path
    |> Sign.sticky_prefix prfx
    |> PureThy.add_defs_i false [(def, [])]
    |-> (fn [def] => interpret def)
    |> Sign.restore_naming thy
  end;

end;
