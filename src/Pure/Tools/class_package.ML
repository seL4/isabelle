(*  Title:      Pure/Tools/class_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Type classes derived from primitive axclasses and locales.
*)

signature CLASS_PACKAGE =
sig
  val fork_mixfix: bool -> string option -> mixfix -> mixfix * mixfix

  val class: bstring -> class list -> Element.context_i Locale.element list
    -> string list -> theory -> string * Proof.context
  val class_cmd: bstring -> string list -> Element.context Locale.element list
    -> string list -> theory -> string * Proof.context
  val instance_arity: arity list -> ((bstring * Attrib.src list) * term) list
    -> theory -> Proof.state
  val instance_arity_cmd: (bstring * string list * string) list
    -> ((bstring * Attrib.src list) * string) list
    -> theory -> Proof.state
  val prove_instance_arity: tactic -> arity list
    -> ((bstring * Attrib.src list) * term) list
    -> theory -> theory
  val instance_class: class * class -> theory -> Proof.state
  val instance_class_cmd: string * string -> theory -> Proof.state
  val instance_sort: class * sort -> theory -> Proof.state
  val instance_sort_cmd: string * string -> theory -> Proof.state
  val prove_instance_sort: tactic -> class * sort -> theory -> theory

  (* experimental class target *)
  val class_of_locale: theory -> string -> class option
  val add_def_in_class: local_theory -> string
    -> (string * Syntax.mixfix) * ((string * Attrib.src list) * (term * thm)) -> theory -> theory

  val print_classes: theory -> unit
  val intro_classes_tac: thm list -> tactic
  val default_intro_classes_tac: thm list -> tactic
end;

structure ClassPackage : CLASS_PACKAGE =
struct

(** auxiliary **)

fun fork_mixfix is_loc some_class mx =
  let
    val mx' = Syntax.unlocalize_mixfix mx;
    val mx_global = if is_some some_class orelse (is_loc andalso mx = mx') then NoSyn else mx';
    val mx_local = if is_loc then mx else NoSyn;
  in (mx_global, mx_local) end;


(** AxClasses with implicit parameter handling **)

(* AxClass instances *)

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

end; (* local *)


(* introducing axclasses with implicit parameter handling *)

fun axclass_params (name, raw_superclasses) raw_consts raw_dep_axioms other_consts thy =
  let
    val superclasses = map (Sign.certify_class thy) raw_superclasses;
    val consts = (map o apfst o apsnd) (Sign.certify_typ thy) raw_consts;
    fun add_const ((c, ty), syn) =
      Sign.add_consts_authentic [(c, ty, syn)] #> pair (Sign.full_name thy c, ty);
    fun mk_axioms cs thy =
      raw_dep_axioms thy cs
      |> (map o apsnd o map) (Sign.cert_prop thy)
      |> rpair thy;
    fun add_constraint class (c, ty) =
      Sign.add_const_constraint_i (c, SOME (Term.map_type_tfree (fn (v, _) => TFree (v, [class])) ty));
  in
    thy
    |> fold_map add_const consts
    |-> (fn cs => mk_axioms cs
    #-> (fn axioms_prop => AxClass.define_class_i (name, superclasses) (map fst cs @ other_consts) axioms_prop
    #-> (fn class => `(fn thy => AxClass.get_definition thy class)
    #-> (fn {intro, axioms, ...} => fold (add_constraint class) cs
    #> pair (class, ((intro, (map Thm.prop_of axioms, axioms)), cs))))))
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

fun gen_instance_arity prep_arity read_def do_proof raw_arities raw_defs theory =
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
        map (fn (c, ty) => (c, ((tyco, class), subst_ty ty))) cs
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
            val ((tyco, class), ty') = case AList.lookup (op =) cs c
             of NONE => error ("illegal definition for constant " ^ quote c)
              | SOME class_ty => class_ty;
            val name = case name_opt
             of NONE => Thm.def_name (Logic.name_arity (tyco, [], c))
              | SOME name => name;
            val t' = case mk_typnorm thy_read (ty', ty)
             of NONE => error ("illegal definition for constant " ^
                  quote c ^ "::" ^ Sign.string_of_typ thy_read ty)
              | SOME norm => map_types norm t
          in (((class, tyco), ((name, t'), atts)), AList.delete (op =) c cs) end;
      in fold_map read defs cs end;
    val (defs, _) = read_defs raw_defs cs
      (fold Sign.primitive_arity arities (Theory.copy theory));
    fun get_remove_contraint c thy =
      let
        val ty = Sign.the_const_constraint thy c;
      in
        thy
        |> Sign.add_const_constraint_i (c, NONE)
        |> pair (c, Logic.unvarifyT ty)
      end;
    fun add_defs defs thy =
      thy
      |> PureThy.add_defs_i true (map ((apsnd o map) (Attrib.attribute thy) o snd) defs)
      |-> (fn thms => pair (map fst defs ~~ thms));
    fun after_qed cs thy =
      thy
      |> fold Sign.add_const_constraint_i (map (apsnd SOME) cs);
  in
    theory
    |> fold_map get_remove_contraint (map fst cs |> distinct (op =))
    ||>> add_defs defs
    |-> (fn (cs, _) => do_proof (after_qed cs) arities)
  end;

fun instance_arity_e' do_proof = gen_instance_arity Sign.read_arity read_def_cmd do_proof;
fun instance_arity' do_proof = gen_instance_arity Sign.cert_arity read_def do_proof;
fun tactic_proof tac after_qed arities =
  fold (fn arity => AxClass.prove_arity arity tac) arities
  #> after_qed;

in

val instance_arity_cmd = instance_arity_e' axclass_instance_arity;
val instance_arity = instance_arity' axclass_instance_arity;
val prove_instance_arity = instance_arity' o tactic_proof;

end; (* local *)



(** combining locales and axclasses **)

(* theory data *)

datatype class_data = ClassData of {
  locale: string,
  consts: (string * string) list
    (*locale parameter ~> toplevel theory constant*),
  intro: thm,
  witness: Element.witness list,
  primdefs: thm list,
    (*for experimental class target*)
  propnames: string list
    (*for ad-hoc instance_in*)
};

fun rep_classdata (ClassData c) = c;

fun merge_pair f1 f2 ((x1, y1), (x2, y2)) = (f1 (x1, x2), f2 (y1, y2));

structure ClassData = TheoryDataFun (
  struct
    val name = "Pure/classes";
    type T = class_data Graph.T * class Symtab.table (*locale name ~> class name*);
    val empty = (Graph.empty, Symtab.empty);
    val copy = I;
    val extend = I;
    fun merge _ = merge_pair (Graph.merge (K true)) (Symtab.merge (K true));
    fun print _ _ = ();
  end
);

val _ = Context.add_setup ClassData.init;


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
    fun params thy class =
      let
        val const_typs = (#params o AxClass.get_definition thy) class;
        val const_names = (#consts o the_class_data thy) class;
      in
        (map o apsnd) (fn c => (c, (the o AList.lookup (op =) const_typs) c)) const_names
      end;
  in maps (params thy) o ancestry thy end;

fun these_intros thy =
  Graph.fold (fn (_, (data, _)) => insert Thm.eq_thm ((#intro o rep_classdata) data))
    ((fst o ClassData.get) thy) [];
val the_witness = #witness oo the_class_data;
val the_propnames = #propnames oo the_class_data;

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
    (Pretty.writeln o Pretty.chunks o separate (Pretty.str "") o map mk_entry o Sorts.all_classes)
      algebra
  end;


(* updaters *)

fun add_class_data ((class, superclasses), (locale, consts, intro, witness, propnames)) =
  ClassData.map (fn (gr, tab) => (
    gr
    |> Graph.new_node (class, ClassData {
      locale = locale,
      consts = consts,
      intro = intro,
      witness = witness,
      propnames = propnames,
      primdefs = []})
    |> fold (curry Graph.add_edge class) superclasses,
    tab
    |> Symtab.update (locale, class)
  ));

fun add_primdef (class, thm) thy =
  (ClassData.map o apfst o Graph.map_node class)
    (fn ClassData { locale, consts, intro, witness, propnames, primdefs } =>
      ClassData { locale = locale, consts = consts, intro = intro,
        witness = witness, propnames = propnames, primdefs = thm :: primdefs });


(* exporting terms and theorems to global toplevel *)

fun globalize thy classes =
  let
    val consts = param_map thy classes;
    val constrain_sort = curry (Sorts.inter_sort (Sign.classes_of thy)) classes;
    val subst_typ = Term.map_type_tfree (fn var as (v, sort) =>
      if v = AxClass.param_tyvarname then TFree (v, constrain_sort sort) else TFree var)
    fun subst_aterm (t as Free (v, ty)) = (case AList.lookup (op =) consts v
         of SOME (c, _) => Const (c, ty)
          | NONE => t)
      | subst_aterm t = t;
  in (subst_typ, map_types subst_typ #> Term.map_aterms subst_aterm) end;

val global_term = snd oo globalize


(* tactics and methods *)

(*FIXME adjust these when minimal intro rules are at hand*)
fun intro_classes_tac' facts st =
  let
    val thy = Thm.theory_of_thm st;
    val ctxt = ProofContext.init thy;
    val intro_classes_tac = ALLGOALS
      (Method.insert_tac facts THEN' REPEAT_ALL_NEW (resolve_tac (AxClass.class_intros thy)))
        THEN Tactic.distinct_subgoals_tac;
    val intro_locales_tac = SOMEGOAL (SELECT_GOAL (Locale.intro_locales_tac true ctxt facts))
      THEN Tactic.distinct_subgoals_tac;
  in
    (intro_classes_tac THEN REPEAT (intro_locales_tac ORELSE intro_locales_tac)) st
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
 [("intro_classes2", Method.no_args (Method.METHOD intro_classes_tac'),
    "back-chain introduction rules of classes"),
  ("intro_classes", Method.no_args (Method.METHOD intro_classes_tac),
    "back-chain introduction rules of classes"),
  ("default", Method.thms_ctxt_args (Method.METHOD oo default_tac),
    "apply some intro/elim rule")]);


(* tactical interfaces to locale commands *)

fun prove_interpretation tac prfx_atts expr insts thy =
  thy
  |> Locale.interpretation_i I prfx_atts expr insts
  |> Proof.global_terminal_proof (Method.Basic (fn _ => Method.SIMPLE_METHOD tac), NONE)
  |> ProofContext.theory_of;

fun prove_interpretation_in tac after_qed (name, expr) thy =
  thy
  |> Locale.interpretation_in_locale (ProofContext.theory after_qed) (name, expr)
  |> Proof.global_terminal_proof (Method.Basic (fn _ => Method.SIMPLE_METHOD tac), NONE)
  |> ProofContext.theory_of;

fun instance_sort' do_proof (class, sort) theory =
  let
    val loc_name = (#locale o the_class_data theory) class;
    val loc_expr =
      (Locale.Merge o map (Locale.Locale o #locale o the_class_data theory)) sort;
    val const_names = (map (NameSpace.base o snd)
      o maps (#consts o the_class_data theory)
      o ancestry theory) [class];
    fun get_thms thy =
      ancestry thy sort
      |> AList.make (the_propnames thy)
      |> map (apsnd (map (NameSpace.append (Logic.const_of_class loc_name))))
      |> map_filter (fn (superclass, thm_names) =>
          case map_filter (try (PureThy.get_thm thy o Name)) thm_names
           of [] => NONE
            | thms => SOME (superclass, thms));
    fun after_qed thy =
      thy
      |> `get_thms
      |-> fold (fn (supclass, thms) => I
            AxClass.prove_classrel (class, supclass)
              (ALLGOALS (K (intro_classes_tac [])) THEN
                (ALLGOALS o ProofContext.fact_tac) thms))
  in
    theory
    |> do_proof after_qed (loc_name, loc_expr)
  end;

val prove_instance_sort = instance_sort' o prove_interpretation_in;


(* constructing class introduction rules from axclass and locale rules *)

fun class_intro thy locale class sups =
  let
    fun OF_LAST thm1 thm2 =
      let
        val n = (length o Logic.strip_imp_prems o prop_of) thm2;
      in (thm1 RSN (n, thm2)) end;
    fun prem_inclass t =
      case Logic.strip_imp_prems t
       of ofcls :: _ => try Logic.dest_inclass ofcls
        | [] => NONE;
    val typ = TVar ((AxClass.param_tyvarname, 0), Sign.super_classes thy class);
    fun strip_ofclass class thm =
      thm OF (fst o AxClass.of_sort thy (typ, [class])) AxClass.cache;
    fun strip_all_ofclass thm =
      case (prem_inclass o Thm.prop_of) thm
       of SOME (_, class) => thm |> strip_ofclass class |> strip_all_ofclass
        | NONE => thm;
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
  in
    raw_intro
    |> Drule.instantiate' [SOME (Thm.ctyp_of thy typ)] []
    |> strip_all_ofclass
    |> Thm.strip_shyps
    |> Drule.unconstrainTs
  end;


(* classes and instances *)

local

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
    val suplocales = map (Locale.Locale o #locale o the_class_data thy) sups;
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
      in
        (map (fst o fst) params, params
        |> (map o apfst o apsnd o Term.map_type_tfree) mk_tyvar
        |> (map o apsnd) (fork_mixfix true NONE #> fst)
        |> chop (length supconsts)
        |> snd)
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
    fun extract_axiom_names thy name_locale =
      name_locale
      |> Locale.global_asms_of thy
      |> map (NameSpace.base o fst o fst) (*FIXME - is finally dropped*);
    fun mk_instT class = Symtab.empty
      |> Symtab.update (AxClass.param_tyvarname, TFree (AxClass.param_tyvarname, [class]));
    fun mk_inst class param_names cs =
      Symtab.empty
      |> fold2 (fn v => fn (c, ty) => Symtab.update (v, Const
           (c, Term.map_type_tfree (fn (v, _) => TFree (v, [class])) ty))) param_names cs;
    fun make_witness t thm = Element.make_witness t (Goal.protect thm);
    fun note_intro name_axclass class_intro =
      PureThy.note_thmss_qualified "" ((Logic.const_of_class o NameSpace.base) name_axclass)
        [(("intro", []), [([class_intro], [])])]
      #> snd
  in
    thy
    |> add_locale (SOME (bname ^ "_pred")) bname supexpr ((*elems_constrains @*) elems)
    |-> (fn name_locale => ProofContext.theory_result (
      `(fn thy => extract_params thy name_locale)
      #-> (fn (param_names, params) =>
        axclass_params (bname, supsort) params (extract_assumes name_locale params) other_consts
      #-> (fn (name_axclass, ((_, (ax_terms, ax_axioms)), consts)) =>
        `(fn thy => class_intro thy name_locale name_axclass sups)
      ##>> `(fn thy => extract_axiom_names thy name_locale)
      #-> (fn (class_intro, axiom_names) =>
        add_class_data ((name_axclass, sups),
          (name_locale, map (fst o fst) params ~~ map fst consts,
            class_intro, map2 make_witness ax_terms ax_axioms, axiom_names))
      #> note_intro name_axclass class_intro
      #> prove_interpretation ((ALLGOALS o ProofContext.fact_tac) ax_axioms)
          ((false, Logic.const_of_class bname), []) (Locale.Locale name_locale)
          (mk_instT name_axclass, mk_inst name_axclass param_names (map snd supconsts @ consts))
      #> pair name_axclass
      )))))
  end;

in

val class_cmd = gen_class Locale.add_locale Sign.intern_class AxClass.read_param;
val class = gen_class Locale.add_locale_i Sign.certify_class (K I);

end; (*local*)

local

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

val instance_sort_cmd = gen_instance_sort Sign.read_class Sign.read_sort;
val instance_sort = gen_instance_sort Sign.certify_class Sign.certify_sort;
val instance_class_cmd = gen_instance_class Sign.read_class;
val instance_class = gen_instance_class Sign.certify_class;

end; (* local *)


(** experimental class target **)

fun print_witness wit =
  let
    val (t, thm) = Element.dest_witness wit;
    val prop = Thm.prop_of thm;
    fun string_of_tfree (v, sort) = v ^ "::" ^ Display.raw_string_of_sort sort;
    fun string_of_tvar (v, sort) = Library.string_of_indexname v ^ "::" ^ Display.raw_string_of_sort sort;
    fun print_term t =
      let
        val term = Display.raw_string_of_term t;
        val tfrees = map string_of_tfree (Term.add_tfrees t []);
        val tvars = map string_of_tvar (Term.add_tvars t []);
      in term :: tfrees @ tvars end;
  in (map Output.info (print_term t); map Output.info (print_term prop)) end;

fun add_def_in_class lthy class ((c, syn), ((name, atts), (rhs, eq))) thy =
  let
    val prfx = (Logic.const_of_class o NameSpace.base) class;
    val rhs' = global_term thy [class] rhs;
    val (syn', _) = fork_mixfix true NONE syn;
    val ty = Term.fastype_of rhs';
    fun mk_name thy c =
      let
        val n1 = Sign.full_name thy c;
        val n2 = NameSpace.qualifier n1;
        val n3 = NameSpace.base n1;
      in NameSpace.implode [n2, prfx, n3] end;
    fun add_const (c, ty, syn) =
      Sign.add_consts_authentic [(c, ty, syn)]
      #> pair (mk_name thy c, ty);
    fun add_def ((name, atts), prop) thy =
      thy
      |> PureThy.add_defs_i false [((name, prop), map (Attrib.attribute thy) atts)]
      |>> the_single;
    val _ = Output.info "------ DEF ------";
    val _ = Output.info c;
    val _ = Output.info name;
    val _ = (Output.info o Sign.string_of_term thy) rhs';
    val eq' = Morphism.thm (LocalTheory.target_morphism lthy) eq;
    val _ = (Output.info o string_of_thm) eq;
    val _ = (Output.info o string_of_thm) eq';
    val witness = the_witness thy class;
    val _ = Output.info "------ WIT ------";
    fun print_wit (t, thm) = "(" ^ Sign.string_of_term thy t ^ ", " ^ Display.string_of_thm thm ^ ")"
    fun print_raw_wit (t, thm) = "(" ^ Display.raw_string_of_term t ^ ", " ^ (Display.raw_string_of_term o Thm.prop_of) thm ^ ")"
    val _ = (Output.info o cat_lines o map (print_wit o Element.dest_witness)) witness;
    val _ = map print_witness witness;
    val _ = (Output.info o string_of_thm) eq';
    val eq'' = Element.satisfy_thm witness eq';
    val _ = (Output.info o string_of_thm) eq'';
  in
    thy
    |> Sign.add_path prfx
    |> add_const (c, ty, syn')
    |-> (fn c => add_def ((name, atts), Logic.mk_equals (Const c, rhs')))
    |-> (fn global_def_thm => tap (fn _ => (Output.info o string_of_thm) global_def_thm))
    |> Sign.restore_naming thy
  end;

end;
