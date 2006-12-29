(*  Title:      Pure/Tools/class_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Type classes derived from primitive axclasses and locales.
*)

signature CLASS_PACKAGE =
sig
  val class: bstring -> class list -> Element.context Locale.element list -> theory ->
    string * Proof.context
  val class_i: bstring -> class list -> Element.context_i Locale.element list -> theory ->
    string * Proof.context
  val instance_arity: ((bstring * string list) * string) list
    -> ((bstring * Attrib.src list) * string) list
    -> theory -> Proof.state
  val instance_arity_i: ((bstring * sort list) * sort) list
    -> ((bstring * attribute list) * term) list
    -> theory -> Proof.state
  val prove_instance_arity: tactic -> ((string * sort list) * sort) list
    -> ((bstring * attribute list) * term) list
    -> theory -> theory
  val instance_sort: string * string -> theory -> Proof.state
  val instance_sort_i: class * sort -> theory -> Proof.state
  val prove_instance_sort: tactic -> class * sort -> theory -> theory

  val certify_class: theory -> class -> class
  val certify_sort: theory -> sort -> sort
  val read_class: theory -> xstring -> class
  val read_sort: theory -> string -> sort
  val assume_arities_of_sort: theory -> ((string * sort list) * sort) list -> typ * sort -> bool
  val assume_arities_thy: theory -> ((string * sort list) * sort) list -> (theory -> 'a) -> 'a
    (*'a must not keep any reference to theory*)

  val add_def: class * thm -> theory -> theory
  val export_typ: theory -> class -> typ -> typ
  val export_def: theory -> class -> term -> term
  val export_thm: theory -> class -> thm -> thm

  val print_classes: theory -> unit
  val intro_classes_tac: thm list -> tactic
  val default_intro_classes_tac: thm list -> tactic
end;

structure ClassPackage : CLASS_PACKAGE =
struct


(** theory data **)

datatype class_data = ClassData of {
  locale: string,
  var: string,
  consts: (string * (string * typ)) list
    (*locale parameter ~> toplevel theory constant*),
  propnames: string list,
  defs: thm list
};

fun rep_classdata (ClassData c) = c;

structure ClassData = TheoryDataFun (
  struct
    val name = "Pure/classes";
    type T = class_data Symtab.table;
    val empty = Symtab.empty;
    val copy = I;
    val extend = I;
    fun merge _ = Symtab.merge (K true);
    fun print _ _ = ();
  end
);

val _ = Context.add_setup ClassData.init;


(* queries *)

val lookup_class_data = Option.map rep_classdata oo Symtab.lookup o ClassData.get;

fun the_class_data thy class =
  case lookup_class_data thy class
    of NONE => error ("undeclared constructive class " ^ quote class)
     | SOME data => data;

fun the_ancestry thy classes =
  let
    fun proj_class class =
      if is_some (lookup_class_data thy class)
      then [class]
      else (Sign.certify_sort thy o maps proj_class o Sign.super_classes thy) class;
    fun ancestry class anc =
      anc
      |> insert (op =) class
      |> fold ancestry ((maps proj_class o Sign.super_classes thy) class);
  in fold ancestry classes [] end;

val the_parm_map = #consts oo the_class_data;

val the_propnames = #propnames oo the_class_data;

fun subst_clsvar v ty_subst =
  map_type_tfree (fn u as (w, _) =>
    if w = v then ty_subst else TFree u);

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

fun add_class_data (class, (locale, var, consts, propnames)) =
  ClassData.map (
    Symtab.update_new (class, ClassData {
      locale = locale,
      var = var,
      consts = consts,
      propnames = propnames,
      defs = []})
  );

fun add_def (class, thm) =
  (ClassData.map o Symtab.map_entry class)
    (fn ClassData { locale,
      var, consts, propnames, defs } => ClassData { locale = locale,
      var = var,
      consts = consts, propnames = propnames, defs = thm :: defs });


(* experimental class target *)

fun export_typ thy loc =
  let
    val class = loc (*FIXME*);
    val (v, _) = AxClass.params_of_class thy class;
  in
    Term.map_type_tfree (fn var as (w, sort) =>
      if w = v then TFree (w, Sorts.inter_sort (Sign.classes_of thy)
        (sort, [class])) else TFree var)
  end;

fun export_def thy loc =
  let
    val class = loc (*FIXME*);
    val data = the_class_data thy class;
    val consts = #consts data;
    val v = #var data;
    val subst_typ = Term.map_type_tfree (fn var as (w, sort) =>
      if w = v then TFree (w, Sorts.inter_sort (Sign.classes_of thy)
        (sort, [class])) else TFree var)
    fun subst (t as Free (v, _)) = (case AList.lookup (op =) consts v
         of SOME c_ty => Const c_ty
          | NONE => t)
      | subst t = t;
  in
    Term.map_aterms subst #> map_types subst_typ
  end;

fun export_thm thy loc =
  let
    val class = loc (*FIXME*);
    val thms = (#defs o the_class_data thy) class;
  in
    MetaSimplifier.rewrite_rule thms
  end;


(* certification and reading *)

fun certify_class thy class =
  (fn class => (the_class_data thy class; class)) (Sign.certify_class thy class);

fun certify_sort thy sort =
  map (fn class => (the_class_data thy class; class)) (Sign.certify_sort thy sort);

fun read_class thy =
  certify_class thy o Sign.intern_class thy;

fun read_sort thy =
  certify_sort thy o Sign.read_sort thy;



(** contexts with arity assumptions **)

fun assume_arities_of_sort thy arities ty_sort =
  let
    val pp = Sign.pp thy;
    val algebra = Sign.classes_of thy
      |> fold (fn ((tyco, asorts), sort) =>
           Sorts.add_arities pp (tyco, map (fn class => (class, asorts)) sort)) arities;
  in Sorts.of_sort algebra ty_sort end;

fun assume_arities_thy thy arities f =
  let
    val thy_read = (fold (fn ((tyco, asorts), sort)
      => Sign.primitive_arity (tyco, asorts, sort)) arities o Theory.copy) thy
  in f thy_read end;



(** tactics and methods **)

fun intro_classes_tac facts st =
  (ALLGOALS (Method.insert_tac facts THEN'
      REPEAT_ALL_NEW (resolve_tac (AxClass.class_intros (Thm.theory_of_thm st))))
    THEN Tactic.distinct_subgoals_tac) st;

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



(** axclass instances **)

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
  gen_instance (Logic.mk_arities oo Sign.read_arity) AxClass.add_arity;
val axclass_instance_arity_i =
  gen_instance (Logic.mk_arities oo Sign.cert_arity) AxClass.add_arity;
val axclass_instance_sort =      
  gen_instance (single oo (Logic.mk_classrel oo AxClass.read_classrel))
    AxClass.add_classrel I o single;

end;



(** classes and instances **)

local

fun add_axclass_i (name, supsort) params axs thy =
  let
    val (c, thy') = thy
      |> AxClass.define_class_i (name, supsort) params axs;
    val {intro, axioms, ...} = AxClass.get_definition thy' c;
  in ((c, (intro, axioms)), thy') end;

(*FIXME proper locale interface*)
fun prove_interpretation_i (prfx, atts) expr insts tac thy =
  let
    fun ad_hoc_term (Const (c, ty)) =
          let
            val p = setmp show_types true (setmp show_sorts true (setmp print_mode [] (Sign.pretty_typ thy))) ty;
            val s = c ^ "::" ^ Pretty.output p;
          in s end
      | ad_hoc_term t =
          let
            val p = setmp show_types true (setmp show_sorts true (setmp print_mode [] (Sign.pretty_term thy))) t;
            val s = Pretty.output p;
          in s end;
  in
    thy
    |> Locale.interpretation I (prfx, atts) expr (map (Option.map ad_hoc_term) insts)
    |> Proof.global_terminal_proof (Method.Basic (fn _ => Method.SIMPLE_METHOD tac), NONE)
    |> ProofContext.theory_of
  end;

fun gen_class add_locale prep_class bname raw_supclasses raw_elems thy =
  let
    val (elems, exprs) = fold_rev (fn Locale.Elem e => apfst (cons e)
                                   | Locale.Expr e => apsnd (cons e))
      raw_elems ([], []);
    val supclasses = map (prep_class thy) raw_supclasses;
    val supsort =
      supclasses
      |> Sign.certify_sort thy
      |> (fn [] => Sign.defaultS thy | S => S);    (* FIXME Why syntax defaultS? *)
    val expr_supclasses = Locale.Merge
      (map (Locale.Locale o #locale o the_class_data thy) supclasses);
    val expr = Locale.Merge (map (Locale.Locale o #locale o the_class_data thy) supclasses
      @ exprs);
    val mapp_sup = AList.make
      (the o AList.lookup (op =) ((flat o map (the_parm_map thy) o the_ancestry thy) supclasses))
      ((map (fst o fst) o Locale.parameters_of_expr thy) expr_supclasses);
    fun extract_tyvar_consts thy name_locale =
      let
        fun extract_classvar ((c, ty), _) w =
          (case Term.add_tfreesT ty []
           of [(v, _)] => (case w
               of SOME u => if u = v then w else error ("Additonal type variable in type signature of constant " ^ quote c)
                | NONE => SOME v)
            | [] => error ("No type variable in type signature of constant " ^ quote c)
            | _ => error ("More than one type variable in type signature of constant " ^ quote c));
        val consts1 =
          Locale.parameters_of thy name_locale
          |> map (apsnd (TheoryTarget.fork_mixfix false true #> fst))
        val SOME v = fold extract_classvar consts1 NONE;
        val consts2 = map ((apfst o apsnd) (subst_clsvar v (TFree (v, [])))) consts1;
      in (v, chop (length mapp_sup) consts2) end;
    fun add_consts v raw_cs_sup raw_cs_this thy =
      let
        fun add_global_const ((c, ty), syn) thy =
          ((c, (Sign.full_name thy c, ty)),
            thy
            |> Sign.add_consts_authentic [(c, ty |> subst_clsvar v (TFree (v, Sign.defaultS thy)), syn)]);
      in
        thy
        |> fold_map add_global_const raw_cs_this
      end;
    fun extract_assumes thy name_locale cs_mapp =
      let
        val subst_assume =
          map_aterms (fn Free (c, ty) => Const ((fst o the o AList.lookup (op =) cs_mapp) c, ty)
                       | t => t)
        fun prep_asm ((name, atts), ts) =
          ((NameSpace.base name, map (Attrib.attribute thy) atts), map subst_assume ts)
      in
        (map prep_asm o Locale.local_asms_of thy) name_locale
      end;
    fun add_global_constraint v class (_, (c, ty)) thy =
      thy
      |> Sign.add_const_constraint_i (c, SOME (subst_clsvar v (TFree (v, [class])) ty));
    fun mk_const thy class v (c, ty) =
      Const (c, subst_clsvar v (TFree (v, [class])) ty);
  in
    thy
    |> add_locale bname expr elems
    |-> (fn name_locale => ProofContext.theory
          (`(fn thy => extract_tyvar_consts thy name_locale)
    #-> (fn (v, (raw_cs_sup, raw_cs_this)) =>
          add_consts v raw_cs_sup raw_cs_this
    #-> (fn mapp_this =>
          `(fn thy => extract_assumes thy name_locale (mapp_sup @ mapp_this))
    #-> (fn loc_axioms =>
          add_axclass_i (bname, supsort) (map (fst o snd) mapp_this) loc_axioms
    #-> (fn (name_axclass, (_, ax_axioms)) =>
          fold (add_global_constraint v name_axclass) mapp_this
    #> add_class_data (name_locale, (name_locale, v, mapp_this,
          map (fst o fst) loc_axioms))
    #> prove_interpretation_i (Logic.const_of_class bname, [])
          (Locale.Locale name_locale) (map (SOME o mk_const thy name_axclass v) (map snd (mapp_sup @ mapp_this)))
          ((ALLGOALS o ProofContext.fact_tac) ax_axioms)
    ))))) #> pair name_locale)
  end;

in

val class = gen_class (Locale.add_locale false) read_class;
val class_i = gen_class (Locale.add_locale_i false) certify_class;

end; (*local*)

local

fun gen_read_def thy prep_att read_def ((raw_name, raw_atts), raw_t) =
  let
    val (_, t) = read_def thy (raw_name, raw_t);
    val ((c, ty), _) = Sign.cert_def (Sign.pp thy) t;
    val atts = map (prep_att thy) raw_atts;
    val insts = (Consts.typargs (Sign.consts_of thy) (c, ty))
    val name = case raw_name
     of "" => NONE
      | _ => SOME raw_name;
  in (c, (insts, ((name, t), atts))) end;

fun read_def thy = gen_read_def thy Attrib.attribute read_axm;
fun read_def_i thy = gen_read_def thy (K I) (K I);

fun gen_instance_arity prep_arity prep_att read_def do_proof raw_arities raw_defs theory =
  let
    fun prep_arity' ((tyco, asorts), sort) = prep_arity theory (tyco, asorts, sort);
    val arities = map prep_arity' raw_arities;
    val arities_pair = map (fn (tyco, asorts, sort) => ((tyco, asorts), sort)) arities;
    val _ = if null arities then error "at least one arity must be given" else ();
    val _ = case (duplicates (op =) o map #1) arities
     of [] => ()
      | dupl_tycos => error ("type constructors occur more than once in arities: "
        ^ (commas o map quote) dupl_tycos);
    fun get_consts_class tyco ty class =
      let
        val (_, cs) = AxClass.params_of_class theory class;
        val subst_ty = map_type_tfree (K ty);
      in
        map (fn (c, ty) => (c, ((tyco, class), subst_ty ty))) cs
      end;
    fun get_consts_sort (tyco, asorts, sort) =
      let
        val ty = Type (tyco, map (fn (v, sort) => TVar ((v, 0), sort)) (Name.names Name.context "'a" asorts))
      in maps (get_consts_class tyco ty) (the_ancestry theory sort) end;
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
             of NONE => error ("superfluous definition for constant " ^ quote c)
              | SOME class_ty => class_ty;
            val name = case name_opt
             of NONE => Thm.def_name (Logic.name_arity (tyco, [], c))
              | SOME name => name;
            val t' = case mk_typnorm thy_read (ty', ty)
             of NONE => error ("superfluous definition for constant " ^
                  quote c ^ "::" ^ Sign.string_of_typ thy_read ty)
              | SOME norm => map_types norm t
          in (((class, tyco), ((name, t'), atts)), AList.delete (op =) c cs) end;
      in fold_map read defs cs end;
    val (defs, _) = assume_arities_thy theory arities_pair (read_defs raw_defs cs);
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
      |> PureThy.add_defs_i true (map snd defs)
      |-> (fn thms => pair (map fst defs ~~ thms));
    fun after_qed cs thy =
      thy
      |> fold Sign.add_const_constraint_i (map (apsnd SOME) cs);
  in
    theory
    |> fold_map get_remove_contraint (map fst cs |> distinct (op =))
    ||>> add_defs defs
    |-> (fn (cs, def_thms) => do_proof (after_qed cs) arities)
  end;

fun instance_arity' do_proof = gen_instance_arity Sign.read_arity Attrib.attribute
  read_def do_proof;
fun instance_arity_i' do_proof = gen_instance_arity Sign.cert_arity (K I)
  read_def_i do_proof;
fun tactic_proof tac after_qed arities =
  fold (fn arity => AxClass.prove_arity arity tac) arities
  #> after_qed;

in

val instance_arity = instance_arity' axclass_instance_arity_i;
val instance_arity_i = instance_arity_i' axclass_instance_arity_i;
val prove_instance_arity = instance_arity_i' o tactic_proof;

end; (*local*)

local

fun prove_interpretation_in tac after_qed (name, expr) thy =
  thy
  |> Locale.interpretation_in_locale (ProofContext.theory after_qed) (name, expr)
  |> Proof.global_terminal_proof (Method.Basic (fn _ => Method.SIMPLE_METHOD tac), NONE)
  |> ProofContext.theory_of;

(*FIXME very ad-hoc, needs proper locale interface*)
fun gen_instance_sort prep_class prep_sort do_proof (raw_class, raw_sort) theory =
  let
    val class = prep_class theory raw_class;
    val sort = prep_sort theory raw_sort;
    val loc_name = (#locale o the_class_data theory) class;
    val loc_expr =
      (Locale.Merge o map (Locale.Locale o #locale o the_class_data theory)) sort;
    val const_names = (map (NameSpace.base o fst o snd)
      o maps (#consts o the_class_data theory)
      o the_ancestry theory) [class];
    fun get_thms thy =
      the_ancestry thy sort
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

fun instance_sort' do_proof = gen_instance_sort read_class read_sort do_proof;
fun instance_sort_i' do_proof = gen_instance_sort certify_class certify_sort do_proof;
val setup_proof = Locale.interpretation_in_locale o ProofContext.theory;
val tactic_proof = prove_interpretation_in;

in

val instance_sort = instance_sort' setup_proof;
val instance_sort_i = instance_sort_i' setup_proof;
val prove_instance_sort = instance_sort_i' o tactic_proof;

end; (* local *)


(** toplevel interface **)

local

structure P = OuterParse
and K = OuterKeyword

in

val (classK, instanceK, print_classesK) = ("class", "instance", "print_classes")

fun wrap_add_instance_sort (class, sort) thy =
  (if forall (is_some o lookup_class_data thy) (Sign.read_sort thy sort)
    andalso (is_some o lookup_class_data thy) (Sign.intern_class thy class)
  then instance_sort else axclass_instance_sort) (class, sort) thy;

val class_subP = P.name -- Scan.repeat (P.$$$ "+" |-- P.name) >> (op ::);
val class_bodyP = P.!!! (Scan.repeat1 P.locale_element);

val parse_arity =
  (P.xname --| P.$$$ "::" -- P.!!! P.arity)
    >> (fn (tyco, (asorts, sort)) => ((tyco, asorts), sort));

val classP =
  OuterSyntax.command classK "define operational type class" K.thy_decl (
    P.name --| P.$$$ "="
    -- (
      class_subP --| P.$$$ "+" -- class_bodyP
      || class_subP >> rpair []
      || class_bodyP >> pair [])
    -- P.opt_begin
    >> (fn ((bname, (supclasses, elems)), begin) =>
        Toplevel.begin_local_theory begin
          (class bname supclasses elems #-> TheoryTarget.begin true)));

val instanceP =
  OuterSyntax.command instanceK "prove type arity or subclass relation" K.thy_goal ((
      P.xname -- ((P.$$$ "\\<subseteq>" || P.$$$ "<") |-- P.!!! P.xname) >> wrap_add_instance_sort
      || P.and_list1 parse_arity -- Scan.repeat (P.opt_thm_name ":" -- P.prop)
           >> (fn ([((tyco, asorts), sort)], []) => axclass_instance_arity I [(tyco, asorts, sort)]
                | (arities, defs) => instance_arity arities defs)
    ) >> (Toplevel.print oo Toplevel.theory_to_proof));

val print_classesP =
  OuterSyntax.improper_command print_classesK "print classes of this theory" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_theory
      o Toplevel.keep (print_classes o Toplevel.theory_of)));

val _ = OuterSyntax.add_parsers [classP, instanceP, print_classesP];

end; (*local*)

end;
