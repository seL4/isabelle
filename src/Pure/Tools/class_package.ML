(*  Title:      Pure/Tools/class_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Type classes derived from primitive axclasses and locales.
*)

signature CLASS_PACKAGE =
sig
  val class: bstring -> class list -> Element.context list -> theory
    -> ProofContext.context * theory
  val class_i: bstring -> class list -> Element.context_i list -> theory
    -> ProofContext.context * theory
  val instance_arity: (xstring * string list) * string
    -> bstring * Attrib.src list -> ((bstring * Attrib.src list) * string) list
    -> theory -> Proof.state
  val instance_arity_i: (string * sort list) * sort
    -> bstring * attribute list -> ((bstring * attribute list) * term) list
    -> theory -> Proof.state
  val prove_instance_arity: tactic -> (string * sort list) * sort
    -> bstring * attribute list -> ((bstring * attribute list) * term) list
    -> theory -> theory
  val instance_sort: string * string -> theory -> Proof.state
  val instance_sort_i: class * sort -> theory -> Proof.state
  val prove_instance_sort: tactic -> class * sort -> theory -> theory

  val use_cp_instance: bool ref;

  val intern_class: theory -> xstring -> class
  val intern_sort: theory -> sort -> sort
  val extern_class: theory -> class -> xstring
  val extern_sort: theory -> sort -> sort
  val certify_class: theory -> class -> class
  val certify_sort: theory -> sort -> sort
  val read_sort: theory -> string -> sort
  val operational_sort_of: theory -> sort -> sort
  val the_superclasses: theory -> class -> class list
  val the_consts_sign: theory -> class -> string * (string * typ) list
  val lookup_const_class: theory -> string -> class option
  val the_instances: theory -> class -> (string * ((sort list) * string)) list
  val the_inst_sign: theory -> class * string -> (string * sort) list * (string * typ) list
  val get_classtab: theory -> (string * string) list Symtab.table

  val print_classes: theory -> unit
  val intro_classes_tac: thm list -> tactic
  val default_intro_classes_tac: thm list -> tactic

  type sortcontext = (string * sort) list
  datatype classlookup = Instance of (class * string) * classlookup list list
                       | Lookup of class list * (string * (int * int))
  val sortcontext_of_typ: theory -> typ -> sortcontext
  val sortlookup: theory -> sort * typ -> classlookup list
  val sortlookups_const: theory -> string * typ -> classlookup list list
end;

structure ClassPackage: CLASS_PACKAGE =
struct


(* theory data *)

datatype class_data = ClassData of {
  name_locale: string,
  name_axclass: string,
  var: string,
  consts: (string * (string * typ)) list
    (*locale parameter ~> toplevel const*)
};

fun rep_classdata (ClassData c) = c;

structure ClassData = TheoryDataFun (
  struct
    val name = "Pure/classes";
    type T = (class_data Graph.T
      * (string * (sort list * string)) list Symtab.table)
        (*class ~> tyco ~> (arity, thyname)*)
      * class Symtab.table;
    val empty = ((Graph.empty, Symtab.empty), Symtab.empty);
    val copy = I;
    val extend = I;
    fun merge _ (((g1, c1), f1) : T, ((g2, c2), f2)) =
      ((Graph.merge (K true) (g1, g2), Symtab.join (fn _ => AList.merge (op =) (op =)) (c1, c2)),
       Symtab.merge (op =) (f1, f2));
    fun print thy ((gr, _), _) =
      let
        fun pretty_class gr (name, ClassData {name_locale, name_axclass, var, consts}) =
          (Pretty.block o Pretty.fbreaks) [
            Pretty.str ("class " ^ name ^ ":"),
            (Pretty.block o Pretty.fbreaks) (
              Pretty.str "superclasses: "
              :: (map Pretty.str o Graph.imm_succs gr) name
            ),
            Pretty.str ("locale: " ^ name_locale),
            Pretty.str ("axclass: " ^ name_axclass),
            Pretty.str ("class variable: " ^ var),
            (Pretty.block o Pretty.fbreaks) (
              Pretty.str "constants: "
              :: map (fn (_, (c, ty)) => Pretty.str (c ^ " :: " ^ Sign.string_of_typ thy ty)) consts
            )
          ]
      in
        (Pretty.writeln o Pretty.chunks o map (pretty_class gr)
          o AList.make (Graph.get_node gr) o flat o Graph.strong_conn) gr
      end;
  end
);

val _ = Context.add_setup ClassData.init;
val print_classes = ClassData.print;


(* queries *)

val lookup_class_data = Option.map rep_classdata oo try o Graph.get_node o fst o fst o ClassData.get;
val the_instances = these oo Symtab.lookup o snd o fst o ClassData.get;
val lookup_const_class = Symtab.lookup o snd o ClassData.get;

fun the_class_data thy class =
  case lookup_class_data thy class
    of NONE => error ("undeclared operational class " ^ quote class)
     | SOME data => data;

val is_class = is_some oo lookup_class_data;

fun is_operational_class thy cls =
  lookup_class_data thy cls
  |> Option.map (not o null o #consts)
  |> the_default false;

fun operational_sort_of thy =
  let
    fun get_sort class =
      if is_operational_class thy class
      then [class]
      else operational_sort_of thy (Sign.super_classes thy class);
  in Sign.certify_sort thy o maps get_sort end;

fun the_superclasses thy class =
  if is_class thy class
  then
    Sign.super_classes thy class
    |> operational_sort_of thy
  else
    error ("no class: " ^ class);

fun get_superclass_derivation thy (subclass, superclass) =
  if subclass = superclass
    then SOME [subclass]
    else case Graph.irreducible_paths ((fst o fst o ClassData.get) thy) (subclass, superclass)
      of [] => NONE
       | (p::_) => (SOME o filter (is_operational_class thy)) p;

fun the_ancestry thy classes =
  let
    fun ancestry class anc =
      anc
      |> cons class
      |> fold ancestry (the_superclasses thy class);
  in fold ancestry classes [] end;

fun subst_clsvar v ty_subst =
  map_type_tfree (fn u as (w, _) =>
    if w = v then ty_subst else TFree u);

fun the_parm_map thy class =
  let
    val data = the_class_data thy class
  in (#consts data) end;

fun the_consts_sign thy class =
  let
    val data = the_class_data thy class
  in (#var data, (map snd o #consts) data) end;

fun the_inst_sign thy (class, tyco) =
  let
    val _ = if is_operational_class thy class then () else error ("no operational class: " ^ class);
    val arity = Sign.arity_sorts thy tyco [class];
    val clsvar = (#var o the_class_data thy) class;
    val const_sign = (snd o the_consts_sign thy) class;
    fun add_var sort used =
      let
        val v = hd (Term.invent_names used "'a" 1)
      in ((v, sort), v::used) end;
    val (vsorts, _) =
      [clsvar]
      |> fold (fn (_, ty) => curry (gen_union (op =))
           ((map (fst o fst) o typ_tvars) ty @ (map fst o typ_tfrees) ty)) const_sign
      |> fold_map add_var arity;
    val ty_inst = Type (tyco, map TFree vsorts);
    val inst_signs = map (apsnd (subst_clsvar clsvar ty_inst)) const_sign;
  in (vsorts, inst_signs) end;

fun get_classtab thy =
  (Symtab.map o map)
    (fn (tyco, (_, thyname)) => (tyco, thyname)) ((snd o fst o ClassData.get) thy);


(* updaters *)

fun add_class_data (class, (superclasses, name_locale, name_axclass, var, consts)) =
  ClassData.map (fn ((gr, tab), consttab) => ((
    gr
    |> Graph.new_node (class, ClassData {
         name_locale = name_locale,
         name_axclass = name_axclass,
         var = var,
         consts = consts
       })
    |> fold (curry Graph.add_edge_acyclic class) superclasses,
    tab
    |> Symtab.update (class, [])),
    consttab
    |> fold (fn (_, (c, _)) => Symtab.update (c, class)) consts
  ));

fun add_inst_data (class, inst) =
  ClassData.map (fn ((gr, tab), consttab) =>
    let
      val undef_supclasses = class :: (filter (Symtab.defined tab) (Graph.all_succs gr [class]));
    in
     ((gr, tab |> fold (fn class => Symtab.map_entry class (AList.update (op =) inst)) undef_supclasses), consttab)
    end);


(* name handling *)

fun certify_class thy class =
  (fn class => (the_class_data thy class; class)) (Sign.certify_class thy class);

fun certify_sort thy sort =
  map (fn class => (the_class_data thy class; class)) (Sign.certify_sort thy sort);

fun intern_class thy =
certify_class thy o Sign.intern_class thy;

fun intern_sort thy =
  certify_sort thy o Sign.intern_sort thy;

fun extern_class thy =
  Sign.extern_class thy o certify_class thy;

fun extern_sort thy =
  Sign.extern_sort thy o certify_sort thy;

fun read_sort thy =
  certify_sort thy o Sign.read_sort thy;


(* tactics and methods *)

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


(* axclass instances *)

local

fun gen_instance mk_prop add_thm after_qed inst thy =
  thy
  |> ProofContext.init
  |> Proof.theorem_i PureThy.internalK NONE (after_qed oo (fold o fold) add_thm) NONE ("", [])
       (map (fn t => (("", []), [(t, [])])) (mk_prop thy inst));

in

val axclass_instance_subclass =
  gen_instance (single oo (Logic.mk_classrel oo AxClass.read_classrel)) AxClass.add_classrel I;
val axclass_instance_arity =
  gen_instance (Logic.mk_arities oo Sign.read_arity) AxClass.add_arity;
val axclass_instance_arity_i =
  gen_instance (Logic.mk_arities oo Sign.cert_arity) AxClass.add_arity;

end;


(* classes and instances *)

local

fun add_axclass_i (name, supsort) axs thy =
  let
    val (c, thy') = thy
      |> AxClass.define_class_i (name, supsort) [] axs;
    val {intro, axioms, ...} = AxClass.get_definition thy' c;
  in ((c, (intro, axioms)), thy') end;

fun prove_interpretation_i (prfx, atts) expr insts tac thy =
  let
    fun ad_hoc_term NONE = NONE
      | ad_hoc_term (SOME (Const (c, ty))) =
          let
            val p = setmp show_types true (setmp show_sorts true (setmp print_mode [] (Sign.pretty_typ thy))) ty;
            val s = c ^ "::" ^ Pretty.output p;
            val _ = writeln s;
          in SOME s end
      | ad_hoc_term (SOME t) =
          let
            val p = setmp show_types true (setmp show_sorts true (setmp print_mode [] (Sign.pretty_term thy))) t;
            val s = Pretty.output p;
            val _ = writeln s;
          in SOME s end;
  in
    thy
    |> Locale.interpretation (prfx, atts) expr (map ad_hoc_term insts)
    |> Proof.global_terminal_proof (Method.Basic (fn _ => Method.SIMPLE_METHOD tac), NONE)
    |-> (fn _ => I)
  end;

fun gen_class add_locale prep_class bname raw_supclasses raw_elems thy =
  let
    val supclasses = map (prep_class thy) raw_supclasses;
    val supsort =
      supclasses
      |> map (#name_axclass o the_class_data thy)
      |> Sign.certify_sort thy
      |> null ? K (Sign.defaultS thy);
    val expr = (Locale.Merge o map (Locale.Locale o #name_locale o the_class_data thy)) supclasses;
    val mapp_sup = AList.make
      (the o AList.lookup (op =) ((flat o map (the_parm_map thy) o the_ancestry thy) supclasses))
      ((map (fst o fst) o Locale.parameters_of_expr thy) expr);
    fun extract_tyvar_consts thy name_locale =
      let
        fun extract_tyvar_name thy tys =
          fold (curry add_typ_tfrees) tys []
          |> (fn [(v, sort)] =>
              if Sign.subsort thy (supsort, sort)
                    then v
                    else error ("illegal sort constraint on class type variable: " ^ Sign.string_of_sort thy sort)
               | [] => error ("no class type variable")
               | vs => error ("more than one type variable: " ^ (commas o map (Sign.string_of_typ thy o TFree)) vs))
        val consts1 =
          Locale.parameters_of thy name_locale
          |> map (apsnd Syntax.unlocalize_mixfix)
        val v = (extract_tyvar_name thy o map (snd o fst)) consts1;
        val consts2 = map ((apfst o apsnd) (subst_clsvar v (TFree (v, [])))) consts1;
      in (v, chop (length mapp_sup) consts2) end;
    fun add_consts v raw_cs_sup raw_cs_this thy =
      let
        fun add_global_const ((c, ty), syn) thy =
          thy
          |> Sign.add_consts_i [(c, ty |> subst_clsvar v (TFree (v, Sign.defaultS thy)), syn)]
          |> `(fn thy => (c, (Sign.intern_const thy c, ty)))
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
          ((NameSpace.base name |> print, map (Attrib.attribute thy) atts), map subst_assume ts)
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
    |> add_locale bname expr raw_elems
    |-> (fn (name_locale, ctxt) =>
          `(fn thy => extract_tyvar_consts thy name_locale)
    #-> (fn (v, (raw_cs_sup, raw_cs_this)) =>
          add_consts v raw_cs_sup raw_cs_this
    #-> (fn mapp_this =>
          `(fn thy => extract_assumes thy name_locale (mapp_sup @ mapp_this))
    #-> (fn loc_axioms =>
          add_axclass_i (bname, supsort) loc_axioms
    #-> (fn (name_axclass, (_, ax_axioms)) =>
          fold (add_global_constraint v name_axclass) mapp_this
    #> add_class_data (name_locale, (supclasses, name_locale, name_axclass, v, mapp_this))
    #> prove_interpretation_i (NameSpace.base name_locale, [])
          (Locale.Locale name_locale) (map (SOME o mk_const thy name_axclass v) (map snd (mapp_sup @ mapp_this)))
          ((ALLGOALS o ProofContext.fact_tac) ax_axioms)
    #> pair ctxt
    )))))
  end;

in

val class = gen_class (Locale.add_locale false) intern_class;
val class_i = gen_class (Locale.add_locale_i false) certify_class;

end; (* local *)

local

fun gen_add_defs_overloaded prep_att tap_def add_defs tyco raw_defs thy =
  let
    fun invent_name raw_t =
      let
        val t = tap_def thy raw_t;
        val c = (fst o dest_Const o fst o strip_comb o fst o Logic.dest_equals) t;
      in
        Thm.def_name (NameSpace.base c ^ "_" ^ NameSpace.base tyco)
      end;
    fun prep_def (_, (("", a), t)) =
          let
            val n = invent_name t
          in ((n, t), map (prep_att thy) a) end
      | prep_def (_, ((n, a), t)) =
          ((n, t), map (prep_att thy) a);
  in
    thy
    |> add_defs true (map prep_def raw_defs)
  end;

val add_defs_overloaded = gen_add_defs_overloaded Attrib.attribute Sign.read_term PureThy.add_defs;
val add_defs_overloaded_i = gen_add_defs_overloaded (K I) (K I) PureThy.add_defs_i;

fun gen_instance_arity prep_arity prep_att add_defs tap_def do_proof raw_arity (raw_name, raw_atts) raw_defs theory =
  let
    val pp = Sign.pp theory;
    val arity as (tyco, asorts, sort) = prep_arity theory ((fn ((x, y), z) => (x, y, z)) raw_arity);
    val ty_inst = Type (tyco, map2 (curry TVar o rpair 0) (Term.invent_names [] "'a" (length asorts)) asorts)
    val name = case raw_name
     of "" => Thm.def_name ((space_implode "_" o map NameSpace.base) sort ^ "_" ^ NameSpace.base tyco)
      | _ => raw_name;
    val atts = map (prep_att theory) raw_atts;
    fun get_classes thy tyco sort =
      let
        fun get class classes =
          if AList.defined (op =) ((the_instances thy) class) tyco
            then classes
            else classes
              |> cons class
              |> fold get (the_superclasses thy class)
      in fold get sort [] end;
    val classes = get_classes theory tyco sort;
    val _ = if null classes then error ("already instantiated") else ();
    fun get_consts class =
      let
        val data = the_class_data theory class;
        val subst_ty = map_type_tfree (fn (var as (v, _)) =>
          if #var data = v then ty_inst else TFree var)
      in (map (apsnd subst_ty o snd) o #consts) data end;
    val cs = (flat o map get_consts) classes;
    fun get_remove_contraint c thy =
      let
        val ty = Sign.the_const_constraint thy c;
      in
        thy
        |> Sign.add_const_constraint_i (c, NONE)
        |> pair (c, Logic.legacy_unvarifyT ty)
      end;
    fun check_defs0 thy raw_defs c_req =
      let
        fun get_c raw_def =
          (fst o Sign.cert_def pp o tap_def thy o snd) raw_def;
        val c_given = map get_c raw_defs;
        fun eq_c ((c1 : string, ty1), (c2, ty2)) =
          let
            val ty1' = Logic.legacy_varifyT ty1;
            val ty2' = Logic.legacy_varifyT ty2;
          in
            c1 = c2
            andalso Sign.typ_instance thy (ty1', ty2')
            andalso Sign.typ_instance thy (ty2', ty1')
          end;
        val _ = case subtract eq_c c_req c_given
         of [] => ()
          | cs => error ("superfluous definition(s) given for "
                    ^ (commas o map (fn (c, ty) => quote (c ^ "::" ^ Sign.string_of_typ thy ty))) cs);
        (*val _ = case subtract eq_c c_given c_req
         of [] => ()
          | cs => error ("no definition(s) given for "
                    ^ (commas o map (fn (c, ty) => quote (c ^ "::" ^ Sign.string_of_typ thy ty))) cs);*)
      in () end;
    fun check_defs1 raw_defs c_req thy =
      let
        val thy' = (Sign.primitive_arity (tyco, asorts, sort) o Theory.copy) thy
      in (check_defs0 thy' raw_defs c_req; thy) end;
    fun mangle_alldef_name tyco sort =
      Thm.def_name ((space_implode "_" o map NameSpace.base) sort ^ "_" ^ NameSpace.base tyco);
    fun note_all tyco sort thms thy =
      thy
      |> PureThy.note_thmss_i PureThy.internalK [((name, atts), [(thms, [])])]
      |> snd;
    fun after_qed cs thy =
      thy
      |> fold (fn class =>
        add_inst_data (class, (tyco,
          (map (operational_sort_of thy) asorts, Context.theory_name thy)))) sort
      |> fold Sign.add_const_constraint_i (map (apsnd SOME) cs);
  in
    theory
    |> check_defs1 raw_defs cs
    |> fold_map get_remove_contraint (map fst cs)
    ||>> add_defs tyco (map (pair NONE) raw_defs)
    |-> (fn (cs, defnames) => note_all tyco sort defnames #> pair cs)
    |-> (fn cs => do_proof (after_qed cs) arity)
  end;

fun instance_arity' do_proof = gen_instance_arity Sign.read_arity Attrib.attribute add_defs_overloaded
  (fn thy => fn t => (snd o read_axm thy) ("", t)) do_proof;
fun instance_arity_i' do_proof = gen_instance_arity Sign.cert_arity (K I) add_defs_overloaded_i
  (K I) do_proof;
val setup_proof = axclass_instance_arity_i;
fun tactic_proof tac after_qed arity = AxClass.prove_arity arity tac #> after_qed;

in

val instance_arity = instance_arity' setup_proof;
val instance_arity_i = instance_arity_i' setup_proof;
val prove_instance_arity = instance_arity_i' o tactic_proof;

end; (* local *)

local

fun fish_thms (name, expr) after_qed thy =
  let
    val _ = writeln ("sub " ^ name)
    val suplocales = (fn Locale.Merge es => map (fn Locale.Locale n => n) es) expr;
    val _ = writeln ("super " ^ commas suplocales)
    fun get_c name =
      (map (NameSpace.base o fst o fst) o Locale.parameters_of thy) name;
    fun get_a name =
      (map (NameSpace.base o fst o fst) o Locale.local_asms_of thy) name;
    fun get_t supname =
      map (NameSpace.append (NameSpace.append name ((space_implode "_" o get_c) supname)) o NameSpace.base)
        (get_a name);
    val names = map get_t suplocales;
    val _ = writeln ("fishing for " ^ (commas o map commas) names);
  in
    thy
    |> after_qed ((map o map) (Drule.standard o get_thm thy o Name) names)
  end;

fun add_interpretation_in (after_qed : thm list list -> theory -> theory) (name, expr) thy =
  thy
  |> Locale.interpretation_in_locale (name, expr);

fun prove_interpretation_in tac (after_qed : thm list list -> theory -> theory) (name, expr) thy =
  thy
  |> Locale.interpretation_in_locale (name, expr)
  |> Proof.global_terminal_proof (Method.Basic (fn _ => Method.SIMPLE_METHOD tac), NONE)
  |-> (fn _ => I);

fun gen_instance_sort prep_class prep_sort do_proof (raw_class, raw_sort) theory =
  let
    val class = prep_class theory raw_class;
    val sort = prep_sort theory raw_sort;
    val loc_name = (#name_locale o the_class_data theory) class;
    val loc_expr =
      (Locale.Merge o map (Locale.Locale o #name_locale o the_class_data theory)) sort;
    fun after_qed thmss thy =
      (writeln "---"; (Pretty.writeln o Display.pretty_thms o flat) thmss; writeln "---"; fold (fn supclass =>
        AxClass.prove_classrel (class, supclass)
          (ALLGOALS (K (intro_classes_tac [])) THEN
            (ALLGOALS o resolve_tac o flat) thmss)
      ) sort thy)
  in
    theory
    |> do_proof after_qed (loc_name, loc_expr)
  end;

fun instance_sort' do_proof = gen_instance_sort intern_class read_sort do_proof;
fun instance_sort_i' do_proof = gen_instance_sort certify_class certify_sort do_proof;
val setup_proof = add_interpretation_in;
val tactic_proof = prove_interpretation_in;

in

val instance_sort = instance_sort' setup_proof;
val instance_sort_i = instance_sort_i' setup_proof;
val prove_instance_sort = instance_sort_i' o tactic_proof;

end; (* local *)

(* extracting dictionary obligations from types *)

type sortcontext = (string * sort) list;

fun sortcontext_of_typ thy ty =
  (typ_tfrees o fst o Type.freeze_thaw_type) ty
  |> map (apsnd (operational_sort_of thy))
  |> filter (not o null o snd);

datatype classlookup = Instance of (class * string) * classlookup list list
                     | Lookup of class list * (string * (int * int))

fun pretty_lookup' (Instance ((class, tyco), lss)) =
      (Pretty.block o Pretty.breaks) (
        Pretty.enum "," "{" "}" [Pretty.str class, Pretty.str tyco]
        :: map pretty_lookup lss
      )
  | pretty_lookup' (Lookup (classes, (v, (i, j)))) =
      Pretty.enum " <" "[" "]" (map Pretty.str classes @
        [Pretty.str (v ^ "!" ^ string_of_int i ^ "/" ^ string_of_int j)])
and pretty_lookup ls = (Pretty.enum "," "(" ")" o map pretty_lookup') ls;

fun sortlookup thy (sort_decl, typ_ctxt) =
  let
    val pp = Sign.pp thy;
    val algebra = Sorts.project_algebra pp (is_operational_class thy)
      (Sign.classes_of thy);
    fun classrel (l as Lookup (classes, p), _) class  =
          Lookup (class :: classes, p)
      | classrel (Instance ((_, tyco), lss), _) class =
          Instance ((class, tyco), lss);
    fun constructor tyco lss class =
      Instance ((class, tyco), (map o map) fst lss)
    fun variable (TFree (v, sort)) =
          map_index (fn (n, class) => (Lookup ([], (v, (n, length sort))), class))
            (operational_sort_of thy sort)
      | variable (TVar _) = error "TVar encountered while deriving sortlookup";
  in
    Sorts.of_sort_derivation pp algebra
      {classrel = classrel, constructor = constructor, variable = variable}
      (typ_ctxt, operational_sort_of thy sort_decl)
  end;

fun sortlookups_const thy (c, typ_ctxt) =
  let
    val typ_decl = case lookup_const_class thy c
     of NONE => Sign.the_const_type thy c
      | SOME class => case the_consts_sign thy class of (v, cs) =>
          (Logic.legacy_varifyT o subst_clsvar v (TFree (v, [class])))
          ((the o AList.lookup (op =) cs) c)
    val vartab = typ_tvars typ_decl;
    fun prep_vartab (v, (_, ty)) =
      case (the o AList.lookup (op =) vartab) v
       of [] => NONE
        | sort => SOME (sort, ty);
  in
    Vartab.empty
    |> Sign.typ_match thy (typ_decl, typ_ctxt)
    |> Vartab.dest
    |> map_filter prep_vartab
    |> map (sortlookup thy)
    |> filter_out null
  end;


(* toplevel interface *)

local

structure P = OuterParse
and K = OuterKeyword

in

val (classK, instanceK) = ("class", "instance")

val use_cp_instance = ref false;

fun wrap_add_instance_subclass (class, sort) thy =
  case Sign.read_sort thy sort
   of [class'] =>
      if ! use_cp_instance
        andalso (is_some o lookup_class_data thy o Sign.intern_class thy) class
        andalso (is_some o lookup_class_data thy o Sign.intern_class thy) class'
      then
        instance_sort (class, sort) thy
      else
        axclass_instance_subclass (class, sort) thy
    | _ => instance_sort (class, sort) thy;

val parse_inst =
  (Scan.optional (P.$$$ "(" |-- P.!!! (P.list1 P.sort --| P.$$$ ")")) [] -- P.xname --| P.$$$ "::" -- P.sort)
    >> (fn ((asorts, tyco), sort) => ((tyco, asorts), sort))
  || (P.xname --| P.$$$ "::" -- P.!!! P.arity)
    >> (fn (tyco, (asorts, sort)) => ((tyco, asorts), sort));

val locale_val =
  (P.locale_expr --
    Scan.optional (P.$$$ "+" |-- P.!!! (Scan.repeat1 P.context_element)) [] ||
  Scan.repeat1 P.context_element >> pair Locale.empty);

val class_subP = P.name -- Scan.repeat (P.$$$ "+" |-- P.name) >> (op ::);
val class_bodyP = P.!!! (Scan.repeat1 P.context_element);

val classP =
  OuterSyntax.command classK "operational type classes" K.thy_decl (
    P.name --| P.$$$ "="
    -- (
      class_subP --| P.$$$ "+" -- class_bodyP
      || class_subP >> rpair []
      || class_bodyP >> pair []
    ) >> (Toplevel.theory_context
          o (fn (bname, (supclasses, elems)) => class bname supclasses elems)));

val instanceP =
  OuterSyntax.command instanceK "prove type arity or subclass relation" K.thy_goal ((
      P.xname -- ((P.$$$ "\\<subseteq>" || P.$$$ "<") |-- P.!!! P.xname) >> wrap_add_instance_subclass
      || P.opt_thm_name ":" -- (parse_inst -- Scan.repeat (P.opt_thm_name ":" -- P.prop))
           >> (fn (("", []), (((tyco, asorts), sort), [])) => axclass_instance_arity I (tyco, asorts, sort)
                | (natts, (inst, defs)) => instance_arity inst natts defs)
    ) >> (Toplevel.print oo Toplevel.theory_to_proof));

val _ = OuterSyntax.add_parsers [classP, instanceP];

end; (* local *)

end; (* struct *)
