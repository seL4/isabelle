(*  Title:      Pure/Tools/class_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Type classes, simulated by locales.
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
  val the_instances: theory -> class -> (string * string) list
  val the_inst_sign: theory -> class * string -> (string * sort) list * (string * typ) list
  val get_classtab: theory -> (string list * (string * string) list) Symtab.table

  val print_classes: theory -> unit
  val intro_classes_tac: thm list -> tactic
  val default_intro_classes_tac: thm list -> tactic

  type sortcontext = (string * sort) list
  datatype classlookup = Instance of (class * string) * classlookup list list
                       | Lookup of class list * (string * int)
  val extract_sortctxt: theory -> typ -> sortcontext
  val extract_classlookup: theory -> string * typ -> classlookup list list
  val extract_classlookup_inst: theory -> class * string -> class -> classlookup list list
end;

structure ClassPackage: CLASS_PACKAGE =
struct


(* theory data *)

type class_data = {
  name_locale: string,
  name_axclass: string,
  intro: thm option,
  var: string,
  consts: (string * typ) list,
  insts: (string * string) list (* [type constructor ~> theory name] *)
};

structure ClassData = TheoryDataFun (
  struct
    val name = "Pure/classes";
    type T = class_data Graph.T * (class Symtab.table * string Symtab.table);
    val empty = (Graph.empty, (Symtab.empty, Symtab.empty));
    val copy = I;
    val extend = I;
    fun merge _ ((t1, (c1, l1)), (t2, (c2, l2)))=
      (Graph.merge (op =) (t1, t2),
       (Symtab.merge (op =) (c1, c2), Symtab.merge (op =) (l1, l2)));
    fun print thy (gr, _) =
      let
        fun pretty_class gr (name, {name_locale, name_axclass, intro, var, consts, insts}) =
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
              :: map (fn (c, ty) => Pretty.str (c ^ " :: " ^ Sign.string_of_typ thy ty)) consts
            ),
            (Pretty.block o Pretty.fbreaks) (
              Pretty.str "instances: "
              :: map (fn (tyco, thyname) => Pretty.str (tyco ^ ", in theory " ^ thyname)) insts
            )
          ]
      in
        (Pretty.writeln o Pretty.chunks o map (pretty_class gr)
          o AList.make (Graph.get_node gr) o Library.flat o Graph.strong_conn) gr
      end;
  end
);

val _ = Context.add_setup ClassData.init;
val print_classes = ClassData.print;


(* queries *)

val lookup_class_data = try o Graph.get_node o fst o ClassData.get;
val lookup_const_class = Symtab.lookup o fst o snd o ClassData.get;
val lookup_locale_class = Symtab.lookup o snd o snd o ClassData.get;

fun the_class_data thy class =
  case lookup_class_data thy class
    of NONE => error ("undeclared operational class " ^ quote class)
     | SOME data => data;

fun is_class thy cls =
  lookup_class_data thy cls
  |> Option.map (not o null o #consts)
  |> the_default false;

fun operational_sort_of thy sort =
  let
    val classes = Sign.classes_of thy;
    fun get_sort class =
      if is_class thy class
      then [class]
      else operational_sort_of thy (Sorts.superclasses classes class);
  in
    map get_sort sort
    |> Library.flat
    |> Sorts.norm_sort classes
  end;

fun the_superclasses thy class =
  if is_class thy class
  then
    Sorts.superclasses (Sign.classes_of thy) class
    |> operational_sort_of thy
  else
    error ("no syntactic class: " ^ class);

fun get_superclass_derivation thy (subclass, superclass) =
  if subclass = superclass
    then SOME [subclass]
    else case Graph.find_paths ((fst o ClassData.get) thy) (subclass, superclass)
      of [] => NONE
       | (p::_) => (SOME o filter (is_class thy)) p;

fun the_ancestry thy classes =
  let
    fun ancestry class anc =
      anc
      |> cons class
      |> fold ancestry (the_superclasses thy class);
  in fold ancestry classes [] end;

fun the_intros thy =
  let
    val gr = (fst o ClassData.get) thy;
  in (List.mapPartial (#intro o Graph.get_node gr) o Graph.keys) gr end;

fun subst_clsvar v ty_subst =
  map_type_tfree (fn u as (w, _) =>
    if w = v then ty_subst else TFree u);

fun the_consts_sign thy class =
  let
    val data = the_class_data thy class
  in (#var data, #consts data) end;

val the_instances =
  #insts oo the_class_data;

fun the_inst_sign thy (class, tyco) =
  let
    val _ = if is_class thy class then () else error ("no syntactic class: " ^ class);
    val arity =
      Sorts.mg_domain (Sign.classes_arities_of thy) tyco [class]
      |> map (operational_sort_of thy);
    val clsvar = (#var o the_class_data thy) class;
    val const_sign = (snd o the_consts_sign thy) class;
    fun add_var sort used =
      let
        val v = hd (Term.invent_names used "'a" 1)
      in ((v, sort), v::used) end;
    val (vsorts, _) =
      []
      |> fold (fn (_, ty) => curry (gen_union (op =))
           ((map (fst o fst) o typ_tvars) ty @ (map fst o typ_tfrees) ty)) const_sign
      |> fold_map add_var arity;
    val ty_inst = Type (tyco, map (fn (v, sort) => TVar ((v, 0), sort)) vsorts);
    val inst_signs = map (apsnd (subst_clsvar clsvar ty_inst)) const_sign;
  in (vsorts, inst_signs) end;

fun get_classtab thy =
  Graph.fold_nodes
    (fn (class, { consts = consts, insts = insts, ... }) =>
      Symtab.update_new (class, (map fst consts, insts)))
       ((fst o ClassData.get) thy) Symtab.empty;


(* updaters *)

fun add_class_data (class, (superclasses, name_locale, name_axclass, intro, var, consts)) =
  ClassData.map (fn (classtab, (consttab, loctab)) => (
    classtab
    |> Graph.new_node (class, {
         name_locale = name_locale,
         name_axclass = name_axclass,
         intro = intro,
         var = var,
         consts = consts,
         insts = []
       })
    |> fold (curry Graph.add_edge_acyclic class) superclasses,
    (consttab
    |> fold (fn (c, _) => Symtab.update (c, class)) consts,
    loctab
    |> Symtab.update (name_locale, class))
  ));

fun add_inst_data (class, inst) =
  (ClassData.map o apfst o Graph.map_node class)
    (fn {name_locale, name_axclass, intro, var, consts, insts}
      => {
           name_locale = name_locale,
           name_axclass = name_axclass,
           intro = intro,
           var = var,
           consts = consts,
           insts = insts @ [inst]
          });


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

fun class_intros thy =
  AxClass.class_intros thy @ the_intros thy;

fun intro_classes_tac facts st =
  (ALLGOALS (Method.insert_tac facts THEN'
      REPEAT_ALL_NEW (resolve_tac (class_intros (Thm.theory_of_thm st))))
    THEN Tactic.distinct_subgoals_tac) st;

fun default_intro_classes_tac [] = intro_classes_tac []
  | default_intro_classes_tac _ = Tactical.no_tac;    (*no error message!*)

fun default_tac rules ctxt facts =
  HEADGOAL (Method.some_rule_tac rules ctxt facts) ORELSE
    default_intro_classes_tac facts;


(* classes and instances *)

local

fun intro_incr thy name expr =
  let
    fun fish_thm basename =
      try (PureThy.get_thm thy) ((Name o NameSpace.append basename) "intro");
  in if expr = Locale.empty
    then fish_thm name
    else fish_thm (name ^ "_axioms")
  end;

fun add_locale opn name expr body thy =
  thy
  |> Locale.add_locale opn name expr body
  ||>> `(fn thy => intro_incr thy name expr)
  |-> (fn (ctxt, intro) => pair ((Sign.full_name thy name, intro), ctxt));

fun add_locale_i opn name expr body thy =
  thy
  |> Locale.add_locale_i opn name expr body
  ||>> `(fn thy => intro_incr thy name expr)
  |-> (fn (ctxt, intro) => pair ((name, intro), ctxt));

fun add_axclass_i (name, supsort) axs thy =
  let
    fun rearrange_axioms ((name, atts), ts) =
      map (rpair atts o pair "") ts
  in
    thy
    |> AxClass.add_axclass_i (name, supsort)
          ((Library.flat o map rearrange_axioms) axs)
    |-> (fn { intro, axioms } =>
              pair (Sign.full_name thy name, (intro, axioms)))
  end;

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
      |> Sorts.certify_sort (Sign.classes_of thy)
      |> null ? K (Sign.defaultS thy);
    val supcs = (Library.flat o map (snd o the_consts_sign thy) o the_ancestry thy)
      supclasses;
    val expr = if null supclasses
      then Locale.empty
      else
       (Locale.Merge o map (Locale.Locale o #name_locale o the_class_data thy)) supclasses;
    fun extract_tyvar_consts thy name_locale =
      let
        fun extract_tyvar_name thy tys =
          fold (curry add_typ_tfrees) tys []
          |> (fn [(v, sort)] =>
                    if Sorts.sort_le (Sign.classes_of thy) (swap (sort, supsort))
                    then v
                    else error ("illegal sort constraint on class type variable: " ^ Sign.string_of_sort thy sort)
               | [] => error ("no class type variable")
               | vs => error ("more than one type variable: " ^ (commas o map (Sign.string_of_typ thy o TFree)) vs))
        val consts1 =
          Locale.parameters_of thy name_locale
          |> map (apsnd Syntax.unlocalize_mixfix)
        val v = (extract_tyvar_name thy o map (snd o fst)) consts1;
        val consts2 = map ((apfst o apsnd) (subst_clsvar v (TFree (v, [])))) consts1;
      in (v, chop (length supcs) consts2) end;
    fun add_consts v raw_cs_sup raw_cs_this thy =
      let
        val mapp_sub = map2 (fn ((c, _), _) => pair c) raw_cs_sup supcs
        fun add_global_const ((c, ty), syn) thy =
          thy
          |> Sign.add_consts_i [(c, ty |> subst_clsvar v (TFree (v, Sign.defaultS thy)), syn)]
          |> `(fn thy => (c, (Sign.intern_const thy c, ty)))
      in
        thy
        |> fold_map add_global_const raw_cs_this
        |-> (fn mapp_this => pair (mapp_sub @ mapp_this, map snd mapp_this))
      end;
    fun extract_assumes thy name_locale cs_mapp =
      let
        val subst_assume =
          map_aterms (fn Free (c, ty) => Const ((fst o the o AList.lookup (op =) cs_mapp) c, ty)
                       | t => t)
        fun prep_asm ((name, atts), ts) =
          ((name, map (Attrib.attribute thy) atts), map subst_assume ts)
      in
        (map prep_asm o Locale.local_asms_of thy) name_locale
      end;
    fun add_global_constraint v class (c, ty) thy =
      thy
      |> Sign.add_const_constraint_i (c, SOME (subst_clsvar v (TFree (v, [class])) ty));
    fun mk_const thy class v (c, ty) =
      Const (c, subst_clsvar v (TFree (v, [class])) ty);
  in
    thy
    |> add_locale bname expr raw_elems
    |-> (fn ((name_locale, intro), ctxt) =>
          `(fn thy => extract_tyvar_consts thy name_locale)
    #-> (fn (v, (raw_cs_sup, raw_cs_this)) =>
          add_consts v raw_cs_sup raw_cs_this
    #-> (fn (cs_map, cs_this) =>
          `(fn thy => extract_assumes thy name_locale cs_map)
    #-> (fn loc_axioms =>
          add_axclass_i (bname, supsort) loc_axioms
    #-> (fn (name_axclass, (_, ax_axioms)) =>
          fold (add_global_constraint v name_axclass) cs_this
    #> add_class_data (name_locale, (supclasses, name_locale, name_axclass, intro, v, cs_this))
    #> prove_interpretation_i (NameSpace.base name_locale, [])
          (Locale.Locale name_locale) (map (SOME o mk_const thy name_axclass v) (supcs @ cs_this))
          ((ALLGOALS o resolve_tac) ax_axioms)
    #> pair ctxt
    )))))
  end;

in

val class = gen_class (add_locale true) intern_class;
val class_i = gen_class (add_locale_i true) certify_class;

end; (* local *)

local

fun lift_local_theory_yield f thy =
  thy
  |> LocalTheory.init NONE
  |> f
  ||>> LocalTheory.exit
  |-> (fn (x, _) => pair x);

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
          if AList.defined (op =) ((#insts o the_class_data thy) class) tyco
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
      in (map (apsnd subst_ty) o #consts) data end;
    val cs = (Library.flat o map get_consts) classes;
    fun get_remove_contraint c thy =
      let
        val ty = Sign.the_const_constraint thy c;
      in
        thy
        |> Sign.add_const_constraint_i (c, NONE)
        |> pair (c, Type.unvarifyT ty)
      end;
    fun check_defs raw_defs c_req thy =
      let
        val thy' = (Sign.add_arities_i [(tyco, asorts, sort)] o Theory.copy) thy;
        fun get_c raw_def =
          (fst o Sign.cert_def pp o tap_def thy' o snd) raw_def;
        val c_given = map get_c raw_defs;
        fun eq_c ((c1, ty1), (c2, ty2)) =
          let
            val ty1' = Type.varifyT ty1;
            val ty2' = Type.varifyT ty2;
          in
            c1 = c2
            andalso Sign.typ_instance thy' (ty1', ty2')
            andalso Sign.typ_instance thy' (ty2', ty1')
          end;
        val _ = case fold (remove eq_c) c_req c_given
         of [] => ()
          | cs => error ("superfluous definition(s) given for "
                    ^ (commas o map (fn (c, ty) => quote (c ^ "::" ^ Sign.string_of_typ thy' ty))) cs);
        val _ = case fold (remove eq_c) c_given c_req
         of [] => ()
          | cs => error ("no definition(s) given for "
                    ^ (commas o map (fn (c, ty) => quote (c ^ "::" ^ Sign.string_of_typ thy' ty))) cs);
      in thy end;
    fun mangle_alldef_name tyco sort =
      Thm.def_name ((space_implode "_" o map NameSpace.base) sort ^ "_" ^ NameSpace.base tyco);
    fun note_all tyco sort thms thy =
      thy
      |> PureThy.note_thmss_i PureThy.internalK [((name, atts), [(thms, [])])]
      |> snd;
    fun after_qed cs thy =
      thy
      |> fold Sign.add_const_constraint_i (map (apsnd SOME) cs)
      |> fold (fn class => add_inst_data (class, (tyco, Context.theory_name thy))) sort;
  in
    theory
    |> check_defs raw_defs cs
    |> fold_map get_remove_contraint (map fst cs)
    ||>> add_defs tyco (map (pair NONE) raw_defs)
    |-> (fn (cs, defnames) => note_all tyco sort defnames #> pair cs)
    |-> (fn cs => do_proof (after_qed cs) arity)
  end;

fun instance_arity' do_proof = gen_instance_arity AxClass.read_arity Attrib.attribute add_defs_overloaded
  (fn thy => fn t => (snd o read_axm thy) ("", t)) do_proof;
fun instance_arity_i' do_proof = gen_instance_arity AxClass.cert_arity (K I) add_defs_overloaded_i
  (K I) do_proof;
val setup_proof = AxClass.instance_arity_i;
fun tactic_proof tac after_qed arity = AxClass.add_inst_arity_i arity tac #> after_qed;

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
    val loc_expr = if null sort
      then Locale.empty
      else
       (Locale.Merge o map (Locale.Locale o #name_locale o the_class_data theory)) sort;
    fun after_qed thmss thy =
      (writeln "---"; (Pretty.writeln o Display.pretty_thms o Library.flat) thmss; writeln "---"; fold (fn supclass =>
        AxClass.add_inst_subclass_i (class, supclass)
          (ALLGOALS (K (intro_classes_tac [])) THEN
            (ALLGOALS o resolve_tac o Library.flat) thmss)
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

fun extract_sortctxt thy ty =
  (typ_tfrees o fst o Type.freeze_thaw_type) ty
  |> map (apsnd (operational_sort_of thy))
  |> filter (not o null o snd);

datatype classlookup = Instance of (class * string) * classlookup list list
                    | Lookup of class list * (string * int)

fun extract_lookup thy sortctxt raw_typ_def raw_typ_use =
  let
    val typ_def = Type.varifyT raw_typ_def;
    val typ_use = Type.varifyT raw_typ_use;
    val match_tab = Sign.typ_match thy (typ_def, typ_use) Vartab.empty;
    fun get_first_index f =
      let
        fun get _ [] = NONE
          | get i (x::xs) = 
              case f x
               of NONE => get (i+1) xs
                | SOME y => SOME (i, y)
      in get 0 end;
    fun tab_lookup vname = (the o Vartab.lookup match_tab) (vname, 0);
    fun mk_class_deriv thy subclasses superclass =
      let
        val (i, (subclass::deriv)) = (the oo get_first_index) (fn subclass =>
            get_superclass_derivation thy (subclass, superclass)
          ) subclasses;
        val i' = if length subclasses = 1 then ~1 else i;
      in (rev deriv, i') end;
    fun mk_lookup (sort_def, (Type (tycon, tys))) =
          let
            val arity_lookup = map2 (curry mk_lookup)
              (map (operational_sort_of thy) (Sorts.mg_domain (Sign.classes_arities_of thy) tycon sort_def)) tys
          in map (fn class => Instance ((class, tycon), arity_lookup)) sort_def end
      | mk_lookup (sort_def, TVar ((vname, _), sort_use)) =
          let
            fun mk_look class =
              let val (deriv, classindex) = mk_class_deriv thy (operational_sort_of thy sort_use) class
              in Lookup (deriv, (vname, classindex)) end;
          in map mk_look sort_def end;
  in
    sortctxt
(*     |> print  *)
    |> map (tab_lookup o fst)
(*     |> print  *)
    |> map (apfst (operational_sort_of thy))
(*     |> print  *)
    |> filter (not o null o fst)
(*     |> print  *)
    |> map mk_lookup
(*     |> print  *)
  end;

fun extract_classlookup thy (c, raw_typ_use) =
  let
    val raw_typ_def = Sign.the_const_constraint thy c;
    val typ_def = Type.varifyT raw_typ_def;
    fun reorder_sortctxt ctxt =
      case lookup_const_class thy c
       of NONE => ctxt
        | SOME class =>
            let
              val data = the_class_data thy class;
              val sign = (Type.varifyT o the o AList.lookup (op =) (#consts data)) c;
              val match_tab = Sign.typ_match thy (sign, typ_def) Vartab.empty;
              val v : string = case Vartab.lookup match_tab (#var data, 0)
                of SOME (_, TVar ((v, _), _)) => v;
            in
              (v, (the o AList.lookup (op =) ctxt) v) :: AList.delete (op =) v ctxt
            end;
  in
    extract_lookup thy
      (reorder_sortctxt (extract_sortctxt thy ((fst o Type.freeze_thaw_type) raw_typ_def)))
      raw_typ_def raw_typ_use
  end;

fun extract_classlookup_inst thy (class, tyco) supclass =
  let
    fun mk_typ class = Type (tyco, (map TFree o fst o the_inst_sign thy) (class, tyco))
    val typ_def = mk_typ supclass;
    val typ_use = mk_typ class;
  in
    extract_lookup thy (extract_sortctxt thy typ_def) typ_def typ_use
  end;


(* toplevel interface *)

local

structure P = OuterParse
and K = OuterKeyword

in

val (classK, instanceK) = ("class", "instance")

fun wrap_add_instance_subclass (class, sort) thy =
  case Sign.read_sort thy sort
   of [class'] =>
      if (is_some o lookup_class_data thy o Sign.intern_class thy) class
        andalso (is_some o lookup_class_data thy o Sign.intern_class thy) class'
      then
        instance_sort (class, sort) thy
      else
        AxClass.instance_subclass (class, sort) thy
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

val classP =
  OuterSyntax.command classK "operational type classes" K.thy_decl (
    P.name --| P.$$$ "="
    -- Scan.optional (Scan.repeat1 (P.name --| P.$$$ "+")) []
    -- Scan.optional (P.!!! (Scan.repeat1 P.context_element)) []
      >> (Toplevel.theory_context
          o (fn ((bname, supclasses), elems) => class bname supclasses elems)));

val instanceP =
  OuterSyntax.command instanceK "prove type arity or subclass relation" K.thy_goal ((
      P.xname -- ((P.$$$ "\\<subseteq>" || P.$$$ "<") |-- P.!!! P.xname) >> wrap_add_instance_subclass
      || P.opt_thm_name ":" -- (parse_inst -- Scan.repeat (P.opt_thm_name ":" -- P.prop))
           >> (fn (("", []), (((tyco, asorts), sort), [])) => AxClass.instance_arity I (tyco, asorts, sort)
                | (natts, (inst, defs)) => instance_arity inst natts defs)
    ) >> (Toplevel.print oo Toplevel.theory_to_proof));

val _ = OuterSyntax.add_parsers [classP, instanceP];

val _ = Context.add_setup (Method.add_methods
 [("intro_classes", Method.no_args (Method.METHOD intro_classes_tac),
    "back-chain introduction rules of classes"),
  ("default", Method.thms_ctxt_args (Method.METHOD oo default_tac), "apply some intro/elim rule")]);

end; (* local *)

end; (* struct *)
