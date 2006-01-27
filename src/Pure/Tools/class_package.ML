(*  Title:      Pure/Tools/class_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Type classes, simulated by locales.
*)

signature CLASS_PACKAGE =
sig
  val add_class: bstring -> class list -> Element.context list -> theory
    -> ProofContext.context * theory
  val add_class_i: bstring -> class list -> Element.context_i list -> theory
    -> ProofContext.context * theory
  val add_instance_arity: (xstring * string list) * string
    -> ((bstring * string) * Attrib.src list) list
    -> theory -> Proof.state
  val add_instance_arity_i: (string * sort list) * sort
    -> ((bstring * term) * attribute list) list
    -> theory -> Proof.state
  val add_classentry: class -> xstring list -> xstring list -> theory -> theory

  val intern_class: theory -> xstring -> string
  val extern_class: theory -> string -> xstring
  val certify_class: theory -> class -> class
  val syntactic_sort_of: theory -> sort -> sort
  val the_superclasses: theory -> class -> class list
  val the_consts_sign: theory -> class -> string * (string * typ) list
  val lookup_const_class: theory -> string -> class option
  val the_instances: theory -> class -> (string * string) list
  val the_inst_sign: theory -> class * string -> (string * sort) list * (string * typ) list
  val get_classtab: theory -> (string list * (string * string) list) Symtab.table
  val print_classes: theory -> unit

  type sortcontext = (string * sort) list
  datatype sortlookup = Instance of (class * string) * sortlookup list list
                      | Lookup of class list * (string * int)
  val extract_sortctxt: theory -> typ -> sortcontext
  val extract_sortlookup: theory -> string * typ -> sortlookup list list
end;

structure ClassPackage: CLASS_PACKAGE =
struct


(* theory data *)

type class_data = {
  superclasses: class list,
  name_locale: string,
  name_axclass: string,
  var: string,
  consts: (string * typ) list,
  insts: (string * string) list
};

structure ClassData = TheoryDataFun (
  struct
    val name = "Pure/classes";
    type T = class_data Symtab.table * class Symtab.table;
    val empty = (Symtab.empty, Symtab.empty);
    val copy = I;
    val extend = I;
    fun merge _ ((t1, r1), (t2, r2))=
      (Symtab.merge (op =) (t1, t2),
       Symtab.merge (op =) (r1, r2));
    fun print thy (tab, _) =
      let
        fun pretty_class (name, {superclasses, name_locale, name_axclass, var, consts, insts}) =
          (Pretty.block o Pretty.fbreaks) [
            Pretty.str ("class " ^ name ^ ":"),
            (Pretty.block o Pretty.fbreaks) (
              Pretty.str "superclasses: "
              :: map Pretty.str superclasses
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
        (Pretty.writeln o Pretty.chunks o map pretty_class o Symtab.dest) tab
      end;
  end
);

val _ = Context.add_setup ClassData.init;
val print_classes = ClassData.print;

val lookup_class_data = Symtab.lookup o fst o ClassData.get;
val lookup_const_class = Symtab.lookup o snd o ClassData.get;

fun get_class_data thy class =
  case lookup_class_data thy class
    of NONE => error ("undeclared operational class " ^ quote class)
     | SOME data => data;

fun add_class_data (class, (superclasses, name_locale, name_axclass, classvar, consts)) =
  ClassData.map (fn (classtab, consttab) => (
    classtab 
    |> Symtab.update (class, {
         superclasses = superclasses,
         name_locale = name_locale,
         name_axclass = name_axclass,
         var = classvar,
         consts = consts,
         insts = []
       }),
    consttab
    |> fold (fn (c, _) => Symtab.update (c, class)) consts
  ));

fun add_inst_data (class, inst) =
  (ClassData.map o apfst o Symtab.map_entry class)
    (fn {superclasses, name_locale, name_axclass, var, consts, insts}
      => {
           superclasses = superclasses,
           name_locale = name_locale,
           name_axclass = name_axclass,
           var = var,
           consts = consts,
           insts = insts @ [inst]
          });


(* name handling *)

fun certify_class thy class =
  (get_class_data thy class; class);

fun intern_class thy raw_class =
  certify_class thy (Sign.intern_class thy raw_class);

fun extern_class thy class =
  Sign.extern_class thy (certify_class thy class);


(* classes and instances *)

fun subst_clsvar v ty_subst =
  map_type_tfree (fn u as (w, _) =>
    if w = v then ty_subst else TFree u);

local

fun gen_add_class add_locale prep_class bname raw_supclasses raw_body thy =
  let
    val supclasses = map (prep_class thy) raw_supclasses;
    val supsort = case map (#name_axclass o get_class_data thy) supclasses
     of [] => Sign.defaultS thy
      | sort => Sorts.certify_sort (Sign.classes_of thy) sort;
    val locexpr = case supclasses
     of [] => Locale.empty
      | _ => (Locale.Merge o map (Locale.Locale o #name_locale o get_class_data thy))
                supclasses;
    fun extract_assumes c_adds elems =
      let
        fun subst_free ts =
          let
            val get_ty = the o AList.lookup (op =) (fold Term.add_frees ts []);
            val subst_map = map (fn (c, (c', _)) =>
              (Free (c, get_ty c), Const (c', get_ty c))) c_adds;
          in map (subst_atomic subst_map) ts end;
      in
        elems
        |> (map o List.mapPartial)
            (fn (Element.Assumes asms) => (SOME o map (map fst o snd)) asms
              | _ => NONE)
        |> Library.flat o Library.flat o Library.flat
        |> subst_free
      end;
    fun extract_tyvar_name thy tys =
      fold (curry add_typ_tfrees) tys []
      |> (fn [(v, sort)] =>
                if Sorts.sort_le (Sign.classes_of thy) (swap (sort, supsort))
                then v 
                else error ("illegal sort constraint on class type variable: " ^ Sign.string_of_sort thy sort)
           | [] => error ("no class type variable")
           | vs => error ("more than one type variable: " ^ (commas o map (Sign.string_of_typ thy o TFree)) vs))
    fun extract_tyvar_consts thy (import_elems, body_elems) =
      let
        fun get_elems elems =
          elems
          |> Library.flat
          |> List.mapPartial
               (fn (Element.Fixes consts) => SOME consts
                 | _ => NONE)
          |> Library.flat
          |> map (fn (c, ty, syn) =>
               ((c, the ty), (Syntax.unlocalize_mixfix o Syntax.fix_mixfix c) syn))
        val import_consts = get_elems import_elems;
        val body_consts = get_elems body_elems;
        val v = extract_tyvar_name thy (map (snd o fst) (import_consts @ body_consts));
        fun subst_ty cs =
          map ((apfst o apsnd) (subst_clsvar v (TFree (v, [])))) cs;
        val import_cs = subst_ty import_consts;
        val body_cs = subst_ty body_consts;
      in (v, (import_cs, body_cs)) end;
    fun add_global_const v ((c, ty), syn) thy =
      thy
      |> Sign.add_consts_i [(c, ty |> subst_clsvar v (TFree (v, Sign.defaultS thy)), syn)]
      |> `(fn thy => (c, (Sign.intern_const thy c, ty)))
    fun add_global_constraint v class (_, (c, ty)) thy =
      thy
      |> Sign.add_const_constraint_i (c, subst_clsvar v (TVar ((v, 0), [class])) ty);
    fun interpret name_locale cs ax_axioms thy =
      thy
      |> Locale.interpretation (NameSpace.base name_locale, [])
           (Locale.Locale name_locale)
             (map (fn ((c, _), _) => SOME (Sign.intern_const thy c)) cs)
      |> Proof.global_terminal_proof (Method.Basic (Method.fact ax_axioms), NONE);
    fun print_ctxt ctxt elem = 
      map Pretty.writeln (Element.pretty_ctxt ctxt elem)
  in
    thy
    |> add_locale bname locexpr raw_body
    |-> (fn ((import_elems, body_elems), ctxt) =>
       `(fn thy => Locale.intern thy bname)
    #-> (fn name_locale =>
          `(fn thy => extract_tyvar_consts thy (import_elems, body_elems))
    #-> (fn (v, (c_global, c_defs)) =>
          fold_map (add_global_const v) c_defs
    #-> (fn c_adds =>
          AxClass.add_axclass_i (bname, supsort)
            (map (Thm.no_attributes o pair "") (extract_assumes c_adds (import_elems @ body_elems)))
    #-> (fn { axioms = ax_axioms : thm list, ...} =>
          `(fn thy => Sign.intern_class thy bname)
    #-> (fn name_axclass =>
          fold (add_global_constraint v name_axclass) c_adds
    #> add_class_data (name_locale, (supclasses, name_locale, name_axclass, v, map snd c_adds))
    #> tap (fn _ => (map o map) (print_ctxt ctxt) import_elems)
    #> tap (fn _ => (map o map) (print_ctxt ctxt) body_elems)
    #> interpret name_locale (c_global @ c_defs) ax_axioms
    ))))))
  end;

in

val add_class = gen_add_class (Locale.add_locale_context true) intern_class;
val add_class_i = gen_add_class (Locale.add_locale_context_i true) certify_class;

end; (* local *)

fun gen_instance_arity prep_arity add_defs tap_def raw_arity raw_defs thy = 
  let
    val dest_def = Theory.dest_def (Sign.pp thy) handle TERM (msg, _) => error msg;
    val arity as (tyco, asorts, sort) = prep_arity thy ((fn ((x, y), z) => (x, y, z)) raw_arity);
    val ty_inst = Type (tyco, map2 (curry TVar o rpair 0) (Term.invent_names [] "'a" (length asorts)) asorts)
    fun get_c_req class =
      let
        val data = get_class_data thy class;
        val subst_ty = map_type_tfree (fn (var as (v, _)) =>
          if #var data = v then ty_inst else TFree var)
      in (map (apsnd subst_ty) o #consts) data end;
    val c_req = (Library.flat o map get_c_req) sort;
    fun get_remove_contraint c thy =
      let
        val ty1 = Sign.the_const_constraint thy c;
        val ty2 = Sign.the_const_type thy c;
      in
        thy
        |> Sign.add_const_constraint_i (c, ty2)
        |> pair (c, ty1)
      end;
    fun get_c_given thy = map (fst o dest_def o snd o tap_def thy o fst) raw_defs;
    fun check_defs c_given c_req thy =
      let
        fun eq_c ((c1, ty1), (c2, ty2)) = c1 = c2
          andalso Sign.typ_instance thy (ty1, ty2)
          andalso Sign.typ_instance thy (ty2, ty1);
        val _ = case fold (remove eq_c) c_req c_given
         of [] => ()
          | cs => error ("superfluous definition(s) given for "
                    ^ (commas o map (fn (c, ty) => quote (c ^ "::" ^ Sign.string_of_typ thy ty))) cs);
        val _ = case fold (remove eq_c) c_given c_req
         of [] => ()
          | cs => error ("no definition(s) given for "
                    ^ (commas o map (fn (c, ty) => quote (c ^ "::" ^ Sign.string_of_typ thy ty))) cs);
      in thy end;
    fun after_qed cs =
      fold Sign.add_const_constraint_i cs
      #> fold (fn class => add_inst_data (class, (tyco, Context.theory_name thy))) sort;
  in
    thy
    |> fold_map get_remove_contraint (map fst c_req)
    ||> tap (fn thy => check_defs (get_c_given thy) c_req thy)
    ||> add_defs (true, raw_defs)
    |-> (fn cs => AxClass.instance_arity_i (after_qed cs) arity)
  end;

val add_instance_arity = fn x => gen_instance_arity (AxClass.read_arity) IsarThy.add_defs read_axm x;
val add_instance_arity_i = fn x => gen_instance_arity (AxClass.cert_arity) IsarThy.add_defs_i (K I) x;


(* queries *)

fun is_class thy cls =
  lookup_class_data thy cls
  |> Option.map (not o null o #consts)
  |> the_default false;

fun syntactic_sort_of thy sort =
  let
    val classes = Sign.classes_of thy;
    fun get_sort cls =
      if is_class thy cls
      then [cls]
      else syntactic_sort_of thy (Sorts.superclasses classes cls);
  in
    map get_sort sort
    |> Library.flat
    |> Sorts.norm_sort classes
  end;

fun the_superclasses thy class =
  if is_class thy class
  then
    Sorts.superclasses (Sign.classes_of thy) class
    |> syntactic_sort_of thy
  else
    error ("no syntactic class: " ^ class);

fun the_consts_sign thy class =
  let
    val data = (the oo Symtab.lookup) ((fst o ClassData.get) thy) class
  in (#var data, #consts data) end;

fun lookup_const_class thy =
  Symtab.lookup ((snd o ClassData.get) thy);

fun the_instances thy class =
  (#insts o the o Symtab.lookup ((fst o ClassData.get) thy)) class;

fun the_inst_sign thy (class, tyco) =
  let
    val _ = if is_class thy class then () else error ("no syntactic class: " ^ class);
    val arity = 
      Sorts.mg_domain (Sign.classes_arities_of thy) tyco [class]
      |> map (syntactic_sort_of thy);
    val clsvar = (#var o the o Symtab.lookup ((fst o ClassData.get) thy)) class;
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
  Symtab.fold
    (fn (class, { consts = consts, insts = insts, ... }) =>
      Symtab.update_new (class, (map fst consts, insts)))
       ((fst o ClassData.get) thy) Symtab.empty;


(* extracting dictionary obligations from types *)

type sortcontext = (string * sort) list;

fun extract_sortctxt thy ty =
  (typ_tfrees o fst o Type.freeze_thaw_type) ty
  |> map (apsnd (syntactic_sort_of thy))
  |> filter (not o null o snd);

datatype sortlookup = Instance of (class * string) * sortlookup list list
                    | Lookup of class list * (string * int)

fun extract_sortlookup thy (c, raw_typ_use) =
  let
    val raw_typ_def = Sign.the_const_constraint thy c;
    val typ_def = Type.varifyT raw_typ_def;
    val typ_use = Type.varifyT raw_typ_use;
    val match_tab = Sign.typ_match thy (typ_def, typ_use) Vartab.empty;
    fun tab_lookup vname = (the o Vartab.lookup match_tab) (vname, 0);
    fun get_superclass_derivation (subclasses, superclass) =
      (the oo get_first) (fn subclass =>
        Sorts.class_le_path (Sign.classes_of thy) (subclass, superclass)
      ) subclasses;
    fun mk_class_deriv thy subclasses superclass =
      case get_superclass_derivation (subclasses, superclass)
      of (subclass::deriv) =>
        ((rev o filter (is_class thy)) deriv, find_index_eq subclass subclasses);
    fun mk_lookup (sort_def, (Type (tycon, tys))) =
          let
            val arity_lookup = map2 (curry mk_lookup)
              (map (syntactic_sort_of thy) (Sorts.mg_domain (Sign.classes_arities_of thy) tycon sort_def)) tys
          in map (fn class => Instance ((class, tycon), arity_lookup)) sort_def end
      | mk_lookup (sort_def, TVar ((vname, _), sort_use)) =
          let
            fun mk_look class =
              let val (deriv, classindex) = mk_class_deriv thy (syntactic_sort_of thy sort_use) class
              in Lookup (deriv, (vname, classindex)) end;
          in map mk_look sort_def end;
    fun reorder_sortctxt ctxt =
      case lookup_const_class thy c
       of NONE => ctxt
        | SOME class =>
            let
              val data = (the o Symtab.lookup ((fst o ClassData.get) thy)) class;
              val sign = (Type.varifyT o the o AList.lookup (op =) (#consts data)) c;
              val match_tab = Sign.typ_match thy (sign, typ_def) Vartab.empty;
              val v : string = case Vartab.lookup match_tab (#var data, 0)
                of SOME (_, TVar ((v, _), _)) => v;
            in
              (v, (the o AList.lookup (op =) ctxt) v) :: AList.delete (op =) v ctxt
            end;
  in
    extract_sortctxt thy ((fst o Type.freeze_thaw_type) raw_typ_def)
    |> reorder_sortctxt
    |> map (tab_lookup o fst)
    |> map (apfst (syntactic_sort_of thy))
    |> filter (not o null o fst)
    |> map mk_lookup
  end;


(* intermediate auxiliary *)

fun add_classentry raw_class raw_cs raw_insts thy =
  let
    val class = Sign.intern_class thy raw_class;
    val cs_proto =
      raw_cs
      |> map (Sign.intern_const thy)
      |> map (fn c => (c, Sign.the_const_constraint thy c));
    val used = 
      []
      |> fold (fn (_, ty) => curry (gen_union (op =))
           ((map (fst o fst) o typ_tvars) ty @ (map fst o typ_tfrees) ty)) cs_proto
    val v = hd (Term.invent_names used "'a" 1);
    val cs =
      cs_proto
      |> map (fn (c, ty) => (c, map_type_tvar (fn var as ((tvar', _), sort) =>
          if Sorts.sort_eq (Sign.classes_of thy) ([class], sort)
          then TFree (v, [])
          else TVar var
         ) ty));
    val insts = map (rpair (Context.theory_name thy) o Sign.intern_type thy) raw_insts;
  in
    thy
    |> add_class_data (class, ([], "", class, v, cs))
    |> fold (curry add_inst_data class) insts
  end;


(* toplevel interface *)

local

structure P = OuterParse
and K = OuterKeyword

in

val (classK, instanceK) = ("class", "class_instance")

val classP =
  OuterSyntax.command classK "operational type classes" K.thy_decl
    (P.name --| P.$$$ "="
     -- Scan.optional (Scan.repeat1 (P.name --| P.$$$ "+")) []
     -- Scan.optional (P.!!! (Scan.repeat1 P.context_element)) []
      >> (Toplevel.theory_context
          o (fn ((bname, supclasses), elems) => add_class bname supclasses elems)));

val instanceP =
  OuterSyntax.command instanceK "declare instance for operational type class" K.thy_goal
    (P.xname -- (P.$$$ "::" |-- P.!!! P.arity)
      -- Scan.repeat1 P.spec_name
      >> (Toplevel.print oo Toplevel.theory_to_proof
          o (fn ((tyco, (asorts, sort)), defs) => add_instance_arity ((tyco, asorts), sort) defs)));

val _ = OuterSyntax.add_parsers [classP, instanceP];

end; (* local *)

end; (* struct *)
