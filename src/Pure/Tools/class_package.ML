(*  Title:      Pure/Tools/class_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Haskell98-like operational view on type classes.
*)

signature CLASS_PACKAGE =
sig
  val add_classentry: class -> string list -> string list -> theory -> theory
  val the_consts: theory -> class -> string list
  val the_tycos: theory -> class -> (string * string) list

  val syntactic_sort_of: theory -> sort -> sort
  val get_arities: theory -> sort -> string -> sort list
  val get_superclasses: theory -> class -> class list
  val get_const_sign: theory -> string -> string -> typ
  val get_inst_consts_sign: theory -> string * class -> (string * typ) list
  val lookup_const_class: theory -> string -> class option
  val get_classtab: theory -> (string list * (string * string) list) Symtab.table

  type sortcontext = (string * sort) list
  datatype sortlookup = Instance of (class * string) * sortlookup list list
                      | Lookup of class list * (string * int)
  val extract_sortctxt: theory -> typ -> sortcontext
  val extract_sortlookup: theory -> typ * typ -> sortlookup list list
end;

structure ClassPackage: CLASS_PACKAGE =
struct


(* data kind 'Pure/classes' *)

type class_data = {
  locale_name: string,
  axclass_name: string,
  consts: string list,
  tycos: (string * string) list
};

structure ClassesData = TheoryDataFun (
  struct
    val name = "Pure/classes";
    type T = class_data Symtab.table * class Symtab.table;
    val empty = (Symtab.empty, Symtab.empty);
    val copy = I;
    val extend = I;
    fun merge _ ((t1, r1), (t2, r2))=
      (Symtab.merge (op =) (t1, t2),
       Symtab.merge (op =) (r1, r2));
    fun print _ (tab, _) = (Pretty.writeln o Pretty.chunks) (map Pretty.str (Symtab.keys tab));
  end
);

val lookup_class_data = Symtab.lookup o fst o ClassesData.get;
val lookup_const_class = Symtab.lookup o snd o ClassesData.get;

fun get_class_data thy class =
  case lookup_class_data thy class
    of NONE => error ("undeclared class " ^ quote class)
     | SOME data => data;

fun put_class_data class data =
  ClassesData.map (apfst (Symtab.update (class, data)));
fun add_const class const =
  ClassesData.map (apsnd (Symtab.update (const, class)));


(* name mangling *)

fun get_locale_for_class thy class =
  #locale_name (get_class_data thy class);

fun get_axclass_for_class thy class =
  #axclass_name (get_class_data thy class);


(* assign consts to type classes *)

local

fun gen_add_consts prep_class prep_const (raw_class, raw_consts_new) thy =
  let
    val class = prep_class thy raw_class;
    val consts_new = map (prep_const thy) raw_consts_new;
    val {locale_name, axclass_name, consts, tycos} =
      get_class_data thy class;
  in
    thy
    |> put_class_data class {
         locale_name = locale_name,
         axclass_name = axclass_name,
         consts = consts @ consts_new,
         tycos = tycos
       }
    |> fold (add_const class) consts_new
  end;

in

val add_consts = gen_add_consts Sign.intern_class Sign.intern_const;
val add_consts_i = gen_add_consts (K I) (K I);

end; (* local *)

val the_consts = #consts oo get_class_data;


(* assign type constructors to type classes *)

local

fun gen_add_tycos prep_class prep_type (raw_class, raw_tycos_new) thy =
  let
    val class = prep_class thy raw_class
    val tycos_new = map (prep_type thy) raw_tycos_new
    val {locale_name, axclass_name, consts, tycos} =
      get_class_data thy class
  in
    thy
    |> put_class_data class {
         locale_name = locale_name,
         axclass_name = axclass_name,
         consts = consts,
         tycos = tycos @ tycos_new
       }
  end;

in

fun add_tycos xs thy =
  gen_add_tycos Sign.intern_class (rpair (Context.theory_name thy) oo Sign.intern_type) xs thy;
val add_tycos_i = gen_add_tycos (K I) (K I);

end; (* local *)

val the_tycos = #tycos oo get_class_data;


(* class queries *)

fun is_class thy cls = lookup_class_data thy cls |> Option.map (not o null o #consts) |> the_default false;

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

fun get_arities thy sort tycon =
  Sorts.mg_domain (Sign.classes_arities_of thy) tycon sort
  |> map (syntactic_sort_of thy);

fun get_superclasses thy class =
  Sorts.superclasses (Sign.classes_of thy) class
  |> syntactic_sort_of thy;


(* instance queries *)

fun get_const_sign thy tvar const =
  let
    val class = (the o lookup_const_class thy) const;
    val (ty, thaw) = (Type.freeze_thaw_type o Sign.the_const_constraint thy) const;
    val tvars_used = Term.add_tfreesT ty [];
    val tvar_rename = hd (Term.invent_names (map fst tvars_used) tvar 1);
  in
    ty
    |> map_type_tfree (fn (tvar', sort) =>
          if Sorts.sort_eq (Sign.classes_of thy) ([class], sort)
          then TFree (tvar, [])
          else if tvar' = tvar
          then TVar ((tvar_rename, 0), sort)
          else TFree (tvar', sort))
    |> thaw
  end;

fun get_inst_consts_sign thy (tyco, class) =
  let
    val consts = the_consts thy class;
    val arities = get_arities thy [class] tyco;
    val const_signs = map (get_const_sign thy "'a") consts;
    val vars_used = fold (fn ty => curry (gen_union (op =))
      (map fst (typ_tfrees ty) |> remove (op =) "'a")) const_signs [];
    val vars_new = Term.invent_names vars_used "'a" (length arities);
    val typ_arity = Type (tyco, map2 (curry TFree) vars_new arities);
    val instmem_signs =
      map (typ_subst_TVars [(("'a", 0), typ_arity)]) const_signs;
  in consts ~~ instmem_signs end;

fun get_classtab thy =
  Symtab.fold
    (fn (class, { consts = consts, tycos = tycos, ... }) =>
      Symtab.update_new (class, (consts, tycos)))
       (fst (ClassesData.get thy)) Symtab.empty;


(* extracting dictionary obligations from types *)

type sortcontext = (string * sort) list;

fun extract_sortctxt thy ty =
  (typ_tfrees o Type.no_tvars) ty
  |> map (apsnd (syntactic_sort_of thy))
  |> filter (not o null o snd);

datatype sortlookup = Instance of (class * string) * sortlookup list list
                    | Lookup of class list * (string * int)

fun extract_sortlookup thy (raw_typ_def, raw_typ_use) =
  let
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
      of (subclass::deriv) => ((rev o filter (is_class thy)) deriv, find_index_eq subclass subclasses);
    fun mk_lookup (sort_def, (Type (tycon, tys))) =
          let
            val arity_lookup = map2 (curry mk_lookup)
              (map (syntactic_sort_of thy) (Sorts.mg_domain (Sign.classes_arities_of thy) tycon sort_def)) tys
          in map (fn class => Instance ((class, tycon), arity_lookup)) sort_def end
      | mk_lookup (sort_def, TVar ((vname, _), sort_use)) =
          let
            fun mk_look class =
              let val (deriv, classindex) = mk_class_deriv thy sort_use class
              in Lookup (deriv, (vname, classindex)) end;
          in map mk_look sort_def end;
  in
    extract_sortctxt thy ((fst o Type.freeze_thaw_type) raw_typ_def)
    |> map (tab_lookup o fst)
    |> map (apfst (syntactic_sort_of thy))
    |> filter (not o null o fst)
    |> map mk_lookup
  end;


(* intermediate auxiliary *)

fun add_classentry raw_class raw_consts raw_tycos thy =
  let
    val class = Sign.intern_class thy raw_class;
  in
    thy
    |> put_class_data class {
         locale_name = "",
         axclass_name = class,
         consts = [],
         tycos = []
       }
    |> add_consts (class, raw_consts)
    |> add_tycos (class, raw_tycos)
  end;
  

(* setup *)

val _ = Context.add_setup [ClassesData.init];

end; (* struct *)
