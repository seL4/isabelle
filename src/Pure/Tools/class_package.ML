(*  Title:      Pure/Tools/class_package.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Haskell98-like operational view on type classes.
*)

signature CLASS_PACKAGE =
sig
  val add_class: bstring -> Locale.expr -> Element.context list -> theory
    -> ProofContext.context * theory
  val add_class_i: bstring -> Locale.expr -> Element.context_i list -> theory
    -> ProofContext.context * theory
  val add_classentry: class -> xstring list -> xstring list -> theory -> theory
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
val the_consts = #consts oo get_class_data;
val the_tycos = #tycos oo get_class_data;


(* name mangling *)

fun get_locale_for_class thy class =
  #locale_name (get_class_data thy class);

fun get_axclass_for_class thy class =
  #axclass_name (get_class_data thy class);


(* classes *)

local

open Element

fun gen_add_class add_locale bname raw_import raw_body thy =
  let
    fun extract_notes_consts thy elems =
      elems
      |> List.mapPartial
           (fn (Notes notes) => SOME notes
             | _ => NONE)
      |> Library.flat
      |> map (fn (_, facts) => map fst facts)
      |> Library.flat o Library.flat
      |> map prop_of
      |> (fn ts => fold (curry add_term_consts) ts [])
      |> tap (writeln o commas);
    fun extract_tyvar_name thy tys =
      fold (curry add_typ_tfrees) tys []
      |> (fn [(v, [])] => v
           | [(v, sort)] =>
                if Sorts.sort_eq (Sign.classes_of thy) (Sign.defaultS thy, sort)
                then v 
                else error ("sort constraint on class type variable: " ^ Sign.string_of_sort thy sort)
           | [] => error ("no class type variable")
           | vs => error ("more than one type variable: " ^ (commas o map (Sign.string_of_typ thy o TFree)) vs))
    fun extract_tyvar_consts thy elems =
      elems
      |> List.mapPartial
           (fn (Fixes consts) => SOME consts
             | _ => NONE)
      |> Library.flat
      |> map (fn (c, ty, syn) => ((c, the ty), the syn))
      |> `(fn consts => extract_tyvar_name thy (map (snd o fst) consts));
    (* fun remove_local_syntax ((c, ty), _) thy =
      thy
      |> Sign.add_syntax_i [(c, ty, Syntax.NoSyn)]; *)
    fun add_global_const ((c, ty), syn) thy =
      thy
      |> Sign.add_consts_i [(c, ty, syn)]
      |> `(fn thy => Sign.intern_const thy c)
    fun add_axclass bname_axiom locale_pred cs thy =
      thy
      |> AxClass.add_axclass_i (bname, Sign.defaultS thy)
           [Thm.no_attributes (bname_axiom,
              Const (ObjectLogic.judgment_name thy, dummyT) $
                list_comb (Const (locale_pred, dummyT), map (fn c => Const (c, dummyT)) cs)
              |> curry (inferT_axm thy) "locale_pred" |> snd)]
      |-> (fn _ => `(fn thy => Sign.intern_class thy bname))
    fun print_ctxt ctxt elem = 
      map Pretty.writeln (Element.pretty_ctxt ctxt elem)
  in
    thy
    |> add_locale bname raw_import raw_body
    |-> (fn (elems : context_i list, ctxt) =>
       tap (fn _ => map (print_ctxt ctxt) elems)
    #> tap (fn thy => extract_notes_consts thy elems)
    #> `(fn thy => Locale.intern thy bname)
    #-> (fn name_locale =>
       `(fn thy => extract_tyvar_consts thy elems)
    #-> (fn (v, consts) =>
       fold_map add_global_const consts
    #-> (fn cs =>
       add_axclass (bname ^ "_intro") name_locale cs
    #-> (fn name_axclass =>
       put_class_data name_locale {
          locale_name = name_locale,
          axclass_name = name_axclass,
          consts = cs,
          tycos = []
        })
    #> fold (add_const name_locale) cs
    #> pair ctxt
    ))))
  end;

in

val add_class = gen_add_class (Locale.add_locale_context true);
val add_class_i = gen_add_class (Locale.add_locale_context_i true);

end; (* local *)


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
  Sorts.mg_domain (Sign.classes_arities_of thy) tycon (syntactic_sort_of thy sort)
  |> map (syntactic_sort_of thy);

fun get_superclasses thy class =
  if is_class thy class
  then
    Sorts.superclasses (Sign.classes_of thy) class
    |> syntactic_sort_of thy
  else
    error ("no syntactic class: " ^ class);


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
  in
    extract_sortctxt thy ((fst o Type.freeze_thaw_type) raw_typ_def)
    |> map (tab_lookup o fst)
    |> map (apfst (syntactic_sort_of thy))
    |> filter (not o null o fst)
    |> map mk_lookup
  end;


(* intermediate auxiliary *)

fun add_classentry raw_class raw_cs raw_tycos thy =
  let
    val class = Sign.intern_class thy raw_class;
    val cs = map (Sign.intern_const thy) raw_cs;
    val tycos = map (rpair (Context.theory_name thy) o Sign.intern_type thy) raw_tycos;
  in
    thy
    |> put_class_data class {
         locale_name = "",
         axclass_name = class,
         consts = cs,
         tycos = tycos
       }
    |> fold (add_const class) cs
  end;


(* toplevel interface *)

local

structure P = OuterParse
and K = OuterKeyword

in

val classK = "class_class"

val locale_val =
  (P.locale_expr --
    Scan.optional (P.$$$ "+" |-- P.!!! (Scan.repeat1 P.context_element)) [] ||
  Scan.repeat1 P.context_element >> pair Locale.empty);

val classP =
  OuterSyntax.command classK "operational type classes" K.thy_decl
    (P.name -- Scan.optional (P.$$$ "=" |-- P.!!! locale_val) (Locale.empty, [])
      >> (Toplevel.theory_context
          o (fn f => swap o f) o (fn (name, (expr, elems)) => add_class name expr elems)));

val _ = OuterSyntax.add_parsers [classP];

end; (* local *)


(* setup *)

val _ = Context.add_setup [ClassesData.init];

end; (* struct *)
