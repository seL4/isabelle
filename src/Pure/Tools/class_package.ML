(*  Title:      Pure/hugsclass.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Haskell98-like type classes, logically simulated by locales ("hugsclass")
*)

(*!!! for now, only experimental scratch code !!!*)

signature CLASS_PACKAGE =
sig
(*   val add_class: (bstring * xstring list * Locale.element list) -> theory -> theory  *)
(*   val add_class_i: bstring -> string list -> Locale.element list -> theory -> theory  *)

  val get_locale_for_class: theory -> string -> string
  val get_axclass_for_class: theory -> string -> class
  val add_members_x: xstring * xstring list -> theory -> theory
  val add_members: string * string list -> theory -> theory
  val add_tycons_x: xstring * xstring list -> theory -> theory
  val add_tycons: string * string list -> theory -> theory
  val the_members: theory -> class -> string list
  val the_tycons: theory -> class -> string list

  val is_class: theory -> class -> bool
  val get_arities: theory -> sort -> string -> sort list
  val get_superclasses: theory -> class -> class list
  type sortcontext = (string * (string * sort)) list
                     (* [(identifier, (varname, sort))] *)
  datatype lookup = Instance of class * string * lookup list list
                  | Context of (string * int) * (int * class list)
  val derive_sortctxt: theory -> string -> typ -> sortcontext
  val derive_lookup: theory -> sortcontext -> typ * typ -> lookup list list
end;

structure ClassPackage : CLASS_PACKAGE =
struct



(** data kind 'Pure/classes' **)

type class_info = {
  locale_name: string,
  axclass_name: string,
  members: string list,
  tycons: string list
};

structure ClassesData = TheoryDataFun (
  struct
    val name = "Pure/classes";
    type T = class_info Symtab.table;
    val empty = Symtab.empty;
    val copy = I;
    val extend = I;
    fun merge _ = Symtab.merge (K true);
    fun print _ tab = (Pretty.writeln o Pretty.chunks) (map Pretty.str (Symtab.keys tab));
  end
);

val _ = Context.add_setup [ClassesData.init];
val print_classes = ClassesData.print;

fun lookup_class_info thy class = Symtab.lookup (ClassesData.get thy, class);

fun get_class_info thy class =
  case lookup_class_info thy class
    of NONE => error ("undeclared class " ^ quote class)
     | SOME info => info;

fun put_class_info class info thy =
  thy
  |> ClassesData.put (Symtab.update ((class, info), ClassesData.get thy));


(* name mangling *)

fun get_locale_for_class thy class =
  #locale_name (get_class_info thy class)

fun get_axclass_for_class thy class =
  #axclass_name (get_class_info thy class)


(* assign members to type classes *)

local

fun gen_add_members prep_class prep_member (raw_class, raw_members_new) thy =
  let
    val class = prep_class thy raw_class
    val members_new = map (prep_member thy) raw_members_new
    val {locale_name, axclass_name, members, tycons} =
      get_class_info thy class
  in
    thy
    |> put_class_info class {
         locale_name = locale_name,
         axclass_name = axclass_name,
         members = members @ members_new,
         tycons = tycons
       }
  end

in

val add_members_x = gen_add_members Sign.intern_class Sign.intern_const
val add_members = gen_add_members (K I) (K I)

end (*local*)


(* assign type constructors to type classes *)

local

fun gen_add_tycons prep_class prep_type (raw_class, raw_tycons_new) thy =
  let
    val class = prep_class thy raw_class
    val tycons_new = map (prep_type thy) raw_tycons_new
    val {locale_name, axclass_name, members, tycons} =
      get_class_info thy class
  in
    thy
    |> put_class_info class {
         locale_name = locale_name,
         axclass_name = axclass_name,
         members = members,
         tycons = tycons @ tycons_new
       }
  end;

in

val add_tycons_x = gen_add_tycons Sign.intern_class Sign.intern_type
val add_tycons = gen_add_tycons (K I) (K I)

end (*local*)


(* retrieve members *)

val the_members = (#members oo get_class_info)


(* retrieve type constructor associations *)

val the_tycons = (#tycons oo get_class_info)



(** generic & useful... !!! move this somewhere else ??? **)

fun subst_clsvar thy class subst typ = map_type_tfree (fn (tvar, sort) =>
    if Sorts.sort_eq (Sign.classes_of thy) ([class], sort)
    then subst (tvar, sort)
    else TFree (tvar, sort)
  ) typ



(** class declaration **)

local

fun gen_add_class prep_class prep_loc
  (bname, raw_superclss, raw_locales, raw_locelems) int thy =
  let
    val name_class = Sign.full_name thy bname
    val name_loc = Sign.full_name thy bname
    val name_intro = name_loc ^ ".intro" (*!!!*)
    val superclss = map (prep_class thy) raw_superclss
    val _ = map (get_class_info thy) superclss
    val defaultS = Sign.defaultS thy
    val axsuperclss = case superclss of [] => defaultS
                                     | _ => superclss
    val _ = writeln ("superclasses: " ^ commas axsuperclss)
    val superlocales = 
      superclss
      |> map (get_locale_for_class thy)
      |> append (map (prep_loc thy) raw_locales)
    val locexpr =
      superlocales
      |> map (Locale.Locale)
      |> Locale.Merge
    fun get_loc_intro thy locname name_intro =
      let
        val ctxt = ProofContext.init thy
                   |> Locale.read_context_statement (SOME locname) [] []
                   |> #4
      in
        case ProofContext.assumptions_of ctxt
        of [] => NONE
         | _ => SOME (PureThy.get_thm thy (Name name_intro))
      end
    fun constify thy (mname, mtyp, _) = Const (Sign.intern_const thy mname, mtyp)
    fun axiom_for loc members thy = case Sign.const_constraint thy loc
      of SOME pred_type => if is_funtype pred_type
           then [((bname, 
             (ObjectLogic.assert_propT thy
             (list_comb (Const (loc, Type.unvarifyT pred_type), map (constify thy) members)))), [])
           ]
           else []
       | NONE => []
    fun get_members thy locname =
      let
        val ctxt = ProofContext.init thy
                   |> Locale.read_context_statement (SOME locname) [] []
                   |> #4
        val fixed = ProofContext.fixed_names_of ctxt
        fun mk_member fixed = (fixed, (the o ProofContext.default_type ctxt) fixed, NoSyn)
      in map mk_member fixed end;
    fun remove_supercls_members thy =
      superlocales
      |> map (get_members thy)
      |> fold (fn fxs => fn rem => gen_rems (fn ((x, _, _), (y, _, _)) => x = y) (rem, fxs))
    fun get_members_only thy locname =
      get_members thy locname
      |> remove_supercls_members thy
    fun add_constraint class (mname, mtyp, _) thy =
      let
        val tfree = case (typ_tfrees o Type.unvarifyT) mtyp
                    of [(tfree, sort)] => if Sorts.sort_eq (Sign.classes_of thy) (sort, defaultS)
                                          then tfree
                                          else error ("sort constraint not permitted in member " ^ quote mname)
                     | _ => error ("no or more than one type variable in declaration for member " ^ quote mname)
        fun constrain_tfree (tfree, _) = TFree (tfree, [class])
      in Sign.add_const_constraint_i
        (mname, map_type_tfree constrain_tfree mtyp) thy
      end
    fun setup_interpretation membernames = IsarThy.register_globally (*!!!*)
      (((bname ^ "_interp", []), Locale.Locale name_loc), membernames)
  in
    thy
    |> Locale.add_locale_context true bname locexpr raw_locelems
       |-> (fn (loccontext, elems) =>
       tap (fn _ => writeln "(1) added locale")
    #> `(fn thy => get_members_only thy name_loc)
       #-> (fn members =>
       Sign.add_consts_i members
    #> `(fn thy => map (fn (n, t, m) => (Sign.intern_const thy n, t, m)) members)
       #-> (fn intern_members =>
       tap (fn _ => writeln "(2) added members")
    #> `(fn thy => get_loc_intro thy name_loc name_intro)
       #-> (fn intro =>
       tap (fn _ => writeln "(3) axiom prep")
    #> `(axiom_for name_loc intern_members)
       #-> (fn axiom =>
(*       `(Sign.restore_naming)  *)
(*        #-> (fn restore_naming =>  *)
(*        Sign.add_path "class"  *)
       tap (fn thy => writeln ("(4) axiom: " ^
         commas (map (Sign.string_of_term thy o snd o fst) axiom)))
    #> AxClass.add_axclass_i (bname, axsuperclss) axiom #> fst
    #> tap (fn _ => writeln "(5) added axclass")
    #> (if is_some intro then PureThy.add_thms [Thm.no_attributes (bname ^ "_intro", the intro)] #> fst else I)
    #> tap (fn _ => writeln "(6) re-introduced intro")
    #> fold (add_constraint name_class) intern_members
(*     #> restore_naming  *)
    #> tap (fn _ => writeln "(7) constrained members")
    #> put_class_info name_class {
         locale_name = name_loc,
         axclass_name = name_class,
         members = map #1 intern_members,
         tycons = []
       }
    #> tap (fn _ => writeln "(8) added class data/members")
    #> setup_interpretation (map (SOME o #1) intern_members) int
    )))))
  end

in

val add_class = gen_add_class (Sign.intern_class) (Locale.intern);

end (*local*)



(** instance definition **)

local

fun read_check_memberdefs thy class tycon arity raw_defs = 
  let
    val pp = Sign.pp thy
    val thy_temp =
      thy
      |> Theory.copy
      |> Sign.add_arities_i [(tycon, arity, [class])]
      |> `(fn thy => Sorts.mg_domain (Sign.classes_arities_of thy) tycon [class])
      |> snd
    val _ = writeln "temp"
    fun read_check_memberdef ((raw_bname, raw_term), attr) members = 
      let
        val _ = writeln ("reading " ^ class ^ " - " ^ tycon)
        val _ = (writeln o commas o map (Sign.string_of_sort thy_temp)) (Sorts.mg_domain (Sign.classes_arities_of thy_temp) tycon [class])
        val _ = writeln (raw_bname ^ ": " ^ raw_term)
        val term = Sign.read_prop thy_temp raw_term
        val _ = writeln "read"
        val ((const, typ_def), rhs) = Theory.dest_def pp term handle TERM (msg, _) => error msg
        val _ = if member (op =) members const
                then {}
                else error ("superfluos definition: " ^ quote const)
        val typ_decl = Sign.the_const_constraint thy_temp const
        val typ_arity = Type (tycon, map (fn sort => TFree ("", sort)) arity)
        val typ_inst = subst_clsvar thy_temp class (fn _ => typ_arity) typ_decl
        val _ = if Sign.typ_instance thy_temp (typ_inst, typ_def)
                andalso Sign.typ_instance thy_temp (typ_def, typ_inst)
                then {}
                else error ("member definition " ^ quote const
                  ^ " does not have required type signature: expected "
                  ^ (quote o Sign.string_of_typ thy_temp) typ_inst ^ ", got "
                  ^ (quote o Sign.string_of_typ thy_temp) typ_decl)
        val bname = case raw_bname
                    of "" => const ^ "_" ^ tycon
                     | bname => bname
        val members' = remove (op =) const members
        val _ = (writeln o commas o map (Sign.string_of_sort thy)) (Sorts.mg_domain (Sign.classes_arities_of thy) tycon [class])
      in (((bname, term), attr), members') end
  in
    the_members thy_temp class
    |> fold_map read_check_memberdef raw_defs
    ||> (fn [] => I
          | members => error ("missing class member definitions: " ^ (commas o map quote) members))
    |> fst
  end

in

fun instance_arity_proof_ext (raw_ty, raw_arity, raw_class, raw_defs) int thy =
  let
    val class = Sign.intern_class thy raw_class
    val tycon = Sign.intern_type thy raw_ty
    val arity = map (Sign.read_sort thy) raw_arity
    val _ = writeln ("(1) mangled " ^ class ^ " - " ^ tycon)
  in
    thy
    |> `(fn thy => read_check_memberdefs thy class tycon arity raw_defs)
       |-> (fn defs =>
       `(fn _ => writeln ("(2) checked")) #> snd
(*!!! attributes     #> IsarThy.add_defs_i (true, defs)  *)
    #> Theory.add_defs_i true (map fst defs)
    #> `(fn _ => writeln ("(3) added")) #> snd
    #> AxClass.instance_arity_proof (raw_ty, raw_arity, raw_class)
         (add_tycons (class, [tycon])) int
    )
  end

end (*local*)



(** code generation suppport (dictionaries) *)

(* filtering non-hugs classes *)

fun is_class thy = is_some o lookup_class_info thy

fun filter_class thy = filter (is_class thy)

fun assert_class thy class =
  if is_class thy class then class
  else error ("not a class: " ^ quote class)

fun get_arities thy sort tycon =
  Sorts.mg_domain (Sign.classes_arities_of thy) tycon sort
  |> (map o map) (assert_class thy)

fun get_superclasses thy class =
  Sorts.superclasses (Sign.classes_of thy) class
  |> filter_class thy


(* sortcontext handling *)

type sortcontext = (string * (string * sort)) list

fun derive_sortctxt_proto thy typ =
  typ
  |> Type.unvarifyT
  |> typ_tfrees
  |> map (fn (v, s) => (v, filter_class thy s))
  |> filter (fn (_, []) => false | _ => true)

fun derive_sortctxt thy sctxtparm typ =
  typ
  |> derive_sortctxt_proto thy
  |> map (pair sctxtparm)

datatype lookup = Instance of class * string * lookup list list
                | Context of (string * int) * (int * class list)

fun derive_lookup thy sctxt_use (raw_typ_def, raw_typ_use) =
  let
    val typ_def = Type.varifyT raw_typ_def
    val typ_use = Type.varifyT raw_typ_use
    val sanatize_sort = filter_class thy
    val match_tab = Sign.typ_match thy (typ_def, typ_use) Vartab.empty
    fun tab_lookup vname = (the o Vartab.lookup) (match_tab, (vname, 0))
    fun get_supercls_derivation (subclasses, superclass) =
      (the oo get_first) (fn subclass =>
        Sorts.class_le_path (Sign.classes_of thy) (subclass, superclass)
      ) subclasses
    fun mk_cls_deriv thy subclasses superclass =
      case get_supercls_derivation (subclasses, superclass)
      of (subclass::deriv) => (find_index_eq subclass subclasses, deriv)
    fun mk_lookup (sort_def, (Type (tycon, tyargs))) =
        let
          val arity_lookup = map2 mk_lookup
            (map sanatize_sort (Sorts.mg_domain (Sign.classes_arities_of thy) tycon sort_def), tyargs)
        in
          map (fn class => Instance (class, tycon, arity_lookup)) sort_def
        end
      | mk_lookup (sort_def, TVar ((vname, _), sort_use)) =
        let
          val vidx = find_index_eq vname (map (fst o snd) sctxt_use)
          val sctxtparm = #1 (List.nth (sctxt_use, vidx))
        in
          map (fn (class) => Context ((sctxtparm, vidx), mk_cls_deriv thy sort_use class)) sort_def
        end
  in
    derive_sortctxt_proto thy raw_typ_def
    |> map #1
    |> map tab_lookup
    |> map (apfst sanatize_sort)
    |> filter (fn ([], _) => false | _ => true)
    |> map mk_lookup
  end



(** outer syntax **)

local

structure P = OuterParse
and K = OuterKeyword

in

val (classK, extendsK, importingK) = ("Xclass", "Xextends", "Ximporting")

val classP =
(*   OuterSyntax.command classK "define class" K.thy_decl (  *)
  OuterSyntax.command classK "define class" K.thy_goal (
    P.name
    -- Scan.optional (P.$$$ extendsK |-- P.list1 P.xname) []
    -- Scan.optional (P.$$$ importingK |-- P.list1 P.xname) []
    -- Scan.repeat1 P.locale_element
    >> (fn (((name, superclasses), locales), locelems)
(*         => Toplevel.theory (add_class (name, superclss, locelems)))  *)
         => (Toplevel.print oo Toplevel.theory_to_proof)
              (add_class (name, superclasses, locales, locelems)))
  )

val (instanceK, whereK) = ("Xinst", "Xwhere")

val instanceP =
  OuterSyntax.command instanceK "prove type arity" K.thy_goal ((
    Scan.optional (P.$$$ "(" |-- P.!!! (P.list1 (P.group "sort" P.xname) --| P.$$$ ")")) []
    -- P.xname --| P.$$$ "::"
    -- P.group "class" P.xname
    -- Scan.optional (P.$$$ whereK |-- Scan.repeat1 P.spec_opt_name) [])
    >> (fn (((arity, ty), class), defs)
        => (Toplevel.print oo Toplevel.theory_to_proof)
             (instance_arity_proof_ext (ty, arity, class, defs))
       )
  )

val _ = OuterSyntax.add_parsers [classP, instanceP]

val _ = OuterSyntax.add_keywords [extendsK, whereK]

val classcgK = "codegen_class"

fun classcg raw_class raw_members raw_tycons thy =
  let
    val class = Sign.intern_class thy raw_class
  in
    thy
    |> put_class_info class {
         locale_name = "",
         axclass_name = class,
         members = [],
         tycons = []
       }
    |> add_members_x (class, raw_members)
    |> add_tycons_x (class, raw_tycons)
  end

val classcgP =
  OuterSyntax.command classcgK "codegen data for classes" K.thy_decl (
    P.xname
    -- ((P.$$$ "\\<Rightarrow>" || P.$$$ "=>") |-- (P.list1 P.name))
    -- (Scan.optional ((P.$$$ "\\<Rightarrow>" || P.$$$ "=>") |-- (P.list1 P.name)) [])
    >> (fn ((name, tycons), members) => (Toplevel.theory (classcg name members tycons)))
  )

val _ = OuterSyntax.add_parsers [classcgP];

end (*local*)

end

(*



isomorphism

locale sg = fixes prod assumes assoc: ...

consts prod :: "'a::type => 'a => 'a"

axclass sg < type
  sg: "sg prod"

constraints prod :: "'a::sg => 'a => 'a"


theory Scratch imports Main begin

(* class definition *)

locale sg =
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<degree>" 60)
  assumes assoc: "(x \<degree> y) \<degree> z = x \<degree> (y \<degree> z)"

classes sg
consts prod :: "'a::sg \<Rightarrow> 'a \<Rightarrow> 'a"  (infix "\<degree>\<degree>" 60)
classrel sg < type
axioms sg: "sg prod"

interpretation sg: sg [prod] by (rule sg)


(* abstract reasoning *)

lemma (in sg)
  bar: "x \<degree> y = x \<degree> y" ..

lemma baz:
  fixes x :: "'a::sg"
  shows "x \<degree>\<degree> y = x \<degree>\<degree> y" ..

(* class instantiation *)

interpretation sg_list: sg ["op @"]
  by (rule sg.intro) (simp only: append_assoc)
arities list :: (type) sg
defs (overloaded) prod_list_def: "prod == op @"

interpretation sg_prod: sg ["%p q. (fst p \<degree>\<degree> fst q, snd p \<degree>\<degree> snd q)"]
  by (rule sg.intro) (simp add: sg.assoc)

arities * :: (sg, sg) sg

    (* fun inferT_axm pre_tm =
      let
        val pp = Sign.pp thy;
        val (t, _) = Sign.infer_types pp thy (K NONE) (K NONE) [] true ([pre_tm], TFree ("a", []));
      in t end
    fun axiom_for members = (bname, inferT_axm
      (ObjectLogic.assert_propT thy (list_comb (Const (name, dummyT), map (fn (mname, mtyp, _) => Const (mname, mtyp)) members)))) *)


*)

