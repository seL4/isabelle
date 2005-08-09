(*  Title:      Pure/hugsclass.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Haskell98-like type classes, logically simulated by locales ("hugsclass")
*)

(*!!! for now, only experimental scratch code !!!*)

signature HUGSCLASS =
sig
  val add_hugsclass: bstring -> xstring list -> Locale.element list -> theory -> theory
(*   val add_hugsclass_i: bstring -> string list -> Locale.element list -> theory -> theory  *)

  val get_locale_for_hugsclass: theory -> string -> string
  val get_axclass_for_hugsclass: theory -> string -> class
  val add_members_x: xstring * xstring list -> theory -> theory
  val add_members: string * string list -> theory -> theory
  val add_tycons_x: xstring * xstring list -> theory -> theory
  val add_tycons: string * string list -> theory -> theory
  val the_members: theory -> class -> string list
  val the_tycons: theory -> class -> string list

  val is_hugsclass: theory -> class -> bool
  val get_arities: theory -> sort -> string -> sort list
  val get_superclasses: theory -> class -> class list
end;

structure Hugsclass : HUGSCLASS =
struct



(** data kind 'Pure/classes' **)

type hugsclass_info = {
  locale_name: string,
  axclass_name: string,
  members: string list,
  tycons: string list
};

structure HugsclassesData = TheoryDataFun (
  struct
    val name = "Pure/hugsclasses";
    type T = hugsclass_info Symtab.table;
    val empty = Symtab.empty;
    val copy = I;
    val extend = I;
    fun merge _ = Symtab.merge (K true);
    fun print _ tab = (Pretty.writeln o Pretty.chunks) (map Pretty.str (Symtab.keys tab));
  end
);

val _ = Context.add_setup [HugsclassesData.init];
val print_hugsclasses = HugsclassesData.print;

fun lookup_hugsclass_info thy class = Symtab.lookup (HugsclassesData.get thy, class);

fun get_hugsclass_info thy class =
  case lookup_hugsclass_info thy class
    of NONE => error ("undeclared hugs class " ^ quote class)
     | SOME info => info;

fun put_hugsclass_info class info thy =
  thy
  |> HugsclassesData.put (Symtab.update ((class, info), HugsclassesData.get thy));


(* name mangling *)

fun get_locale_for_hugsclass thy class =
  #locale_name (get_hugsclass_info thy class)

fun get_axclass_for_hugsclass thy class =
  #axclass_name (get_hugsclass_info thy class)


(* assign members to type classes *)

local

fun gen_add_members prep_class prep_member (raw_class, raw_members_new) thy =
  let
    val class = prep_class thy raw_class
    val members_new = map (prep_member thy) raw_members_new
    val {locale_name, axclass_name, members, tycons} =
      get_hugsclass_info thy class
  in
    thy
    |> put_hugsclass_info class {
         locale_name = locale_name,
         axclass_name = axclass_name,
         members = members @ members_new,
         tycons = tycons
       }
  end

in

val add_members_x = gen_add_members Sign.intern_class Sign.intern_const
val add_members = gen_add_members (K I) (K I)

end


(* assign type constructors to type classes *)

local

fun gen_add_tycons prep_class prep_type (raw_class, raw_tycons_new) thy =
  let
    val class = prep_class thy raw_class
    val tycons_new = map (prep_type thy) raw_tycons_new
    val {locale_name, axclass_name, members, tycons} =
      get_hugsclass_info thy class
  in
    thy
    |> put_hugsclass_info class {
         locale_name = locale_name,
         axclass_name = axclass_name,
         members = members,
         tycons = tycons @ tycons_new
       }
  end;

in

val add_tycons_x = gen_add_tycons Sign.intern_class Sign.intern_type
val add_tycons = gen_add_tycons (K I) (K I)

end


(* retrieve members *)

val the_members = (#members oo get_hugsclass_info)


(* retrieve type constructor associations *)

val the_tycons = (#tycons oo get_hugsclass_info)



(** class declaration **)

local

fun gen_add_hugsclass prep_class bname raw_superclss raw_locelems thy =
  let
    val name_class = Sign.full_name thy bname
    val name_loc = Sign.full_name thy bname
    val superclss = map (prep_class thy) raw_superclss
    val _ = map (get_hugsclass_info thy) superclss
    val defaultS = Sign.defaultS thy
    val axsuperclss = case superclss of [] => defaultS
                                     | _ => superclss
    val locexpr =
      superclss
      |> map (get_locale_for_hugsclass thy) 
      |> map (Locale.Locale)
      |> Locale.Merge
    (* fun inferT_axm pre_tm =
      let
        val pp = Sign.pp thy;
        val (t, _) = Sign.infer_types pp thy (K NONE) (K NONE) [] true ([pre_tm], TFree ("a", []));
      in t end
    fun axiom_for members = (bname, inferT_axm
      (ObjectLogic.assert_propT thy (list_comb (Const (name, dummyT), map (fn (mname, mtyp, _) => Const (mname, mtyp)) members)))) *)
    fun constify thy (mname, mtyp, _) = Const (Sign.intern_const thy mname, mtyp)
    fun axiom_for loc members thy = case Sign.const_type thy loc
      of SOME pred_type => [((bname, 
         (ObjectLogic.assert_propT thy
           (list_comb (Const (loc, Type.unvarifyT pred_type), map (constify thy) members)))), [])
        ]
       | NONE => (writeln "--- no const_type"; [])
    fun get_members locname thy =
      let
        val ctxt = ProofContext.init thy
                   |> Locale.read_context_statement (SOME locname) [] []
                   |> #4
                   |> `(fn ctxt => ((writeln o commas o ProofContext.fixed_names_of) ctxt; ctxt)) |> snd
        val ctx' = ProofContext.init thy
                   |> Locale.read_context_statement (SOME locname) [] []
                   |> #3
                   |> `(fn ctxt => ((writeln o commas o ProofContext.fixed_names_of) ctxt; ctxt)) |> snd
        val fixed = ProofContext.fixed_names_of ctxt
        fun mk_member fixed = (fixed, (the o ProofContext.default_type ctxt) fixed, NoSyn)
      in map mk_member fixed end;
    fun add_constraint class (mname, mtyp, _) thy =
      let
        val classes = snd (#classes (Type.rep_tsig (#tsig (Sign.rep_sg thy))))
        val tfree = case (typ_tfrees o Type.unvarifyT) mtyp
                    of [(tfree, sort)] => if Sorts.sort_eq classes (sort, defaultS)
                                          then tfree
                                          else error ("sort constraint not permitted in member " ^ quote mname)
                     | _ => error ("no or more than one type variable in declaration for member " ^ quote mname)
        fun constrain_tfree (tfree, _) = TFree (tfree, [class])
      in Sign.add_const_constraint_i
        (Sign.intern_const thy mname, map_type_tfree constrain_tfree mtyp) thy
      end;
  in
    thy
    |> Locale.add_locale true bname locexpr raw_locelems
    |> `(fn _ => writeln "(1) added locale") |> snd
    |> `(get_members name_loc)
       |-> (fn members =>
       Sign.add_consts_i members
    #> `(fn _ => writeln "(2) added members") #> snd
    #> `(axiom_for name_loc members)
       #-> (fn axiom =>
       AxClass.add_axclass_i (bname, axsuperclss) axiom #> fst
    #> `(fn _ => writeln "(3) added axclass") #> snd
    #> fold (add_constraint name_class) members
    #> `(fn _ => writeln "(4) constrained members") #> snd
    #> add_members (name_class, map #1 members)
    #> `(fn _ => writeln "(5) added class members") #> snd
    #> put_hugsclass_info name_class {
         locale_name = name_loc,
         axclass_name = name_class,
         members = [],
         tycons = []
       }
    ))
  end

in

val add_hugsclass = gen_add_hugsclass (Sign.intern_class);
val add_hugsclass_i = gen_add_hugsclass (K I);

end;



(** technical class relations *)

fun is_hugsclass thy = can (the_tycons thy)

fun get_arities thy sort tycons =
  let
    val tsig = Type.rep_tsig (#tsig (Sign.rep_sg thy))
    val clss_arities = (snd (#classes tsig), #arities tsig)
  in
    Sorts.mg_domain clss_arities tycons sort
    |> map (filter (is_hugsclass thy))
    (*!!! assert -> error on fail *)
  end

fun get_superclasses thy class =
  Sorts.direct_supercls (snd (#classes (Type.rep_tsig (#tsig (Sign.rep_sg thy))))) class
  |> filter (is_hugsclass thy)


(** outer syntax **)

local

structure P = OuterParse
and K = OuterSyntax.Keyword

in

val (classK, extendsK) = ("class", "extends")

val classP =
  OuterSyntax.command classK "define type class" K.thy_decl (
    P.name
    -- Scan.optional (P.$$$ extendsK |-- P.list1 P.xname) []
    -- Scan.repeat P.locale_element
    >> (fn (((name, superclss), locelems))
        => Toplevel.theory (add_hugsclass name superclss locelems))
  )

val (instanceK, whereK) = ("inst", "where")

val instanceP =
  OuterSyntax.command instanceK "prove type arity" K.thy_goal ((
    Scan.optional (P.$$$ "(" |-- P.!!! (P.list1 (P.group "sort" P.xname) --| P.$$$ ")")) []
    -- P.xname --| P.$$$ "::"
    -- P.group "class" P.xname
    -- Scan.optional (P.$$$ whereK |-- Scan.repeat1 P.spec_name) [])
    >> (fn (((arity, ty), class), defs)
        =>
        Toplevel.theory (IsarThy.add_defs (true, defs))
        #> (AxClass.instance_arity_proof (ty, arity, class)
            |> (Toplevel.print oo Toplevel.theory_to_proof))
       )
  )

val _ = OuterSyntax.add_parsers [classP, instanceP]

val _ = OuterSyntax.add_keywords [extendsK]

end

end

(*

PureThy.add_thms [Thm.no_attributes (intro_name bclass, intro)]
get_thm thy PureThy.

rename intro rule
check defs -> should contain any member
wie syntax extrahieren?
cases für locales

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

*)
