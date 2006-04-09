(*  Title:      Pure/axclass.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Axiomatic type classes: pure logical content.
*)

signature AX_CLASS =
sig
  val mk_classrel: class * class -> term
  val dest_classrel: term -> class * class
  val mk_arity: string * sort list * class -> term
  val mk_arities: string * sort list * sort -> term list
  val dest_arity: term -> string * sort list * class
  val print_axclasses: theory -> unit
  val get_info: theory -> class -> {super_classes: class list, intro: thm, axioms: thm list}
  val get_instances: theory ->
    {classrel: unit Graph.T, subsorts: ((sort * sort) * thm) list, arities: (arity * thm) list}
  val class_intros: theory -> thm list
  val add_axclass: bstring * xstring list -> ((bstring * string) * Attrib.src list) list ->
    theory -> class * theory
  val add_axclass_i: bstring * class list -> ((bstring * term) * attribute list) list ->
    theory -> class * theory
  val add_classrel: thm list -> theory -> theory
  val add_arity: thm list -> theory -> theory
  val prove_subclass: class * class -> tactic -> theory -> theory
  val prove_arity: string * sort list * sort -> tactic -> theory -> theory
end;

structure AxClass: AX_CLASS =
struct


(** abstract syntax operations **)

(* subclass propositions *)

fun mk_classrel (c1, c2) = Logic.mk_inclass (Term.aT [c1], c2);

fun dest_classrel tm =
  let
    fun err () = raise TERM ("AxClass.dest_classrel", [tm]);

    val (ty, c2) = Logic.dest_inclass tm handle TERM _ => err ();
    val c1 = (case dest_TVar ty of (_, [c]) => c | _ => err ())
      handle TYPE _ => err ();
  in (c1, c2) end;


(* arity propositions *)

fun mk_arity (t, Ss, c) =
  let
    val tfrees = ListPair.map TFree (Term.invent_names [] "'a" (length Ss), Ss);
  in Logic.mk_inclass (Type (t, tfrees), c) end;

fun mk_arities (t, Ss, S) = map (fn c => mk_arity (t, Ss, c)) S;

fun dest_arity tm =
  let
    fun err () = raise TERM ("AxClass.dest_arity", [tm]);

    val (ty, c) = Logic.dest_inclass tm handle TERM _ => err ();
    val (t, tvars) =
      (case ty of
        Type (t, tys) => (t, map dest_TVar tys handle TYPE _ => err ())
      | _ => err ());
    val ss =
      if has_duplicates (eq_fst (op =)) tvars then err ()
      else map snd tvars;
  in (t, ss, c) end;



(** theory data **)

(* axclass *)

val introN = "intro";
val axiomsN = "axioms";

datatype axclass = AxClass of
 {super_classes: class list,
  intro: thm,
  axioms: thm list};

fun make_axclass (super_classes, intro, axioms) =
  AxClass {super_classes = super_classes, intro = intro, axioms = axioms};


(* instances *)

datatype instances = Instances of
 {classrel: unit Graph.T,                 (*raw relation -- no closure!*)
  subsorts: ((sort * sort) * thm) list,
  arities: (arity * thm) list};

fun make_instances (classrel, subsorts, arities) =
  Instances {classrel = classrel, subsorts = subsorts, arities = arities};

fun map_instances f (Instances {classrel, subsorts, arities}) =
  make_instances (f (classrel, subsorts, arities));

fun merge_instances
   (Instances {classrel = classrel1, subsorts = subsorts1, arities = arities1},
    Instances {classrel = classrel2, subsorts = subsorts2, arities = arities2}) =
  make_instances
   (Graph.merge (K true) (classrel1, classrel2),
    merge (eq_fst op =) (subsorts1, subsorts2),
    merge (eq_fst op =) (arities1, arities2));


(* setup data *)

structure AxClassData = TheoryDataFun
(struct
  val name = "Pure/axclass";
  type T = axclass Symtab.table * instances;

  val empty = (Symtab.empty, make_instances (Graph.empty, [], []));
  val copy = I;
  val extend = I;

  fun merge _ ((axclasses1, instances1), (axclasses2, instances2)) =
    (Symtab.merge (K true) (axclasses1, axclasses2), merge_instances (instances1, instances2));

  fun print thy (axclasses, _) =
    let
      fun pretty_class c cs = Pretty.block
        (Pretty.str (Sign.extern_class thy c) :: Pretty.str " <" :: Pretty.brk 1 ::
          Pretty.breaks (map (Pretty.str o Sign.extern_class thy) cs));

      fun pretty_thms name thms = Pretty.big_list (name ^ ":")
        (map (Display.pretty_thm_sg thy) thms);

      fun pretty_axclass (name, AxClass {super_classes, intro, axioms}) =
        Pretty.block (Pretty.fbreaks
          [pretty_class name super_classes, pretty_thms introN [intro], pretty_thms axiomsN axioms]);
    in Pretty.writeln (Pretty.chunks (map pretty_axclass (Symtab.dest axclasses))) end;
end);

val _ = Context.add_setup AxClassData.init;
val print_axclasses = AxClassData.print;

val get_instances = AxClassData.get #> (fn (_, Instances insts) => insts);



(** axclass definitions **)

(* lookup *)

val lookup_info = Symtab.lookup o #1 o AxClassData.get;

fun get_info thy c =
  (case lookup_info thy c of
    SOME (AxClass info) => info
  | NONE => error ("Unknown axclass " ^ quote c));

fun class_intros thy =
  let
    fun add_intro c =
      (case lookup_info thy c of SOME (AxClass {intro, ...}) => cons intro | _ => I);
    val classes = Sign.classes thy;
  in map (Thm.class_triv thy) classes @ fold add_intro classes [] end;


(* add_axclass(_i) *)

local

fun err_bad_axsort ax c =
  error ("Sort constraint in axiom " ^ quote ax ^ " not supersort of " ^ quote c);

fun err_bad_tfrees ax =
  error ("More than one type variable in axiom " ^ quote ax);

fun replace_tfree T = map_term_types (Term.map_atyps (fn TFree _ => T | U => U));

fun gen_axclass prep_class prep_axm prep_att
    (bclass, raw_super_classes) raw_axioms_atts thy =
  let
    val class = Sign.full_name thy bclass;
    val super_classes = map (prep_class thy) raw_super_classes;
    val axms = map (prep_axm thy o fst) raw_axioms_atts;
    val atts = map (map (prep_att thy) o snd) raw_axioms_atts;

    (*declare class*)
    val class_thy =
      thy |> Theory.add_classes_i [(bclass, super_classes)];

    (*prepare abstract axioms*)
    fun abs_axm ax =
      if null (term_tfrees ax) then
        Logic.mk_implies (Logic.mk_inclass (Term.aT [], class), ax)
      else replace_tfree (Term.aT [class]) ax;
    val abs_axms = map (abs_axm o snd) axms;

    fun axm_sort (name, ax) =
      (case term_tfrees ax of
        [] => []
      | [(_, S)] => if Sign.subsort class_thy ([class], S) then S else err_bad_axsort name class
      | _ => err_bad_tfrees name);
    val axS = Sign.certify_sort class_thy (List.concat (map axm_sort axms));

    val int_axm = Logic.close_form o replace_tfree (Term.aT axS);
    fun inclass c = Logic.mk_inclass (Term.aT axS, c);

    val intro_axm = Logic.list_implies
      (map inclass super_classes @ map (int_axm o #2) axms, inclass class);

    (*declare axioms and rule*)
    val (([intro], [axioms]), axms_thy) =
      class_thy
      |> Theory.add_path (Logic.const_of_class bclass)
      |> PureThy.add_axioms_i [Thm.no_attributes (introN, intro_axm)]
      ||>> PureThy.add_axiomss_i [Thm.no_attributes (axiomsN, abs_axms)];
    val info = make_axclass (super_classes, intro, axioms);

    (*store info*)
    val (_, final_thy) =
      axms_thy
      |> Theory.add_finals_i false [Const (Logic.const_of_class class, Term.a_itselfT --> propT)]
      |> PureThy.add_thms ((map #1 axms ~~ axioms) ~~ atts)
      ||> Theory.restore_naming class_thy
      ||> AxClassData.map (apfst (Symtab.update (class, info)));
  in (class, final_thy) end;

in

val add_axclass = gen_axclass Sign.intern_class Theory.read_axm Attrib.attribute;
val add_axclass_i = gen_axclass (K I) Theory.cert_axm (K I);

end;



(** instantiation proofs **)

(* primitives *)

fun add_classrel ths thy =
  let
    fun add_rel (c1, c2) =
      Graph.default_node (c1, ()) #> Graph.default_node (c2, ()) #> Graph.add_edge (c1, c2);
    val rels = ths |> map (fn th =>
      let
        val prop = Drule.plain_prop_of (Thm.transfer thy th);
        val (c1, c2) = dest_classrel prop handle TERM _ =>
          raise THM ("AxClass.add_classrel: not a class relation", 0, [th]);
      in (c1, c2) end);
  in
    thy
    |> Theory.add_classrel_i rels
    |> AxClassData.map (apsnd (map_instances (fn (classrel, subsorts, arities) =>
        (classrel |> fold add_rel rels, (map (pairself single) rels ~~ ths) @ subsorts, arities))))
  end;

fun add_arity ths thy =
  let
    val ars = ths |> map (fn th =>
      let
        val prop = Drule.plain_prop_of (Thm.transfer thy th);
        val (t, ss, c) = dest_arity prop handle TERM _ =>
          raise THM ("AxClass.add_arity: not a type arity", 0, [th]);
      in (t, ss, [c]) end);
  in
    thy
    |> Theory.add_arities_i ars
    |> AxClassData.map (apsnd (map_instances (fn (classrel, subsorts, arities) =>
      (classrel, subsorts, (ars ~~ ths) @ arities))))
  end;


(* tactical proofs *)

fun prove_subclass raw_rel tac thy =
  let
    val (c1, c2) = Sign.cert_classrel thy raw_rel;
    val th = Goal.prove thy [] [] (mk_classrel (c1, c2)) (fn _ => tac) handle ERROR msg =>
      cat_error msg ("The error(s) above occurred while trying to prove class relation " ^
        quote (Sign.string_of_classrel thy [c1, c2]));
  in add_classrel [th] thy end;

fun prove_arity raw_arity tac thy =
  let
    val arity = Sign.cert_arity thy raw_arity;
    val props = mk_arities arity;
    val ths = Goal.prove_multi thy [] [] props
      (fn _ => Tactic.precise_conjunction_tac (length props) 1 THEN tac) handle ERROR msg =>
        cat_error msg ("The error(s) above occurred while trying to prove type arity " ^
          quote (Sign.string_of_arity thy arity));
  in add_arity ths thy end;


end;
