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
  val get_info: theory -> string -> {super_classes: class list, intro: thm, axioms: thm list}
  val class_intros: theory -> thm list
  val add_axclass: bstring * xstring list -> ((bstring * string) * Attrib.src list) list ->
    theory -> {intro: thm, axioms: thm list} * theory
  val add_axclass_i: bstring * class list -> ((bstring * term) * attribute list) list ->
    theory -> {intro: thm, axioms: thm list} * theory
  val add_classrel: thm list -> theory -> theory
  val add_arity: thm list -> theory -> theory
  val prove_subclass: class * class -> tactic -> theory -> theory
  val prove_arity: string * sort list * sort -> tactic -> theory -> theory
end;

structure AxClass: AX_CLASS =
struct


(** abstract syntax operations **)

fun aT S = TFree ("'a", S);

fun dest_varT (TFree (x, S)) = ((x, ~1), S)
  | dest_varT (TVar a) = a
  | dest_varT T = raise TYPE ("AxClass.dest_varT", [T], []);


(* subclass propositions *)

fun mk_classrel (c1, c2) = Logic.mk_inclass (aT [c1], c2);

fun dest_classrel tm =
  let
    fun err () = raise TERM ("AxClass.dest_classrel", [tm]);

    val (ty, c2) = Logic.dest_inclass tm handle TERM _ => err ();
    val c1 = (case dest_varT ty of (_, [c]) => c | _ => err ())
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
        Type (t, tys) => (t, map dest_varT tys handle TYPE _ => err ())
      | _ => err ());
    val ss =
      if has_duplicates (eq_fst (op =)) tvars then err ()
      else map snd tvars;
  in (t, ss, c) end;



(** axclass info **)

val introN = "intro";
val axiomsN = "axioms";

type axclass_info =
  {super_classes: class list,
    intro: thm,
    axioms: thm list};

structure AxclassesData = TheoryDataFun
(struct
  val name = "Pure/axclasses";
  type T = axclass_info Symtab.table;

  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.merge (K true);

  fun print thy tab =
    let
      fun pretty_class c cs = Pretty.block
        (Pretty.str (Sign.extern_class thy c) :: Pretty.str " <" :: Pretty.brk 1 ::
          Pretty.breaks (map (Pretty.str o Sign.extern_class thy) cs));

      fun pretty_thms name thms = Pretty.big_list (name ^ ":")
        (map (Display.pretty_thm_sg thy) thms);

      fun pretty_axclass (name, {super_classes, intro, axioms}) = Pretty.block (Pretty.fbreaks
        [pretty_class name super_classes, pretty_thms introN [intro], pretty_thms axiomsN axioms]);
    in Pretty.writeln (Pretty.chunks (map pretty_axclass (Symtab.dest tab))) end;
end);

val _ = Context.add_setup AxclassesData.init;
val print_axclasses = AxclassesData.print;


val lookup_info = Symtab.lookup o AxclassesData.get;

fun get_info thy c =
  (case lookup_info thy c of
    NONE => error ("Unknown axclass " ^ quote c)
  | SOME info => info);

fun class_intros thy =
  let val classes = Sign.classes thy in
    map (Thm.class_triv thy) classes @
    List.mapPartial (Option.map #intro o lookup_info thy) classes
  end;



(** add axiomatic type classes **)

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
        Logic.mk_implies (Logic.mk_inclass (aT [], class), ax)
      else replace_tfree (aT [class]) ax;
    val abs_axms = map (abs_axm o snd) axms;

    fun axm_sort (name, ax) =
      (case term_tfrees ax of
        [] => []
      | [(_, S)] => if Sign.subsort class_thy ([class], S) then S else err_bad_axsort name class
      | _ => err_bad_tfrees name);
    val axS = Sign.certify_sort class_thy (List.concat (map axm_sort axms));

    val int_axm = Logic.close_form o replace_tfree (aT axS);
    fun inclass c = Logic.mk_inclass (aT axS, c);

    val intro_axm = Logic.list_implies
      (map inclass super_classes @ map (int_axm o #2) axms, inclass class);

    (*declare axioms and rule*)
    val (([intro], [axioms]), axms_thy) =
      class_thy
      |> Theory.add_path (Logic.const_of_class bclass)
      |> PureThy.add_axioms_i [Thm.no_attributes (introN, intro_axm)]
      ||>> PureThy.add_axiomss_i [Thm.no_attributes (axiomsN, abs_axms)];
    val info = {super_classes = super_classes, intro = intro, axioms = axioms};

    (*store info*)
    val (_, final_thy) =
      axms_thy
      |> Theory.add_finals_i false [Const (Logic.const_of_class class, a_itselfT --> propT)]
      |> PureThy.add_thms ((map #1 axms ~~ axioms) ~~ atts)
      ||> Theory.restore_naming class_thy
      ||> AxclassesData.map (Symtab.update (class, info));
  in ({intro = intro, axioms = axioms}, final_thy) end;

in

val add_axclass = gen_axclass Sign.intern_class Theory.read_axm Attrib.attribute;
val add_axclass_i = gen_axclass (K I) Theory.cert_axm (K I);

end;



(** proven class instantiation **)

(* primitive rules *)

fun add_classrel ths thy =
  let
    fun prep_thm th =
      let
        val prop = Drule.plain_prop_of (Thm.transfer thy th);
        val (c1, c2) = dest_classrel prop handle TERM _ =>
          raise THM ("AxClass.add_classrel: not a class relation", 0, [th]);
      in (c1, c2) end;
  in Theory.add_classrel_i (map prep_thm ths) thy end;

fun add_arity ths thy =
  let
    fun prep_thm th =
      let
        val prop = Drule.plain_prop_of (Thm.transfer thy th);
        val (t, ss, c) = dest_arity prop handle TERM _ =>
          raise THM ("AxClass.add_arity: not a type arity", 0, [th]);
      in (t, ss, [c]) end;
  in Theory.add_arities_i (map prep_thm ths) thy end;


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
