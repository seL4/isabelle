(*  Title:      Pure/axclass.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Axiomatic type classes.
*)

signature AX_CLASS =
sig
  val print_axclasses: theory -> unit
  val get_info: theory -> class -> {super_classes: class list, intro: thm, axioms: thm list}
  val get_instances: theory ->
   {classes: unit Graph.T,
    classrel: ((class * class) * thm) list,
    arities: ((string * sort list * class) * thm) list}
  val class_intros: theory -> thm list
  val add_axclass: bstring * xstring list -> string list ->
    ((bstring * string) * Attrib.src list) list -> theory -> class * theory
  val add_axclass_i: bstring * class list -> string list ->
    ((bstring * term) * attribute list) list -> theory -> class * theory
  val params_of_sort: theory -> sort -> string list
  val cert_classrel: theory -> class * class -> class * class
  val read_classrel: theory -> xstring * xstring -> class * class
  val add_classrel: thm -> theory -> theory
  val add_arity: thm -> theory -> theory
  val prove_classrel: class * class -> tactic -> theory -> theory
  val prove_arity: string * sort list * sort -> tactic -> theory -> theory
end;

structure AxClass: AX_CLASS =
struct

(** theory data **)

(* class parameters (canonical order) *)

type param = string * class;

fun add_param pp ((x, c): param) params =
  (case AList.lookup (op =) params x of
    NONE => (x, c) :: params
  | SOME c' => error ("Duplicate class parameter " ^ quote x ^
      " for " ^ Pretty.string_of_sort pp [c] ^
      (if c = c' then "" else " and " ^ Pretty.string_of_sort pp [c'])));

fun merge_params _ ([], qs) = qs
  | merge_params pp (ps, qs) =
      fold_rev (fn q => if member (op =) ps q then I else add_param pp q) qs ps;


(* axclass *)

val introN = "intro";
val axiomsN = "axioms";

datatype axclass = AxClass of
 {super_classes: class list,
  intro: thm,
  axioms: thm list};

fun make_axclass (super_classes, intro, axioms) =
  AxClass {super_classes = super_classes, intro = intro, axioms = axioms};

type axclasses = axclass Symtab.table * param list;

fun merge_axclasses pp ((tab1, params1), (tab2, params2)) : axclasses =
  (Symtab.merge (K true) (tab1, tab2), merge_params pp (params1, params2));


(* instances *)

datatype instances = Instances of
 {classes: unit Graph.T,                 (*raw relation -- no closure!*)
  classrel: ((class * class) * thm) list,
  arities: ((string * sort list * class) * thm) list};

fun make_instances (classes, classrel, arities) =
  Instances {classes = classes, classrel = classrel, arities = arities};

fun map_instances f (Instances {classes, classrel, arities}) =
  make_instances (f (classes, classrel, arities));

fun merge_instances
   (Instances {classes = classes1, classrel = classrel1, arities = arities1},
    Instances {classes = classes2, classrel = classrel2, arities = arities2}) =
  make_instances
   (Graph.merge (K true) (classes1, classes2),
    merge (eq_fst op =) (classrel1, classrel2),
    merge (eq_fst op =) (arities1, arities2));


(* data *)

structure AxClassData = TheoryDataFun
(struct
  val name = "Pure/axclass";
  type T = axclasses * instances;
  val empty : T = ((Symtab.empty, []), make_instances (Graph.empty, [], []));
  val copy = I;
  val extend = I;

  fun merge pp ((axclasses1, instances1), (axclasses2, instances2)) =
    (merge_axclasses pp (axclasses1, axclasses2), merge_instances (instances1, instances2));

  fun print thy ((axclasses, params), _) =
    let
      val ctxt = ProofContext.init thy;
      val prt_cls = ProofContext.pretty_sort ctxt o single;

      fun pretty_class c [] = prt_cls c
        | pretty_class c cs = Pretty.block
            (prt_cls c :: Pretty.str " <" :: Pretty.brk 1 :: Pretty.commas (map prt_cls cs));

      fun pretty_axclass (class, AxClass {super_classes, intro, axioms}) =
        Pretty.block (Pretty.fbreaks
         [pretty_class class super_classes,
          Pretty.strs ("parameters:" ::
            fold (fn (x, c) => if c = class then cons x else I) params []),
          ProofContext.pretty_fact ctxt (introN, [intro]),
          ProofContext.pretty_fact ctxt (axiomsN, axioms)]);
    in
      Pretty.writeln (Pretty.chunks (map pretty_axclass (Symtab.dest axclasses)))
    end;
end);

val _ = Context.add_setup AxClassData.init;
val print_axclasses = AxClassData.print;

val get_instances = AxClassData.get #> (fn (_, Instances insts) => insts);



(** axclass definitions **)

(* lookup *)

val lookup_info = Symtab.lookup o #1 o #1 o AxClassData.get;

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
    (bclass, raw_super_classes) params raw_axioms_atts thy =
  let
    val pp = Sign.pp thy;

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
      ||> AxClassData.map (apfst (fn (is, ps) =>
        (Symtab.update (class, info) is, fold (fn x => add_param pp (x, class)) params ps)));
  in (class, final_thy) end;

in

val add_axclass = gen_axclass Sign.intern_class Theory.read_axm Attrib.attribute;
val add_axclass_i = gen_axclass (K I) Theory.cert_axm (K I);

end;



(** instantiation proofs **)

(* parameters *)

fun params_of_sort thy S =
  let
    val range = Graph.all_succs (Sign.classes_of thy) (Sign.certify_sort thy S);
    val params = #2 (#1 (AxClassData.get thy));
  in fold (fn (x, c) => if member (op =) range c then cons x else I) params [] end;

fun cert_classrel thy raw_rel =
  let
    val (c1, c2) = pairself (Sign.certify_class thy) raw_rel;
    val _ = Type.add_classrel (Sign.pp thy) [(c1, c2)] (Sign.tsig_of thy);
    val _ =
      (case subtract (op =) (params_of_sort thy [c1]) (params_of_sort thy [c2]) of
        [] => ()
      | xs => raise TYPE ("Class " ^ Sign.string_of_sort thy [c1] ^ " lacks parameter(s) " ^
          commas_quote xs ^ " of " ^ Sign.string_of_sort thy [c2], [], []));
  in (c1, c2) end;

fun read_classrel thy raw_rel =
  cert_classrel thy (pairself (Sign.read_class thy) raw_rel)
    handle TYPE (msg, _, _) => error msg;


(* primitive rules *)

fun add_classrel th thy =
  let
    fun err () = raise THM ("add_classrel: malformed class relation", 0, [th]);
    val prop = Drule.plain_prop_of (Thm.transfer thy th);
    val rel = Logic.dest_classrel prop handle TERM _ => err ();
    val (c1, c2) = cert_classrel thy rel handle TYPE _ => err ();
  in
    thy
    |> Theory.add_classrel_i [(c1, c2)]
    |> AxClassData.map (apsnd (map_instances (fn (classes, classrel, arities) =>
      (classes
          |> Graph.default_node (c1, ())
          |> Graph.default_node (c2, ())
          |> Graph.add_edge (c1, c2),
        ((c1, c2), th) :: classrel, arities))))
  end;

fun add_arity th thy =
  let
    val prop = Drule.plain_prop_of (Thm.transfer thy th);
    val (t, Ss, c) = Logic.dest_arity prop handle TERM _ =>
      raise THM ("add_arity: malformed type arity", 0, [th]);
  in
    thy
    |> Theory.add_arities_i [(t, Ss, [c])]
    |> AxClassData.map (apsnd (map_instances (fn (classes, classrel, arities) =>
      (classes, classrel, ((t, Ss, c), th) :: arities))))
  end;


(* tactical proofs *)

fun prove_classrel raw_rel tac thy =
  let
    val (c1, c2) = cert_classrel thy raw_rel;
    val th = Goal.prove thy [] [] (Logic.mk_classrel (c1, c2)) (fn _ => tac) handle ERROR msg =>
      cat_error msg ("The error(s) above occurred while trying to prove class relation " ^
        quote (Sign.string_of_classrel thy [c1, c2]));
  in add_classrel th thy end;

fun prove_arity raw_arity tac thy =
  let
    val arity = Sign.cert_arity thy raw_arity;
    val props = Logic.mk_arities arity;
    val ths = Goal.prove_multi thy [] [] props
      (fn _ => Tactic.precise_conjunction_tac (length props) 1 THEN tac) handle ERROR msg =>
        cat_error msg ("The error(s) above occurred while trying to prove type arity " ^
          quote (Sign.string_of_arity thy arity));
  in fold add_arity ths thy end;

end;
