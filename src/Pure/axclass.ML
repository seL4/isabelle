(*  Title:      Pure/axclass.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Axiomatic type class package.
*)

signature AX_CLASS =
sig
  val quiet_mode: bool ref
  val print_axclasses: theory -> unit
  val get_info: theory -> string -> {super_classes: class list, intro: thm, axioms: thm list}
  val add_axclass: bstring * xstring list -> ((bstring * string) * Attrib.src list) list ->
    theory -> {intro: thm, axioms: thm list} * theory
  val add_axclass_i: bstring * class list -> ((bstring * term) * attribute list) list ->
    theory -> {intro: thm, axioms: thm list} * theory
  val add_classrel_thms: thm list -> theory -> theory
  val add_arity_thms: thm list -> theory -> theory
  val add_inst_subclass: xstring * xstring -> tactic -> theory -> theory
  val add_inst_subclass_i: class * class -> tactic -> theory -> theory
  val add_inst_arity: xstring * string list * string -> tactic -> theory -> theory
  val add_inst_arity_i: string * sort list * sort -> tactic -> theory -> theory
  val instance_subclass: xstring * xstring -> theory -> Proof.state
  val instance_subclass_i: class * class -> theory -> Proof.state
  val instance_arity: (theory -> theory) -> xstring * string list * string -> theory -> Proof.state
  val instance_arity_i: (theory -> theory) -> string * sort list * sort -> theory -> Proof.state
  val read_arity: theory -> xstring * string list * string -> arity
  val cert_arity: theory -> string * sort list * sort -> arity
  val intro_classes_tac: thm list -> tactic
  val default_intro_classes_tac: thm list -> tactic
end;

structure AxClass: AX_CLASS =
struct


(** utilities **)

(* messages *)

val quiet_mode = ref false;
fun message s = if ! quiet_mode then () else writeln s;


(* type vars *)

fun map_typ_frees f (Type (t, tys)) = Type (t, map (map_typ_frees f) tys)
  | map_typ_frees f (TFree a) = f a
  | map_typ_frees _ a = a;

val map_term_tfrees = map_term_types o map_typ_frees;

fun aT S = TFree ("'a", S);

fun dest_varT (TFree (x, S)) = ((x, ~1), S)
  | dest_varT (TVar xi_S) = xi_S
  | dest_varT T = raise TYPE ("dest_varT", [T], []);



(** abstract syntax operations **)

(* names *)

val introN = "intro";
val axiomsN = "axioms";


(* subclass relations as terms *)

fun mk_classrel (c1, c2) = Logic.mk_inclass (aT [c1], c2);

fun dest_classrel tm =
  let
    fun err () = raise TERM ("dest_classrel", [tm]);

    val (ty, c2) = Logic.dest_inclass tm handle TERM _ => err ();
    val c1 = (case dest_varT ty of (_, [c]) => c | _ => err ())
      handle TYPE _ => err ();
  in (c1, c2) end;


(* arities as terms *)

fun mk_arity (t, Ss, c) =
  let
    val tfrees = ListPair.map TFree (Term.invent_names [] "'a" (length Ss), Ss);
  in Logic.mk_inclass (Type (t, tfrees), c) end;

fun mk_arities (t, Ss, S) = map (fn c => mk_arity (t, Ss, c)) S;

fun dest_arity tm =
  let
    fun err () = raise TERM ("dest_arity", [tm]);

    val (ty, c) = Logic.dest_inclass tm handle TERM _ => err ();
    val (t, tvars) =
      (case ty of
        Type (t, tys) => (t, map dest_varT tys handle TYPE _ => err ())
      | _ => err ());
    val ss =
      if null (gen_duplicates (eq_fst (op =)) tvars)
      then map snd tvars else err ();
  in (t, ss, c) end;



(** axclass info **)

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


fun class_axms thy =
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

fun ext_axclass prep_class prep_axm prep_att (bclass, raw_super_classes) raw_axioms_atts thy =
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
      else map_term_tfrees (K (aT [class])) ax;
    val abs_axms = map (abs_axm o snd) axms;

    fun axm_sort (name, ax) =
      (case term_tfrees ax of
        [] => []
      | [(_, S)] => if Sign.subsort class_thy ([class], S) then S else err_bad_axsort name class
      | _ => err_bad_tfrees name);
    val axS = Sign.certify_sort class_thy (List.concat (map axm_sort axms));

    val int_axm = Logic.close_form o map_term_tfrees (K (aT axS));
    fun inclass c = Logic.mk_inclass (aT axS, c);

    val intro_axm = Logic.list_implies
      (map inclass super_classes @ map (int_axm o #2) axms, inclass class);

    (*declare axioms and rule*)
    val (([intro], [axioms]), axms_thy) =
      class_thy
      |> Theory.add_path (Sign.const_of_class bclass)
      |> PureThy.add_axioms_i [Thm.no_attributes (introN, intro_axm)]
      ||>> PureThy.add_axiomss_i [Thm.no_attributes (axiomsN, abs_axms)];
    val info = {super_classes = super_classes, intro = intro, axioms = axioms};

    (*store info*)
    val (_, final_thy) =
      axms_thy
      |> Theory.add_finals_i false [Const (Sign.const_of_class class, a_itselfT --> propT)]
      |> PureThy.add_thms ((map #1 axms ~~ axioms) ~~ atts)
      ||> Theory.restore_naming class_thy
      ||> AxclassesData.map (Symtab.update (class, info));
  in ({intro = intro, axioms = axioms}, final_thy) end;

in

val add_axclass = ext_axclass Sign.intern_class Theory.read_axm Attrib.attribute;
val add_axclass_i = ext_axclass (K I) Theory.cert_axm (K I);

end;



(** proven class instantiation **)

(* add thms to type signature *)

fun add_classrel_thms thms thy =
  let
    fun prep_thm thm =
      let
        val prop = Drule.plain_prop_of (Thm.transfer thy thm);
        val (c1, c2) = dest_classrel prop handle TERM _ =>
          raise THM ("add_classrel_thms: not a class relation", 0, [thm]);
      in (c1, c2) end;
  in Theory.add_classrel_i (map prep_thm thms) thy end;

fun add_arity_thms thms thy =
  let
    fun prep_thm thm =
      let
        val prop = Drule.plain_prop_of (Thm.transfer thy thm);
        val (t, ss, c) = dest_arity prop handle TERM _ =>
          raise THM ("add_arity_thms: not an arity", 0, [thm]);
      in (t, ss, [c]) end;
  in Theory.add_arities_i (map prep_thm thms) thy end;


(* prepare classes and arities *)

fun read_class thy c = Sign.certify_class thy (Sign.intern_class thy c);

fun test_classrel thy cc = (Type.add_classrel (Sign.pp thy) [cc] (Sign.tsig_of thy); cc);
fun cert_classrel thy = test_classrel thy o Library.pairself (Sign.certify_class thy);
fun read_classrel thy = test_classrel thy o Library.pairself (read_class thy);

fun test_arity thy ar = (Type.add_arities (Sign.pp thy) [ar] (Sign.tsig_of thy); ar);

fun prep_arity prep_tycon prep_sort prep thy (t, Ss, x) =
  test_arity thy (prep_tycon thy t, map (prep_sort thy) Ss, prep thy x);

val read_arity = prep_arity Sign.intern_type Sign.read_sort Sign.read_sort;
val cert_arity = prep_arity (K I) Sign.certify_sort Sign.certify_sort;


(* instance declarations -- tactical proof *)

local

fun ext_inst_subclass prep_classrel raw_cc tac thy =
  let
    val (c1, c2) = prep_classrel thy raw_cc;
    val txt = quote (Sign.string_of_classrel thy [c1, c2]);
    val _ = message ("Proving class inclusion " ^ txt ^ " ...");
    val th = Goal.prove thy [] [] (mk_classrel (c1, c2)) (K tac) handle ERROR msg =>
      cat_error msg ("The error(s) above occurred while trying to prove " ^ txt);
  in add_classrel_thms [th] thy end;

fun ext_inst_arity prep_arity raw_arity tac thy =
  let
    val arity = prep_arity thy raw_arity;
    val txt = quote (Sign.string_of_arity thy arity);
    val _ = message ("Proving type arity " ^ txt ^ " ...");
    val props = (mk_arities arity);
    val ths = Goal.prove_multi thy [] [] props
      (fn _ => Tactic.precise_conjunction_tac (length props) 1 THEN tac) handle ERROR msg =>
        cat_error msg ("\nThe error(s) above occurred while trying to prove " ^ txt);
  in add_arity_thms ths thy end;

in

val add_inst_subclass = ext_inst_subclass read_classrel;
val add_inst_subclass_i = ext_inst_subclass cert_classrel;
val add_inst_arity = ext_inst_arity read_arity;
val add_inst_arity_i = ext_inst_arity cert_arity;

end;


(* instance declarations -- Isar proof *)

local

fun gen_instance mk_prop add_thms after_qed inst thy =
  thy
  |> ProofContext.init
  |> Proof.theorem_i Drule.internalK NONE (after_qed oo fold add_thms) NONE ("", [])
       (map (fn t => (("", []), [(t, ([], []))])) (mk_prop thy inst));

in

val instance_subclass =
  gen_instance (single oo (mk_classrel oo read_classrel)) add_classrel_thms I;
val instance_subclass_i =
  gen_instance (single oo (mk_classrel oo cert_classrel)) add_classrel_thms I;
val instance_arity =
  gen_instance (mk_arities oo read_arity) add_arity_thms;
val instance_arity_i =
  gen_instance (mk_arities oo cert_arity) add_arity_thms;

end;


(* tactics and methods *)

fun intro_classes_tac facts st =
  (ALLGOALS (Method.insert_tac facts THEN'
      REPEAT_ALL_NEW (resolve_tac (class_axms (Thm.theory_of_thm st))))
    THEN Tactic.distinct_subgoals_tac) st;

fun default_intro_classes_tac [] = intro_classes_tac []
  | default_intro_classes_tac _ = Tactical.no_tac;    (*no error message!*)

fun default_tac rules ctxt facts =
  HEADGOAL (Method.some_rule_tac rules ctxt facts) ORELSE
    default_intro_classes_tac facts;

val _ = Context.add_setup (Method.add_methods
 [("intro_classes", Method.no_args (Method.METHOD intro_classes_tac),
    "back-chain introduction rules of axiomatic type classes"),
  ("default", Method.thms_ctxt_args (Method.METHOD oo default_tac), "apply some intro/elim rule")]);



(** outer syntax **)

local structure P = OuterParse and K = OuterKeyword in

val axclassP =
  OuterSyntax.command "axclass" "define axiomatic type class" K.thy_decl
    ((P.name -- Scan.optional ((P.$$$ "\\<subseteq>" || P.$$$ "<") |--
        P.!!! (P.list1 P.xname)) []) -- Scan.repeat P.spec_name
      >> (Toplevel.theory o (snd oo uncurry add_axclass)));

val instanceP =
  OuterSyntax.command "instance" "prove type arity or subclass relation" K.thy_goal
   ((P.xname -- ((P.$$$ "\\<subseteq>" || P.$$$ "<") |-- P.!!! P.xname) >> instance_subclass ||
      P.xname -- (P.$$$ "::" |-- P.!!! P.arity) >> (instance_arity I o P.triple2))
    >> (Toplevel.print oo Toplevel.theory_to_proof));

val _ = OuterSyntax.add_parsers [axclassP, instanceP];

end;

end;
