(*  Title:      Pure/axclass.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Axiomatic type class package.
*)

signature AX_CLASS =
sig
  val quiet_mode: bool ref
  val print_axclasses: theory -> unit
  val add_classrel_thms: thm list -> theory -> theory
  val add_arity_thms: thm list -> theory -> theory
  val add_axclass: bclass * xclass list -> ((bstring * string) * Args.src list) list
    -> theory -> theory * {intro: thm, axioms: thm list}
  val add_axclass_i: bclass * class list -> ((bstring * term) * theory attribute list) list
    -> theory -> theory * {intro: thm, axioms: thm list}
  val add_inst_subclass: xclass * xclass -> string list -> thm list
    -> tactic option -> theory -> theory
  val add_inst_subclass_i: class * class -> string list -> thm list
    -> tactic option -> theory -> theory
  val add_inst_arity: xstring * xsort list * xclass list -> string list
    -> thm list -> tactic option -> theory -> theory
  val add_inst_arity_i: string * sort list * class list -> string list
    -> thm list -> tactic option -> theory -> theory
  val axclass_tac: thm list -> tactic
  val prove_subclass: theory -> class * class -> thm list
    -> tactic option -> thm
  val prove_arity: theory -> string * sort list * class -> thm list
    -> tactic option -> thm
  val goal_subclass: theory -> xclass * xclass -> thm list
  val goal_arity: theory -> xstring * xsort list * xclass -> thm list
  val instance_subclass_proof: (xclass * xclass) * Comment.text -> bool -> theory -> ProofHistory.T
  val instance_subclass_proof_i: (class * class) * Comment.text -> bool -> theory -> ProofHistory.T
  val instance_arity_proof: (xstring * xsort list * xclass) * Comment.text
    -> bool -> theory -> ProofHistory.T
  val instance_arity_proof_i: (string * sort list * class) * Comment.text
    -> bool -> theory -> ProofHistory.T
  val setup: (theory -> theory) list
end;

structure AxClass : AX_CLASS =
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


(* get axioms and theorems *)

val is_def = Logic.is_equals o #prop o rep_thm;

fun witnesses thy names thms =
  PureThy.get_thmss thy names @ thms @ filter is_def (map snd (axioms_of thy));



(** abstract syntax operations **)

(* names *)

fun intro_name c = c ^ "I";
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

fun mk_arity (t, ss, c) =
  let
    val names = tl (variantlist (replicate (length ss + 1) "'", []));
    val tfrees = ListPair.map TFree (names, ss);
  in Logic.mk_inclass (Type (t, tfrees), c) end;

fun dest_arity tm =
  let
    fun err () = raise TERM ("dest_arity", [tm]);

    val (ty, c) = Logic.dest_inclass tm handle TERM _ => err ();
    val (t, tvars) =
      (case ty of
        Type (t, tys) => (t, map dest_varT tys handle TYPE _ => err ())
      | _ => err ());
    val ss =
      if null (gen_duplicates eq_fst tvars)
      then map snd tvars else err ();
  in (t, ss, c) end;



(** add theorems as axioms **)

fun prep_thm_axm thy thm =
  let
    fun err msg = raise THM ("prep_thm_axm: " ^ msg, 0, [thm]);

    val {sign, hyps, prop, ...} = rep_thm thm;
  in
    if not (Sign.subsig (sign, Theory.sign_of thy)) then
      err "theorem not of same theory"
    else if not (null (extra_shyps thm)) orelse not (null hyps) then
      err "theorem may not contain hypotheses"
    else prop
  end;

(*theorems expressing class relations*)
fun add_classrel_thms thms thy =
  let
    fun prep_thm thm =
      let
        val prop = prep_thm_axm thy thm;
        val (c1, c2) = dest_classrel prop handle TERM _ =>
          raise THM ("add_classrel_thms: theorem is not a class relation", 0, [thm]);
      in (c1, c2) end;
  in Theory.add_classrel (map prep_thm thms) thy end;

(*theorems expressing arities*)
fun add_arity_thms thms thy =
  let
    fun prep_thm thm =
      let
        val prop = prep_thm_axm thy thm;
        val (t, ss, c) = dest_arity prop handle TERM _ =>
          raise THM ("add_arity_thms: theorem is not an arity", 0, [thm]);
      in (t, ss, [c]) end;
  in Theory.add_arities (map prep_thm thms) thy end;



(** axclass info **)

(* data kind 'Pure/axclasses' *)

type axclass_info =
  {super_classes: class list,
    intro: thm,
    axioms: thm list};

structure AxclassesArgs =
struct
  val name = "Pure/axclasses";
  type T = axclass_info Symtab.table;

  val empty = Symtab.empty;
  val copy = I;
  val prep_ext = I;
  fun merge (tab1, tab2) = Symtab.merge (K true) (tab1, tab2);

  fun print sg tab =
    let
      val ext_class = Sign.cond_extern sg Sign.classK;
      val ext_thm = PureThy.cond_extern_thm_sg sg;

      fun pretty_class c cs = Pretty.block
        (Pretty.str (ext_class c) :: Pretty.str " <" :: Pretty.brk 1 ::
          Pretty.breaks (map (Pretty.str o ext_class) cs));

      fun pretty_thms name thms = Pretty.big_list (name ^ ":") (map Display.pretty_thm thms);

      fun pretty_axclass (name, {super_classes, intro, axioms}) = Pretty.block (Pretty.fbreaks
        [pretty_class name super_classes, pretty_thms introN [intro], pretty_thms axiomsN axioms]);
    in Pretty.writeln (Pretty.chunks (map pretty_axclass (Symtab.dest tab))) end;
end;

structure AxclassesData = TheoryDataFun(AxclassesArgs);
val print_axclasses = AxclassesData.print;


(* get and put data *)

fun lookup_axclass_info_sg sg c = Symtab.lookup (AxclassesData.get_sg sg, c);

fun get_axclass_info thy c =
  (case lookup_axclass_info_sg (Theory.sign_of thy) c of
    None => error ("Unknown axclass " ^ quote c)
  | Some info => info);

fun put_axclass_info c info thy =
  thy |> AxclassesData.put (Symtab.update ((c, info), AxclassesData.get thy));



(** add axiomatic type classes **)

(* errors *)

fun err_not_logic c =
  error ("Axiomatic class " ^ quote c ^ " not subclass of " ^ quote logicC);

fun err_bad_axsort ax c =
  error ("Sort constraint in axiom " ^ quote ax ^ " not supersort of " ^ quote c);

fun err_bad_tfrees ax =
  error ("More than one type variable in axiom " ^ quote ax);


(* ext_axclass *)

fun ext_axclass prep_class prep_axm prep_att (bclass, raw_super_classes) raw_axioms_atts thy =
  let
    val sign = Theory.sign_of thy;

    val class = Sign.full_name sign bclass;
    val super_classes = map (prep_class sign) raw_super_classes;
    val axms = map (prep_axm sign o fst) raw_axioms_atts;
    val atts = map (map (prep_att thy) o snd) raw_axioms_atts;

    (*declare class*)
    val class_thy =
      thy |> Theory.add_classes_i [(bclass, super_classes)];
    val class_sign = Theory.sign_of class_thy;

    (*prepare abstract axioms*)
    fun abs_axm ax =
      if null (term_tfrees ax) then
        Logic.mk_implies (Logic.mk_inclass (aT logicS, class), ax)
      else map_term_tfrees (K (aT [class])) ax;
    val abs_axms = map (abs_axm o #2) axms;

    (*prepare introduction rule*)
    val _ = if Sign.subsort class_sign ([class], logicS) then () else err_not_logic class;

    fun axm_sort (name, ax) =
      (case term_tfrees ax of
        [] => []
      | [(_, S)] => if Sign.subsort class_sign ([class], S) then S else err_bad_axsort name class
      | _ => err_bad_tfrees name);
    val axS = Sign.norm_sort class_sign (logicC :: flat (map axm_sort axms));

    val int_axm = Logic.close_form o map_term_tfrees (K (aT axS));
    fun inclass c = Logic.mk_inclass (aT axS, c);

    val intro_axm = Logic.list_implies
      (map inclass super_classes @ map (int_axm o #2) axms, inclass class);

    (*declare axioms and rule*)
    val (axms_thy, ([intro], [axioms])) =
      class_thy
      |> Theory.add_path bclass
      |> PureThy.add_axioms_i [Thm.no_attributes (introN, intro_axm)]
      |>>> PureThy.add_axiomss_i [Thm.no_attributes (axiomsN, abs_axms)];
    val info = {super_classes = super_classes, intro = intro, axioms = axioms};

    (*store info*)
    val final_thy =
      axms_thy
      |> (#1 o PureThy.add_thms ((map #1 axms ~~ axioms) ~~ atts))
      |> Theory.parent_path
      |> (#1 o PureThy.add_thms [Thm.no_attributes (intro_name bclass, intro)])
      |> put_axclass_info class info;
  in (final_thy, {intro = intro, axioms = axioms}) end;


(* external interfaces *)

val add_axclass = ext_axclass Sign.intern_class Theory.read_axm Attrib.global_attribute;
val add_axclass_i = ext_axclass (K I) Theory.cert_axm (K I);



(** prove class relations and type arities **)

(* class_axms *)

fun class_axms sign =
  let val classes = Sign.classes sign in
    map (Thm.class_triv sign) classes @
    mapfilter (apsome #intro o lookup_axclass_info_sg sign) classes
  end;


(* intro_classes *)

fun intro_classes_tac facts st =
  HEADGOAL (Method.insert_tac facts THEN'
      REPEAT_ALL_NEW (resolve_tac (class_axms (Thm.sign_of_thm st)))) st;

val intro_classes_method =
  ("intro_classes", Method.no_args (Method.METHOD intro_classes_tac),
    "back-chain introduction rules of axiomatic type classes");


(* axclass_tac *)

(*(1) repeatedly resolve goals of form "OFCLASS(ty, c_class)",
      try class_trivs first, then "cI" axioms
  (2) rewrite goals using user supplied definitions
  (3) repeatedly resolve goals with user supplied non-definitions*)

fun axclass_tac thms =
  let
    val defs = filter is_def thms;
    val non_defs = filter_out is_def thms;
  in
    intro_classes_tac [] THEN
    TRY (rewrite_goals_tac defs) THEN
    TRY (REPEAT_FIRST (fn i => assume_tac i ORELSE resolve_tac non_defs i))
  end;


(* provers *)

fun prove mk_prop str_of thy sig_prop thms usr_tac =
  let
    val sign = Theory.sign_of thy;
    val goal = Thm.cterm_of sign (mk_prop sig_prop)
      handle TERM (msg, _) => error msg
        | TYPE (msg, _, _) => error msg;
    val tac = axclass_tac thms THEN (if_none usr_tac all_tac);
  in
    prove_goalw_cterm [] goal (K [tac])
  end
  handle ERROR => error ("The error(s) above occurred while trying to prove "
    ^ quote (str_of (Theory.sign_of thy, sig_prop)));

val prove_subclass =
  prove mk_classrel (fn (sg, c1_c2) => Sign.str_of_classrel sg c1_c2);

val prove_arity =
  prove mk_arity (fn (sg, (t, Ss, c)) => Sign.str_of_arity sg (t, Ss, [c]));



(** add proved subclass relations and arities **)

fun intrn_classrel sg c1_c2 =
  pairself (Sign.intern_class sg) c1_c2;

fun intrn_arity intrn sg (raw_t, Ss, x) =
  let val t = Sign.intern_tycon sg raw_t in
    if Sign.is_type_abbr sg t then error ("Illegal type abbreviation: " ^ quote t)
    else (t, map (Sign.intern_sort sg) Ss, intrn sg x)
  end;


fun ext_inst_subclass prep_classrel raw_c1_c2 names thms usr_tac thy =
  let val c1_c2 = prep_classrel (Theory.sign_of thy) raw_c1_c2 in
    message ("Proving class inclusion " ^
      quote (Sign.str_of_classrel (Theory.sign_of thy) c1_c2) ^ " ...");
    thy |> add_classrel_thms [prove_subclass thy c1_c2 (witnesses thy names thms) usr_tac]
  end;

fun ext_inst_arity prep_arity (raw_t, raw_Ss, raw_cs) names thms usr_tac thy =
  let
    val sign = Theory.sign_of thy;
    val (t, Ss, cs) = prep_arity sign (raw_t, raw_Ss, raw_cs);
    val wthms = witnesses thy names thms;
    fun prove c =
     (message ("Proving type arity " ^
        quote (Sign.str_of_arity sign (t, Ss, [c])) ^ " ...");
        prove_arity thy (t, Ss, c) wthms usr_tac);
  in add_arity_thms (map prove cs) thy end;


val add_inst_subclass = ext_inst_subclass intrn_classrel;
val add_inst_subclass_i = ext_inst_subclass (K I);
val add_inst_arity = ext_inst_arity (intrn_arity Sign.intern_sort);
val add_inst_arity_i = ext_inst_arity (K I);


(* make old-style interactive goals *)

fun mk_goal mk_prop thy sig_prop =
  Goals.goalw_cterm [] (Thm.cterm_of (Theory.sign_of thy) (mk_prop (Theory.sign_of thy) sig_prop));

val goal_subclass = mk_goal (mk_classrel oo intrn_classrel);
val goal_arity = mk_goal (mk_arity oo intrn_arity Sign.intern_class);



(** instance proof interfaces **)

fun inst_attribute add_thms (thy, thm) = (add_thms [thm] thy, thm);

fun inst_proof mk_prop add_thms (sig_prop, comment) int thy =
  thy
  |> IsarThy.theorem_i (("", [inst_attribute add_thms],
    (mk_prop (Theory.sign_of thy) sig_prop, ([], []))), comment) int;

val instance_subclass_proof = inst_proof (mk_classrel oo intrn_classrel) add_classrel_thms;
val instance_subclass_proof_i = inst_proof (K mk_classrel) add_classrel_thms;
val instance_arity_proof = inst_proof (mk_arity oo intrn_arity Sign.intern_class) add_arity_thms;
val instance_arity_proof_i = inst_proof (K mk_arity) add_arity_thms;



(** package setup **)

(* setup theory *)

val setup =
 [AxclassesData.init,
  Method.add_methods [intro_classes_method]];


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val axclassP =
  OuterSyntax.command "axclass" "define axiomatic type class" K.thy_decl
    (((P.name -- Scan.optional (P.$$$ "<" |-- P.!!! (P.list1 P.xname)) []) --| P.marg_comment)
      -- Scan.repeat (P.spec_name --| P.marg_comment)
      >> (fn (cls, axs) => Toplevel.theory (#1 o add_axclass cls axs)));

val instanceP =
  OuterSyntax.command "instance" "prove type arity or subclass relation" K.thy_goal
    ((P.xname -- (P.$$$ "<" |-- P.xname) -- P.marg_comment >> instance_subclass_proof ||
      (P.xname -- (P.$$$ "::" |-- P.simple_arity) >> P.triple2) -- P.marg_comment
        >> instance_arity_proof)
      >> (Toplevel.print oo Toplevel.theory_to_proof));

val _ = OuterSyntax.add_parsers [axclassP, instanceP];

end;


end;
