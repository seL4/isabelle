(*  Title:      Pure/axclass.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

User interfaces for axiomatic type classes.
*)

signature AX_CLASS =
  sig
  val add_thms_as_axms: (string * thm) list -> theory -> theory
  val add_classrel_thms: thm list -> theory -> theory
  val add_arity_thms: thm list -> theory -> theory
  val add_axclass: class * class list -> (string * string) list
    -> theory -> theory
  val add_axclass_i: class * class list -> (string * term) list
    -> theory -> theory
  val add_inst_subclass_i: class * class -> string list -> thm list
    -> tactic option -> theory -> theory
  val add_inst_subclass: class * class -> string list -> thm list
    -> tactic option -> theory -> theory
  val add_inst_arity_i: string * sort list * class list -> string list
    -> thm list -> tactic option -> theory -> theory
  val add_inst_arity: string * sort list * class list -> string list
    -> thm list -> tactic option -> theory -> theory
  val axclass_tac: theory -> thm list -> tactic
  val prove_subclass: theory -> class * class -> thm list
    -> tactic option -> thm
  val prove_arity: theory -> string * sort list * class -> thm list
    -> tactic option -> thm
  val goal_subclass: theory -> class * class -> thm list
  val goal_arity: theory -> string * sort list * class -> thm list
  end;

structure AxClass : AX_CLASS =
struct

(** utilities **)

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

fun get_ax thy name =
  Some (get_axiom thy name) handle THEORY _ => None;

val get_axioms = mapfilter o get_ax;

val is_def = Logic.is_equals o #prop o rep_thm;

fun witnesses thy axms thms =
  map (get_axiom thy) axms @ thms @ filter is_def (map snd (axioms_of thy));



(** abstract syntax operations **)

(* subclass relations as terms *)

fun mk_classrel (c1, c2) = Logic.mk_inclass (aT [c1], c2);

fun dest_classrel tm =
  let
    fun err () = raise TERM ("dest_classrel", [tm]);

    val (ty, c2) = Logic.dest_inclass tm handle TERM _ => err ();
    val c1 = (case dest_varT ty of (_, [c]) => c | _ => err ())
      handle TYPE _ => err ();
  in
    (c1, c2)
  end;


(* arities as terms *)

fun mk_arity (t, ss, c) =
  let
    val names = tl (variantlist (replicate (length ss + 1) "'", []));
    val tfrees = ListPair.map TFree (names, ss);
  in
    Logic.mk_inclass (Type (t, tfrees), c)
  end;

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
  in
    (t, ss, c)
  end;



(** add theorems as axioms **)

fun prep_thm_axm thy thm =
  let
    fun err msg = raise THM ("prep_thm_axm: " ^ msg, 0, [thm]);

    val {sign, hyps, prop, ...} = rep_thm thm;
  in
    if not (Sign.subsig (sign, sign_of thy)) then
      err "theorem not of same theory"
    else if not (null (extra_shyps thm)) orelse not (null hyps) then
      err "theorem may not contain hypotheses"
    else prop
  end;

(*general theorems*)
fun add_thms_as_axms thms thy =
  Theory.add_axioms_i (map (apsnd (prep_thm_axm thy)) thms) thy;

(*theorems expressing class relations*)
fun add_classrel_thms thms thy =
  let
    fun prep_thm thm =
      let
        val prop = prep_thm_axm thy thm;
        val (c1, c2) = dest_classrel prop handle TERM _ =>
          raise THM ("add_classrel_thms: theorem is not a class relation", 0, [thm]);
      in (c1, c2) end;
  in
    Theory.add_classrel (map prep_thm thms) thy
  end;

(*theorems expressing arities*)
fun add_arity_thms thms thy =
  let
    fun prep_thm thm =
      let
        val prop = prep_thm_axm thy thm;
        val (t, ss, c) = dest_arity prop handle TERM _ =>
          raise THM ("add_arity_thms: theorem is not an arity", 0, [thm]);
      in (t, ss, [c]) end;
  in
    Theory.add_arities (map prep_thm thms) thy
  end;



(** add axiomatic type classes **)

(* errors *)

fun err_not_logic c =
  error ("Axiomatic class " ^ quote c ^ " not subclass of \"logic\"");

fun err_bad_axsort ax c =
  error ("Sort constraint in axiom " ^ quote ax ^ " not supersort of " ^ quote c);

fun err_bad_tfrees ax =
  error ("More than one type variable in axiom " ^ quote ax);


(* ext_axclass *)

fun ext_axclass int prep_axm (raw_class, raw_super_classes) raw_axioms old_thy =
  let
    val axioms = map (prep_axm (sign_of old_thy)) raw_axioms;
    val thy =
      (if int then Theory.add_classes else Theory.add_classes_i)
        [(raw_class, raw_super_classes)] old_thy;
    val sign = sign_of thy;
    val class = Sign.intern_class sign raw_class;
    val super_classes = map (Sign.intern_class sign) raw_super_classes;


    (* prepare abstract axioms *)

    fun abs_axm ax =
      if null (term_tfrees ax) then
        Logic.mk_implies (Logic.mk_inclass (aT logicS, class), ax)
      else map_term_tfrees (K (aT [class])) ax;

    val abs_axioms = map (apsnd abs_axm) axioms;


    (* prepare introduction orule *)

    val _ =
      if Sign.subsort sign ([class], logicS) then ()
      else err_not_logic class;

    fun axm_sort (name, ax) =
      (case term_tfrees ax of
        [] => []
      | [(_, S)] =>
          if Sign.subsort sign ([class], S) then S
          else err_bad_axsort name class
      | _ => err_bad_tfrees name);

    val axS = Sign.norm_sort sign (logicC :: flat (map axm_sort axioms))

    val int_axm = Logic.close_form o map_term_tfrees (K (aT axS));
    fun inclass c = Logic.mk_inclass (aT axS, c);

    val intro_axm = Logic.list_implies
      (map inclass super_classes @ map (int_axm o snd) axioms, inclass class);
  in
    Theory.add_axioms_i ((raw_class ^ "I", intro_axm) :: abs_axioms) thy
  end;


(* external interfaces *)

val add_axclass = ext_axclass true read_axm;
val add_axclass_i = ext_axclass false cert_axm;



(** prove class relations and type arities **)

(* class_axms *)

fun class_axms thy =
  let
    val classes = Sign.classes (sign_of thy);
    val intros = map (fn c => c ^ "I") classes;
  in
    map (class_triv thy) classes @
    get_axioms thy intros
  end;


(* axclass_tac *)

(*(1) repeatedly resolve goals of form "OFCLASS(ty, c_class)",
      try class_trivs first, then "cI" axioms
  (2) rewrite goals using user supplied definitions
  (3) repeatedly resolve goals with user supplied non-definitions*)

fun axclass_tac thy thms =
  let
    val defs = filter is_def thms;
    val non_defs = filter_out is_def thms;
  in
    TRY (REPEAT_FIRST (resolve_tac (class_axms thy))) THEN
    TRY (rewrite_goals_tac defs) THEN
    TRY (REPEAT_FIRST (fn i => assume_tac i ORELSE resolve_tac non_defs i))
  end;


(* provers *)

fun prove term_of str_of thy sig_prop thms usr_tac =
  let
    val sign = sign_of thy;
    val goal = cterm_of sign (term_of sig_prop);
    val tac = axclass_tac thy thms THEN (if_none usr_tac all_tac);
  in
    prove_goalw_cterm [] goal (K [tac])
  end
  handle ERROR => error ("The error(s) above occurred while trying to prove "
    ^ quote (str_of sig_prop));

val prove_subclass =
  prove mk_classrel (fn (c1, c2) => c1 ^ " < " ^ c2);

val prove_arity =
  prove mk_arity (fn (t, ss, c) => Sorts.str_of_arity (t, ss, [c]));


(* make goals (for interactive use) *)

fun mk_goal term_of thy sig_prop =
  goalw_cterm [] (cterm_of (sign_of thy) (term_of sig_prop));

val goal_subclass = mk_goal mk_classrel;
val goal_arity = mk_goal mk_arity;



(** add proved subclass relations and arities **)

fun ext_inst_subclass int raw_c1_c2 axms thms usr_tac thy =
  let
    val intrn = if int then pairself (Sign.intern_class (sign_of thy)) else I;
    val c1_c2 = intrn raw_c1_c2;
  in
    writeln ("Proving class inclusion " ^ quote (Sorts.str_of_classrel c1_c2) ^ " ...");
    add_classrel_thms
      [prove_subclass thy c1_c2 (witnesses thy axms thms) usr_tac] thy
  end;


fun ext_inst_arity int (raw_t, raw_Ss, raw_cs) axms thms usr_tac thy =
  let
    val sign = sign_of thy;
    val (t, Ss, cs) =
      if int then
        (Sign.intern_tycon sign raw_t,
          map (Sign.intern_sort sign) raw_Ss,
          map (Sign.intern_class sign) raw_cs)
      else (raw_t, raw_Ss, raw_cs);
    val wthms = witnesses thy axms thms;
    fun prove c =
     (writeln ("Proving type arity " ^ quote (Sorts.str_of_arity (t, Ss, [c])) ^ " ...");
      prove_arity thy (t, Ss, c) wthms usr_tac);
  in
    add_arity_thms (map prove cs) thy
  end;

val add_inst_subclass = ext_inst_subclass true;
val add_inst_subclass_i = ext_inst_subclass false;
val add_inst_arity = ext_inst_arity true;
val add_inst_arity_i = ext_inst_arity false;


end;
