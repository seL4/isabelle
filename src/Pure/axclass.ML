(*  Title:      Pure/axclass.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

User interface for axiomatic type classes.

TODO:
  arity_tac: FILTER is_arity (?), assume_tac (?) (no?)
*)

signature AX_CLASS =
sig
  structure Tactical: TACTICAL
  local open Tactical Tactical.Thm in
    val add_axclass: class * class list -> (string * string) list
      -> theory -> theory
    val add_axclass_i: class * class list -> (string * term) list
      -> theory -> theory
    val add_instance: string * sort list * class -> string list -> thm list
      -> tactic option -> theory -> theory
    val axclass_tac: theory -> tactic
  end
end;

functor AxClassFun(structure Logic: LOGIC and Goals: GOALS and Tactic: TACTIC
  sharing Goals.Tactical = Tactic.Tactical)(*: AX_CLASS *) = (* FIXME *)
struct

structure Tactical = Goals.Tactical;
structure Thm = Tactical.Thm;
structure Sign = Thm.Sign;
structure Type = Sign.Type;

open Logic Thm Tactical Tactic Goals;


(* FIXME -> type.ML *)

structure Type =
struct
  open Type;

  fun str_of_sort [c] = c
    | str_of_sort cs = parents "{" "}" (commas cs);

  fun str_of_dom dom = parents "(" ")" (commas (map str_of_sort dom));

  fun str_of_arity (t, [], S) = t ^ " :: " ^ str_of_sort S
    | str_of_arity (t, SS, S) =
        t ^ " :: " ^ str_of_dom SS ^ " " ^ str_of_sort S;
end;


(** add constant definitions **)  (* FIXME -> drule.ML (?) *)

(* FIXME fake! *)
val add_defns = add_axioms;
val add_defns_i = add_axioms_i;


(** utilities **)

(* type vars *)

fun map_typ_frees f (Type (t, tys)) = Type (t, map (map_typ_frees f) tys)
  | map_typ_frees f (TFree a) = f a
  | map_typ_frees _ a = a;

val map_term_tfrees = map_term_types o map_typ_frees;

fun aT S = TFree ("'a", S);


(* get axioms *)

fun get_ax thy name =
  Some (get_axiom thy name) handle THEORY _ => None;

val get_axioms = mapfilter o get_ax;


(* is_defn *)

fun is_defn thm =
  (case #prop (rep_thm thm) of
    Const ("==", _) $ _ $ _ => true
  | _ => false);



(** add axiomatic type class **)

(* errors *)

fun err_not_logic c =
  error ("Axiomatic class " ^ quote c ^ " not subclass of \"logic\"");

fun err_bad_axsort ax c =
  error ("Sort constraint in axiom " ^ quote ax ^ " not supersort of " ^ quote c);

fun err_bad_tfrees ax =
  error ("More than one type variable in axiom " ^ quote ax);


(* ext_axclass *)

fun ext_axclass prep_axm (class, super_classes) raw_axioms old_thy =
  let
    val axioms = map (prep_axm (sign_of old_thy)) raw_axioms;
    val thy = add_classes [([], class, super_classes)] old_thy;
    val sign = sign_of thy;


    (* prepare abstract axioms *)

    fun abs_axm ax =
      if null (term_tfrees ax) then
        mk_implies (mk_inclass (aT logicS, class), ax)
      else
        map_term_tfrees (K (aT [class])) ax;

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

    val axS = Sign.norm_sort sign (logicC :: flat (map axm_sort axioms));

    val int_axm = close_form o map_term_tfrees (K (aT axS));
    fun inclass c = mk_inclass (aT axS, c);

    val intro_axm = list_implies
      (map inclass super_classes @ map (int_axm o snd) axioms, inclass class);
  in
    add_axioms_i ((class ^ "I", intro_axm) :: abs_axioms) thy
  end;


(* external interfaces *)

val add_axclass = ext_axclass read_axm;
val add_axclass_i = ext_axclass cert_axm;



(** add class instance **)

(* arities as terms *)

fun mk_arity (t, ss, c) =
  let
    val names = variantlist (replicate (length ss) "'a", []);
    val tvars = map (fn a => TVar ((a, 0), logicS)) names;
  in
    mk_inclass (Type (t, tvars), c)
  end;

fun dest_arity tm =
  let
    fun err () = raise_term "dest_arity" [tm];

    val (ty, c) = dest_inclass tm handle TERM _ => err ();
    val (t, tvars) =
      (case ty of
        Type (t, tys) => (t, map (fn TVar x => x | _ => err ()) tys)
      | _ => err ());
    val ss =
      if null (gen_duplicates eq_fst tvars)
      then map snd tvars else err ();
  in
    (t, ss, c)
  end;


(* axclass_tac *)

(*repeatedly resolve subgoals of form "(| ty : c_class |)";
  try "cI" axioms first and use class_triv as last resort*)

fun class_axms thy =
  let
    val classes = Sign.classes (sign_of thy);
    val intros = map (fn c => c ^ "I") classes;
  in
    get_axioms thy intros @
    map (class_triv thy) classes
  end;

fun axclass_tac thy =
  REPEAT_FIRST (resolve_tac (class_axms thy));


(* prove_arity *)

(*(* FIXME *)
(* FIXME state sign vs sign (!?) *)
fun weaker_arity state =
  all_subsort (ss, #2 (dest_arity (concl_of state)))
    handle TERM _ => false;
*)

fun prove_arity thy (arity as (t, ss, c)) thms usr_tac =
  let
    val sign = sign_of thy;
    val all_subsort = forall2 (Sign.subsort sign);

    val arity_goal = cterm_of sign (mk_arity arity);

    val arity_tac =
      axclass_tac thy THEN
      TRY (rewrite_goals_tac (filter is_defn thms)) THEN
      TRY (REPEAT_FIRST (resolve_tac (filter_out is_defn thms))) THEN
      (if_none usr_tac all_tac);

    val arity_thm = prove_goalw_cterm [] arity_goal (K [arity_tac]);

    val (t', ss', c') = dest_arity (#prop (rep_thm arity_thm))
      handle TERM _ => error "Result is not an arity";
  in
    if t = t' andalso all_subsort (ss, ss') andalso c = c' then ()
    else error ("Proved different arity: " ^ Type.str_of_arity (t', ss', [c']))
  end
  handle ERROR => error ("The error(s) above occurred while trying to prove: " ^
    Type.str_of_arity (t, ss, [c]));


(* external interface *)

fun add_instance (t, ss, c) axms thms usr_tac thy =
  (prove_arity thy (t, ss, c) (get_axioms thy axms @ thms) usr_tac;
    add_arities [(t, ss, [c])] thy);


end;

