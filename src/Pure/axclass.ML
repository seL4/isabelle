(*  Title:      Pure/axclass.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Higher level user interfaces for axiomatic type classes.

TODO:
  remove add_sigclass (?)
  remove goal_... (?)
  clean signature
*)

signature AX_CLASS =
sig
  structure Tactical: TACTICAL
  local open Tactical Tactical.Thm Tactical.Thm.Sign.Syntax.Mixfix in
    val add_thms_as_axms: (string * thm) list -> theory -> theory
    val add_classrel_thms: thm list -> theory -> theory
    val add_arity_thms: thm list -> theory -> theory
    val add_axclass: class * class list -> (string * string) list
      -> theory -> theory
    val add_axclass_i: class * class list -> (string * term) list
      -> theory -> theory
    val add_sigclass: class * class list -> (string * string * mixfix) list
      -> theory -> theory
    val add_sigclass_i: class * class list -> (string * typ * mixfix) list
      -> theory -> theory
    val prove_classrel: theory -> class * class -> thm list
      -> tactic option -> thm
    val prove_arity: theory -> string * sort list * class -> thm list
      -> tactic option -> thm
    val add_inst_subclass: class * class -> string list -> thm list
      -> tactic option -> theory -> theory
    val add_inst_arity: string * sort list * class list -> string list
      -> thm list -> tactic option -> theory -> theory
    val add_defns: (string * string) list -> theory -> theory
    val add_defns_i: (string * term) list -> theory -> theory
    val mk_classrel: class * class -> term
    val dest_classrel: term -> class * class
    val mk_arity: string * sort list * class -> term
    val dest_arity: term -> string * sort list * class
    val class_axms: theory -> thm list
    val axclass_tac: theory -> thm list -> tactic
    val goal_subclass: theory -> class * class -> thm list
    val goal_arity: theory -> string * sort list * class -> thm list
  end
end;

functor AxClassFun(structure Logic: LOGIC and Goals: GOALS and Tactic: TACTIC
  sharing Goals.Tactical = Tactic.Tactical): AX_CLASS =
struct

structure Tactical = Goals.Tactical;
structure Thm = Tactical.Thm;
structure Sign = Thm.Sign;
structure Type = Sign.Type;
structure Pretty = Sign.Syntax.Pretty;

open Logic Thm Tactical Tactic Goals;


(** add constant definitions **)  (* FIXME -> drule.ML (?) *)

(* all_axioms_of *)

(*results may contain duplicates!*)

fun ancestry_of thy =
  thy :: flat (map ancestry_of (parents_of thy));

val all_axioms_of = flat o map axioms_of o ancestry_of;


(* clash_types, clash_consts *)

(*check if types have common instance (ignoring sorts)*)

fun clash_types ty1 ty2 =
  let
    val ty1' = Type.varifyT ty1;
    val ty2' = incr_tvar (maxidx_of_typ ty1' + 1) (Type.varifyT ty2);
  in
    Type.raw_unify (ty1', ty2')
  end;

fun clash_consts (c1, ty1) (c2, ty2) =
  c1 = c2 andalso clash_types ty1 ty2;


(* clash_defns *)

fun clash_defn c_ty (name, tm) =
  let val (c, ty') = dest_Const (head_of (fst (Logic.dest_equals tm))) in
    if clash_consts c_ty (c, ty') then Some (name, ty') else None
  end handle TERM _ => None;

fun clash_defns c_ty axms =
  distinct (mapfilter (clash_defn c_ty) axms);


(* dest_defn *)

fun dest_defn tm =
  let
    fun err msg = raise_term msg [tm];

    val (lhs, rhs) = Logic.dest_equals tm
      handle TERM _ => err "Not a meta-equality (==)";
    val (head, args) = strip_comb lhs;
    val (c, ty) = dest_Const head
      handle TERM _ => err "Head of lhs not a constant";

    fun occs_const (Const c_ty') = clash_consts (c, ty) c_ty'
      | occs_const (Abs (_, _, t)) = occs_const t
      | occs_const (t $ u) = occs_const t orelse occs_const u
      | occs_const _ = false;
  in
    if not (forall is_Free args) then
      err "Arguments of lhs have to be variables"
    else if not (null (duplicates args)) then
      err "Duplicate variables on lhs"
    else if not (term_frees rhs subset args) then
      err "Extra variables on rhs"
    else if not (term_tfrees rhs subset typ_tfrees ty) then
      err "Extra type variables on rhs"
    else if occs_const rhs then
      err "Constant to be defined clashes with occurrence(s) on rhs"
    else (c, ty)
  end;


(* check_defn *)

fun err_in_axm name msg =
  (writeln msg; error ("The error(s) above occurred in axiom " ^ quote name));

fun check_defn sign (axms, (name, tm)) =
  let
    fun show_const (c, ty) = quote (Pretty.string_of (Pretty.block
      [Pretty.str (c ^ " ::"), Pretty.brk 1, Sign.pretty_typ sign ty]));

    fun show_defn c (dfn, ty') = show_const (c, ty') ^ " in " ^ dfn;
    fun show_defns c = commas o map (show_defn c);

    val (c, ty) = dest_defn tm
      handle TERM (msg, _) => err_in_axm name msg;
    val defns = clash_defns (c, ty) axms;
  in
    if not (null defns) then
      err_in_axm name ("Definition of " ^ show_const (c, ty) ^
        " clashes with " ^ show_defns c defns)
    else (name, tm) :: axms
  end;


(* add_defns *)

fun ext_defns prep_axm raw_axms thy =
  let
    val axms = map (prep_axm (sign_of thy)) raw_axms;
    val all_axms = all_axioms_of thy;
  in
    foldl (check_defn (sign_of thy)) (all_axms, axms);
    add_axioms_i axms thy
  end;

val add_defns_i = ext_defns cert_axm;
val add_defns = ext_defns read_axm;



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



(** abstract syntax operations **)    (* FIXME -> logic.ML (?) *)

(* subclass relations as terms *)

fun mk_classrel (c1, c2) = mk_inclass (aT [c1], c2);

fun dest_classrel tm =
  let
    fun err () = raise_term "dest_classrel" [tm];

    val (ty, c2) = dest_inclass (freeze_vars tm) handle TERM _ => err ();
    val c1 = (case ty of TFree (_, [c]) => c | _ => err ());
  in
    (c1, c2)
  end;


(* arities as terms *)

fun mk_arity (t, ss, c) =
  let
    val names = tl (variantlist (replicate (length ss + 1) "'", []));
    val tfrees = map TFree (names ~~ ss);
  in
    mk_inclass (Type (t, tfrees), c)
  end;

fun dest_arity tm =
  let
    fun err () = raise_term "dest_arity" [tm];

    val (ty, c) = dest_inclass (freeze_vars tm) handle TERM _ => err ();
    val (t, tfrees) =
      (case ty of
        Type (t, tys) => (t, map (fn TFree x => x | _ => err ()) tys)
      | _ => err ());
    val ss =
      if null (gen_duplicates eq_fst tfrees)
      then map snd tfrees else err ();
  in
    (t, ss, c)
  end;



(** add theorems as axioms **)    (* FIXME -> drule.ML (?) *)

fun prep_thm_axm thy thm =
  let
    fun err msg = raise THM ("prep_thm_axm: " ^ msg, 0, [thm]);

    val {sign, hyps, prop, ...} = rep_thm thm;
  in
    if not (Sign.subsig (sign, sign_of thy)) then
      err "theorem not of same theory"
    else if not (null hyps) then
      err "theorem may not contain hypotheses"
    else prop
  end;

(*general theorems*)
fun add_thms_as_axms thms thy =
  add_axioms_i (map (apsnd (prep_thm_axm thy)) thms) thy;

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
    add_classrel (map prep_thm thms) thy
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
    add_arities (map prep_thm thms) thy
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


(* add signature classes *)

fun ext_sigclass add_cnsts (class, super_classes) consts old_thy =
  old_thy
  |> add_axclass (class, super_classes) []
  |> add_defsort [class]
  |> add_cnsts consts
  |> add_defsort (Type.defaultS (#tsig (Sign.rep_sg (sign_of old_thy))));

val add_sigclass = ext_sigclass add_consts;
val add_sigclass_i = ext_sigclass add_consts_i;



(** prove class relations and type arities **)

(* class_axms *)

fun class_axms thy =
  let
    val classes = Sign.classes (sign_of thy);
    val intros = map (fn c => c ^ "I") classes;
  in
    get_axioms thy intros @
    map (class_triv thy) classes
  end;


(* axclass_tac *)

(*(1) repeatedly resolve goals of form "OFCLASS(ty, c_class)",
      try "cI" axioms first and use class_triv as last resort
  (2) rewrite goals using user supplied definitions
  (3) repeatedly resolve goals with user supplied non-definitions*)

fun axclass_tac thy thms =
  TRY (REPEAT_FIRST (resolve_tac (class_axms thy))) THEN
  TRY (rewrite_goals_tac (filter is_defn thms)) THEN
  TRY (REPEAT_FIRST (resolve_tac (filter_out is_defn thms)));


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

val prove_classrel =
  prove mk_classrel (fn (c1, c2) => c1 ^ " < " ^ c2);

val prove_arity =
  prove mk_arity (fn (t, ss, c) => Type.str_of_arity (t, ss, [c]));


(* make goals (for interactive use) *)

fun mk_goal term_of thy sig_prop =
  goalw_cterm [] (cterm_of (sign_of thy) (term_of sig_prop));

val goal_subclass = mk_goal mk_classrel;
val goal_arity = mk_goal mk_arity;



(** add proved subclass relations and arities **)

fun add_inst_subclass (c1, c2) axms thms usr_tac thy =
  add_classrel_thms
  [prove_classrel thy (c1, c2) (get_axioms thy axms @ thms) usr_tac] thy;

fun add_inst_arity (t, ss, cs) axms thms usr_tac thy =
  let
    val usr_thms = get_axioms thy axms @ thms;
    fun prove c =
      prove_arity thy (t, ss, c) usr_thms usr_tac;
  in
    add_arity_thms (map prove cs) thy
  end;


end;

