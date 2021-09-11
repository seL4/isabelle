(*  Title:      ZF/Tools/induct_tacs.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Induction and exhaustion tactics for Isabelle/ZF.  The theory
information needed to support them (and to support primrec).  Also a
function to install other sets as if they were datatypes.
*)

signature DATATYPE_TACTICS =
sig
  val exhaust_tac: Proof.context -> string -> (binding * string option * mixfix) list ->
    int -> tactic
  val induct_tac: Proof.context -> string -> (binding * string option * mixfix) list ->
    int -> tactic
  val rep_datatype_i: thm -> thm -> thm list -> thm list -> theory -> theory
  val rep_datatype: Facts.ref * Token.src list -> Facts.ref * Token.src list ->
    (Facts.ref * Token.src list) list -> (Facts.ref * Token.src list) list -> theory -> theory
end;


(** Datatype information, e.g. associated theorems **)

type datatype_info =
  {inductive: bool,             (*true if inductive, not coinductive*)
   constructors : term list,    (*the constructors, as Consts*)
   rec_rewrites : thm list,     (*recursor equations*)
   case_rewrites : thm list,    (*case equations*)
   induct : thm,
   mutual_induct : thm,
   exhaustion : thm};

structure DatatypesData = Theory_Data
(
  type T = datatype_info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);



(** Constructor information: needed to map constructors to datatypes **)

type constructor_info =
  {big_rec_name : string,     (*name of the mutually recursive set*)
   constructors : term list,  (*the constructors, as Consts*)
   free_iffs    : thm list,   (*freeness simprules*)
   rec_rewrites : thm list};  (*recursor equations*)


structure ConstructorsData = Theory_Data
(
  type T = constructor_info Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data;
);

structure DatatypeTactics : DATATYPE_TACTICS =
struct

fun datatype_info thy name =
  (case Symtab.lookup (DatatypesData.get thy) name of
    SOME info => info
  | NONE => error ("Unknown datatype " ^ quote name));


(*Given a variable, find the inductive set associated it in the assumptions*)
exception Find_tname of string

fun find_tname ctxt var As =
  let fun mk_pair \<^Const_>\<open>mem for \<open>Free (v,_)\<close> A\<close> = (v, #1 (dest_Const (head_of A)))
        | mk_pair _ = raise Match
      val pairs = map_filter (try (mk_pair o FOLogic.dest_Trueprop)) As
      val x =
        (case try (dest_Free o Syntax.read_term ctxt) var of
          SOME (x, _) => x
        | _ => raise Find_tname ("Bad variable " ^ quote var))
  in case AList.lookup (op =) pairs x of
       NONE => raise Find_tname ("Cannot determine datatype of " ^ quote var)
     | SOME t => t
  end;

(** generic exhaustion and induction tactic for datatypes
    Differences from HOL:
      (1) no checking if the induction var occurs in premises, since it always
          appears in one of them, and it's hard to check for other occurrences
      (2) exhaustion works for VARIABLES in the premises, not general terms
**)

fun exhaust_induct_tac exh ctxt var fixes i state = SUBGOAL (fn _ =>
  let
    val thy = Proof_Context.theory_of ctxt
    val ({context = ctxt', asms, ...}, _) = Subgoal.focus ctxt i NONE state
    val tn = find_tname ctxt' var (map Thm.term_of asms)
    val rule =
      datatype_info thy tn
      |> (if exh then #exhaustion else #induct)
      |> Thm.transfer thy;
    val \<^Const_>\<open>mem for \<open>Var(ixn,_)\<close> _\<close> =
        (case Thm.prems_of rule of
             [] => error "induction is not available for this datatype"
           | major::_ => FOLogic.dest_Trueprop major)
  in
    Rule_Insts.eres_inst_tac ctxt [((ixn, Position.none), var)] fixes rule i
  end
  handle Find_tname msg =>
            if exh then (*try boolean case analysis instead*)
                case_tac ctxt var fixes i
            else error msg) i state;

val exhaust_tac = exhaust_induct_tac true;
val induct_tac = exhaust_induct_tac false;


(**** declare non-datatype as datatype ****)

fun rep_datatype_i elim induct case_eqns recursor_eqns thy =
  let
    (*analyze the LHS of a case equation to get a constructor*)
    fun const_of \<^Const_>\<open>IFOL.eq _ for \<open>_ $ c\<close> _\<close> = c
      | const_of eqn = error ("Ill-formed case equation: " ^
                              Syntax.string_of_term_global thy eqn);

    val constructors =
        map (head_of o const_of o FOLogic.dest_Trueprop o Thm.prop_of) case_eqns;

    val \<^Const_>\<open>mem for _ data\<close> = FOLogic.dest_Trueprop (hd (Thm.prems_of elim));

    val Const(big_rec_name, _) = head_of data;

    val simps = case_eqns @ recursor_eqns;

    val dt_info =
          {inductive = true,
           constructors = constructors,
           rec_rewrites = map Thm.trim_context recursor_eqns,
           case_rewrites = map Thm.trim_context case_eqns,
           induct = Thm.trim_context induct,
           mutual_induct = Thm.trim_context @{thm TrueI},  (*No need for mutual induction*)
           exhaustion = Thm.trim_context elim};

    val con_info =
          {big_rec_name = big_rec_name,
           constructors = constructors,
              (*let primrec handle definition by cases*)
           free_iffs = [],  (*thus we expect the necessary freeness rewrites
                              to be in the simpset already, as is the case for
                              Nat and disjoint sum*)
           rec_rewrites =
            (case recursor_eqns of [] => case_eqns | _ => recursor_eqns)
            |> map Thm.trim_context};

    (*associate with each constructor the datatype name and rewrites*)
    val con_pairs = map (fn c => (#1 (dest_Const c), con_info)) constructors

  in
    thy
    |> Sign.add_path (Long_Name.base_name big_rec_name)
    |> Global_Theory.add_thmss [((Binding.name "simps", simps), [Simplifier.simp_add])] |> snd
    |> DatatypesData.put (Symtab.update (big_rec_name, dt_info) (DatatypesData.get thy))
    |> ConstructorsData.put (fold_rev Symtab.update con_pairs (ConstructorsData.get thy))
    |> Sign.parent_path
  end;

fun rep_datatype raw_elim raw_induct raw_case_eqns raw_recursor_eqns thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val elim = Facts.the_single ("elimination", Position.none) (Attrib.eval_thms ctxt [raw_elim]);
    val induct = Facts.the_single ("induction", Position.none) (Attrib.eval_thms ctxt [raw_induct]);
    val case_eqns = Attrib.eval_thms ctxt raw_case_eqns;
    val recursor_eqns = Attrib.eval_thms ctxt raw_recursor_eqns;
  in rep_datatype_i elim induct case_eqns recursor_eqns thy end;


(* theory setup *)

val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>induct_tac\<close>
      (Args.goal_spec -- Scan.lift (Args.embedded -- Parse.for_fixes) >>
        (fn (quant, (s, xs)) => fn ctxt => SIMPLE_METHOD'' quant (induct_tac ctxt s xs)))
      "induct_tac emulation (dynamic instantiation!)" #>
    Method.setup \<^binding>\<open>case_tac\<close>
     (Args.goal_spec -- Scan.lift (Args.embedded -- Parse.for_fixes) >>
        (fn (quant, (s, xs)) => fn ctxt => SIMPLE_METHOD'' quant (exhaust_tac ctxt s xs)))
      "datatype case_tac emulation (dynamic instantiation!)");


(* outer syntax *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>rep_datatype\<close> "represent existing set inductively"
    ((\<^keyword>\<open>elimination\<close> |-- Parse.!!! Parse.thm) --
     (\<^keyword>\<open>induction\<close> |-- Parse.!!! Parse.thm) --
     (\<^keyword>\<open>case_eqns\<close> |-- Parse.!!! Parse.thms1) --
     Scan.optional (\<^keyword>\<open>recursor_eqns\<close> |-- Parse.!!! Parse.thms1) []
     >> (fn (((x, y), z), w) => Toplevel.theory (rep_datatype x y z w)));

end;

val exhaust_tac = DatatypeTactics.exhaust_tac;
val induct_tac  = DatatypeTactics.induct_tac;
