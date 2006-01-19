(*  Title:      ZF/Tools/induct_tacs.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Induction and exhaustion tactics for Isabelle/ZF.  The theory
information needed to support them (and to support primrec).  Also a
function to install other sets as if they were datatypes.
*)

signature DATATYPE_TACTICS =
sig
  val induct_tac: string -> int -> tactic
  val exhaust_tac: string -> int -> tactic
  val rep_datatype_i: thm -> thm -> thm list -> thm list -> theory -> theory
  val rep_datatype: thmref * Attrib.src list -> thmref * Attrib.src list ->
    (thmref * Attrib.src list) list -> (thmref * Attrib.src list) list -> theory -> theory
  val setup: theory -> theory
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

structure DatatypesData = TheoryDataFun
(struct
  val name = "ZF/datatypes";
  type T = datatype_info Symtab.table;

  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ tabs : T = Symtab.merge (K true) tabs;

  fun print thy tab =
    Pretty.writeln (Pretty.strs ("datatypes:" ::
      map #1 (NameSpace.extern_table (Sign.type_space thy, tab))));
end);


(** Constructor information: needed to map constructors to datatypes **)

type constructor_info =
  {big_rec_name : string,     (*name of the mutually recursive set*)
   constructors : term list,  (*the constructors, as Consts*)
   free_iffs    : thm list,   (*freeness simprules*)
   rec_rewrites : thm list};  (*recursor equations*)


structure ConstructorsData = TheoryDataFun
(struct
  val name = "ZF/constructors"
  type T = constructor_info Symtab.table
  val empty = Symtab.empty
  val copy = I;
  val extend = I
  fun merge _ tabs: T = Symtab.merge (K true) tabs;
  fun print _ _= ();
end);

structure DatatypeTactics : DATATYPE_TACTICS =
struct

fun datatype_info thy name =
  (case Symtab.lookup (DatatypesData.get thy) name of
    SOME info => info
  | NONE => error ("Unknown datatype " ^ quote name));


(*Given a variable, find the inductive set associated it in the assumptions*)
exception Find_tname of string

fun find_tname var Bi =
  let fun mk_pair (Const("op :",_) $ Free (v,_) $ A) =
             (v, #1 (dest_Const (head_of A)))
        | mk_pair _ = raise Match
      val pairs = List.mapPartial (try (mk_pair o FOLogic.dest_Trueprop))
          (#2 (strip_context Bi))
  in case AList.lookup (op =) pairs var of
       NONE => raise Find_tname ("Cannot determine datatype of " ^ quote var)
     | SOME t => t
  end;

(** generic exhaustion and induction tactic for datatypes
    Differences from HOL:
      (1) no checking if the induction var occurs in premises, since it always
          appears in one of them, and it's hard to check for other occurrences
      (2) exhaustion works for VARIABLES in the premises, not general terms
**)

fun exhaust_induct_tac exh var i state =
  let
    val (_, _, Bi, _) = dest_state (state, i)
    val thy = Thm.theory_of_thm state
    val tn = find_tname var Bi
    val rule =
        if exh then #exhaustion (datatype_info thy tn)
               else #induct  (datatype_info thy tn)
    val (Const("op :",_) $ Var(ixn,_) $ _) =
        (case prems_of rule of
             [] => error "induction is not available for this datatype"
           | major::_ => FOLogic.dest_Trueprop major)
  in
    Tactic.eres_inst_tac' [(ixn, var)] rule i state
  end
  handle Find_tname msg =>
            if exh then (*try boolean case analysis instead*)
                case_tac var i state
            else error msg;

val exhaust_tac = exhaust_induct_tac true;
val induct_tac = exhaust_induct_tac false;


(**** declare non-datatype as datatype ****)

fun rep_datatype_i elim induct case_eqns recursor_eqns thy =
  let
    (*analyze the LHS of a case equation to get a constructor*)
    fun const_of (Const("op =", _) $ (_ $ c) $ _) = c
      | const_of eqn = error ("Ill-formed case equation: " ^
                              Sign.string_of_term thy eqn);

    val constructors =
        map (head_of o const_of o FOLogic.dest_Trueprop o
             #prop o rep_thm) case_eqns;

    val Const ("op :", _) $ _ $ data =
        FOLogic.dest_Trueprop (hd (prems_of elim));

    val Const(big_rec_name, _) = head_of data;

    val simps = case_eqns @ recursor_eqns;

    val dt_info =
          {inductive = true,
           constructors = constructors,
           rec_rewrites = recursor_eqns,
           case_rewrites = case_eqns,
           induct = induct,
           mutual_induct = TrueI,  (*No need for mutual induction*)
           exhaustion = elim};

    val con_info =
          {big_rec_name = big_rec_name,
           constructors = constructors,
              (*let primrec handle definition by cases*)
           free_iffs = [],  (*thus we expect the necessary freeness rewrites
                              to be in the simpset already, as is the case for
                              Nat and disjoint sum*)
           rec_rewrites = (case recursor_eqns of
                               [] => case_eqns | _ => recursor_eqns)};

    (*associate with each constructor the datatype name and rewrites*)
    val con_pairs = map (fn c => (#1 (dest_Const c), con_info)) constructors

  in
    thy
    |> Theory.add_path (Sign.base_name big_rec_name)
    |> PureThy.add_thmss [(("simps", simps), [Attrib.theory Simplifier.simp_add])] |> snd
    |> DatatypesData.put (Symtab.update (big_rec_name, dt_info) (DatatypesData.get thy))
    |> ConstructorsData.put (fold_rev Symtab.update con_pairs (ConstructorsData.get thy))
    |> Theory.parent_path
  end;

fun rep_datatype raw_elim raw_induct raw_case_eqns raw_recursor_eqns thy =
  thy
  |> IsarThy.apply_theorems [raw_elim]
  ||>> IsarThy.apply_theorems [raw_induct]
  ||>> IsarThy.apply_theorems raw_case_eqns
  ||>> IsarThy.apply_theorems raw_recursor_eqns
  |-> (fn (((elims, inducts), case_eqns), recursor_eqns) =>
          rep_datatype_i (PureThy.single_thm "elimination" elims)
            (PureThy.single_thm "induction" inducts) case_eqns recursor_eqns);


(* theory setup *)

val setup =
 (DatatypesData.init #>
  ConstructorsData.init #>
  Method.add_methods
    [("induct_tac", Method.goal_args Args.name induct_tac,
      "induct_tac emulation (dynamic instantiation!)"),
     ("case_tac", Method.goal_args Args.name exhaust_tac,
      "datatype case_tac emulation (dynamic instantiation!)")]);


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val rep_datatype_decl =
  (P.$$$ "elimination" |-- P.!!! P.xthm) --
  (P.$$$ "induction" |-- P.!!! P.xthm) --
  (P.$$$ "case_eqns" |-- P.!!! P.xthms1) --
  Scan.optional (P.$$$ "recursor_eqns" |-- P.!!! P.xthms1) []
  >> (fn (((x, y), z), w) => rep_datatype x y z w);

val rep_datatypeP =
  OuterSyntax.command "rep_datatype" "represent existing set inductively" K.thy_decl
    (rep_datatype_decl >> Toplevel.theory);

val _ = OuterSyntax.add_keywords ["elimination", "induction", "case_eqns", "recursor_eqns"];
val _ = OuterSyntax.add_parsers [rep_datatypeP];

end;

end;


val exhaust_tac = DatatypeTactics.exhaust_tac;
val induct_tac  = DatatypeTactics.induct_tac;
