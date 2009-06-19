(*  Title:      HOL/Tools/TFL/casesplit.ML
    Author:     Lucas Dixon, University of Edinburgh

A structure that defines a tactic to program case splits.

    casesplit_free :
      string * typ -> int -> thm -> thm Seq.seq

    casesplit_name :
      string -> int -> thm -> thm Seq.seq

These use the induction theorem associated with the recursive data
type to be split.

The structure includes a function to try and recursively split a
conjecture into a list sub-theorems:

    splitto : thm list -> thm -> thm
*)

(* logic-specific *)
signature CASE_SPLIT_DATA =
sig
  val dest_Trueprop : term -> term
  val mk_Trueprop : term -> term
  val atomize : thm list
  val rulify : thm list
end;

structure CaseSplitData_HOL : CASE_SPLIT_DATA =
struct
val dest_Trueprop = HOLogic.dest_Trueprop;
val mk_Trueprop = HOLogic.mk_Trueprop;

val atomize = thms "induct_atomize";
val rulify = thms "induct_rulify";
val rulify_fallback = thms "induct_rulify_fallback";

end;


signature CASE_SPLIT =
sig
  (* failure to find a free to split on *)
  exception find_split_exp of string

  (* getting a case split thm from the induction thm *)
  val case_thm_of_ty : theory -> typ -> thm
  val cases_thm_of_induct_thm : thm -> thm

  (* case split tactics *)
  val casesplit_free :
      string * typ -> int -> thm -> thm Seq.seq
  val casesplit_name : string -> int -> thm -> thm Seq.seq

  (* finding a free var to split *)
  val find_term_split :
      term * term -> (string * typ) option
  val find_thm_split :
      thm -> int -> thm -> (string * typ) option
  val find_thms_split :
      thm list -> int -> thm -> (string * typ) option

  (* try to recursively split conjectured thm to given list of thms *)
  val splitto : thm list -> thm -> thm

  (* for use with the recdef package *)
  val derive_init_eqs :
      theory ->
      (thm * int) list -> term list -> (thm * int) list
end;

functor CaseSplitFUN(Data : CASE_SPLIT_DATA) =
struct

val rulify_goals = MetaSimplifier.rewrite_goals_rule Data.rulify;
val atomize_goals = MetaSimplifier.rewrite_goals_rule Data.atomize;

(* beta-eta contract the theorem *)
fun beta_eta_contract thm =
    let
      val thm2 = equal_elim (Thm.beta_conversion true (Thm.cprop_of thm)) thm
      val thm3 = equal_elim (Thm.eta_conversion (Thm.cprop_of thm2)) thm2
    in thm3 end;

(* make a casethm from an induction thm *)
val cases_thm_of_induct_thm =
     Seq.hd o (ALLGOALS (fn i => REPEAT (etac Drule.thin_rl i)));

(* get the case_thm (my version) from a type *)
fun case_thm_of_ty sgn ty  =
    let
      val dtypestab = Datatype.get_datatypes sgn;
      val ty_str = case ty of
                     Type(ty_str, _) => ty_str
                   | TFree(s,_)  => error ("Free type: " ^ s)
                   | TVar((s,i),_) => error ("Free variable: " ^ s)
      val dt = case Symtab.lookup dtypestab ty_str
                of SOME dt => dt
                 | NONE => error ("Not a Datatype: " ^ ty_str)
    in
      cases_thm_of_induct_thm (#induction dt)
    end;

(*
 val ty = (snd o hd o map Term.dest_Free o OldTerm.term_frees) t;
*)


(* for use when there are no prems to the subgoal *)
(* does a case split on the given variable *)
fun mk_casesplit_goal_thm sgn (vstr,ty) gt =
    let
      val x = Free(vstr,ty)
      val abst = Abs(vstr, ty, Term.abstract_over (x, gt));

      val ctermify = Thm.cterm_of sgn;
      val ctypify = Thm.ctyp_of sgn;
      val case_thm = case_thm_of_ty sgn ty;

      val abs_ct = ctermify abst;
      val free_ct = ctermify x;

      val casethm_vars = rev (OldTerm.term_vars (Thm.concl_of case_thm));

      val casethm_tvars = OldTerm.term_tvars (Thm.concl_of case_thm);
      val (Pv, Dv, type_insts) =
          case (Thm.concl_of case_thm) of
            (_ $ ((Pv as Var(P,Pty)) $ (Dv as Var(D, Dty)))) =>
            (Pv, Dv,
             Sign.typ_match sgn (Dty, ty) Vartab.empty)
          | _ => error "not a valid case thm";
      val type_cinsts = map (fn (ixn, (S, T)) => (ctypify (TVar (ixn, S)), ctypify T))
        (Vartab.dest type_insts);
      val cPv = ctermify (Envir.subst_TVars type_insts Pv);
      val cDv = ctermify (Envir.subst_TVars type_insts Dv);
    in
      (beta_eta_contract
         (case_thm
            |> Thm.instantiate (type_cinsts, [])
            |> Thm.instantiate ([], [(cPv, abs_ct), (cDv, free_ct)])))
    end;


(* for use when there are no prems to the subgoal *)
(* does a case split on the given variable (Free fv) *)
fun casesplit_free fv i th =
    let
      val (subgoalth, exp) = IsaND.fix_alls i th;
      val subgoalth' = atomize_goals subgoalth;
      val gt = Data.dest_Trueprop (Logic.get_goal (Thm.prop_of subgoalth') 1);
      val sgn = Thm.theory_of_thm th;

      val splitter_thm = mk_casesplit_goal_thm sgn fv gt;
      val nsplits = Thm.nprems_of splitter_thm;

      val split_goal_th = splitter_thm RS subgoalth';
      val rulified_split_goal_th = rulify_goals split_goal_th;
    in
      IsaND.export_back exp rulified_split_goal_th
    end;


(* for use when there are no prems to the subgoal *)
(* does a case split on the given variable *)
fun casesplit_name vstr i th =
    let
      val (subgoalth, exp) = IsaND.fix_alls i th;
      val subgoalth' = atomize_goals subgoalth;
      val gt = Data.dest_Trueprop (Logic.get_goal (Thm.prop_of subgoalth') 1);

      val freets = OldTerm.term_frees gt;
      fun getter x =
          let val (n,ty) = Term.dest_Free x in
            (if vstr = n orelse vstr = Name.dest_skolem n
             then SOME (n,ty) else NONE )
            handle Fail _ => NONE (* dest_skolem *)
          end;
      val (n,ty) = case Library.get_first getter freets
                of SOME (n, ty) => (n, ty)
                 | _ => error ("no such variable " ^ vstr);
      val sgn = Thm.theory_of_thm th;

      val splitter_thm = mk_casesplit_goal_thm sgn (n,ty) gt;
      val nsplits = Thm.nprems_of splitter_thm;

      val split_goal_th = splitter_thm RS subgoalth';

      val rulified_split_goal_th = rulify_goals split_goal_th;
    in
      IsaND.export_back exp rulified_split_goal_th
    end;


(* small example:
Goal "P (x :: nat) & (C y --> Q (y :: nat))";
by (rtac (thm "conjI") 1);
val th = topthm();
val i = 2;
val vstr = "y";

by (casesplit_name "y" 2);

val th = topthm();
val i = 1;
val th' = casesplit_name "x" i th;
*)


(* the find_XXX_split functions are simply doing a lightwieght (I
think) term matching equivalent to find where to do the next split *)

(* assuming two twems are identical except for a free in one at a
subterm, or constant in another, ie assume that one term is a plit of
another, then gives back the free variable that has been split. *)
exception find_split_exp of string
fun find_term_split (Free v, _ $ _) = SOME v
  | find_term_split (Free v, Const _) = SOME v
  | find_term_split (Free v, Abs _) = SOME v (* do we really want this case? *)
  | find_term_split (Free v, Var _) = NONE (* keep searching *)
  | find_term_split (a $ b, a2 $ b2) =
    (case find_term_split (a, a2) of
       NONE => find_term_split (b,b2)
     | vopt => vopt)
  | find_term_split (Abs(_,ty,t1), Abs(_,ty2,t2)) =
    find_term_split (t1, t2)
  | find_term_split (Const (x,ty), Const(x2,ty2)) =
    if x = x2 then NONE else (* keep searching *)
    raise find_split_exp (* stop now *)
            "Terms are not identical upto a free varaible! (Consts)"
  | find_term_split (Bound i, Bound j) =
    if i = j then NONE else (* keep searching *)
    raise find_split_exp (* stop now *)
            "Terms are not identical upto a free varaible! (Bound)"
  | find_term_split (a, b) =
    raise find_split_exp (* stop now *)
            "Terms are not identical upto a free varaible! (Other)";

(* assume that "splitth" is a case split form of subgoal i of "genth",
then look for a free variable to split, breaking the subgoal closer to
splitth. *)
fun find_thm_split splitth i genth =
    find_term_split (Logic.get_goal (Thm.prop_of genth) i,
                     Thm.concl_of splitth) handle find_split_exp _ => NONE;

(* as above but searches "splitths" for a theorem that suggest a case split *)
fun find_thms_split splitths i genth =
    Library.get_first (fn sth => find_thm_split sth i genth) splitths;


(* split the subgoal i of "genth" until we get to a member of
splitths. Assumes that genth will be a general form of splitths, that
can be case-split, as needed. Otherwise fails. Note: We assume that
all of "splitths" are split to the same level, and thus it doesn't
matter which one we choose to look for the next split. Simply add
search on splitthms and split variable, to change this.  *)
(* Note: possible efficiency measure: when a case theorem is no longer
useful, drop it? *)
(* Note: This should not be a separate tactic but integrated into the
case split done during recdef's case analysis, this would avoid us
having to (re)search for variables to split. *)
fun splitto splitths genth =
    let
      val _ = not (null splitths) orelse error "splitto: no given splitths";
      val sgn = Thm.theory_of_thm genth;

      (* check if we are a member of splitths - FIXME: quicker and
      more flexible with discrim net. *)
      fun solve_by_splitth th split =
          Thm.biresolution false [(false,split)] 1 th;

      fun split th =
          (case find_thms_split splitths 1 th of
             NONE =>
             (writeln "th:";
              Display.print_thm th; writeln "split ths:";
              Display.print_thms splitths; writeln "\n--";
              error "splitto: cannot find variable to split on")
            | SOME v =>
             let
               val gt = Data.dest_Trueprop (List.nth(Thm.prems_of th, 0));
               val split_thm = mk_casesplit_goal_thm sgn v gt;
               val (subthms, expf) = IsaND.fixed_subgoal_thms split_thm;
             in
               expf (map recsplitf subthms)
             end)

      and recsplitf th =
          (* note: multiple unifiers! we only take the first element,
             probably fine -- there is probably only one anyway. *)
          (case Library.get_first (Seq.pull o solve_by_splitth th) splitths of
             NONE => split th
           | SOME (solved_th, more) => solved_th)
    in
      recsplitf genth
    end;


(* Note: We dont do this if wf conditions fail to be solved, as each
case may have a different wf condition - we could group the conditions
togeather and say that they must be true to solve the general case,
but that would hide from the user which sub-case they were related
to. Probably this is not important, and it would work fine, but I
prefer leaving more fine grain control to the user. *)

(* derive eqs, assuming strict, ie the rules have no assumptions = all
   the well-foundness conditions have been solved. *)
fun derive_init_eqs sgn rules eqs =
  let
    fun get_related_thms i =
      List.mapPartial ((fn (r, x) => if x = i then SOME r else NONE));
    fun add_eq (i, e) xs =
      (e, (get_related_thms i rules), i) :: xs
    fun solve_eq (th, [], i) =
          error "derive_init_eqs: missing rules"
      | solve_eq (th, [a], i) = (a, i)
      | solve_eq (th, splitths as (_ :: _), i) = (splitto splitths th, i);
    val eqths =
      map (Thm.trivial o Thm.cterm_of sgn o Data.mk_Trueprop) eqs;
  in
    []
    |> fold_index add_eq eqths
    |> map solve_eq
    |> rev
  end;

end;


structure CaseSplit = CaseSplitFUN(CaseSplitData_HOL);
