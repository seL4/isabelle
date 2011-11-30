(*  Title:      HOL/Tools/TFL/casesplit.ML
    Author:     Lucas Dixon, University of Edinburgh

Extra case splitting for TFL.
*)

signature CASE_SPLIT =
sig

  (* try to recursively split conjectured thm to given list of thms *)
  val splitto : thm list -> thm -> thm

end;

structure CaseSplit: CASE_SPLIT =
struct

val rulify_goals = Raw_Simplifier.rewrite_goals_rule @{thms induct_rulify};
val atomize_goals = Raw_Simplifier.rewrite_goals_rule @{thms induct_atomize};

(* beta-eta contract the theorem *)
fun beta_eta_contract thm =
    let
      val thm2 = Thm.equal_elim (Thm.beta_conversion true (Thm.cprop_of thm)) thm
      val thm3 = Thm.equal_elim (Thm.eta_conversion (Thm.cprop_of thm2)) thm2
    in thm3 end;

(* make a casethm from an induction thm *)
val cases_thm_of_induct_thm =
     Seq.hd o (ALLGOALS (fn i => REPEAT (etac Drule.thin_rl i)));

(* get the case_thm (my version) from a type *)
fun case_thm_of_ty thy ty  =
    let
      val ty_str = case ty of
                     Type(ty_str, _) => ty_str
                   | TFree(s,_)  => error ("Free type: " ^ s)
                   | TVar((s,i),_) => error ("Free variable: " ^ s)
      val {induct, ...} = Datatype.the_info thy ty_str
    in
      cases_thm_of_induct_thm induct
    end;


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

      val casethm_vars = rev (Misc_Legacy.term_vars (Thm.concl_of case_thm));

      val casethm_tvars = Misc_Legacy.term_tvars (Thm.concl_of case_thm);
      val (Pv, Dv, type_insts) =
          case (Thm.concl_of case_thm) of
            (_ $ ((Pv as Var(P,Pty)) $ (Dv as Var(D, Dty)))) =>
            (Pv, Dv,
             Sign.typ_match sgn (Dty, ty) Vartab.empty)
          | _ => error "not a valid case thm";
      val type_cinsts = map (fn (ixn, (S, T)) => (ctypify (TVar (ixn, S)), ctypify T))
        (Vartab.dest type_insts);
      val cPv = ctermify (Envir.subst_term_types type_insts Pv);
      val cDv = ctermify (Envir.subst_term_types type_insts Dv);
    in
      (beta_eta_contract
         (case_thm
            |> Thm.instantiate (type_cinsts, [])
            |> Thm.instantiate ([], [(cPv, abs_ct), (cDv, free_ct)])))
    end;


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
      val thy = Thm.theory_of_thm genth;

      (* check if we are a member of splitths - FIXME: quicker and
      more flexible with discrim net. *)
      fun solve_by_splitth th split =
        Thm.biresolution false [(false,split)] 1 th;

      fun split th =
        (case find_thms_split splitths 1 th of
          NONE =>
           (writeln (cat_lines
            (["th:", Display.string_of_thm_without_context th, "split ths:"] @
              map Display.string_of_thm_without_context splitths @ ["\n--"]));
            error "splitto: cannot find variable to split on")
        | SOME v =>
            let
              val gt = HOLogic.dest_Trueprop (#1 (Logic.dest_implies (Thm.prop_of th)));
              val split_thm = mk_casesplit_goal_thm thy v gt;
              val (subthms, expf) = IsaND.fixed_subgoal_thms split_thm;
            in
              expf (map recsplitf subthms)
            end)

      and recsplitf th =
        (* note: multiple unifiers! we only take the first element,
           probably fine -- there is probably only one anyway. *)
        (case get_first (Seq.pull o solve_by_splitth th) splitths of
          NONE => split th
        | SOME (solved_th, more) => solved_th);
    in
      recsplitf genth
    end;

end;
