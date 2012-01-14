(*  Title:      HOL/ex/SVC_Oracle.thy
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Based upon the work of Søren T. Heilmann.
*)

header {* Installing an oracle for SVC (Stanford Validity Checker) *}

theory SVC_Oracle
imports Main
uses "svc_funcs.ML"
begin

consts
  iff_keep :: "[bool, bool] => bool"
  iff_unfold :: "[bool, bool] => bool"

hide_const iff_keep iff_unfold

oracle svc_oracle = Svc.oracle

ML {*
(*
Installing the oracle for SVC (Stanford Validity Checker)

The following code merely CALLS the oracle;
  the soundness-critical functions are at svc_funcs.ML

Based upon the work of Søren T. Heilmann
*)


(*Generalize an Isabelle formula, replacing by Vars
  all subterms not intelligible to SVC.*)
fun svc_abstract t =
  let
    (*The oracle's result is given to the subgoal using compose_tac because
      its premises are matched against the assumptions rather than used
      to make subgoals.  Therefore , abstraction must copy the parameters
      precisely and make them available to all generated Vars.*)
    val params = Term.strip_all_vars t
    and body   = Term.strip_all_body t
    val Us = map #2 params
    val nPar = length params
    val vname = Unsynchronized.ref "V_a"
    val pairs = Unsynchronized.ref ([] : (term*term) list)
    fun insert t =
        let val T = fastype_of t
            val v = Logic.combound (Var ((!vname,0), Us--->T), 0, nPar)
        in  vname := Symbol.bump_string (!vname);
            pairs := (t, v) :: !pairs;
            v
        end;
    fun replace t =
        case t of
            Free _  => t  (*but not existing Vars, lest the names clash*)
          | Bound _ => t
          | _ => (case AList.lookup Pattern.aeconv (!pairs) t of
                      SOME v => v
                    | NONE   => insert t)
    (*abstraction of a numeric literal*)
    fun lit t = if can HOLogic.dest_number t then t else replace t;
    (*abstraction of a real/rational expression*)
    fun rat ((c as Const(@{const_name Groups.plus}, _)) $ x $ y) = c $ (rat x) $ (rat y)
      | rat ((c as Const(@{const_name Groups.minus}, _)) $ x $ y) = c $ (rat x) $ (rat y)
      | rat ((c as Const(@{const_name Fields.divide}, _)) $ x $ y) = c $ (rat x) $ (rat y)
      | rat ((c as Const(@{const_name Groups.times}, _)) $ x $ y) = c $ (rat x) $ (rat y)
      | rat ((c as Const(@{const_name Groups.uminus}, _)) $ x) = c $ (rat x)
      | rat t = lit t
    (*abstraction of an integer expression: no div, mod*)
    fun int ((c as Const(@{const_name Groups.plus}, _)) $ x $ y) = c $ (int x) $ (int y)
      | int ((c as Const(@{const_name Groups.minus}, _)) $ x $ y) = c $ (int x) $ (int y)
      | int ((c as Const(@{const_name Groups.times}, _)) $ x $ y) = c $ (int x) $ (int y)
      | int ((c as Const(@{const_name Groups.uminus}, _)) $ x) = c $ (int x)
      | int t = lit t
    (*abstraction of a natural number expression: no minus*)
    fun nat ((c as Const(@{const_name Groups.plus}, _)) $ x $ y) = c $ (nat x) $ (nat y)
      | nat ((c as Const(@{const_name Groups.times}, _)) $ x $ y) = c $ (nat x) $ (nat y)
      | nat ((c as Const(@{const_name Suc}, _)) $ x) = c $ (nat x)
      | nat t = lit t
    (*abstraction of a relation: =, <, <=*)
    fun rel (T, c $ x $ y) =
            if T = HOLogic.realT then c $ (rat x) $ (rat y)
            else if T = HOLogic.intT then c $ (int x) $ (int y)
            else if T = HOLogic.natT then c $ (nat x) $ (nat y)
            else if T = HOLogic.boolT then c $ (fm x) $ (fm y)
            else replace (c $ x $ y)   (*non-numeric comparison*)
    (*abstraction of a formula*)
    and fm ((c as Const(@{const_name HOL.conj}, _)) $ p $ q) = c $ (fm p) $ (fm q)
      | fm ((c as Const(@{const_name HOL.disj}, _)) $ p $ q) = c $ (fm p) $ (fm q)
      | fm ((c as Const(@{const_name HOL.implies}, _)) $ p $ q) = c $ (fm p) $ (fm q)
      | fm ((c as Const(@{const_name Not}, _)) $ p) = c $ (fm p)
      | fm ((c as Const(@{const_name True}, _))) = c
      | fm ((c as Const(@{const_name False}, _))) = c
      | fm (t as Const(@{const_name HOL.eq},  Type ("fun", [T,_])) $ _ $ _) = rel (T, t)
      | fm (t as Const(@{const_name Orderings.less},  Type ("fun", [T,_])) $ _ $ _) = rel (T, t)
      | fm (t as Const(@{const_name Orderings.less_eq}, Type ("fun", [T,_])) $ _ $ _) = rel (T, t)
      | fm t = replace t
    (*entry point, and abstraction of a meta-formula*)
    fun mt ((c as Const(@{const_name Trueprop}, _)) $ p) = c $ (fm p)
      | mt ((c as Const("==>", _)) $ p $ q)  = c $ (mt p) $ (mt q)
      | mt t = fm t  (*it might be a formula*)
  in (Logic.list_all (params, mt body), !pairs) end;


(*Present the entire subgoal to the oracle, assumptions and all, but possibly
  abstracted.  Use via compose_tac, which performs no lifting but will
  instantiate variables.*)

val svc_tac = CSUBGOAL (fn (ct, i) =>
  let
    val thy = Thm.theory_of_cterm ct;
    val (abs_goal, _) = svc_abstract (Thm.term_of ct);
    val th = svc_oracle (Thm.cterm_of thy abs_goal);
   in compose_tac (false, th, 0) i end
   handle TERM _ => no_tac);
*}

end
