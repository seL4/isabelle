(*  Title:      Provers/quantifier1
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997  TU Munich

Simplification procedures for turning

            ? x. ... & x = t & ...
     into   ? x. x = t & ... & ...
     where the `? x. x = t &' in the latter formula must be eliminated
           by ordinary simplification. 

     and   ! x. (... & x = t & ...) --> P x
     into  ! x. x = t --> (... & ...) --> P x
     where the `!x. x=t -->' in the latter formula is eliminated
           by ordinary simplification.

     And analogously for t=x, but the eqn is not turned around!

     NB Simproc is only triggered by "!x. P(x) & P'(x) --> Q(x)";
        "!x. x=t --> P(x)" is covered by the congreunce rule for -->;
        "!x. t=x --> P(x)" must be taken care of by an ordinary rewrite rule.
        As must be "? x. t=x & P(x)".

        
     And similarly for the bounded quantifiers.

Gries etc call this the "1 point rules"
*)

signature QUANTIFIER1_DATA =
sig
  (*abstract syntax*)
  val dest_eq: term -> (term*term*term)option
  val dest_conj: term -> (term*term*term)option
  val dest_imp:  term -> (term*term*term)option
  val conj: term
  val imp:  term
  (*rules*)
  val iff_reflection: thm (* P <-> Q ==> P == Q *)
  val iffI:  thm
  val conjI: thm
  val conjE: thm
  val impI:  thm
  val mp:    thm
  val exI:   thm
  val exE:   thm
  val uncurry: thm (* P --> Q --> R ==> P & Q --> R *)
  val iff_allI: thm (* !!x. P x <-> Q x ==> (!x. P x) = (!x. Q x) *)
end;

signature QUANTIFIER1 =
sig
  val prove_one_point_all_tac: tactic
  val prove_one_point_ex_tac: tactic
  val rearrange_all: Sign.sg -> thm list -> term -> thm option
  val rearrange_ex:  Sign.sg -> thm list -> term -> thm option
  val rearrange_ball: tactic -> Sign.sg -> thm list -> term -> thm option
  val rearrange_bex:  tactic -> Sign.sg -> thm list -> term -> thm option
end;

functor Quantifier1Fun(Data: QUANTIFIER1_DATA): QUANTIFIER1 =
struct

open Data;

(* FIXME: only test! *)
fun def eq = case dest_eq eq of
      Some(c,s,t) =>
        s = Bound 0 andalso not(loose_bvar1(t,0)) orelse
        t = Bound 0 andalso not(loose_bvar1(s,0))
    | None => false;

fun extract_conj t = case dest_conj t of None => None
    | Some(conj,P,Q) =>
        (if def P then Some(P,Q) else
         if def Q then Some(Q,P) else
         (case extract_conj P of
            Some(eq,P') => Some(eq, conj $ P' $ Q)
          | None => (case extract_conj Q of
                       Some(eq,Q') => Some(eq,conj $ P $ Q')
                     | None => None)));

fun extract_imp t = case dest_imp t of None => None
    | Some(imp,P,Q) => if def P then Some(P,Q)
                       else (case extract_conj P of
                               Some(eq,P') => Some(eq, imp $ P' $ Q)
                             | None => (case extract_imp Q of
                                          None => None
                                        | Some(eq,Q') => Some(eq, imp$P$Q')));
    

fun prove_conv tac sg tu =
  let val meta_eq = cterm_of sg (Logic.mk_equals tu)
  in prove_goalw_cterm [] meta_eq (K [rtac iff_reflection 1, tac])
     handle ERROR =>
            error("The error(s) above occurred while trying to prove " ^
                  string_of_cterm meta_eq)
  end;

(* Proves (? x. ... & x = t & ...) = (? x. x = t & ... & ...)
   Better: instantiate exI
*)
val prove_one_point_ex_tac = rtac iffI 1 THEN
    ALLGOALS(EVERY'[etac exE, REPEAT_DETERM o (etac conjE), rtac exI,
                    DEPTH_SOLVE_1 o (ares_tac [conjI])]);

(* Proves (! x. (... & x = t & ...) --> P x) =
          (! x. x = t --> (... & ...) --> P x)
*)
local
val tac = SELECT_GOAL
          (EVERY1[REPEAT o (dtac uncurry), REPEAT o (rtac impI), etac mp,
                  REPEAT o (etac conjE), REPEAT o (ares_tac [conjI])])
in
val prove_one_point_all_tac = EVERY1[rtac iff_allI, rtac iffI, tac, tac]
end

fun rearrange_all sg _ (F as all $ Abs(x,T, P)) =
     (case extract_imp P of
        None => None
      | Some(eq,Q) =>
          let val R = imp $ eq $ Q
          in Some(prove_conv prove_one_point_all_tac sg (F,all$Abs(x,T,R))) end)
  | rearrange_all _ _ _ = None;

fun rearrange_ball tac sg _ (F as Ball $ A $ Abs(x,T,P)) =
     (case extract_imp P of
        None => None
      | Some(eq,Q) =>
          let val R = imp $ eq $ Q
          in Some(prove_conv tac sg (F,Ball $ A $ Abs(x,T,R))) end)
  | rearrange_ball _ _ _ _ = None;

fun rearrange_ex sg _ (F as ex $ Abs(x,T,P)) =
     (case extract_conj P of
        None => None
      | Some(eq,Q) =>
          Some(prove_conv prove_one_point_ex_tac sg (F,ex $ Abs(x,T,conj$eq$Q))))
  | rearrange_ex _ _ _ = None;

fun rearrange_bex tac sg _ (F as Bex $ A $ Abs(x,T,P)) =
     (case extract_conj P of
        None => None
      | Some(eq,Q) =>
          Some(prove_conv tac sg (F,Bex $ A $ Abs(x,T,conj$eq$Q))))
  | rearrange_bex _ _ _ _ = None;

end;
