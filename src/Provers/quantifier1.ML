(*  Title:      Provers/quantifier1
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997  TU Munich

Simplification procedures for turning

            ? x. ... & x = t & ...
     into   ? x. x = t & ... & ...
     where the `? x. x = t &' in the latter formula is eliminated
           by ordinary simplification. 

     and   ! x. (... & x = t & ...) --> P x
     into  ! x. x = t --> (... & ...) --> P x
     where the `!x. x=t -->' in the latter formula is eliminated
           by ordinary simplification.

     NB Simproc is only triggered by "!x. P(x) & P'(x) --> Q(x)";
        "!x. x=t --> P(x)" is covered by the congreunce rule for -->;
        "!x. t=x --> P(x)" must be taken care of by an ordinary rewrite rule.

Gries etc call this the "1 point rules"
*)

signature QUANTIFIER1_DATA =
sig
  (*abstract syntax*)
  val dest_eq: term -> (term*term*term)option
  val dest_conj: term -> (term*term*term)option
  val conj: term
  val imp:  term
  (*rules*)
  val iff_reflection: thm (* P <-> Q ==> P == Q *)
  val iffI:  thm
  val sym:   thm
  val conjI: thm
  val conjE: thm
  val impI:  thm
  val impE:  thm
  val mp:    thm
  val exI:   thm
  val exE:   thm
  val allI:  thm
  val allE:  thm
end;

signature QUANTIFIER1 =
sig
  val rearrange_all: Sign.sg -> thm list -> term -> thm option
  val rearrange_ex:  Sign.sg -> thm list -> term -> thm option
end;

functor Quantifier1Fun(Data: QUANTIFIER1_DATA): QUANTIFIER1 =
struct

open Data;

fun def eq = case dest_eq eq of
      Some(c,s,t) =>
        if s = Bound 0 andalso not(loose_bvar1(t,0)) then Some eq else
        if t = Bound 0 andalso not(loose_bvar1(s,0)) then Some(c$t$s)
        else None
    | None => None;

fun extract conj = case dest_conj conj of
      Some(conj,P,Q) =>
        (case def P of
           Some eq => Some(eq,Q)
         | None =>
             (case def Q of
                Some eq => Some(eq,P)
              | None =>
                 (case extract P of
                    Some(eq,P') => Some(eq, conj $ P' $ Q)
                  | None =>
                      (case extract Q of
                         Some(eq,Q') => Some(eq,conj $ P $ Q')
                       | None => None))))
    | None => None;

fun prove_conv tac sg tu =
  let val meta_eq = cterm_of sg (Logic.mk_equals tu)
  in prove_goalw_cterm [] meta_eq (K [rtac iff_reflection 1, tac])
     handle ERROR =>
            error("The error(s) above occurred while trying to prove " ^
                  string_of_cterm meta_eq)
  end;

val prove_all_tac = EVERY1[rtac iffI,
                       rtac allI, etac allE, rtac impI, rtac impI, etac mp,
                          REPEAT o (etac conjE),
                          REPEAT o (ares_tac [conjI] ORELSE' etac sym),
                       rtac allI, etac allE, rtac impI, REPEAT o (etac conjE),
                          etac impE, atac ORELSE' etac sym, etac mp,
                          REPEAT o (ares_tac [conjI])];

fun rearrange_all sg _ (F as all $ Abs(x,T,(* --> *)_ $ P $ Q)) =
     (case extract P of
        None => None
      | Some(eq,P') =>
          let val R = imp $ eq $ (imp $ P' $ Q)
          in Some(prove_conv prove_all_tac sg (F,all$Abs(x,T,R))) end)
  | rearrange_all _ _ _ = None;

val prove_ex_tac = rtac iffI 1 THEN
    ALLGOALS(EVERY'[etac exE, REPEAT o (etac conjE),
                    rtac exI, REPEAT o (ares_tac [conjI] ORELSE' etac sym)]);

fun rearrange_ex sg _ (F as ex $ Abs(x,T,P)) =
     (case extract P of
        None => None
      | Some(eq,Q) =>
          Some(prove_conv prove_ex_tac sg (F,ex $ Abs(x,T,conj$eq$Q))))
  | rearrange_ex _ _ _ = None;

end;
