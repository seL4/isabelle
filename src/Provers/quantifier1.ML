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
  val iff_trans: thm
  val conjI: thm
  val conjE: thm
  val impI:  thm
  val mp:    thm
  val exI:   thm
  val exE:   thm
  val uncurry: thm (* P --> Q --> R ==> P & Q --> R *)
  val iff_allI: thm (* !!x. P x <-> Q x ==> (!x. P x) = (!x. Q x) *)
  val iff_exI: thm (* !!x. P x <-> Q x ==> (? x. P x) = (? x. Q x) *)
  val all_comm: thm (* (!x y. P x y) = (!y x. P x y) *)
  val ex_comm: thm (* (? x y. P x y) = (? y x. P x y) *)
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
fun def xs eq =
  let val n = length xs
  in case dest_eq eq of
      Some(c,s,t) =>
        s = Bound n andalso not(loose_bvar1(t,n)) orelse
        t = Bound n andalso not(loose_bvar1(s,n))
    | None => false
  end;

fun extract_conj xs t = case dest_conj t of None => None
    | Some(conj,P,Q) =>
        (if def xs P then Some(xs,P,Q) else
         if def xs Q then Some(xs,Q,P) else
         (case extract_conj xs P of
            Some(xs,eq,P') => Some(xs,eq, conj $ P' $ Q)
          | None => (case extract_conj xs Q of
                       Some(xs,eq,Q') => Some(xs,eq,conj $ P $ Q')
                     | None => None)));

fun extract_imp xs t = case dest_imp t of None => None
    | Some(imp,P,Q) => if def xs P then Some(xs,P,Q)
                       else (case extract_conj xs P of
                               Some(xs,eq,P') => Some(xs, eq, imp $ P' $ Q)
                             | None => (case extract_imp xs Q of
                                          None => None
                                        | Some(xs,eq,Q') =>
                                            Some(xs,eq,imp$P$Q')));

fun extract_quant extract q =
  let fun exqu xs ((qC as Const(qa,_)) $ Abs(x,T,Q)) =
            if qa = q then exqu ((qC,x,T)::xs) Q else None
        | exqu xs P = extract xs P
  in exqu end;

fun prove_conv tac sg tu =
  let val meta_eq = cterm_of sg (Logic.mk_equals tu)
  in prove_goalw_cterm [] meta_eq (K [rtac iff_reflection 1, tac])
     handle ERROR =>
            error("The error(s) above occurred while trying to prove " ^
                  string_of_cterm meta_eq)
  end;

fun qcomm_tac qcomm qI i = REPEAT_DETERM (rtac qcomm i THEN rtac qI i) 

(* Proves (? x0..xn. ... & x0 = t & ...) = (? x1..xn x0. x0 = t & ... & ...)
   Better: instantiate exI
*)
local
val excomm = ex_comm RS iff_trans
in
val prove_one_point_ex_tac = qcomm_tac excomm iff_exI 1 THEN rtac iffI 1 THEN
    ALLGOALS(EVERY'[etac exE, REPEAT_DETERM o (etac conjE), rtac exI,
                    DEPTH_SOLVE_1 o (ares_tac [conjI])])
end;

(* Proves (! x0..xn. (... & x0 = t & ...) --> P x0) =
          (! x1..xn x0. x0 = t --> (... & ...) --> P x0)
*)
local
val tac = SELECT_GOAL
          (EVERY1[REPEAT o (dtac uncurry), REPEAT o (rtac impI), etac mp,
                  REPEAT o (etac conjE), REPEAT o (ares_tac [conjI])])
val allcomm = all_comm RS iff_trans
in
val prove_one_point_all_tac =
      EVERY1[qcomm_tac allcomm iff_allI,rtac iff_allI, rtac iffI, tac, tac]
end

fun renumber l u (Bound i) = Bound(if i < l orelse i > u then i else
                                   if i=u then l else i+1)
  | renumber l u (s$t) = renumber l u s $ renumber l u t
  | renumber l u (Abs(x,T,t)) = Abs(x,T,renumber (l+1) (u+1) t)
  | renumber _ _ atom = atom;

fun quantify qC x T xs P =
  let fun quant [] P = P
        | quant ((qC,x,T)::xs) P = quant xs (qC $ Abs(x,T,P))
      val n = length xs
      val Q = if n=0 then P else renumber 0 n P
  in quant xs (qC $ Abs(x,T,Q)) end;

fun rearrange_all sg _ (F as (all as Const(q,_)) $ Abs(x,T, P)) =
     (case extract_quant extract_imp q [] P of
        None => None
      | Some(xs,eq,Q) =>
          let val R = quantify all x T xs (imp $ eq $ Q)
          in Some(prove_conv prove_one_point_all_tac sg (F,R)) end)
  | rearrange_all _ _ _ = None;

fun rearrange_ball tac sg _ (F as Ball $ A $ Abs(x,T,P)) =
     (case extract_imp [] P of
        None => None
      | Some(xs,eq,Q) => if not(null xs) then None else
          let val R = imp $ eq $ Q
          in Some(prove_conv tac sg (F,Ball $ A $ Abs(x,T,R))) end)
  | rearrange_ball _ _ _ _ = None;

fun rearrange_ex sg _ (F as (ex as Const(q,_)) $ Abs(x,T,P)) =
     (case extract_quant extract_conj q [] P of
        None => None
      | Some(xs,eq,Q) =>
          let val R = quantify ex x T xs (conj $ eq $ Q)
          in Some(prove_conv prove_one_point_ex_tac sg (F,R)) end)
  | rearrange_ex _ _ _ = None;

fun rearrange_bex tac sg _ (F as Bex $ A $ Abs(x,T,P)) =
     (case extract_conj [] P of
        None => None
      | Some(xs,eq,Q) => if not(null xs) then None else
          Some(prove_conv tac sg (F,Bex $ A $ Abs(x,T,conj$eq$Q))))
  | rearrange_bex _ _ _ _ = None;

end;
