(*  Title:      Provers/quantifier1.ML
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
        "!x. x=t --> P(x)" is covered by the congruence rule for -->;
        "!x. t=x --> P(x)" must be taken care of by an ordinary rewrite rule.
        As must be "? x. t=x & P(x)".

     And similarly for the bounded quantifiers.

Gries etc call this the "1 point rules"

The above also works for !x1..xn. and ?x1..xn by moving the defined
quantifier inside first, but not for nested bounded quantifiers.

For set comprehensions the basic permutations
      ... & x = t & ...  ->  x = t & (... & ...)
      ... & t = x & ...  ->  t = x & (... & ...)
are also exported.

To avoid looping, NONE is returned if the term cannot be rearranged,
esp if x=t/t=x sits at the front already.
*)

signature QUANTIFIER1_DATA =
sig
  (*abstract syntax*)
  val dest_eq: term -> (term * term) option
  val dest_conj: term -> (term * term) option
  val dest_imp: term -> (term * term) option
  val conj: term
  val imp: term
  (*rules*)
  val iff_reflection: thm (* P <-> Q ==> P == Q *)
  val iffI: thm
  val iff_trans: thm
  val conjI: thm
  val conjE: thm
  val impI: thm
  val mp: thm
  val exI: thm
  val exE: thm
  val uncurry: thm (* P --> Q --> R ==> P & Q --> R *)
  val iff_allI: thm (* !!x. P x <-> Q x ==> (!x. P x) = (!x. Q x) *)
  val iff_exI: thm (* !!x. P x <-> Q x ==> (? x. P x) = (? x. Q x) *)
  val all_comm: thm (* (!x y. P x y) = (!y x. P x y) *)
  val ex_comm: thm (* (? x y. P x y) = (? y x. P x y) *)
end;

signature QUANTIFIER1 =
sig
  val prove_one_point_all_tac: Proof.context -> tactic
  val prove_one_point_ex_tac: Proof.context -> tactic
  val rearrange_all: Proof.context -> cterm -> thm option
  val rearrange_ex: Proof.context -> cterm -> thm option
  val rearrange_ball: (Proof.context -> tactic) -> Proof.context -> cterm -> thm option
  val rearrange_bex: (Proof.context -> tactic) -> Proof.context -> cterm -> thm option
  val rearrange_Collect: (Proof.context -> tactic) -> Proof.context -> cterm -> thm option
end;

functor Quantifier1(Data: QUANTIFIER1_DATA): QUANTIFIER1 =
struct

(* FIXME: only test! *)
fun def xs eq =
  (case Data.dest_eq eq of
    SOME (s, t) =>
      let val n = length xs in
        s = Bound n andalso not (loose_bvar1 (t, n)) orelse
        t = Bound n andalso not (loose_bvar1 (s, n))
      end
  | NONE => false);

fun extract_conj fst xs t =
  (case Data.dest_conj t of
    NONE => NONE
  | SOME (P, Q) =>
      if def xs P then (if fst then NONE else SOME (xs, P, Q))
      else if def xs Q then SOME (xs, Q, P)
      else
        (case extract_conj false xs P of
          SOME (xs, eq, P') => SOME (xs, eq, Data.conj $ P' $ Q)
        | NONE =>
            (case extract_conj false xs Q of
              SOME (xs, eq, Q') => SOME (xs, eq, Data.conj $ P $ Q')
            | NONE => NONE)));

fun extract_imp fst xs t =
  (case Data.dest_imp t of
    NONE => NONE
  | SOME (P, Q) =>
      if def xs P then (if fst then NONE else SOME (xs, P, Q))
      else
        (case extract_conj false xs P of
          SOME (xs, eq, P') => SOME (xs, eq, Data.imp $ P' $ Q)
        | NONE =>
            (case extract_imp false xs Q of
              NONE => NONE
            | SOME (xs, eq, Q') => SOME (xs, eq, Data.imp $ P $ Q'))));

fun extract_quant extract q =
  let
    fun exqu xs ((qC as Const (qa, _)) $ Abs (x, T, Q)) =
          if qa = q then exqu ((qC, x, T) :: xs) Q else NONE
      | exqu xs P = extract (null xs) xs P
  in exqu [] end;

fun prove_conv ctxt tu tac =
  let
    val (goal, ctxt') =
      yield_singleton (Variable.import_terms true) (Logic.mk_equals tu) ctxt;
    val thm =
      Goal.prove ctxt' [] [] goal
        (fn {context = ctxt'', ...} =>
          resolve_tac ctxt'' [Data.iff_reflection] 1 THEN tac ctxt'');
  in singleton (Variable.export ctxt' ctxt) thm end;

fun qcomm_tac ctxt qcomm qI i =
  REPEAT_DETERM (resolve_tac ctxt [qcomm] i THEN resolve_tac ctxt [qI] i);

(* Proves (? x0..xn. ... & x0 = t & ...) = (? x1..xn x0. x0 = t & ... & ...)
   Better: instantiate exI
*)
local
  val excomm = Data.ex_comm RS Data.iff_trans;
in
  fun prove_one_point_ex_tac ctxt =
    qcomm_tac ctxt excomm Data.iff_exI 1 THEN resolve_tac ctxt [Data.iffI] 1 THEN
    ALLGOALS
      (EVERY' [eresolve_tac ctxt [Data.exE], REPEAT_DETERM o eresolve_tac ctxt [Data.conjE],
        resolve_tac ctxt [Data.exI],
        DEPTH_SOLVE_1 o ares_tac [Data.conjI]])
end;

(* Proves (! x0..xn. (... & x0 = t & ...) --> P x0) =
          (! x1..xn x0. x0 = t --> (... & ...) --> P x0)
*)
local
  fun tac ctxt =
    SELECT_GOAL
      (EVERY1 [REPEAT o dresolve_tac ctxt [Data.uncurry],
        REPEAT o resolve_tac ctxt [Data.impI],
        eresolve_tac ctxt [Data.mp],
        REPEAT o eresolve_tac ctxt [Data.conjE],
        REPEAT o ares_tac [Data.conjI]]);
  val allcomm = Data.all_comm RS Data.iff_trans;
in
  fun prove_one_point_all_tac ctxt =
    EVERY1 [qcomm_tac ctxt allcomm Data.iff_allI,
      resolve_tac ctxt [Data.iff_allI],
      resolve_tac ctxt [Data.iffI], tac ctxt, tac ctxt];
end

fun renumber l u (Bound i) =
      Bound (if i < l orelse i > u then i else if i = u then l else i + 1)
  | renumber l u (s $ t) = renumber l u s $ renumber l u t
  | renumber l u (Abs (x, T, t)) = Abs (x, T, renumber (l + 1) (u + 1) t)
  | renumber _ _ atom = atom;

fun quantify qC x T xs P =
  let
    fun quant [] P = P
      | quant ((qC, x, T) :: xs) P = quant xs (qC $ Abs (x, T, P));
    val n = length xs;
    val Q = if n = 0 then P else renumber 0 n P;
  in quant xs (qC $ Abs (x, T, Q)) end;

fun rearrange_all ctxt ct =
  (case term_of ct of
    F as (all as Const (q, _)) $ Abs (x, T, P) =>
      (case extract_quant extract_imp q P of
        NONE => NONE
      | SOME (xs, eq, Q) =>
          let val R = quantify all x T xs (Data.imp $ eq $ Q)
          in SOME (prove_conv ctxt (F, R) prove_one_point_all_tac) end)
  | _ => NONE);

fun rearrange_ball tac ctxt ct =
  (case term_of ct of
    F as Ball $ A $ Abs (x, T, P) =>
      (case extract_imp true [] P of
        NONE => NONE
      | SOME (xs, eq, Q) =>
          if not (null xs) then NONE
          else
            let val R = Data.imp $ eq $ Q
            in SOME (prove_conv ctxt (F, Ball $ A $ Abs (x, T, R)) tac) end)
  | _ => NONE);

fun rearrange_ex ctxt ct =
  (case term_of ct of
    F as (ex as Const (q, _)) $ Abs (x, T, P) =>
      (case extract_quant extract_conj q P of
        NONE => NONE
      | SOME (xs, eq, Q) =>
          let val R = quantify ex x T xs (Data.conj $ eq $ Q)
          in SOME (prove_conv ctxt (F, R) prove_one_point_ex_tac) end)
  | _ => NONE);

fun rearrange_bex tac ctxt ct =
  (case term_of ct of
    F as Bex $ A $ Abs (x, T, P) =>
      (case extract_conj true [] P of
        NONE => NONE
      | SOME (xs, eq, Q) =>
          if not (null xs) then NONE
          else SOME (prove_conv ctxt (F, Bex $ A $ Abs (x, T, Data.conj $ eq $ Q)) tac))
  | _ => NONE);

fun rearrange_Collect tac ctxt ct =
  (case term_of ct of
    F as Collect $ Abs (x, T, P) =>
      (case extract_conj true [] P of
        NONE => NONE
      | SOME (_, eq, Q) =>
          let val R = Collect $ Abs (x, T, Data.conj $ eq $ Q)
          in SOME (prove_conv ctxt (F, R) tac) end)
  | _ => NONE);

end;

