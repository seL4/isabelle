(*  Title:      HOL/Hoare/hoare_syntax.ML
    Author:     Leonor Prensa Nieto & Tobias Nipkow

Syntax translations for Hoare logic.
*)

signature HOARE_SYNTAX =
sig
  val hoare_vars_tr: term list -> term
  val spec_tr': string -> term list -> term
end;

structure Hoare_Syntax: HOARE_SYNTAX =
struct

(** parse translation **)

local

fun idt_name (Free (x, _)) = SOME x
  | idt_name (Const (@{syntax_const "_constrain"}, _) $ t $ _) = idt_name t
  | idt_name _ = NONE;

fun eq_idt tu =
  (case pairself idt_name tu of
    (SOME x, SOME y) => x = y
  | _ => false);

fun mk_abstuple [x] body = Syntax_Trans.abs_tr [x, body]
  | mk_abstuple (x :: xs) body =
      Syntax.const @{const_syntax case_prod} $ Syntax_Trans.abs_tr [x, mk_abstuple xs body];

fun mk_fbody x e [y] = if eq_idt (x, y) then e else y
  | mk_fbody x e (y :: xs) =
      Syntax.const @{const_syntax Pair} $
        (if eq_idt (x, y) then e else y) $ mk_fbody x e xs;

fun mk_fexp x e xs = mk_abstuple xs (mk_fbody x e xs);


(* bexp_tr & assn_tr *)
(*all meta-variables for bexp except for TRUE are translated as if they
  were boolean expressions*)

fun bexp_tr (Const ("TRUE", _)) xs = Syntax.const "TRUE"   (* FIXME !? *)
  | bexp_tr b xs = Syntax.const @{const_syntax Collect} $ mk_abstuple xs b;

fun assn_tr r xs = Syntax.const @{const_syntax Collect} $ mk_abstuple xs r;


(* com_tr *)

fun com_tr (Const (@{syntax_const "_assign"}, _) $ x $ e) xs =
      Syntax.const @{const_syntax Basic} $ mk_fexp x e xs
  | com_tr (Const (@{const_syntax Basic},_) $ f) xs = Syntax.const @{const_syntax Basic} $ f
  | com_tr (Const (@{const_syntax Seq},_) $ c1 $ c2) xs =
      Syntax.const @{const_syntax Seq} $ com_tr c1 xs $ com_tr c2 xs
  | com_tr (Const (@{const_syntax Cond},_) $ b $ c1 $ c2) xs =
      Syntax.const @{const_syntax Cond} $ bexp_tr b xs $ com_tr c1 xs $ com_tr c2 xs
  | com_tr (Const (@{const_syntax While},_) $ b $ I $ c) xs =
      Syntax.const @{const_syntax While} $ bexp_tr b xs $ assn_tr I xs $ com_tr c xs
  | com_tr t _ = t;

fun vars_tr (Const (@{syntax_const "_idts"}, _) $ idt $ vars) = idt :: vars_tr vars
  | vars_tr t = [t];

in

fun hoare_vars_tr [vars, pre, prg, post] =
      let val xs = vars_tr vars
      in Syntax.const @{const_syntax Valid} $
         assn_tr pre xs $ com_tr prg xs $ assn_tr post xs
      end
  | hoare_vars_tr ts = raise TERM ("hoare_vars_tr", ts);

end;



(** print translation **)

local

fun dest_abstuple
      (Const (@{const_syntax case_prod}, _) $ Abs (v, _, body)) =
        subst_bound (Syntax.free v, dest_abstuple body)
  | dest_abstuple (Abs (v,_, body)) = subst_bound (Syntax.free v, body)
  | dest_abstuple tm = tm;

fun abs2list (Const (@{const_syntax case_prod}, _) $ Abs (x, T, t)) = Free (x, T) :: abs2list t
  | abs2list (Abs (x, T, t)) = [Free (x, T)]
  | abs2list _ = [];

fun mk_ts (Const (@{const_syntax case_prod}, _) $ Abs (x, _, t)) = mk_ts t
  | mk_ts (Abs (x, _, t)) = mk_ts t
  | mk_ts (Const (@{const_syntax Pair}, _) $ a $ b) = a :: mk_ts b
  | mk_ts t = [t];

fun mk_vts (Const (@{const_syntax case_prod},_) $ Abs (x, _, t)) =
      (Syntax.free x :: abs2list t, mk_ts t)
  | mk_vts (Abs (x, _, t)) = ([Syntax.free x], [t])
  | mk_vts t = raise Match;

fun find_ch [] i xs = (false, (Syntax.free "not_ch", Syntax.free "not_ch"))  (* FIXME no_ch!? *)
  | find_ch ((v, t) :: vts) i xs =
      if t = Bound i then find_ch vts (i - 1) xs
      else (true, (v, subst_bounds (xs, t)));

fun is_f (Const (@{const_syntax case_prod}, _) $ Abs (x, _, t)) = true
  | is_f (Abs (x, _, t)) = true
  | is_f t = false;


(* assn_tr' & bexp_tr'*)

fun assn_tr' (Const (@{const_syntax Collect}, _) $ T) = dest_abstuple T
  | assn_tr' (Const (@{const_syntax inter}, _) $
        (Const (@{const_syntax Collect}, _) $ T1) $ (Const (@{const_syntax Collect}, _) $ T2)) =
      Syntax.const @{const_syntax inter} $ dest_abstuple T1 $ dest_abstuple T2
  | assn_tr' t = t;

fun bexp_tr' (Const (@{const_syntax Collect}, _) $ T) = dest_abstuple T
  | bexp_tr' t = t;


(* com_tr' *)

fun mk_assign f =
  let
    val (vs, ts) = mk_vts f;
    val (ch, which) = find_ch (vs ~~ ts) (length vs - 1) (rev vs);
  in
    if ch
    then Syntax.const @{syntax_const "_assign"} $ fst which $ snd which
    else Syntax.const @{const_syntax annskip}
  end;

fun com_tr' (Const (@{const_syntax Basic}, _) $ f) =
      if is_f f then mk_assign f
      else Syntax.const @{const_syntax Basic} $ f
  | com_tr' (Const (@{const_syntax Seq},_) $ c1 $ c2) =
      Syntax.const @{const_syntax Seq} $ com_tr' c1 $ com_tr' c2
  | com_tr' (Const (@{const_syntax Cond}, _) $ b $ c1 $ c2) =
      Syntax.const @{const_syntax Cond} $ bexp_tr' b $ com_tr' c1 $ com_tr' c2
  | com_tr' (Const (@{const_syntax While}, _) $ b $ I $ c) =
      Syntax.const @{const_syntax While} $ bexp_tr' b $ assn_tr' I $ com_tr' c
  | com_tr' t = t;

in

fun spec_tr' syn [p, c, q] = Syntax.const syn $ assn_tr' p $ com_tr' c $ assn_tr' q

end;

end;

