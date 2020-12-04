(*  Title:      HOL/Hoare/hoare_syntax.ML
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Author:     Walter Guttmann (extension to total-correctness proofs)

Syntax translations for Hoare logic.
*)

signature HOARE_SYNTAX =
sig
  val hoare_vars_tr: term list -> term
  val hoare_tc_vars_tr: term list -> term
  val spec_tr': string -> term list -> term
end;

structure Hoare_Syntax: HOARE_SYNTAX =
struct

(** parse translation **)

local

fun idt_name (Free (x, _)) = SOME x
  | idt_name (Const (\<^syntax_const>\<open>_constrain\<close>, _) $ t $ _) = idt_name t
  | idt_name _ = NONE;

fun eq_idt tu =
  (case apply2 idt_name tu of
    (SOME x, SOME y) => x = y
  | _ => false);

fun mk_abstuple [x] body = Syntax_Trans.abs_tr [x, body]
  | mk_abstuple (x :: xs) body =
      Syntax.const \<^const_syntax>\<open>case_prod\<close> $ Syntax_Trans.abs_tr [x, mk_abstuple xs body];

fun mk_fbody x e [y] = if eq_idt (x, y) then e else y
  | mk_fbody x e (y :: xs) =
      Syntax.const \<^const_syntax>\<open>Pair\<close> $
        (if eq_idt (x, y) then e else y) $ mk_fbody x e xs;

fun mk_fexp x e xs = mk_abstuple xs (mk_fbody x e xs);


(* bexp_tr & assn_tr *)
(*all meta-variables for bexp except for TRUE are translated as if they
  were boolean expressions*)

fun bexp_tr (Const ("TRUE", _)) _ = Syntax.const "TRUE"   (* FIXME !? *)
  | bexp_tr b xs = Syntax.const \<^const_syntax>\<open>Collect\<close> $ mk_abstuple xs b;

fun assn_tr r xs = Syntax.const \<^const_syntax>\<open>Collect\<close> $ mk_abstuple xs r;

fun var_tr v xs = mk_abstuple xs v;


(* com_tr *)

fun com_tr (Const (\<^syntax_const>\<open>_assign\<close>, _) $ x $ e) xs =
      Syntax.const \<^const_syntax>\<open>Basic\<close> $ mk_fexp x e xs
  | com_tr (Const (\<^const_syntax>\<open>Basic\<close>,_) $ f) _ = Syntax.const \<^const_syntax>\<open>Basic\<close> $ f
  | com_tr (Const (\<^const_syntax>\<open>Seq\<close>,_) $ c1 $ c2) xs =
      Syntax.const \<^const_syntax>\<open>Seq\<close> $ com_tr c1 xs $ com_tr c2 xs
  | com_tr (Const (\<^const_syntax>\<open>Cond\<close>,_) $ b $ c1 $ c2) xs =
      Syntax.const \<^const_syntax>\<open>Cond\<close> $ bexp_tr b xs $ com_tr c1 xs $ com_tr c2 xs
  | com_tr (Const (\<^const_syntax>\<open>While\<close>,_) $ b $ I $ V $ c) xs =
      Syntax.const \<^const_syntax>\<open>While\<close> $ bexp_tr b xs $ assn_tr I xs $ var_tr V xs $ com_tr c xs
  | com_tr t _ = t;

fun vars_tr (Const (\<^syntax_const>\<open>_idts\<close>, _) $ idt $ vars) = idt :: vars_tr vars
  | vars_tr t = [t];

in

fun hoare_vars_tr [vars, pre, prg, post] =
      let val xs = vars_tr vars
      in Syntax.const \<^const_syntax>\<open>Valid\<close> $
         assn_tr pre xs $ com_tr prg xs $ assn_tr post xs
      end
  | hoare_vars_tr ts = raise TERM ("hoare_vars_tr", ts);

fun hoare_tc_vars_tr [vars, pre, prg, post] =
      let val xs = vars_tr vars
      in Syntax.const \<^const_syntax>\<open>ValidTC\<close> $
         assn_tr pre xs $ com_tr prg xs $ assn_tr post xs
      end
  | hoare_tc_vars_tr ts = raise TERM ("hoare_tc_vars_tr", ts);

end;



(** print translation **)

local

fun dest_abstuple
      (Const (\<^const_syntax>\<open>case_prod\<close>, _) $ Abs (v, _, body)) =
        subst_bound (Syntax.free v, dest_abstuple body)
  | dest_abstuple (Abs (v,_, body)) = subst_bound (Syntax.free v, body)
  | dest_abstuple tm = tm;

fun abs2list (Const (\<^const_syntax>\<open>case_prod\<close>, _) $ Abs (x, T, t)) = Free (x, T) :: abs2list t
  | abs2list (Abs (x, T, _)) = [Free (x, T)]
  | abs2list _ = [];

fun mk_ts (Const (\<^const_syntax>\<open>case_prod\<close>, _) $ Abs (_, _, t)) = mk_ts t
  | mk_ts (Abs (_, _, t)) = mk_ts t
  | mk_ts (Const (\<^const_syntax>\<open>Pair\<close>, _) $ a $ b) = a :: mk_ts b
  | mk_ts t = [t];

fun mk_vts (Const (\<^const_syntax>\<open>case_prod\<close>,_) $ Abs (x, _, t)) =
      (Syntax.free x :: abs2list t, mk_ts t)
  | mk_vts (Abs (x, _, t)) = ([Syntax.free x], [t])
  | mk_vts _ = raise Match;

fun find_ch [] _ _ = (false, (Syntax.free "not_ch", Syntax.free "not_ch"))  (* FIXME no_ch!? *)
  | find_ch ((v, t) :: vts) i xs =
      if t = Bound i then find_ch vts (i - 1) xs
      else (true, (v, subst_bounds (xs, t)));

fun is_f (Const (\<^const_syntax>\<open>case_prod\<close>, _) $ Abs _) = true
  | is_f (Abs _) = true
  | is_f _ = false;


(* assn_tr' & bexp_tr'*)

fun assn_tr' (Const (\<^const_syntax>\<open>Collect\<close>, _) $ T) = dest_abstuple T
  | assn_tr' (Const (\<^const_syntax>\<open>inter\<close>, _) $
        (Const (\<^const_syntax>\<open>Collect\<close>, _) $ T1) $ (Const (\<^const_syntax>\<open>Collect\<close>, _) $ T2)) =
      Syntax.const \<^const_syntax>\<open>inter\<close> $ dest_abstuple T1 $ dest_abstuple T2
  | assn_tr' t = t;

fun bexp_tr' (Const (\<^const_syntax>\<open>Collect\<close>, _) $ T) = dest_abstuple T
  | bexp_tr' t = t;

fun var_tr' (Const (\<^const_syntax>\<open>Collect\<close>, _) $ T) = dest_abstuple T
  | var_tr' t = t;


(* com_tr' *)

fun mk_assign f =
  let
    val (vs, ts) = mk_vts f;
    val (ch, which) = find_ch (vs ~~ ts) (length vs - 1) (rev vs);
  in
    if ch
    then Syntax.const \<^syntax_const>\<open>_assign\<close> $ fst which $ snd which
    else Syntax.const \<^const_syntax>\<open>annskip\<close>
  end;

fun com_tr' (Const (\<^const_syntax>\<open>Basic\<close>, _) $ f) =
      if is_f f then mk_assign f
      else Syntax.const \<^const_syntax>\<open>Basic\<close> $ f
  | com_tr' (Const (\<^const_syntax>\<open>Seq\<close>,_) $ c1 $ c2) =
      Syntax.const \<^const_syntax>\<open>Seq\<close> $ com_tr' c1 $ com_tr' c2
  | com_tr' (Const (\<^const_syntax>\<open>Cond\<close>, _) $ b $ c1 $ c2) =
      Syntax.const \<^const_syntax>\<open>Cond\<close> $ bexp_tr' b $ com_tr' c1 $ com_tr' c2
  | com_tr' (Const (\<^const_syntax>\<open>While\<close>, _) $ b $ I $ V $ c) =
      Syntax.const \<^const_syntax>\<open>While\<close> $ bexp_tr' b $ assn_tr' I $ var_tr' V $ com_tr' c
  | com_tr' t = t;

in

fun spec_tr' syn [p, c, q] = Syntax.const syn $ assn_tr' p $ com_tr' c $ assn_tr' q;

end;

end;

