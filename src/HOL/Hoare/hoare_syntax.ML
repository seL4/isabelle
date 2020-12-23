(*  Title:      HOL/Hoare/hoare_syntax.ML
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Author:     Walter Guttmann (extension to total-correctness proofs)

Syntax translations for Hoare logic.
*)

signature HOARE_SYNTAX =
sig
  val hoare_vars_tr: Proof.context -> term list -> term
  val hoare_tc_vars_tr: Proof.context -> term list -> term
  val spec_tr': string -> Proof.context -> term list -> term
  val setup:
    {Basic: string, Skip: string, Seq: string, Cond: string, While: string,
      Valid: string, ValidTC: string} -> theory -> theory
end;

structure Hoare_Syntax: HOARE_SYNTAX =
struct

(** theory data **)

structure Data = Theory_Data
(
  type T =
    {Basic: string, Skip: string, Seq: string, Cond: string, While: string,
      Valid: string, ValidTC: string} option;
  val empty: T = NONE;
  val extend = I;
  fun merge (data1, data2) =
    if is_some data1 andalso is_some data2 andalso data1 <> data2 then
      error "Cannot merge syntax from different Hoare Logics"
    else merge_options (data1, data2);
);

fun const_syntax ctxt which =
  (case Data.get (Proof_Context.theory_of ctxt) of
    SOME consts => which consts
  | NONE => error "Undefined Hoare syntax consts");

val syntax_const = Syntax.const oo const_syntax;



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

fun com_tr ctxt =
  let
    fun tr (Const (\<^syntax_const>\<open>_assign\<close>, _) $ x $ e) xs =
          syntax_const ctxt #Basic $ mk_fexp x e xs
      | tr (Const (\<^syntax_const>\<open>_Seq\<close>,_) $ c1 $ c2) xs =
          syntax_const ctxt #Seq $ tr c1 xs $ tr c2 xs
      | tr (Const (\<^syntax_const>\<open>_Cond\<close>,_) $ b $ c1 $ c2) xs =
          syntax_const ctxt #Cond $ bexp_tr b xs $ tr c1 xs $ tr c2 xs
      | tr (Const (\<^syntax_const>\<open>_While\<close>,_) $ b $ I $ V $ c) xs =
          syntax_const ctxt #While $ bexp_tr b xs $ assn_tr I xs $ var_tr V xs $ tr c xs
      | tr t _ = t;
  in tr end;

fun vars_tr (Const (\<^syntax_const>\<open>_idts\<close>, _) $ idt $ vars) = idt :: vars_tr vars
  | vars_tr t = [t];

in

fun hoare_vars_tr ctxt [vars, pre, prg, post] =
      let val xs = vars_tr vars
      in syntax_const ctxt #Valid $ assn_tr pre xs $ com_tr ctxt prg xs $ assn_tr post xs end
  | hoare_vars_tr _ ts = raise TERM ("hoare_vars_tr", ts);

fun hoare_tc_vars_tr ctxt [vars, pre, prg, post] =
      let val xs = vars_tr vars
      in syntax_const ctxt #ValidTC $ assn_tr pre xs $ com_tr ctxt prg xs $ assn_tr post xs end
  | hoare_tc_vars_tr _ ts = raise TERM ("hoare_tc_vars_tr", ts);

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

fun mk_assign ctxt f =
  let
    val (vs, ts) = mk_vts f;
    val (ch, (a, b)) = find_ch (vs ~~ ts) (length vs - 1) (rev vs);
  in
    if ch
    then Syntax.const \<^syntax_const>\<open>_assign\<close> $ a $ b
    else syntax_const ctxt #Skip
  end;

fun com_tr' ctxt t =
  let
    val (head, args) = apfst (try (#1 o Term.dest_Const)) (Term.strip_comb t);
    fun arg k = nth args (k - 1);
    val n = length args;
  in
    (case head of
      NONE => t
    | SOME c =>
        if c = const_syntax ctxt #Basic andalso n = 1 andalso is_f (arg 1) then
          mk_assign ctxt (arg 1)
        else if c = const_syntax ctxt #Seq andalso n = 2 then
          Syntax.const \<^syntax_const>\<open>_Seq\<close> $ com_tr' ctxt (arg 1) $ com_tr' ctxt (arg 2)
        else if c = const_syntax ctxt #Cond andalso n = 3 then
          Syntax.const \<^syntax_const>\<open>_Cond\<close> $
            bexp_tr' (arg 1) $ com_tr' ctxt (arg 2) $ com_tr' ctxt (arg 3)
        else if c = const_syntax ctxt #While andalso n = 4 then
          Syntax.const \<^syntax_const>\<open>_While\<close> $
            bexp_tr' (arg 1) $ assn_tr' (arg 2) $ var_tr' (arg 3) $ com_tr' ctxt (arg 4)
        else t)
  end;

in

fun spec_tr' syn ctxt [p, c, q] =
  Syntax.const syn $ assn_tr' p $ com_tr' ctxt c $ assn_tr' q;

end;


(** setup **)

fun setup consts =
  Data.put (SOME consts) #>
  Sign.parse_translation
   [(\<^syntax_const>\<open>_hoare_vars\<close>, hoare_vars_tr),
    (\<^syntax_const>\<open>_hoare_vars_tc\<close>, hoare_tc_vars_tr)] #>
  Sign.print_translation
   [(#Valid consts, spec_tr' \<^syntax_const>\<open>_hoare\<close>),
    (#ValidTC consts, spec_tr' \<^syntax_const>\<open>_hoare_tc\<close>)];

end;
