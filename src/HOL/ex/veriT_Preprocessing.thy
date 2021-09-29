(*  Title:      HOL/ex/veriT_Preprocessing.thy
    Author:     Jasmin Christian Blanchette, Inria, LORIA, MPII
*)

section \<open>Proof Reconstruction for veriT's Preprocessing\<close>

theory veriT_Preprocessing
imports Main
begin

declare [[eta_contract = false]]

lemma
  some_All_iffI: "p (SOME x. \<not> p x) = q \<Longrightarrow> (\<forall>x. p x) = q" and
  some_Ex_iffI: "p (SOME x. p x) = q \<Longrightarrow> (\<exists>x. p x) = q"
  by (metis (full_types) someI_ex)+

ML \<open>
fun mk_prod1 bound_Ts (t, u) =
  HOLogic.pair_const (fastype_of1 (bound_Ts, t)) (fastype_of1 (bound_Ts, u)) $ t $ u;

fun mk_tuple1 bound_Ts = the_default HOLogic.unit o try (foldr1 (mk_prod1 bound_Ts));

fun mk_arg_congN 0 = refl
  | mk_arg_congN 1 = arg_cong
  | mk_arg_congN 2 = @{thm arg_cong2}
  | mk_arg_congN n = arg_cong RS funpow (n - 2) (fn th => @{thm cong} RS th) @{thm cong};

fun mk_let_iffNI ctxt n =
  let
    val ((As, [B]), _) = ctxt
      |> Ctr_Sugar_Util.mk_TFrees n
      ||>> Ctr_Sugar_Util.mk_TFrees 1;

    val ((((ts, us), [p]), [q]), _) = ctxt
      |> Ctr_Sugar_Util.mk_Frees "t" As
      ||>> Ctr_Sugar_Util.mk_Frees "u" As
      ||>> Ctr_Sugar_Util.mk_Frees "p" [As ---> B]
      ||>> Ctr_Sugar_Util.mk_Frees "q" [B];

    val tuple_t = HOLogic.mk_tuple ts;
    val tuple_T = fastype_of tuple_t;

    val lambda_t = HOLogic.tupled_lambda tuple_t (list_comb (p, ts));

    val left_prems = map2 (curry Ctr_Sugar_Util.mk_Trueprop_eq) ts us;
    val right_prem = Ctr_Sugar_Util.mk_Trueprop_eq (list_comb (p, us), q);
    val concl = Ctr_Sugar_Util.mk_Trueprop_eq (\<^Const>\<open>Let tuple_T B for tuple_t lambda_t\<close>, q);

    val goal = Logic.list_implies (left_prems @ [right_prem], concl);
    val vars = Variable.add_free_names ctxt goal [];
  in
    Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, ...} =>
      HEADGOAL (hyp_subst_tac ctxt) THEN
      Local_Defs.unfold0_tac ctxt @{thms Let_def prod.case} THEN
      HEADGOAL (resolve_tac ctxt [refl]))
  end;

datatype rule_name =
  Refl
| Taut of thm
| Trans of term
| Cong
| Bind
| Sko_Ex
| Sko_All
| Let of term list;

fun str_of_rule_name Refl = "Refl"
  | str_of_rule_name (Taut th) = "Taut[" ^ \<^make_string> th ^ "]"
  | str_of_rule_name (Trans t) = "Trans[" ^ Syntax.string_of_term \<^context> t ^ "]"
  | str_of_rule_name Cong = "Cong"
  | str_of_rule_name Bind = "Bind"
  | str_of_rule_name Sko_Ex = "Sko_Ex"
  | str_of_rule_name Sko_All = "Sko_All"
  | str_of_rule_name (Let ts) =
    "Let[" ^ commas (map (Syntax.string_of_term \<^context>) ts) ^ "]";

datatype node = N of rule_name * node list;

fun lambda_count (Abs (_, _, t)) = lambda_count t + 1
  | lambda_count ((t as Abs _) $ _) = lambda_count t - 1
  | lambda_count ((t as \<^Const_>\<open>case_prod _ _ _\<close> $ _) $ _) = lambda_count t - 1
  | lambda_count \<^Const_>\<open>case_prod _ _ _ for t\<close> = lambda_count t - 1
  | lambda_count _ = 0;

fun zoom apply =
  let
    fun zo 0 bound_Ts (Abs (r, T, t), Abs (s, U, u)) =
        let val (t', u') = zo 0 (T :: bound_Ts) (t, u) in
          (lambda (Free (r, T)) t', lambda (Free (s, U)) u')
        end
      | zo 0 bound_Ts ((t as Abs (_, T, _)) $ arg, u) =
        let val (t', u') = zo 1 (T :: bound_Ts) (t, u) in
          (t' $ arg, u')
        end
      | zo 0 bound_Ts ((t as \<^Const_>\<open>case_prod _ _ _\<close> $ _) $ arg, u) =
        let val (t', u') = zo 1 bound_Ts (t, u) in
          (t' $ arg, u')
        end
      | zo 0 bound_Ts tu = apply bound_Ts tu
      | zo n bound_Ts (\<^Const_>\<open>case_prod A B _ for t\<close>, u) =
        let
          val (t', u') = zo (n + 1) bound_Ts (t, u);
          val C = range_type (range_type (fastype_of t'));
        in (\<^Const>\<open>case_prod A B C for t'\<close>, u') end
      | zo n bound_Ts (Abs (s, T, t), u) =
        let val (t', u') = zo (n - 1) (T :: bound_Ts) (t, u) in
          (Abs (s, T, t'), u')
        end
      | zo _ _ (t, u) = raise TERM ("zoom", [t, u]);
  in
    zo 0 []
  end;

fun apply_Trans_left t (lhs, _) = (lhs, t);
fun apply_Trans_right t (_, rhs) = (t, rhs);

fun apply_Cong ary j (lhs, rhs) =
  (case apply2 strip_comb (lhs, rhs) of
    ((c, ts), (d, us)) =>
    if c aconv d andalso length ts = ary andalso length us = ary then (nth ts j, nth us j)
    else raise TERM ("apply_Cong", [lhs, rhs]));

fun apply_Bind (lhs, rhs) =
  (case (lhs, rhs) of
    (\<^Const_>\<open>All _ for \<open>Abs (_, T, t)\<close>\<close>, \<^Const_>\<open>All _ for \<open>Abs (s, U, u)\<close>\<close>) =>
    (Abs (s, T, t), Abs (s, U, u))
  | (\<^Const_>\<open>Ex _ for t\<close>, \<^Const_>\<open>Ex _ for u\<close>) => (t, u)
  | _ => raise TERM ("apply_Bind", [lhs, rhs]));

fun apply_Sko_Ex (lhs, rhs) =
  (case lhs of
    \<^Const_>\<open>Ex _ for \<open>t as Abs (_, T, _)\<close>\<close> =>
    (t $ (HOLogic.choice_const T $ t), rhs)
  | _ => raise TERM ("apply_Sko_Ex", [lhs]));

fun apply_Sko_All (lhs, rhs) =
  (case lhs of
    \<^Const_>\<open>All _ for \<open>t as Abs (s, T, body)\<close>\<close> =>
    (t $ (HOLogic.choice_const T $ Abs (s, T, HOLogic.mk_not body)), rhs)
  | _ => raise TERM ("apply_Sko_All", [lhs]));

fun apply_Let_left ts j (lhs, _) =
  (case lhs of
    \<^Const_>\<open>Let _ _ for t _\<close> =>
    let val ts0 = HOLogic.strip_tuple t in
      (nth ts0 j, nth ts j)
    end
  | _ => raise TERM ("apply_Let_left", [lhs]));

fun apply_Let_right ts bound_Ts (lhs, rhs) =
  let val t' = mk_tuple1 bound_Ts ts in
    (case lhs of
      \<^Const_>\<open>Let _ _ for _ u\<close> => (u $ t', rhs)
    | _ => raise TERM ("apply_Let_right", [lhs, rhs]))
  end;

fun reconstruct_proof ctxt (lrhs as (_, rhs), N (rule_name, prems)) =
  let
    val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq lrhs);
    val ary = length prems;

    val _ = warning (Syntax.string_of_term \<^context> goal);
    val _ = warning (str_of_rule_name rule_name);

    val parents =
      (case (rule_name, prems) of
        (Refl, []) => []
      | (Taut _, []) => []
      | (Trans t, [left_prem, right_prem]) =>
        [reconstruct_proof ctxt (zoom (K (apply_Trans_left t)) lrhs, left_prem),
         reconstruct_proof ctxt (zoom (K (apply_Trans_right t)) (rhs, rhs), right_prem)]
      | (Cong, _) =>
        map_index (fn (j, prem) => reconstruct_proof ctxt (zoom (K (apply_Cong ary j)) lrhs, prem))
          prems
      | (Bind, [prem]) => [reconstruct_proof ctxt (zoom (K apply_Bind) lrhs, prem)]
      | (Sko_Ex, [prem]) => [reconstruct_proof ctxt (zoom (K apply_Sko_Ex) lrhs, prem)]
      | (Sko_All, [prem]) => [reconstruct_proof ctxt (zoom (K apply_Sko_All) lrhs, prem)]
      | (Let ts, prems) =>
        let val (left_prems, right_prem) = split_last prems in
          map2 (fn j => fn prem =>
              reconstruct_proof ctxt (zoom (K (apply_Let_left ts j)) lrhs, prem))
            (0 upto length left_prems - 1) left_prems @
          [reconstruct_proof ctxt (zoom (apply_Let_right ts) lrhs, right_prem)]
        end
      | _ => raise Fail ("Invalid rule: " ^ str_of_rule_name rule_name ^ "/" ^
          string_of_int (length prems)));

    val rule_thms =
      (case rule_name of
        Refl => [refl]
      | Taut th => [th]
      | Trans _ => [trans]
      | Cong => [mk_arg_congN ary]
      | Bind => @{thms arg_cong[of _ _ All] arg_cong[of _ _ Ex]}
      | Sko_Ex => [@{thm some_Ex_iffI}]
      | Sko_All => [@{thm some_All_iffI}]
      | Let ts => [mk_let_iffNI ctxt (length ts)]);

    val num_lams = lambda_count rhs;
    val conged_parents = map (funpow num_lams (fn th => th RS fun_cong)
      #> Local_Defs.unfold0 ctxt @{thms prod.case}) parents;
  in
    Goal.prove_sorry ctxt [] [] goal (fn {context = ctxt, ...} =>
      Local_Defs.unfold0_tac ctxt @{thms prod.case} THEN
      HEADGOAL (REPEAT_DETERM_N num_lams o resolve_tac ctxt [ext] THEN'
      resolve_tac ctxt rule_thms THEN'
      K (Local_Defs.unfold0_tac ctxt @{thms prod.case}) THEN'
      EVERY' (map (resolve_tac ctxt o single) conged_parents)))
  end;
\<close>

ML \<open>
val proof0 =
  ((\<^term>\<open>\<exists>x :: nat. p x\<close>,
    \<^term>\<open>p (SOME x :: nat. p x)\<close>),
   N (Sko_Ex, [N (Refl, [])]));

reconstruct_proof \<^context> proof0;
\<close>

ML \<open>
val proof1 =
  ((\<^term>\<open>\<not> (\<forall>x :: nat. \<exists>y :: nat. p x y)\<close>,
    \<^term>\<open>\<not> (\<exists>y :: nat. p (SOME x :: nat. \<not> (\<exists>y :: nat. p x y)) y)\<close>),
   N (Cong, [N (Sko_All, [N (Bind, [N (Refl, [])])])]));

reconstruct_proof \<^context> proof1;
\<close>

ML \<open>
val proof2 =
  ((\<^term>\<open>\<forall>x :: nat. \<exists>y :: nat. \<exists>z :: nat. p x y z\<close>,
    \<^term>\<open>\<forall>x :: nat. p x (SOME y :: nat. \<exists>z :: nat. p x y z)
        (SOME z :: nat. p x (SOME y :: nat. \<exists>z :: nat. p x y z) z)\<close>),
   N (Bind, [N (Sko_Ex, [N (Sko_Ex, [N (Refl, [])])])]));

reconstruct_proof \<^context> proof2
\<close>

ML \<open>
val proof3 =
  ((\<^term>\<open>\<forall>x :: nat. \<exists>x :: nat. \<exists>x :: nat. p x x x\<close>,
    \<^term>\<open>\<forall>x :: nat. p (SOME x :: nat. p x x x) (SOME x. p x x x) (SOME x. p x x x)\<close>),
   N (Bind, [N (Sko_Ex, [N (Sko_Ex, [N (Refl, [])])])]));

reconstruct_proof \<^context> proof3
\<close>

ML \<open>
val proof4 =
  ((\<^term>\<open>\<forall>x :: nat. \<exists>x :: nat. \<exists>x :: nat. p x x x\<close>,
    \<^term>\<open>\<forall>x :: nat. \<exists>x :: nat. p (SOME x :: nat. p x x x) (SOME x. p x x x) (SOME x. p x x x)\<close>),
   N (Bind, [N (Bind, [N (Sko_Ex, [N (Refl, [])])])]));

reconstruct_proof \<^context> proof4
\<close>

ML \<open>
val proof5 =
  ((\<^term>\<open>\<forall>x :: nat. q \<and> (\<exists>x :: nat. \<exists>x :: nat. p x x x)\<close>,
    \<^term>\<open>\<forall>x :: nat. q \<and>
        (\<exists>x :: nat. p (SOME x :: nat. p x x x) (SOME x. p x x x) (SOME x. p x x x))\<close>),
   N (Bind, [N (Cong, [N (Refl, []), N (Bind, [N (Sko_Ex, [N (Refl, [])])])])]));

reconstruct_proof \<^context> proof5
\<close>

ML \<open>
val proof6 =
  ((\<^term>\<open>\<not> (\<forall>x :: nat. p \<and> (\<exists>x :: nat. \<forall>x :: nat. q x x))\<close>,
    \<^term>\<open>\<not> (\<forall>x :: nat. p \<and>
        (\<exists>x :: nat. q (SOME x :: nat. \<not> q x x) (SOME x. \<not> q x x)))\<close>),
   N (Cong, [N (Bind, [N (Cong, [N (Refl, []), N (Bind, [N (Sko_All, [N (Refl, [])])])])])]));

reconstruct_proof \<^context> proof6
\<close>

ML \<open>
val proof7 =
  ((\<^term>\<open>\<not> \<not> (\<exists>x. p x)\<close>,
    \<^term>\<open>\<not> \<not> p (SOME x. p x)\<close>),
   N (Cong, [N (Cong, [N (Sko_Ex, [N (Refl, [])])])]));

reconstruct_proof \<^context> proof7
\<close>

ML \<open>
val proof8 =
  ((\<^term>\<open>\<not> \<not> (let x = Suc x in x = 0)\<close>,
    \<^term>\<open>\<not> \<not> Suc x = 0\<close>),
   N (Cong, [N (Cong, [N (Let [\<^term>\<open>Suc x\<close>], [N (Refl, []), N (Refl, [])])])]));

reconstruct_proof \<^context> proof8
\<close>

ML \<open>
val proof9 =
  ((\<^term>\<open>\<not> (let x = Suc x in x = 0)\<close>,
    \<^term>\<open>\<not> Suc x = 0\<close>),
   N (Cong, [N (Let [\<^term>\<open>Suc x\<close>], [N (Refl, []), N (Refl, [])])]));

reconstruct_proof \<^context> proof9
\<close>

ML \<open>
val proof10 =
  ((\<^term>\<open>\<exists>x :: nat. p (x + 0)\<close>,
    \<^term>\<open>\<exists>x :: nat. p x\<close>),
   N (Bind, [N (Cong, [N (Taut @{thm add_0_right}, [])])]));

reconstruct_proof \<^context> proof10;
\<close>

ML \<open>
val proof11 =
  ((\<^term>\<open>\<not> (let (x, y) = (Suc y, Suc x) in y = 0)\<close>,
    \<^term>\<open>\<not> Suc x = 0\<close>),
   N (Cong, [N (Let [\<^term>\<open>Suc y\<close>, \<^term>\<open>Suc x\<close>], [N (Refl, []), N (Refl, []),
     N (Refl, [])])]));

reconstruct_proof \<^context> proof11
\<close>

ML \<open>
val proof12 =
  ((\<^term>\<open>\<not> (let (x, y) = (Suc y, Suc x); (u, v, w) = (y, x, y) in w = 0)\<close>,
    \<^term>\<open>\<not> Suc x = 0\<close>),
   N (Cong, [N (Let [\<^term>\<open>Suc y\<close>, \<^term>\<open>Suc x\<close>], [N (Refl, []), N (Refl, []),
     N (Let [\<^term>\<open>Suc x\<close>, \<^term>\<open>Suc y\<close>, \<^term>\<open>Suc x\<close>],
       [N (Refl, []), N (Refl, []), N (Refl, []), N (Refl, [])])])]));

reconstruct_proof \<^context> proof12
\<close>

ML \<open>
val proof13 =
  ((\<^term>\<open>\<not> \<not> (let x = Suc x in x = 0)\<close>,
    \<^term>\<open>\<not> \<not> Suc x = 0\<close>),
   N (Cong, [N (Cong, [N (Let [\<^term>\<open>Suc x\<close>], [N (Refl, []), N (Refl, [])])])]));

reconstruct_proof \<^context> proof13
\<close>

ML \<open>
val proof14 =
  ((\<^term>\<open>let (x, y) = (f (a :: nat), b :: nat) in x > a\<close>,
    \<^term>\<open>f (a :: nat) > a\<close>),
   N (Let [\<^term>\<open>f (a :: nat) :: nat\<close>, \<^term>\<open>b :: nat\<close>],
     [N (Cong, [N (Refl, [])]), N (Refl, []), N (Refl, [])]));

reconstruct_proof \<^context> proof14
\<close>

ML \<open>
val proof15 =
  ((\<^term>\<open>let x = (let y = g (z :: nat) in f (y :: nat)) in x = Suc 0\<close>,
    \<^term>\<open>f (g (z :: nat) :: nat) = Suc 0\<close>),
   N (Let [\<^term>\<open>f (g (z :: nat) :: nat) :: nat\<close>],
     [N (Let [\<^term>\<open>g (z :: nat) :: nat\<close>], [N (Refl, []), N (Refl, [])]), N (Refl, [])]));

reconstruct_proof \<^context> proof15
\<close>

ML \<open>
val proof16 =
  ((\<^term>\<open>a > Suc b\<close>,
    \<^term>\<open>a > Suc b\<close>),
   N (Trans \<^term>\<open>a > Suc b\<close>, [N (Refl, []), N (Refl, [])]));

reconstruct_proof \<^context> proof16
\<close>

thm Suc_1
thm numeral_2_eq_2
thm One_nat_def

ML \<open>
val proof17 =
  ((\<^term>\<open>2 :: nat\<close>,
    \<^term>\<open>Suc (Suc 0) :: nat\<close>),
   N (Trans \<^term>\<open>Suc 1\<close>, [N (Taut @{thm Suc_1[symmetric]}, []), N (Cong,
     [N (Taut @{thm One_nat_def}, [])])]));

reconstruct_proof \<^context> proof17
\<close>

ML \<open>
val proof18 =
  ((\<^term>\<open>let x = a in let y = b in Suc x + y\<close>,
    \<^term>\<open>Suc a + b\<close>),
   N (Trans \<^term>\<open>let y = b in Suc a + y\<close>,
     [N (Let [\<^term>\<open>a :: nat\<close>], [N (Refl, []), N (Refl, [])]),
      N (Let [\<^term>\<open>b :: nat\<close>], [N (Refl, []), N (Refl, [])])]));

reconstruct_proof \<^context> proof18
\<close>

ML \<open>
val proof19 =
  ((\<^term>\<open>\<forall>x. let x = f (x :: nat) :: nat in g x\<close>,
    \<^term>\<open>\<forall>x. g (f (x :: nat) :: nat)\<close>),
   N (Bind, [N (Let [\<^term>\<open>f :: nat \<Rightarrow> nat\<close> $ Bound 0],
     [N (Refl, []), N (Refl, [])])]));

reconstruct_proof \<^context> proof19
\<close>

ML \<open>
val proof20 =
  ((\<^term>\<open>\<forall>x. let y = Suc 0 in let x = f (x :: nat) :: nat in g x\<close>,
    \<^term>\<open>\<forall>x. g (f (x :: nat) :: nat)\<close>),
   N (Bind, [N (Let [\<^term>\<open>Suc 0\<close>], [N (Refl, []), N (Let [\<^term>\<open>f (x :: nat) :: nat\<close>],
     [N (Refl, []), N (Refl, [])])])]));

reconstruct_proof \<^context> proof20
\<close>

ML \<open>
val proof21 =
  ((\<^term>\<open>\<forall>x :: nat. let x = f x :: nat in let y = x in p y\<close>,
    \<^term>\<open>\<forall>z :: nat. p (f z :: nat)\<close>),
   N (Bind, [N (Let [\<^term>\<open>f (z :: nat) :: nat\<close>],
     [N (Refl, []), N (Let [\<^term>\<open>f (z :: nat) :: nat\<close>],
       [N (Refl, []), N (Refl, [])])])]));

reconstruct_proof \<^context> proof21
\<close>

ML \<open>
val proof22 =
  ((\<^term>\<open>\<forall>x :: nat. let x = f x :: nat in let y = x in p y\<close>,
    \<^term>\<open>\<forall>x :: nat. p (f x :: nat)\<close>),
   N (Bind, [N (Let [\<^term>\<open>f (x :: nat) :: nat\<close>],
     [N (Refl, []), N (Let [\<^term>\<open>f (x :: nat) :: nat\<close>],
       [N (Refl, []), N (Refl, [])])])]));

reconstruct_proof \<^context> proof22
\<close>

ML \<open>
val proof23 =
  ((\<^term>\<open>\<forall>x :: nat. let (x, a) = (f x :: nat, 0 ::nat) in let y = x in p y\<close>,
    \<^term>\<open>\<forall>z :: nat. p (f z :: nat)\<close>),
   N (Bind, [N (Let [\<^term>\<open>f (z :: nat) :: nat\<close>, \<^term>\<open>0 :: nat\<close>],
     [N (Refl, []), N (Refl, []), N (Let [\<^term>\<open>f (z :: nat) :: nat\<close>],
       [N (Refl, []), N (Refl, [])])])]));

reconstruct_proof \<^context> proof23
\<close>

ML \<open>
val proof24 =
  ((\<^term>\<open>\<forall>x :: nat. let (x, a) = (f x :: nat, 0 ::nat) in let y = x in p y\<close>,
    \<^term>\<open>\<forall>x :: nat. p (f x :: nat)\<close>),
   N (Bind, [N (Let [\<^term>\<open>f (x :: nat) :: nat\<close>, \<^term>\<open>0 :: nat\<close>],
     [N (Refl, []), N (Refl, []), N (Let [\<^term>\<open>f (x :: nat) :: nat\<close>],
       [N (Refl, []), N (Refl, [])])])]));

reconstruct_proof \<^context> proof24
\<close>

ML \<open>
val proof25 =
  ((\<^term>\<open>let vr0 = vr1 in let vr1 = vr2 in vr0 + vr1 + vr2 :: nat\<close>,
    \<^term>\<open>vr1 + vr2 + vr2 :: nat\<close>),
   N (Trans \<^term>\<open>let vr1a = vr2 in vr1 + vr1a + vr2 :: nat\<close>,
     [N (Let [\<^term>\<open>vr1 :: nat\<close>], [N (Refl, []), N (Refl, [])]),
      N (Let [\<^term>\<open>vr2 :: nat\<close>], [N (Refl, []), N (Refl, [])])]));

reconstruct_proof \<^context> proof25
\<close>

end
