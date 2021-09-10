(*  Title:      HOL/Analysis/normarith.ML
    Author:     Amine Chaieb, University of Cambridge

Simple decision procedure for linear problems in Euclidean space.
*)

signature NORM_ARITH =
sig
 val norm_arith : Proof.context -> conv
 val norm_arith_tac : Proof.context -> int -> tactic
end

structure NormArith : NORM_ARITH =
struct

 open Conv;
 val bool_eq = op = : bool *bool -> bool
  fun dest_ratconst t = case Thm.term_of t of
   Const(\<^const_name>\<open>divide\<close>, _)$a$b => Rat.make(HOLogic.dest_number a |> snd, HOLogic.dest_number b |> snd)
 | Const(\<^const_name>\<open>inverse\<close>, _)$a => Rat.make(1, HOLogic.dest_number a |> snd)
 | _ => Rat.of_int (HOLogic.dest_number (Thm.term_of t) |> snd)
 fun is_ratconst t = can dest_ratconst t
 fun augment_norm b t acc = case Thm.term_of t of
     Const(\<^const_name>\<open>norm\<close>, _) $ _ => insert (eq_pair bool_eq (op aconvc)) (b,Thm.dest_arg t) acc
   | _ => acc
 fun find_normedterms t acc = case Thm.term_of t of
    \<^term>\<open>(+) :: real => _\<close>$_$_ =>
            find_normedterms (Thm.dest_arg1 t) (find_normedterms (Thm.dest_arg t) acc)
      | \<^term>\<open>(*) :: real => _\<close>$_$_ =>
            if not (is_ratconst (Thm.dest_arg1 t)) then acc else
            augment_norm (dest_ratconst (Thm.dest_arg1 t) >= @0)
                      (Thm.dest_arg t) acc
      | _ => augment_norm true t acc

 val cterm_lincomb_neg = FuncUtil.Ctermfunc.map (K ~)
 fun cterm_lincomb_cmul c t =
    if c = @0 then FuncUtil.Ctermfunc.empty else FuncUtil.Ctermfunc.map (fn _ => fn x => x * c) t
 fun cterm_lincomb_add l r = FuncUtil.Ctermfunc.combine (curry op +) (fn x => x = @0) l r
 fun cterm_lincomb_sub l r = cterm_lincomb_add l (cterm_lincomb_neg r)
 fun cterm_lincomb_eq l r = FuncUtil.Ctermfunc.is_empty (cterm_lincomb_sub l r)

(*
 val int_lincomb_neg = FuncUtil.Intfunc.map (K ~)
*)
 fun int_lincomb_cmul c t =
    if c = @0 then FuncUtil.Intfunc.empty else FuncUtil.Intfunc.map (fn _ => fn x => x * c) t
 fun int_lincomb_add l r = FuncUtil.Intfunc.combine (curry op +) (fn x => x = @0) l r
(*
 fun int_lincomb_sub l r = int_lincomb_add l (int_lincomb_neg r)
 fun int_lincomb_eq l r = FuncUtil.Intfunc.is_empty (int_lincomb_sub l r)
*)

fun vector_lincomb t = case Thm.term_of t of
   Const(\<^const_name>\<open>plus\<close>, _) $ _ $ _ =>
    cterm_lincomb_add (vector_lincomb (Thm.dest_arg1 t)) (vector_lincomb (Thm.dest_arg t))
 | Const(\<^const_name>\<open>minus\<close>, _) $ _ $ _ =>
    cterm_lincomb_sub (vector_lincomb (Thm.dest_arg1 t)) (vector_lincomb (Thm.dest_arg t))
 | Const(\<^const_name>\<open>scaleR\<close>, _)$_$_ =>
    cterm_lincomb_cmul (dest_ratconst (Thm.dest_arg1 t)) (vector_lincomb (Thm.dest_arg t))
 | Const(\<^const_name>\<open>uminus\<close>, _)$_ =>
     cterm_lincomb_neg (vector_lincomb (Thm.dest_arg t))
(* FIXME: how should we handle numerals?
 | Const(@ {const_name vec},_)$_ =>
   let
     val b = ((snd o HOLogic.dest_number o term_of o Thm.dest_arg) t = 0
               handle TERM _=> false)
   in if b then FuncUtil.Ctermfunc.onefunc (t,@1)
      else FuncUtil.Ctermfunc.empty
   end
*)
 | _ => FuncUtil.Ctermfunc.onefunc (t,@1)

 fun vector_lincombs ts =
  fold_rev
   (fn t => fn fns => case AList.lookup (op aconvc) fns t of
     NONE =>
       let val f = vector_lincomb t
       in case find_first (fn (_,f') => cterm_lincomb_eq f f') fns of
           SOME (_,f') => (t,f') :: fns
         | NONE => (t,f) :: fns
       end
   | SOME _ => fns) ts []

fun replacenegnorms cv t = case Thm.term_of t of
  \<^term>\<open>(+) :: real => _\<close>$_$_ => binop_conv (replacenegnorms cv) t
| \<^term>\<open>(*) :: real => _\<close>$_$_ =>
    if dest_ratconst (Thm.dest_arg1 t) < @0 then arg_conv cv t else Thm.reflexive t
| _ => Thm.reflexive t
(*
fun flip v eq =
  if FuncUtil.Ctermfunc.defined eq v
  then FuncUtil.Ctermfunc.update (v, ~ (FuncUtil.Ctermfunc.apply eq v)) eq else eq
*)
fun allsubsets s = case s of
  [] => [[]]
|(a::t) => let val res = allsubsets t in
               map (cons a) res @ res end
fun evaluate env lin =
 FuncUtil.Intfunc.fold (fn (x,c) => fn s => s + c * (FuncUtil.Intfunc.apply env x))
   lin @0

fun solve (vs,eqs) = case (vs,eqs) of
  ([],[]) => SOME (FuncUtil.Intfunc.onefunc (0,@1))
 |(_,eq::oeqs) =>
   (case filter (member (op =) vs) (FuncUtil.Intfunc.dom eq) of (*FIXME use find_first here*)
     [] => NONE
    | v::_ =>
       if FuncUtil.Intfunc.defined eq v
       then
        let
         val c = FuncUtil.Intfunc.apply eq v
         val vdef = int_lincomb_cmul (~ (Rat.inv c)) eq
         fun eliminate eqn = if not (FuncUtil.Intfunc.defined eqn v) then eqn
                             else int_lincomb_add (int_lincomb_cmul (FuncUtil.Intfunc.apply eqn v) vdef) eqn
        in (case solve (remove (op =) v vs, map eliminate oeqs) of
            NONE => NONE
          | SOME soln => SOME (FuncUtil.Intfunc.update (v, evaluate soln (FuncUtil.Intfunc.delete_safe v vdef)) soln))
        end
       else NONE)

fun combinations k l = if k = 0 then [[]] else
 case l of
  [] => []
| h::t => map (cons h) (combinations (k - 1) t) @ combinations k t

fun vertices vs eqs =
 let
  fun vertex cmb = case solve(vs,cmb) of
    NONE => NONE
   | SOME soln => SOME (map (fn v => FuncUtil.Intfunc.tryapplyd soln v @0) vs)
  val rawvs = map_filter vertex (combinations (length vs) eqs)
  val unset = filter (forall (fn c => c >= @0)) rawvs
 in fold_rev (insert (eq_list op =)) unset []
 end

val subsumes = eq_list (fn (x, y) => Rat.abs x <= Rat.abs y)

fun subsume todo dun = case todo of
 [] => dun
|v::ovs =>
   let val dun' = if exists (fn w => subsumes (w, v)) dun then dun
                  else v:: filter (fn w => not (subsumes (v, w))) dun
   in subsume ovs dun'
   end;

fun match_mp PQ P = P RS PQ;

fun cterm_of_rat x =
let val (a, b) = Rat.dest x
in
 if b = 1 then Numeral.mk_cnumber \<^ctyp>\<open>real\<close> a
  else Thm.apply (Thm.apply \<^cterm>\<open>(/) :: real => _\<close>
                   (Numeral.mk_cnumber \<^ctyp>\<open>real\<close> a))
        (Numeral.mk_cnumber \<^ctyp>\<open>real\<close> b)
end;

fun norm_cmul_rule c th = Thm.instantiate' [] [SOME (cterm_of_rat c)] (th RS @{thm norm_cmul_rule_thm});

fun norm_add_rule th1 th2 = [th1, th2] MRS @{thm norm_add_rule_thm};

  (* I think here the static context should be sufficient!! *)
fun inequality_canon_rule ctxt =
 let
  (* FIXME : Should be computed statically!! *)
  val real_poly_conv =
    Semiring_Normalizer.semiring_normalize_wrapper ctxt
     (the (Semiring_Normalizer.match ctxt \<^cterm>\<open>(0::real) + 1\<close>))
 in
  fconv_rule (arg_conv ((rewr_conv @{thm ge_iff_diff_ge_0}) then_conv
    arg_conv (Numeral_Simprocs.field_comp_conv ctxt then_conv real_poly_conv)))
end;

 val apply_pth1 = rewr_conv @{thm pth_1};
 val apply_pth2 = rewr_conv @{thm pth_2};
 val apply_pth3 = rewr_conv @{thm pth_3};
 val apply_pth4 = rewrs_conv @{thms pth_4};
 val apply_pth5 = rewr_conv @{thm pth_5};
 val apply_pth6 = rewr_conv @{thm pth_6};
 val apply_pth7 = rewrs_conv @{thms pth_7};
 fun apply_pth8 ctxt =
  rewr_conv @{thm pth_8} then_conv
  arg1_conv (Numeral_Simprocs.field_comp_conv ctxt) then_conv
  (try_conv (rewr_conv (mk_meta_eq @{thm scaleR_zero_left})));
 fun apply_pth9 ctxt =
  rewrs_conv @{thms pth_9} then_conv
  arg1_conv (arg1_conv (Numeral_Simprocs.field_comp_conv ctxt));
 val apply_ptha = rewr_conv @{thm pth_a};
 val apply_pthb = rewrs_conv @{thms pth_b};
 val apply_pthc = rewrs_conv @{thms pth_c};
 val apply_pthd = try_conv (rewr_conv @{thm pth_d});

fun headvector t = case t of
  Const(\<^const_name>\<open>plus\<close>, _)$
   (Const(\<^const_name>\<open>scaleR\<close>, _)$_$v)$_ => v
 | Const(\<^const_name>\<open>scaleR\<close>, _)$_$v => v
 | _ => error "headvector: non-canonical term"

fun vector_cmul_conv ctxt ct =
   ((apply_pth5 then_conv arg1_conv (Numeral_Simprocs.field_comp_conv ctxt)) else_conv
    (apply_pth6 then_conv binop_conv (vector_cmul_conv ctxt))) ct

fun vector_add_conv ctxt ct = apply_pth7 ct
 handle CTERM _ =>
  (apply_pth8 ctxt ct
   handle CTERM _ =>
    (case Thm.term_of ct of
     Const(\<^const_name>\<open>plus\<close>,_)$lt$rt =>
      let
       val l = headvector lt
       val r = headvector rt
      in (case Term_Ord.fast_term_ord (l,r) of
         LESS => (apply_pthb then_conv arg_conv (vector_add_conv ctxt)
                  then_conv apply_pthd) ct
        | GREATER => (apply_pthc then_conv arg_conv (vector_add_conv ctxt)
                     then_conv apply_pthd) ct
        | EQUAL => (apply_pth9 ctxt then_conv
                ((apply_ptha then_conv (vector_add_conv ctxt)) else_conv
              arg_conv (vector_add_conv ctxt) then_conv apply_pthd)) ct)
      end
     | _ => Thm.reflexive ct))

fun vector_canon_conv ctxt ct = case Thm.term_of ct of
 Const(\<^const_name>\<open>plus\<close>,_)$_$_ =>
  let
   val ((p,l),r) = Thm.dest_comb ct |>> Thm.dest_comb
   val lth = vector_canon_conv ctxt l
   val rth = vector_canon_conv ctxt r
   val th = Drule.binop_cong_rule p lth rth
  in fconv_rule (arg_conv (vector_add_conv ctxt)) th end

| Const(\<^const_name>\<open>scaleR\<close>, _)$_$_ =>
  let
   val (p,r) = Thm.dest_comb ct
   val rth = Drule.arg_cong_rule p (vector_canon_conv ctxt r)
  in fconv_rule (arg_conv (apply_pth4 else_conv (vector_cmul_conv ctxt))) rth
  end

| Const(\<^const_name>\<open>minus\<close>,_)$_$_ => (apply_pth2 then_conv (vector_canon_conv ctxt)) ct

| Const(\<^const_name>\<open>uminus\<close>,_)$_ => (apply_pth3 then_conv (vector_canon_conv ctxt)) ct

(* FIXME
| Const(@{const_name vec},_)$n =>
  let val n = Thm.dest_arg ct
  in if is_ratconst n andalso not (dest_ratconst n =/ @0)
     then Thm.reflexive ct else apply_pth1 ct
  end
*)
| _ => apply_pth1 ct

fun norm_canon_conv ctxt ct = case Thm.term_of ct of
  Const(\<^const_name>\<open>norm\<close>,_)$_ => arg_conv (vector_canon_conv ctxt) ct
 | _ => raise CTERM ("norm_canon_conv", [ct])

fun int_flip v eq =
  if FuncUtil.Intfunc.defined eq v
  then FuncUtil.Intfunc.update (v, ~ (FuncUtil.Intfunc.apply eq v)) eq else eq;

local
 val pth_zero = @{thm norm_zero}
 val tv_n =
  (dest_TVar o Thm.typ_of_cterm o Thm.dest_arg o Thm.dest_arg1 o Thm.dest_arg o Thm.cprop_of)
    pth_zero
 val concl = Thm.dest_arg o Thm.cprop_of
 fun real_vector_combo_prover ctxt translator (nubs,ges,gts) =
  let
   (* FIXME: Should be computed statically!!*)
   val real_poly_conv =
      Semiring_Normalizer.semiring_normalize_wrapper ctxt
       (the (Semiring_Normalizer.match ctxt \<^cterm>\<open>(0::real) + 1\<close>))
   val sources = map (Thm.dest_arg o Thm.dest_arg1 o concl) nubs
   val rawdests = fold_rev (find_normedterms o Thm.dest_arg o concl) (ges @ gts) []
   val _ = if not (forall fst rawdests) then error "real_vector_combo_prover: Sanity check"
           else ()
   val dests = distinct (op aconvc) (map snd rawdests)
   val srcfuns = map vector_lincomb sources
   val destfuns = map vector_lincomb dests
   val vvs = fold_rev (union (op aconvc) o FuncUtil.Ctermfunc.dom) (srcfuns @ destfuns) []
   val n = length srcfuns
   val nvs = 1 upto n
   val srccombs = srcfuns ~~ nvs
   fun consider d =
    let
     fun coefficients x =
      let
       val inp =
        if FuncUtil.Ctermfunc.defined d x
        then FuncUtil.Intfunc.onefunc (0, ~ (FuncUtil.Ctermfunc.apply d x))
        else FuncUtil.Intfunc.empty
      in fold_rev (fn (f,v) => fn g => if FuncUtil.Ctermfunc.defined f x then FuncUtil.Intfunc.update (v, FuncUtil.Ctermfunc.apply f x) g else g) srccombs inp
      end
     val equations = map coefficients vvs
     val inequalities = map (fn n => FuncUtil.Intfunc.onefunc (n,@1)) nvs
     fun plausiblevertices f =
      let
       val flippedequations = map (fold_rev int_flip f) equations
       val constraints = flippedequations @ inequalities
       val rawverts = vertices nvs constraints
       fun check_solution v =
        let
          val f = fold_rev FuncUtil.Intfunc.update (nvs ~~ v) (FuncUtil.Intfunc.onefunc (0, @1))
        in forall (fn e => evaluate f e = @0) flippedequations
        end
       val goodverts = filter check_solution rawverts
       val signfixups = map (fn n => if member (op =) f n then ~1 else 1) nvs
      in map (map2 (fn s => fn c => Rat.of_int s * c) signfixups) goodverts
      end
     val allverts = fold_rev append (map plausiblevertices (allsubsets nvs)) []
    in subsume allverts []
    end
   fun compute_ineq v =
    let
     val ths = map_filter (fn (v,t) => if v = @0 then NONE
                                     else SOME(norm_cmul_rule v t))
                            (v ~~ nubs)
     fun end_itlist f xs = split_last xs |> uncurry (fold_rev f)
    in inequality_canon_rule ctxt (end_itlist norm_add_rule ths)
    end
   val ges' = map_filter (try compute_ineq) (fold_rev (append o consider) destfuns []) @
                 map (inequality_canon_rule ctxt) nubs @ ges
   val zerodests = filter
        (fn t => null (FuncUtil.Ctermfunc.dom (vector_lincomb t))) (map snd rawdests)

  in fst (RealArith.real_linear_prover translator
        (map (fn t =>
          Drule.instantiate_normalize (TVars.make [(tv_n, Thm.ctyp_of_cterm t)], Vars.empty) pth_zero)
            zerodests,
        map (fconv_rule (try_conv (Conv.top_sweep_conv (K (norm_canon_conv ctxt)) ctxt) then_conv
                       arg_conv (arg_conv real_poly_conv))) ges',
        map (fconv_rule (try_conv (Conv.top_sweep_conv (K (norm_canon_conv ctxt)) ctxt) then_conv
                       arg_conv (arg_conv real_poly_conv))) gts))
  end
in val real_vector_combo_prover = real_vector_combo_prover
end;

local
 val pth = @{thm norm_imp_pos_and_ge}
 val norm_mp = match_mp pth
 val concl = Thm.dest_arg o Thm.cprop_of
 fun conjunct1 th = th RS @{thm conjunct1}
 fun conjunct2 th = th RS @{thm conjunct2}
fun real_vector_ineq_prover ctxt translator (ges,gts) =
 let
(*   val _ = error "real_vector_ineq_prover: pause" *)
  val ntms = fold_rev find_normedterms (map (Thm.dest_arg o concl) (ges @ gts)) []
  val lctab = vector_lincombs (map snd (filter (not o fst) ntms))
  val (fxns, ctxt') = Variable.variant_fixes (replicate (length lctab) "x") ctxt
  fun instantiate_cterm' ty tms = Drule.cterm_rule (Thm.instantiate' ty tms)
  fun mk_norm t =
    let val T = Thm.typ_of_cterm t
    in Thm.apply (Thm.cterm_of ctxt' (Const (\<^const_name>\<open>norm\<close>, T --> \<^typ>\<open>real\<close>))) t end
  fun mk_equals l r =
    let
      val T = Thm.typ_of_cterm l
      val eq = Thm.cterm_of ctxt (Const (\<^const_name>\<open>Pure.eq\<close>, T --> T --> propT))
    in Thm.apply (Thm.apply eq l) r end
  val asl = map2 (fn (t,_) => fn n => Thm.assume (mk_equals (mk_norm t) (Thm.cterm_of ctxt' (Free(n,\<^typ>\<open>real\<close>))))) lctab fxns
  val replace_conv = try_conv (rewrs_conv asl)
  val replace_rule = fconv_rule (funpow 2 arg_conv (replacenegnorms replace_conv))
  val ges' =
       fold_rev (fn th => fn ths => conjunct1(norm_mp th)::ths)
              asl (map replace_rule ges)
  val gts' = map replace_rule gts
  val nubs = map (conjunct2 o norm_mp) asl
  val th1 = real_vector_combo_prover ctxt' translator (nubs,ges',gts')
  val shs = filter (member (fn (t,th) => t aconvc Thm.cprop_of th) asl) (Thm.chyps_of th1)
  val th11 = hd (Variable.export ctxt' ctxt [fold Thm.implies_intr shs th1])
  val cps = map (swap o Thm.dest_equals) (cprems_of th11)
  val th12 = Drule.instantiate_normalize (TVars.empty, Vars.make (map (apfst (dest_Var o Thm.term_of)) cps)) th11
  val th13 = fold Thm.elim_implies (map (Thm.reflexive o snd) cps) th12;
 in hd (Variable.export ctxt' ctxt [th13])
 end
in val real_vector_ineq_prover = real_vector_ineq_prover
end;

local
 val rawrule = fconv_rule (arg_conv (rewr_conv @{thm real_eq_0_iff_le_ge_0}))
 fun conj_pair th = (th RS @{thm conjunct1}, th RS @{thm conjunct2})
  (* FIXME: Lookup in the context every time!!! Fix this !!!*)
 fun splitequation ctxt th acc =
  let
   val real_poly_neg_conv = #neg
       (Semiring_Normalizer.semiring_normalizers_ord_wrapper ctxt
        (the (Semiring_Normalizer.match ctxt \<^cterm>\<open>(0::real) + 1\<close>)) Thm.term_ord)
   val (th1,th2) = conj_pair(rawrule th)
  in th1::fconv_rule (arg_conv (arg_conv (real_poly_neg_conv ctxt))) th2::acc
  end
in fun real_vector_prover ctxt _ translator (eqs,ges,gts) =
     (real_vector_ineq_prover ctxt translator
         (fold_rev (splitequation ctxt) eqs ges,gts), RealArith.Trivial)
end;

  fun init_conv ctxt =
   Simplifier.rewrite (put_simpset HOL_basic_ss ctxt
    addsimps ([(*@{thm vec_0}, @{thm vec_1},*) @{thm dist_norm}, @{thm right_minus},
      @{thm diff_self}, @{thm norm_zero}] @ @{thms arithmetic_simps} @ @{thms norm_pths}))
   then_conv Numeral_Simprocs.field_comp_conv ctxt
   then_conv nnf_conv ctxt

 fun pure ctxt = fst o RealArith.gen_prover_real_arith ctxt (real_vector_prover ctxt);
 fun norm_arith ctxt ct =
  let
   val ctxt' = Variable.declare_term (Thm.term_of ct) ctxt
   val th = init_conv ctxt' ct
  in Thm.equal_elim (Drule.arg_cong_rule \<^cterm>\<open>Trueprop\<close> (Thm.symmetric th))
                (pure ctxt' (Thm.rhs_of th))
 end

 fun norm_arith_tac ctxt =
   clarify_tac (put_claset HOL_cs ctxt) THEN'
   Object_Logic.full_atomize_tac ctxt THEN'
   CSUBGOAL ( fn (p,i) => resolve_tac ctxt [norm_arith ctxt (Thm.dest_arg p )] i);

end;
