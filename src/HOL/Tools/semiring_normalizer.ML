(*  Title:      HOL/Tools/semiring_normalizer.ML
    Author:     Amine Chaieb, TU Muenchen

Normalization of expressions in semirings.
*)

signature SEMIRING_NORMALIZER =
sig
  type entry
  val match: Proof.context -> cterm -> entry option
  val the_semiring: Proof.context -> thm -> cterm list * thm list
  val the_ring: Proof.context -> thm -> cterm list * thm list
  val the_field: Proof.context -> thm -> cterm list * thm list
  val the_idom: Proof.context -> thm -> thm list
  val the_ideal: Proof.context -> thm -> thm list
  val declare: thm -> {semiring: term list * thm list, ring: term list * thm list,
    field: term list * thm list, idom: thm list, ideal: thm list} ->
    local_theory -> local_theory

  val semiring_normalize_conv: Proof.context -> conv
  val semiring_normalize_ord_conv: Proof.context -> cterm ord -> conv
  val semiring_normalize_wrapper: Proof.context -> entry -> conv
  val semiring_normalize_ord_wrapper: Proof.context -> entry -> cterm ord -> conv
  val semiring_normalizers_conv: cterm list -> cterm list * thm list
    -> cterm list * thm list -> cterm list * thm list ->
      (cterm -> bool) * conv * conv * conv -> cterm ord ->
        {add: Proof.context -> conv,
         mul: Proof.context -> conv,
         neg: Proof.context -> conv,
         main: Proof.context -> conv,
         pow: Proof.context -> conv,
         sub: Proof.context -> conv}
  val semiring_normalizers_ord_wrapper:  Proof.context -> entry -> cterm ord ->
      {add: Proof.context -> conv,
       mul: Proof.context -> conv,
       neg: Proof.context -> conv,
       main: Proof.context -> conv,
       pow: Proof.context -> conv,
       sub: Proof.context -> conv}
end

structure Semiring_Normalizer: SEMIRING_NORMALIZER =
struct

(** data **)

type entry =
 {vars: cterm list,
  semiring: cterm list * thm list,
  ring: cterm list * thm list,
  field: cterm list * thm list,
  idom: thm list,
  ideal: thm list} *
 {is_const: cterm -> bool,
  dest_const: cterm -> Rat.rat,
  mk_const: ctyp -> Rat.rat -> cterm,
  conv: Proof.context -> cterm -> thm};

structure Data = Generic_Data
(
  type T = (thm * entry) list;
  val empty = [];
  val extend = I;
  fun merge data = AList.merge Thm.eq_thm (K true) data;
);

fun the_rules ctxt = fst o the o AList.lookup Thm.eq_thm (Data.get (Context.Proof ctxt))

val the_semiring = #semiring oo the_rules
val the_ring = #ring oo the_rules
val the_field = #field oo the_rules
val the_idom = #idom oo the_rules
val the_ideal = #ideal oo the_rules

fun match ctxt tm =
  let
    fun match_inst
        ({vars, semiring = (sr_ops, sr_rules),
          ring = (r_ops, r_rules), field = (f_ops, f_rules), idom, ideal},
         fns) pat =
       let
        fun h instT =
          let
            val substT = Thm.instantiate (instT, Vars.empty);
            val substT_cterm = Drule.cterm_rule substT;

            val vars' = map substT_cterm vars;
            val semiring' = (map substT_cterm sr_ops, map substT sr_rules);
            val ring' = (map substT_cterm r_ops, map substT r_rules);
            val field' = (map substT_cterm f_ops, map substT f_rules);
            val idom' = map substT idom;
            val ideal' = map substT ideal;

            val result = ({vars = vars', semiring = semiring',
                           ring = ring', field = field', idom = idom', ideal = ideal'}, fns);
          in SOME result end
      in (case try Thm.match (pat, tm) of
           NONE => NONE
         | SOME (instT, _) => h instT)
      end;

    fun match_struct (_,
        entry as ({semiring = (sr_ops, _), ring = (r_ops, _), field = (f_ops, _), ...}, _): entry) =
      get_first (match_inst entry) (sr_ops @ r_ops @ f_ops);
  in get_first match_struct (Data.get (Context.Proof ctxt)) end;


(* extra-logical functions *)

val semiring_norm_ss =
  simpset_of (put_simpset HOL_basic_ss \<^context> addsimps @{thms semiring_norm});

val semiring_funs =
   {is_const = can HOLogic.dest_number o Thm.term_of,
    dest_const = (fn ct =>
      Rat.of_int (snd
        (HOLogic.dest_number (Thm.term_of ct)
          handle TERM _ => error "ring_dest_const"))),
    mk_const = (fn cT => fn x => Numeral.mk_cnumber cT
      (case Rat.dest x of (i, 1) => i | _ => error "int_of_rat: bad int")),
    conv = (fn ctxt =>
      Simplifier.rewrite (put_simpset semiring_norm_ss ctxt)
      then_conv Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps @{thms numeral_One}))};

val divide_const = Thm.cterm_of \<^context> (Logic.varify_global \<^term>\<open>(/)\<close>);
val [divide_tvar] = Term.add_tvars (Thm.term_of divide_const) [];

val field_funs =
  let
    fun numeral_is_const ct =
      case Thm.term_of ct of
       Const (\<^const_name>\<open>Rings.divide\<close>,_) $ a $ b =>
         can HOLogic.dest_number a andalso can HOLogic.dest_number b
     | Const (\<^const_name>\<open>Fields.inverse\<close>,_)$t => can HOLogic.dest_number t
     | t => can HOLogic.dest_number t
    fun dest_const ct = ((case Thm.term_of ct of
       Const (\<^const_name>\<open>Rings.divide\<close>,_) $ a $ b=>
        Rat.make (snd (HOLogic.dest_number a), snd (HOLogic.dest_number b))
     | Const (\<^const_name>\<open>Fields.inverse\<close>,_)$t =>
                   Rat.inv (Rat.of_int (snd (HOLogic.dest_number t)))
     | t => Rat.of_int (snd (HOLogic.dest_number t)))
       handle TERM _ => error "ring_dest_const")
    fun mk_const cT x =
      let val (a, b) = Rat.dest x
      in if b = 1 then Numeral.mk_cnumber cT a
        else Thm.apply
             (Thm.apply
               (Thm.instantiate_cterm (TVars.make [(divide_tvar, cT)], Vars.empty) divide_const)
               (Numeral.mk_cnumber cT a))
             (Numeral.mk_cnumber cT b)
      end
  in
     {is_const = numeral_is_const,
      dest_const = dest_const,
      mk_const = mk_const,
      conv = Numeral_Simprocs.field_comp_conv}
  end;


(* logical content *)

val semiringN = "semiring";
val ringN = "ring";
val fieldN = "field";
val idomN = "idom";

fun declare raw_key
    {semiring = raw_semiring0, ring = raw_ring0, field = raw_field0, idom = raw_idom, ideal = raw_ideal}
    lthy =
  let
    val ctxt' = fold Proof_Context.augment (fst raw_semiring0 @ fst raw_ring0 @ fst raw_field0) lthy;
    val prepare_ops = apfst (Variable.export_terms ctxt' lthy #> map (Thm.cterm_of lthy));
    val raw_semiring = prepare_ops raw_semiring0;
    val raw_ring = prepare_ops raw_ring0;
    val raw_field = prepare_ops raw_field0;
  in
    lthy |> Local_Theory.declaration {syntax = false, pervasive = false} (fn phi => fn context =>
      let
        val ctxt = Context.proof_of context;
        val key = Morphism.thm phi raw_key;
        fun transform_ops_rules (ops, rules) =
          (map (Morphism.cterm phi) ops, Morphism.fact phi rules);
        val (sr_ops, sr_rules) = transform_ops_rules raw_semiring;
        val (r_ops, r_rules) = transform_ops_rules raw_ring;
        val (f_ops, f_rules) = transform_ops_rules raw_field;
        val idom = Morphism.fact phi raw_idom;
        val ideal = Morphism.fact phi raw_ideal;

        fun check kind name xs n =
          null xs orelse length xs = n orelse
          error ("Expected " ^ string_of_int n ^ " " ^ kind ^ " for " ^ name);
        val check_ops = check "operations";
        val check_rules = check "rules";
        val _ =
          check_ops semiringN sr_ops 5 andalso
          check_rules semiringN sr_rules 36 andalso
          check_ops ringN r_ops 2 andalso
          check_rules ringN r_rules 2 andalso
          check_ops fieldN f_ops 2 andalso
          check_rules fieldN f_rules 2 andalso
          check_rules idomN idom 2;

        val mk_meta = Local_Defs.meta_rewrite_rule ctxt;
        val sr_rules' = map mk_meta sr_rules;
        val r_rules' = map mk_meta r_rules;
        val f_rules' = map mk_meta f_rules;

        fun rule i = nth sr_rules' (i - 1);

        val (cx, cy) = Thm.dest_binop (hd sr_ops);
        val cz = rule 34 |> Thm.rhs_of |> Thm.dest_arg |> Thm.dest_arg;
        val cn = rule 36 |> Thm.rhs_of |> Thm.dest_arg |> Thm.dest_arg;
        val ((clx, crx), (cly, cry)) =
          rule 13 |> Thm.rhs_of |> Thm.dest_binop |> apply2 Thm.dest_binop;
        val ((ca, cb), (cc, cd)) =
          rule 20 |> Thm.lhs_of |> Thm.dest_binop |> apply2 Thm.dest_binop;
        val cm = rule 1 |> Thm.rhs_of |> Thm.dest_arg;
        val (cp, cq) = rule 26 |> Thm.lhs_of |> Thm.dest_binop |> apply2 Thm.dest_arg;

        val vars = [ca, cb, cc, cd, cm, cn, cp, cq, cx, cy, cz, clx, crx, cly, cry];

        val semiring = (sr_ops, sr_rules');
        val ring = (r_ops, r_rules');
        val field = (f_ops, f_rules');
        val ideal' = map (Thm.symmetric o mk_meta) ideal
      in
        context
        |> Data.map (AList.update Thm.eq_thm (key,
            ({vars = vars, semiring = semiring, ring = ring, field = field, idom = idom, ideal = ideal'},
              (if null f_ops then semiring_funs else field_funs))))
      end)
  end;


(** auxiliary **)

fun is_comb ct =
  (case Thm.term_of ct of
    _ $ _ => true
  | _ => false);

val concl = Thm.cprop_of #> Thm.dest_arg;

fun is_binop ct ct' =
  (case Thm.term_of ct' of
    c $ _ $ _ => Thm.term_of ct aconv c
  | _ => false);

fun dest_binop ct ct' =
  if is_binop ct ct' then Thm.dest_binop ct'
  else raise CTERM ("dest_binop: bad binop", [ct, ct'])

fun inst_thm inst =
  Thm.instantiate (TVars.empty, Vars.make (map (apfst (dest_Var o Thm.term_of)) inst));

val dest_number = Thm.term_of #> HOLogic.dest_number #> snd;
val is_number = can dest_number;

fun numeral01_conv ctxt =
  Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps [@{thm numeral_One}]);

fun zero1_numeral_conv ctxt =
  Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps [@{thm numeral_One} RS sym]);

fun zerone_conv ctxt cv =
  zero1_numeral_conv ctxt then_conv cv then_conv numeral01_conv ctxt;

val nat_add_ss = simpset_of
  (put_simpset HOL_basic_ss \<^context>
     addsimps @{thms arith_simps} @ @{thms diff_nat_numeral} @ @{thms rel_simps}
       @ @{thms if_False if_True Nat.add_0 add_Suc add_numeral_left Suc_eq_plus1}
       @ map (fn th => th RS sym) @{thms numerals});

fun nat_add_conv ctxt =
  zerone_conv ctxt (Simplifier.rewrite (put_simpset nat_add_ss ctxt));

val zeron_tm = \<^cterm>\<open>0::nat\<close>;
val onen_tm  = \<^cterm>\<open>1::nat\<close>;
val true_tm = \<^cterm>\<open>True\<close>;


(** normalizing conversions **)

(* core conversion *)

fun semiring_normalizers_conv vars (sr_ops, sr_rules) (r_ops, r_rules) (f_ops, f_rules)
  (is_semiring_constant, semiring_add_conv, semiring_mul_conv, semiring_pow_conv) =
let

val [pthm_02, pthm_03, pthm_04, pthm_05, pthm_07, pthm_08,
     pthm_09, pthm_10, pthm_11, pthm_12, pthm_13, pthm_14, pthm_15, pthm_16,
     pthm_17, pthm_18, pthm_19, pthm_21, pthm_22, pthm_23, pthm_24,
     pthm_25, pthm_26, pthm_27, pthm_28, pthm_29, pthm_30, pthm_31, pthm_32,
     pthm_33, pthm_34, pthm_35, pthm_36, pthm_37, pthm_38, _] = sr_rules;

val [ca, cb, cc, cd, cm, cn, cp, cq, cx, cy, cz, clx, crx, cly, cry] = vars;
val [add_pat, mul_pat, pow_pat, zero_tm, one_tm] = sr_ops;
val [add_tm, mul_tm, pow_tm] = map (Thm.dest_fun o Thm.dest_fun) [add_pat, mul_pat, pow_pat];

val dest_add = dest_binop add_tm
val dest_mul = dest_binop mul_tm
fun dest_pow tm =
 let val (l,r) = dest_binop pow_tm tm
 in if is_number r then (l,r) else raise CTERM ("dest_pow",[tm])
 end;
val is_add = is_binop add_tm
val is_mul = is_binop mul_tm

val (neg_mul, sub_add, sub_tm, neg_tm, dest_sub, cx', cy') =
  (case (r_ops, r_rules) of
    ([sub_pat, neg_pat], [neg_mul, sub_add]) =>
      let
        val sub_tm = Thm.dest_fun (Thm.dest_fun sub_pat)
        val neg_tm = Thm.dest_fun neg_pat
        val dest_sub = dest_binop sub_tm
      in (neg_mul, sub_add, sub_tm, neg_tm, dest_sub, neg_mul |> concl |> Thm.dest_arg,
          sub_add |> concl |> Thm.dest_arg |> Thm.dest_arg)
      end
    | _ => (TrueI, TrueI, true_tm, true_tm, (fn t => (t,t)), true_tm, true_tm));

val (divide_inverse, divide_tm, inverse_tm) =
  (case (f_ops, f_rules) of
   ([divide_pat, inverse_pat], [div_inv, _]) =>
     let val div_tm = funpow 2 Thm.dest_fun divide_pat
         val inv_tm = Thm.dest_fun inverse_pat
     in (div_inv, div_tm, inv_tm)
     end
   | _ => (TrueI, true_tm, true_tm));

in fn variable_ord =>
 let

(* Conversion for "x^n * x^m", with either x^n = x and/or x^m = x possible.  *)
(* Also deals with "const * const", but both terms must involve powers of    *)
(* the same variable, or both be constants, or behaviour may be incorrect.   *)

 fun powvar_mul_conv ctxt tm =
  let
  val (l,r) = dest_mul tm
  in if is_semiring_constant l andalso is_semiring_constant r
     then semiring_mul_conv tm
     else
      ((let
         val (lx,ln) = dest_pow l
        in
         ((let val (_, rn) = dest_pow r
               val th1 = inst_thm [(cx,lx),(cp,ln),(cq,rn)] pthm_29
                val (tm1,tm2) = Thm.dest_comb(concl th1) in
               Thm.transitive th1 (Drule.arg_cong_rule tm1 (nat_add_conv ctxt tm2)) end)
           handle CTERM _ =>
            (let val th1 = inst_thm [(cx,lx),(cq,ln)] pthm_31
                 val (tm1,tm2) = Thm.dest_comb(concl th1) in
               Thm.transitive th1 (Drule.arg_cong_rule tm1 (nat_add_conv ctxt tm2)) end)) end)
       handle CTERM _ =>
           ((let val (rx,rn) = dest_pow r
                val th1 = inst_thm [(cx,rx),(cq,rn)] pthm_30
                val (tm1,tm2) = Thm.dest_comb(concl th1) in
               Thm.transitive th1 (Drule.arg_cong_rule tm1 (nat_add_conv ctxt tm2)) end)
           handle CTERM _ => inst_thm [(cx,l)] pthm_32

))
 end;

(* Remove "1 * m" from a monomial, and just leave m.                         *)

 fun monomial_deone th =
       (let val (l,r) = dest_mul(concl th) in
           if l aconvc one_tm
          then Thm.transitive th (inst_thm [(ca,r)] pthm_13)  else th end)
       handle CTERM _ => th;

(* Conversion for "(monomial)^n", where n is a numeral.                      *)

 fun monomial_pow_conv ctxt =
  let
   fun monomial_pow tm bod ntm =
    if not(is_comb bod)
    then Thm.reflexive tm
    else
     if is_semiring_constant bod
     then semiring_pow_conv tm
     else
      let
      val (lopr,r) = Thm.dest_comb bod
      in if not(is_comb lopr)
         then Thm.reflexive tm
        else
          let
          val (opr,l) = Thm.dest_comb lopr
         in
           if opr aconvc pow_tm andalso is_number r
          then
            let val th1 = inst_thm [(cx,l),(cp,r),(cq,ntm)] pthm_34
                val (l,r) = Thm.dest_comb(concl th1)
           in Thm.transitive th1 (Drule.arg_cong_rule l (nat_add_conv ctxt r))
           end
           else
            if opr aconvc mul_tm
            then
             let
              val th1 = inst_thm [(cx,l),(cy,r),(cq,ntm)] pthm_33
             val (xy,z) = Thm.dest_comb(concl th1)
              val (x,y) = Thm.dest_comb xy
              val thl = monomial_pow y l ntm
              val thr = monomial_pow z r ntm
             in Thm.transitive th1 (Thm.combination (Drule.arg_cong_rule x thl) thr)
             end
             else Thm.reflexive tm
          end
      end
  in fn tm =>
   let
    val (lopr,r) = Thm.dest_comb tm
    val (opr,l) = Thm.dest_comb lopr
   in if not (opr aconvc pow_tm) orelse not(is_number r)
      then raise CTERM ("monomial_pow_conv", [tm])
      else if r aconvc zeron_tm
      then inst_thm [(cx,l)] pthm_35
      else if r aconvc onen_tm
      then inst_thm [(cx,l)] pthm_36
      else monomial_deone(monomial_pow tm l r)
   end
  end;

(* Multiplication of canonical monomials.                                    *)
 fun monomial_mul_conv ctxt =
  let
   fun powvar tm =
    if is_semiring_constant tm then one_tm
    else
     ((let val (lopr,r) = Thm.dest_comb tm
           val (opr,l) = Thm.dest_comb lopr
       in if opr aconvc pow_tm andalso is_number r then l
          else raise CTERM ("monomial_mul_conv",[tm]) end)
     handle CTERM _ => tm)   (* FIXME !? *)
   fun  vorder x y =
    if x aconvc y then 0
    else
     if x aconvc one_tm then ~1
     else if y aconvc one_tm then 1
      else if is_less (variable_ord (x, y)) then ~1 else 1
   fun monomial_mul tm l r =
    ((let val (lx,ly) = dest_mul l val vl = powvar lx
      in
      ((let
        val (rx,ry) = dest_mul r
         val vr = powvar rx
         val ord = vorder vl vr
        in
         if ord = 0
        then
          let
             val th1 = inst_thm [(clx,lx),(cly,ly),(crx,rx),(cry,ry)] pthm_15
             val (tm1,tm2) = Thm.dest_comb(concl th1)
             val (tm3,tm4) = Thm.dest_comb tm1
             val th2 = Drule.fun_cong_rule (Drule.arg_cong_rule tm3 (powvar_mul_conv ctxt tm4)) tm2
             val th3 = Thm.transitive th1 th2
              val  (tm5,tm6) = Thm.dest_comb(concl th3)
              val  (tm7,tm8) = Thm.dest_comb tm6
             val  th4 = monomial_mul tm6 (Thm.dest_arg tm7) tm8
         in Thm.transitive th3 (Drule.arg_cong_rule tm5 th4)
         end
         else
          let val th0 = if ord < 0 then pthm_16 else pthm_17
             val th1 = inst_thm [(clx,lx),(cly,ly),(crx,rx),(cry,ry)] th0
             val (tm1,tm2) = Thm.dest_comb(concl th1)
             val (tm3,tm4) = Thm.dest_comb tm2
         in Thm.transitive th1 (Drule.arg_cong_rule tm1 (monomial_mul tm2 (Thm.dest_arg tm3) tm4))
         end
        end)
       handle CTERM _ =>
        (let val vr = powvar r val ord = vorder vl vr
        in
          if ord = 0 then
           let
           val th1 = inst_thm [(clx,lx),(cly,ly),(crx,r)] pthm_18
                 val (tm1,tm2) = Thm.dest_comb(concl th1)
           val (tm3,tm4) = Thm.dest_comb tm1
           val th2 = Drule.fun_cong_rule (Drule.arg_cong_rule tm3 (powvar_mul_conv ctxt tm4)) tm2
          in Thm.transitive th1 th2
          end
          else
          if ord < 0 then
            let val th1 = inst_thm [(clx,lx),(cly,ly),(crx,r)] pthm_19
                val (tm1,tm2) = Thm.dest_comb(concl th1)
                val (tm3,tm4) = Thm.dest_comb tm2
           in Thm.transitive th1 (Drule.arg_cong_rule tm1 (monomial_mul tm2 (Thm.dest_arg tm3) tm4))
           end
           else inst_thm [(ca,l),(cb,r)] pthm_09
        end)) end)
     handle CTERM _ =>
      (let val vl = powvar l in
        ((let
          val (rx,ry) = dest_mul r
          val vr = powvar rx
           val ord = vorder vl vr
         in if ord = 0 then
              let val th1 = inst_thm [(clx,l),(crx,rx),(cry,ry)] pthm_21
                 val (tm1,tm2) = Thm.dest_comb(concl th1)
                 val (tm3,tm4) = Thm.dest_comb tm1
             in Thm.transitive th1 (Drule.fun_cong_rule (Drule.arg_cong_rule tm3 (powvar_mul_conv ctxt tm4)) tm2)
             end
             else if ord > 0 then
                 let val th1 = inst_thm [(clx,l),(crx,rx),(cry,ry)] pthm_22
                     val (tm1,tm2) = Thm.dest_comb(concl th1)
                    val (tm3,tm4) = Thm.dest_comb tm2
                in Thm.transitive th1 (Drule.arg_cong_rule tm1 (monomial_mul tm2 (Thm.dest_arg tm3) tm4))
                end
             else Thm.reflexive tm
         end)
        handle CTERM _ =>
          (let val vr = powvar r
               val  ord = vorder vl vr
          in if ord = 0 then powvar_mul_conv ctxt tm
              else if ord > 0 then inst_thm [(ca,l),(cb,r)] pthm_09
              else Thm.reflexive tm
          end)) end))
  in fn tm => let val (l,r) = dest_mul tm in monomial_deone(monomial_mul tm l r)
             end
  end;
(* Multiplication by monomial of a polynomial.                               *)

 fun polynomial_monomial_mul_conv ctxt =
  let
   fun pmm_conv tm =
    let val (l,r) = dest_mul tm
    in
    ((let val (y,z) = dest_add r
          val th1 = inst_thm [(cx,l),(cy,y),(cz,z)] pthm_37
          val (tm1,tm2) = Thm.dest_comb(concl th1)
          val (tm3,tm4) = Thm.dest_comb tm1
          val th2 =
            Thm.combination (Drule.arg_cong_rule tm3 (monomial_mul_conv ctxt tm4)) (pmm_conv tm2)
      in Thm.transitive th1 th2
      end)
     handle CTERM _ => monomial_mul_conv ctxt tm)
   end
 in pmm_conv
 end;

(* Addition of two monomials identical except for constant multiples.        *)

fun monomial_add_conv tm =
 let val (l,r) = dest_add tm
 in if is_semiring_constant l andalso is_semiring_constant r
    then semiring_add_conv tm
    else
     let val th1 =
           if is_mul l andalso is_semiring_constant(Thm.dest_arg1 l)
           then if is_mul r andalso is_semiring_constant(Thm.dest_arg1 r) then
                    inst_thm [(ca,Thm.dest_arg1 l),(cm,Thm.dest_arg r), (cb,Thm.dest_arg1 r)] pthm_02
                else inst_thm [(ca,Thm.dest_arg1 l),(cm,r)] pthm_03
           else if is_mul r andalso is_semiring_constant(Thm.dest_arg1 r)
           then inst_thm [(cm,l),(ca,Thm.dest_arg1 r)] pthm_04
           else inst_thm [(cm,r)] pthm_05
         val (tm1,tm2) = Thm.dest_comb(concl th1)
         val (tm3,tm4) = Thm.dest_comb tm1
         val th2 = Drule.arg_cong_rule tm3 (semiring_add_conv tm4)
         val th3 = Thm.transitive th1 (Drule.fun_cong_rule th2 tm2)
         val tm5 = concl th3
      in
      if (Thm.dest_arg1 tm5) aconvc zero_tm
      then Thm.transitive th3 (inst_thm [(ca,Thm.dest_arg tm5)] pthm_11)
      else monomial_deone th3
     end
 end;

(* Ordering on monomials.                                                    *)

fun striplist dest =
 let fun strip x acc =
   ((let val (l,r) = dest x in
        strip l (strip r acc) end)
    handle CTERM _ => x::acc)    (* FIXME !? *)
 in fn x => strip x []
 end;


fun powervars tm =
 let val ptms = striplist dest_mul tm
 in if is_semiring_constant (hd ptms) then tl ptms else ptms
 end;
val num_0 = 0;
val num_1 = 1;
fun dest_varpow tm =
 ((let val (x,n) = dest_pow tm in (x,dest_number n) end)
   handle CTERM _ =>
   (tm,(if is_semiring_constant tm then num_0 else num_1)));

val morder =
 let fun lexorder ls =
  case ls of
    ([],[]) => 0
  | (_ ,[]) => ~1
  | ([], _) => 1
  | (((x1,n1)::vs1),((x2,n2)::vs2)) =>
     (case variable_ord (x1, x2) of
       LESS => 1
     | GREATER => ~1
     | EQUAL =>
         if n1 < n2 then ~1
         else if n2 < n1 then 1
         else lexorder (vs1, vs2))
 in fn tm1 => fn tm2 =>
  let val vdegs1 = map dest_varpow (powervars tm1)
      val vdegs2 = map dest_varpow (powervars tm2)
      val deg1 = fold (Integer.add o snd) vdegs1 num_0
      val deg2 = fold (Integer.add o snd) vdegs2 num_0
  in if deg1 < deg2 then ~1 else if deg1 > deg2 then 1
                            else lexorder (vdegs1, vdegs2)
  end
 end;

(* Addition of two polynomials.                                              *)

fun polynomial_add_conv ctxt =
 let
 fun dezero_rule th =
  let
   val tm = concl th
  in
   if not(is_add tm) then th else
   let val (lopr,r) = Thm.dest_comb tm
       val l = Thm.dest_arg lopr
   in
    if l aconvc zero_tm
    then Thm.transitive th (inst_thm [(ca,r)] pthm_07)   else
        if r aconvc zero_tm
        then Thm.transitive th (inst_thm [(ca,l)] pthm_08)  else th
   end
  end
 fun padd tm =
  let
   val (l,r) = dest_add tm
  in
   if l aconvc zero_tm then inst_thm [(ca,r)] pthm_07
   else if r aconvc zero_tm then inst_thm [(ca,l)] pthm_08
   else
    if is_add l
    then
     let val (a,b) = dest_add l
     in
     if is_add r then
      let val (c,d) = dest_add r
          val ord = morder a c
      in
       if ord = 0 then
        let val th1 = inst_thm [(ca,a),(cb,b),(cc,c),(cd,d)] pthm_23
            val (tm1,tm2) = Thm.dest_comb(concl th1)
            val (tm3,tm4) = Thm.dest_comb tm1
            val th2 = Drule.arg_cong_rule tm3 (monomial_add_conv tm4)
        in dezero_rule (Thm.transitive th1 (Thm.combination th2 (padd tm2)))
        end
       else (* ord <> 0*)
        let val th1 =
                if ord > 0 then inst_thm [(ca,a),(cb,b),(cc,r)] pthm_24
                else inst_thm [(ca,l),(cc,c),(cd,d)] pthm_25
            val (tm1,tm2) = Thm.dest_comb(concl th1)
        in dezero_rule (Thm.transitive th1 (Drule.arg_cong_rule tm1 (padd tm2)))
        end
      end
     else (* not (is_add r)*)
      let val ord = morder a r
      in
       if ord = 0 then
        let val th1 = inst_thm [(ca,a),(cb,b),(cc,r)] pthm_26
            val (tm1,tm2) = Thm.dest_comb(concl th1)
            val (tm3,tm4) = Thm.dest_comb tm1
            val th2 = Drule.fun_cong_rule (Drule.arg_cong_rule tm3 (monomial_add_conv tm4)) tm2
        in dezero_rule (Thm.transitive th1 th2)
        end
       else (* ord <> 0*)
        if ord > 0 then
          let val th1 = inst_thm [(ca,a),(cb,b),(cc,r)] pthm_24
              val (tm1,tm2) = Thm.dest_comb(concl th1)
          in dezero_rule (Thm.transitive th1 (Drule.arg_cong_rule tm1 (padd tm2)))
          end
        else dezero_rule (inst_thm [(ca,l),(cc,r)] pthm_27)
      end
    end
   else (* not (is_add l)*)
    if is_add r then
      let val (c,d) = dest_add r
          val  ord = morder l c
      in
       if ord = 0 then
         let val th1 = inst_thm [(ca,l),(cc,c),(cd,d)] pthm_28
             val (tm1,tm2) = Thm.dest_comb(concl th1)
             val (tm3,tm4) = Thm.dest_comb tm1
             val th2 = Drule.fun_cong_rule (Drule.arg_cong_rule tm3 (monomial_add_conv tm4)) tm2
         in dezero_rule (Thm.transitive th1 th2)
         end
       else
        if ord > 0 then Thm.reflexive tm
        else
         let val th1 = inst_thm [(ca,l),(cc,c),(cd,d)] pthm_25
             val (tm1,tm2) = Thm.dest_comb(concl th1)
         in dezero_rule (Thm.transitive th1 (Drule.arg_cong_rule tm1 (padd tm2)))
         end
      end
    else
     let val ord = morder l r
     in
      if ord = 0 then monomial_add_conv tm
      else if ord > 0 then dezero_rule(Thm.reflexive tm)
      else dezero_rule (inst_thm [(ca,l),(cc,r)] pthm_27)
     end
  end
 in padd
 end;

(* Multiplication of two polynomials.                                        *)

fun polynomial_mul_conv ctxt =
 let
  fun pmul tm =
   let val (l,r) = dest_mul tm
   in
    if not(is_add l) then polynomial_monomial_mul_conv ctxt tm
    else
     if not(is_add r) then
      let val th1 = inst_thm [(ca,l),(cb,r)] pthm_09
      in Thm.transitive th1 (polynomial_monomial_mul_conv ctxt (concl th1))
      end
     else
       let val (a,b) = dest_add l
           val th1 = inst_thm [(ca,a),(cb,b),(cc,r)] pthm_10
           val (tm1,tm2) = Thm.dest_comb(concl th1)
           val (tm3,tm4) = Thm.dest_comb tm1
           val th2 = Drule.arg_cong_rule tm3 (polynomial_monomial_mul_conv ctxt tm4)
           val th3 = Thm.transitive th1 (Thm.combination th2 (pmul tm2))
       in Thm.transitive th3 (polynomial_add_conv ctxt (concl th3))
       end
   end
 in fn tm =>
   let val (l,r) = dest_mul tm
   in
    if l aconvc zero_tm then inst_thm [(ca,r)] pthm_11
    else if r aconvc zero_tm then inst_thm [(ca,l)] pthm_12
    else if l aconvc one_tm then inst_thm [(ca,r)] pthm_13
    else if r aconvc one_tm then inst_thm [(ca,l)] pthm_14
    else pmul tm
   end
 end;

(* Power of polynomial (optimized for the monomial and trivial cases).       *)

fun num_conv ctxt n =
  nat_add_conv ctxt (Thm.apply \<^cterm>\<open>Suc\<close> (Numeral.mk_cnumber \<^ctyp>\<open>nat\<close> (dest_number n - 1)))
  |> Thm.symmetric;


fun polynomial_pow_conv ctxt =
 let
  fun ppow tm =
    let val (l,n) = dest_pow tm
    in
     if n aconvc zeron_tm then inst_thm [(cx,l)] pthm_35
     else if n aconvc onen_tm then inst_thm [(cx,l)] pthm_36
     else
         let val th1 = num_conv ctxt n
             val th2 = inst_thm [(cx,l),(cq,Thm.dest_arg (concl th1))] pthm_38
             val (tm1,tm2) = Thm.dest_comb(concl th2)
             val th3 = Thm.transitive th2 (Drule.arg_cong_rule tm1 (ppow tm2))
             val th4 = Thm.transitive (Drule.arg_cong_rule (Thm.dest_fun tm) th1) th3
         in Thm.transitive th4 (polynomial_mul_conv ctxt (concl th4))
         end
    end
 in fn tm =>
       if is_add(Thm.dest_arg1 tm) then ppow tm else monomial_pow_conv ctxt tm
 end;

(* Negation.                                                                 *)

fun polynomial_neg_conv ctxt tm =
   let val (l,r) = Thm.dest_comb tm in
        if not (l aconvc neg_tm) then raise CTERM ("polynomial_neg_conv",[tm]) else
        let val th1 = inst_thm [(cx', r)] neg_mul
            val th2 = Thm.transitive th1 (Conv.arg1_conv semiring_mul_conv (concl th1))
        in Thm.transitive th2 (polynomial_monomial_mul_conv ctxt (concl th2))
        end
   end;


(* Subtraction.                                                              *)
fun polynomial_sub_conv ctxt tm =
  let val (l,r) = dest_sub tm
      val th1 = inst_thm [(cx', l), (cy', r)] sub_add
      val (tm1,tm2) = Thm.dest_comb(concl th1)
      val th2 = Drule.arg_cong_rule tm1 (polynomial_neg_conv ctxt tm2)
  in Thm.transitive th1 (Thm.transitive th2 (polynomial_add_conv ctxt (concl th2)))
  end;

(* Conversion from HOL term.                                                 *)

fun polynomial_conv ctxt tm =
 if is_semiring_constant tm then semiring_add_conv tm
 else if not(is_comb tm) then Thm.reflexive tm
 else
  let val (lopr,r) = Thm.dest_comb tm
  in if lopr aconvc neg_tm then
       let val th1 = Drule.arg_cong_rule lopr (polynomial_conv ctxt r)
       in Thm.transitive th1 (polynomial_neg_conv ctxt (concl th1))
       end
     else if lopr aconvc inverse_tm then
       let val th1 = Drule.arg_cong_rule lopr (polynomial_conv ctxt r)
       in Thm.transitive th1 (semiring_mul_conv (concl th1))
       end
     else
       if not(is_comb lopr) then Thm.reflexive tm
       else
         let val (opr,l) = Thm.dest_comb lopr
         in if opr aconvc pow_tm andalso is_number r
            then
              let val th1 = Drule.fun_cong_rule (Drule.arg_cong_rule opr (polynomial_conv ctxt l)) r
              in Thm.transitive th1 (polynomial_pow_conv ctxt (concl th1))
              end
         else if opr aconvc divide_tm
            then
              let val th1 = Thm.combination (Drule.arg_cong_rule opr (polynomial_conv ctxt l))
                                        (polynomial_conv ctxt r)
                  val th2 = (Conv.rewr_conv divide_inverse then_conv polynomial_mul_conv ctxt)
                              (Thm.rhs_of th1)
              in Thm.transitive th1 th2
              end
            else
              if opr aconvc add_tm orelse opr aconvc mul_tm orelse opr aconvc sub_tm
              then
               let val th1 =
                    Thm.combination
                      (Drule.arg_cong_rule opr (polynomial_conv ctxt l)) (polynomial_conv ctxt r)
                   val f = if opr aconvc add_tm then polynomial_add_conv ctxt
                      else if opr aconvc mul_tm then polynomial_mul_conv ctxt
                      else polynomial_sub_conv ctxt
               in Thm.transitive th1 (f (concl th1))
               end
              else Thm.reflexive tm
         end
  end;
 in
   {main = polynomial_conv,
    add = polynomial_add_conv,
    mul = polynomial_mul_conv,
    pow = polynomial_pow_conv,
    neg = polynomial_neg_conv,
    sub = polynomial_sub_conv}
 end
end;

val nat_exp_ss =
  simpset_of
   (put_simpset HOL_basic_ss \<^context>
    addsimps (@{thms eval_nat_numeral} @ @{thms diff_nat_numeral} @ @{thms arith_simps} @ @{thms rel_simps})
    addsimps [@{thm Let_def}, @{thm if_False}, @{thm if_True}, @{thm Nat.add_0}, @{thm add_Suc}]);


(* various normalizing conversions *)

fun semiring_normalizers_ord_wrapper ctxt ({vars, semiring, ring, field, idom, ideal},
                                     {conv, dest_const, mk_const, is_const}) term_ord =
  let
    val pow_conv =
      Conv.arg_conv (Simplifier.rewrite (put_simpset nat_exp_ss ctxt))
      then_conv Simplifier.rewrite
        (put_simpset HOL_basic_ss ctxt addsimps [nth (snd semiring) 31, nth (snd semiring) 34])
      then_conv conv ctxt
    val dat = (is_const, conv ctxt, conv ctxt, pow_conv)
  in semiring_normalizers_conv vars semiring ring field dat term_ord end;

fun semiring_normalize_ord_wrapper ctxt
  ({vars, semiring, ring, field, idom, ideal}, {conv, dest_const, mk_const, is_const}) term_ord =
 #main (semiring_normalizers_ord_wrapper ctxt
  ({vars = vars, semiring = semiring, ring = ring, field = field, idom = idom, ideal = ideal},
   {conv = conv, dest_const = dest_const, mk_const = mk_const, is_const = is_const}) term_ord) ctxt;

fun semiring_normalize_wrapper ctxt data =
  semiring_normalize_ord_wrapper ctxt data Thm.term_ord;

fun semiring_normalize_ord_conv ctxt ord tm =
  (case match ctxt tm of
    NONE => Thm.reflexive tm
  | SOME res => semiring_normalize_ord_wrapper ctxt res ord tm);

fun semiring_normalize_conv ctxt = semiring_normalize_ord_conv ctxt Thm.term_ord;

end;
