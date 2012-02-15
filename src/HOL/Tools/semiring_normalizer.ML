(*  Title:      HOL/Tools/semiring_normalizer.ML
    Author:     Amine Chaieb, TU Muenchen

Normalization of expressions in semirings.
*)

signature SEMIRING_NORMALIZER = 
sig
  type entry
  val get: Proof.context -> (thm * entry) list
  val match: Proof.context -> cterm -> entry option
  val del: attribute
  val add: {semiring: cterm list * thm list, ring: cterm list * thm list,
    field: cterm list * thm list, idom: thm list, ideal: thm list} -> attribute
  val funs: thm -> {is_const: morphism -> cterm -> bool,
    dest_const: morphism -> cterm -> Rat.rat,
    mk_const: morphism -> ctyp -> Rat.rat -> cterm,
    conv: morphism -> Proof.context -> cterm -> thm} -> declaration
  val semiring_funs: thm -> declaration
  val field_funs: thm -> declaration

  val semiring_normalize_conv: Proof.context -> conv
  val semiring_normalize_ord_conv: Proof.context -> (cterm -> cterm -> bool) -> conv
  val semiring_normalize_wrapper: Proof.context -> entry -> conv
  val semiring_normalize_ord_wrapper: Proof.context -> entry
    -> (cterm -> cterm -> bool) -> conv
  val semiring_normalizers_conv: cterm list -> cterm list * thm list
    -> cterm list * thm list -> cterm list * thm list ->
      (cterm -> bool) * conv * conv * conv -> (cterm -> cterm -> bool) ->
        {add: conv, mul: conv, neg: conv, main: conv, pow: conv, sub: conv}
  val semiring_normalizers_ord_wrapper:  Proof.context -> entry ->
    (cterm -> cterm -> bool) ->
      {add: conv, mul: conv, neg: conv, main: conv, pow: conv, sub: conv}

  val setup: theory -> theory
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

val get = Data.get o Context.Proof;

fun match ctxt tm =
  let
    fun match_inst
        ({vars, semiring = (sr_ops, sr_rules), 
          ring = (r_ops, r_rules), field = (f_ops, f_rules), idom, ideal},
         fns as {is_const, dest_const, mk_const, conv}) pat =
       let
        fun h instT =
          let
            val substT = Thm.instantiate (instT, []);
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
  in get_first match_struct (get ctxt) end;


(* logical content *)

val semiringN = "semiring";
val ringN = "ring";
val idomN = "idom";
val idealN = "ideal";
val fieldN = "field";

val del = Thm.declaration_attribute (Data.map o AList.delete Thm.eq_thm);

fun add {semiring = (sr_ops, sr_rules), ring = (r_ops, r_rules), 
         field = (f_ops, f_rules), idom, ideal} =
  Thm.declaration_attribute (fn key => fn context => context |> Data.map
    let
      val ctxt = Context.proof_of context;

      fun check kind name xs n =
        null xs orelse length xs = n orelse
        error ("Expected " ^ string_of_int n ^ " " ^ kind ^ " for " ^ name);
      val check_ops = check "operations";
      val check_rules = check "rules";

      val _ =
        check_ops semiringN sr_ops 5 andalso
        check_rules semiringN sr_rules 37 andalso
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
        rule 13 |> Thm.rhs_of |> Thm.dest_binop |> pairself Thm.dest_binop;
      val ((ca, cb), (cc, cd)) =
        rule 20 |> Thm.lhs_of |> Thm.dest_binop |> pairself Thm.dest_binop;
      val cm = rule 1 |> Thm.rhs_of |> Thm.dest_arg;
      val (cp, cq) = rule 26 |> Thm.lhs_of |> Thm.dest_binop |> pairself Thm.dest_arg;

      val vars = [ca, cb, cc, cd, cm, cn, cp, cq, cx, cy, cz, clx, crx, cly, cry];
      val semiring = (sr_ops, sr_rules');
      val ring = (r_ops, r_rules');
      val field = (f_ops, f_rules');
      val ideal' = map (Thm.symmetric o mk_meta) ideal
    in
      AList.delete Thm.eq_thm key #>
      cons (key, ({vars = vars, semiring = semiring, 
                          ring = ring, field = field, idom = idom, ideal = ideal'},
             {is_const = undefined, dest_const = undefined, mk_const = undefined,
             conv = undefined}))
    end);


(* extra-logical functions *)

fun funs raw_key {is_const, dest_const, mk_const, conv} phi = 
 Data.map (fn data =>
  let
    val key = Morphism.thm phi raw_key;
    val _ = AList.defined Thm.eq_thm data key orelse
      raise THM ("No data entry for structure key", 0, [key]);
    val fns = {is_const = is_const phi, dest_const = dest_const phi,
      mk_const = mk_const phi, conv = conv phi};
  in AList.map_entry Thm.eq_thm key (apsnd (K fns)) data end);

fun semiring_funs key = funs key
   {is_const = fn phi => can HOLogic.dest_number o Thm.term_of,
    dest_const = fn phi => fn ct =>
      Rat.rat_of_int (snd
        (HOLogic.dest_number (Thm.term_of ct)
          handle TERM _ => error "ring_dest_const")),
    mk_const = fn phi => fn cT => fn x => Numeral.mk_cnumber cT
      (case Rat.quotient_of_rat x of (i, 1) => i | _ => error "int_of_rat: bad int"),
    conv = fn phi => fn _ => Simplifier.rewrite (HOL_basic_ss addsimps @{thms semiring_norm})
      then_conv Simplifier.rewrite (HOL_basic_ss addsimps
        (@{thms numeral_1_eq_1} @ @{thms numeral_0_eq_0} @ @{thms numerals(1-2)}))};

fun field_funs key =
  let
    fun numeral_is_const ct =
      case term_of ct of
       Const (@{const_name Fields.divide},_) $ a $ b =>
         can HOLogic.dest_number a andalso can HOLogic.dest_number b
     | Const (@{const_name Fields.inverse},_)$t => can HOLogic.dest_number t
     | t => can HOLogic.dest_number t
    fun dest_const ct = ((case term_of ct of
       Const (@{const_name Fields.divide},_) $ a $ b=>
        Rat.rat_of_quotient (snd (HOLogic.dest_number a), snd (HOLogic.dest_number b))
     | Const (@{const_name Fields.inverse},_)$t => 
                   Rat.inv (Rat.rat_of_int (snd (HOLogic.dest_number t)))
     | t => Rat.rat_of_int (snd (HOLogic.dest_number t))) 
       handle TERM _ => error "ring_dest_const")
    fun mk_const phi cT x =
      let val (a, b) = Rat.quotient_of_rat x
      in if b = 1 then Numeral.mk_cnumber cT a
        else Thm.apply
             (Thm.apply (Drule.cterm_rule (instantiate' [SOME cT] []) @{cpat "op /"})
                         (Numeral.mk_cnumber cT a))
             (Numeral.mk_cnumber cT b)
      end
  in funs key
     {is_const = K numeral_is_const,
      dest_const = K dest_const,
      mk_const = mk_const,
      conv = K (K Numeral_Simprocs.field_comp_conv)}
  end;



(** auxiliary **)

fun is_comb ct =
  (case Thm.term_of ct of
    _ $ _ => true
  | _ => false);

val concl = Thm.cprop_of #> Thm.dest_arg;

fun is_binop ct ct' =
  (case Thm.term_of ct' of
    c $ _ $ _ => term_of ct aconv c
  | _ => false);

fun dest_binop ct ct' =
  if is_binop ct ct' then Thm.dest_binop ct'
  else raise CTERM ("dest_binop: bad binop", [ct, ct'])

fun inst_thm inst = Thm.instantiate ([], inst);

val dest_numeral = term_of #> HOLogic.dest_number #> snd;
val is_numeral = can dest_numeral;

val numeral01_conv = Simplifier.rewrite
                         (HOL_basic_ss addsimps [@{thm numeral_1_eq_1}, @{thm numeral_0_eq_0}]);
val zero1_numeral_conv = 
 Simplifier.rewrite (HOL_basic_ss addsimps [@{thm numeral_1_eq_1} RS sym, @{thm numeral_0_eq_0} RS sym]);
fun zerone_conv cv = zero1_numeral_conv then_conv cv then_conv numeral01_conv;
val natarith = [@{thm "add_nat_number_of"}, @{thm "diff_nat_number_of"},
                @{thm "mult_nat_number_of"}, @{thm "eq_nat_number_of"}, 
                @{thm "less_nat_number_of"}];

val nat_add_conv = 
 zerone_conv 
  (Simplifier.rewrite 
    (HOL_basic_ss 
       addsimps @{thms arith_simps} @ natarith @ @{thms rel_simps}
             @ [@{thm if_False}, @{thm if_True}, @{thm Nat.add_0}, @{thm add_Suc},
                 @{thm add_number_of_left}, @{thm Suc_eq_plus1}]
             @ map (fn th => th RS sym) @{thms numerals}));

val zeron_tm = @{cterm "0::nat"};
val onen_tm  = @{cterm "1::nat"};
val true_tm = @{cterm "True"};


(** normalizing conversions **)

(* core conversion *)

fun semiring_normalizers_conv vars (sr_ops, sr_rules) (r_ops, r_rules) (f_ops, f_rules)
  (is_semiring_constant, semiring_add_conv, semiring_mul_conv, semiring_pow_conv) =
let

val [pthm_02, pthm_03, pthm_04, pthm_05, pthm_07, pthm_08,
     pthm_09, pthm_10, pthm_11, pthm_12, pthm_13, pthm_14, pthm_15, pthm_16,
     pthm_17, pthm_18, pthm_19, pthm_21, pthm_22, pthm_23, pthm_24,
     pthm_25, pthm_26, pthm_27, pthm_28, pthm_29, pthm_30, pthm_31, pthm_32,
     pthm_33, pthm_34, pthm_35, pthm_36, pthm_37, pthm_38,pthm_39,pthm_40] = sr_rules;

val [ca, cb, cc, cd, cm, cn, cp, cq, cx, cy, cz, clx, crx, cly, cry] = vars;
val [add_pat, mul_pat, pow_pat, zero_tm, one_tm] = sr_ops;
val [add_tm, mul_tm, pow_tm] = map (Thm.dest_fun o Thm.dest_fun) [add_pat, mul_pat, pow_pat];

val dest_add = dest_binop add_tm
val dest_mul = dest_binop mul_tm
fun dest_pow tm =
 let val (l,r) = dest_binop pow_tm tm
 in if is_numeral r then (l,r) else raise CTERM ("dest_pow",[tm])
 end;
val is_add = is_binop add_tm
val is_mul = is_binop mul_tm
fun is_pow tm = is_binop pow_tm tm andalso is_numeral(Thm.dest_arg tm);

val (neg_mul,sub_add,sub_tm,neg_tm,dest_sub,is_sub,cx',cy') =
  (case (r_ops, r_rules) of
    ([sub_pat, neg_pat], [neg_mul, sub_add]) =>
      let
        val sub_tm = Thm.dest_fun (Thm.dest_fun sub_pat)
        val neg_tm = Thm.dest_fun neg_pat
        val dest_sub = dest_binop sub_tm
        val is_sub = is_binop sub_tm
      in (neg_mul,sub_add,sub_tm,neg_tm,dest_sub,is_sub, neg_mul |> concl |> Thm.dest_arg,
          sub_add |> concl |> Thm.dest_arg |> Thm.dest_arg)
      end
    | _ => (TrueI, TrueI, true_tm, true_tm, (fn t => (t,t)), K false, true_tm, true_tm));

val (divide_inverse, inverse_divide, divide_tm, inverse_tm, is_divide) = 
  (case (f_ops, f_rules) of 
   ([divide_pat, inverse_pat], [div_inv, inv_div]) => 
     let val div_tm = funpow 2 Thm.dest_fun divide_pat
         val inv_tm = Thm.dest_fun inverse_pat
     in (div_inv, inv_div, div_tm, inv_tm, is_binop div_tm)
     end
   | _ => (TrueI, TrueI, true_tm, true_tm, K false));

in fn variable_order =>
 let

(* Conversion for "x^n * x^m", with either x^n = x and/or x^m = x possible.  *)
(* Also deals with "const * const", but both terms must involve powers of    *)
(* the same variable, or both be constants, or behaviour may be incorrect.   *)

 fun powvar_mul_conv tm =
  let
  val (l,r) = dest_mul tm
  in if is_semiring_constant l andalso is_semiring_constant r
     then semiring_mul_conv tm
     else
      ((let
         val (lx,ln) = dest_pow l
        in
         ((let val (rx,rn) = dest_pow r
               val th1 = inst_thm [(cx,lx),(cp,ln),(cq,rn)] pthm_29
                val (tm1,tm2) = Thm.dest_comb(concl th1) in
               Thm.transitive th1 (Drule.arg_cong_rule tm1 (nat_add_conv tm2)) end)
           handle CTERM _ =>
            (let val th1 = inst_thm [(cx,lx),(cq,ln)] pthm_31
                 val (tm1,tm2) = Thm.dest_comb(concl th1) in
               Thm.transitive th1 (Drule.arg_cong_rule tm1 (nat_add_conv tm2)) end)) end)
       handle CTERM _ =>
           ((let val (rx,rn) = dest_pow r
                val th1 = inst_thm [(cx,rx),(cq,rn)] pthm_30
                val (tm1,tm2) = Thm.dest_comb(concl th1) in
               Thm.transitive th1 (Drule.arg_cong_rule tm1 (nat_add_conv tm2)) end)
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

 val monomial_pow_conv =
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
           if opr aconvc pow_tm andalso is_numeral r
          then
            let val th1 = inst_thm [(cx,l),(cp,r),(cq,ntm)] pthm_34
                val (l,r) = Thm.dest_comb(concl th1)
           in Thm.transitive th1 (Drule.arg_cong_rule l (nat_add_conv r))
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
   in if not (opr aconvc pow_tm) orelse not(is_numeral r)
      then raise CTERM ("monomial_pow_conv", [tm])
      else if r aconvc zeron_tm
      then inst_thm [(cx,l)] pthm_35
      else if r aconvc onen_tm
      then inst_thm [(cx,l)] pthm_36
      else monomial_deone(monomial_pow tm l r)
   end
  end;

(* Multiplication of canonical monomials.                                    *)
 val monomial_mul_conv =
  let
   fun powvar tm =
    if is_semiring_constant tm then one_tm
    else
     ((let val (lopr,r) = Thm.dest_comb tm
           val (opr,l) = Thm.dest_comb lopr
       in if opr aconvc pow_tm andalso is_numeral r then l 
          else raise CTERM ("monomial_mul_conv",[tm]) end)
     handle CTERM _ => tm)   (* FIXME !? *)
   fun  vorder x y =
    if x aconvc y then 0
    else
     if x aconvc one_tm then ~1
     else if y aconvc one_tm then 1
      else if variable_order x y then ~1 else 1
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
             val th2 = Drule.fun_cong_rule (Drule.arg_cong_rule tm3 (powvar_mul_conv tm4)) tm2
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
           val th2 = Drule.fun_cong_rule (Drule.arg_cong_rule tm3 (powvar_mul_conv tm4)) tm2
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
             in Thm.transitive th1 (Drule.fun_cong_rule (Drule.arg_cong_rule tm3 (powvar_mul_conv tm4)) tm2)
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
          in if ord = 0 then powvar_mul_conv tm
              else if ord > 0 then inst_thm [(ca,l),(cb,r)] pthm_09
              else Thm.reflexive tm
          end)) end))
  in fn tm => let val (l,r) = dest_mul tm in monomial_deone(monomial_mul tm l r)
             end
  end;
(* Multiplication by monomial of a polynomial.                               *)

 val polynomial_monomial_mul_conv =
  let
   fun pmm_conv tm =
    let val (l,r) = dest_mul tm
    in
    ((let val (y,z) = dest_add r
          val th1 = inst_thm [(cx,l),(cy,y),(cz,z)] pthm_37
          val (tm1,tm2) = Thm.dest_comb(concl th1)
          val (tm3,tm4) = Thm.dest_comb tm1
          val th2 = Thm.combination (Drule.arg_cong_rule tm3 (monomial_mul_conv tm4)) (pmm_conv tm2)
      in Thm.transitive th1 th2
      end)
     handle CTERM _ => monomial_mul_conv tm)
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
 ((let val (x,n) = dest_pow tm in (x,dest_numeral n) end)
   handle CTERM _ =>
   (tm,(if is_semiring_constant tm then num_0 else num_1)));

val morder =
 let fun lexorder l1 l2 =
  case (l1,l2) of
    ([],[]) => 0
  | (vps,[]) => ~1
  | ([],vps) => 1
  | (((x1,n1)::vs1),((x2,n2)::vs2)) =>
     if variable_order x1 x2 then 1
     else if variable_order x2 x1 then ~1
     else if n1 < n2 then ~1
     else if n2 < n1 then 1
     else lexorder vs1 vs2
 in fn tm1 => fn tm2 =>
  let val vdegs1 = map dest_varpow (powervars tm1)
      val vdegs2 = map dest_varpow (powervars tm2)
      val deg1 = fold (Integer.add o snd) vdegs1 num_0
      val deg2 = fold (Integer.add o snd) vdegs2 num_0
  in if deg1 < deg2 then ~1 else if deg1 > deg2 then 1
                            else lexorder vdegs1 vdegs2
  end
 end;

(* Addition of two polynomials.                                              *)

val polynomial_add_conv =
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

val polynomial_mul_conv =
 let
  fun pmul tm =
   let val (l,r) = dest_mul tm
   in
    if not(is_add l) then polynomial_monomial_mul_conv tm
    else
     if not(is_add r) then
      let val th1 = inst_thm [(ca,l),(cb,r)] pthm_09
      in Thm.transitive th1 (polynomial_monomial_mul_conv(concl th1))
      end
     else
       let val (a,b) = dest_add l
           val th1 = inst_thm [(ca,a),(cb,b),(cc,r)] pthm_10
           val (tm1,tm2) = Thm.dest_comb(concl th1)
           val (tm3,tm4) = Thm.dest_comb tm1
           val th2 = Drule.arg_cong_rule tm3 (polynomial_monomial_mul_conv tm4)
           val th3 = Thm.transitive th1 (Thm.combination th2 (pmul tm2))
       in Thm.transitive th3 (polynomial_add_conv (concl th3))
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

fun num_conv n =
  nat_add_conv (Thm.apply @{cterm Suc} (Numeral.mk_cnumber @{ctyp nat} (dest_numeral n - 1)))
  |> Thm.symmetric;


val polynomial_pow_conv =
 let
  fun ppow tm =
    let val (l,n) = dest_pow tm
    in
     if n aconvc zeron_tm then inst_thm [(cx,l)] pthm_35
     else if n aconvc onen_tm then inst_thm [(cx,l)] pthm_36
     else
         let val th1 = num_conv n
             val th2 = inst_thm [(cx,l),(cq,Thm.dest_arg (concl th1))] pthm_38
             val (tm1,tm2) = Thm.dest_comb(concl th2)
             val th3 = Thm.transitive th2 (Drule.arg_cong_rule tm1 (ppow tm2))
             val th4 = Thm.transitive (Drule.arg_cong_rule (Thm.dest_fun tm) th1) th3
         in Thm.transitive th4 (polynomial_mul_conv (concl th4))
         end
    end
 in fn tm =>
       if is_add(Thm.dest_arg1 tm) then ppow tm else monomial_pow_conv tm
 end;

(* Negation.                                                                 *)

fun polynomial_neg_conv tm =
   let val (l,r) = Thm.dest_comb tm in
        if not (l aconvc neg_tm) then raise CTERM ("polynomial_neg_conv",[tm]) else
        let val th1 = inst_thm [(cx',r)] neg_mul
            val th2 = Thm.transitive th1 (Conv.arg1_conv semiring_mul_conv (concl th1))
        in Thm.transitive th2 (polynomial_monomial_mul_conv (concl th2))
        end
   end;


(* Subtraction.                                                              *)
fun polynomial_sub_conv tm =
  let val (l,r) = dest_sub tm
      val th1 = inst_thm [(cx',l),(cy',r)] sub_add
      val (tm1,tm2) = Thm.dest_comb(concl th1)
      val th2 = Drule.arg_cong_rule tm1 (polynomial_neg_conv tm2)
  in Thm.transitive th1 (Thm.transitive th2 (polynomial_add_conv (concl th2)))
  end;

(* Conversion from HOL term.                                                 *)

fun polynomial_conv tm =
 if is_semiring_constant tm then semiring_add_conv tm
 else if not(is_comb tm) then Thm.reflexive tm
 else
  let val (lopr,r) = Thm.dest_comb tm
  in if lopr aconvc neg_tm then
       let val th1 = Drule.arg_cong_rule lopr (polynomial_conv r)
       in Thm.transitive th1 (polynomial_neg_conv (concl th1))
       end
     else if lopr aconvc inverse_tm then
       let val th1 = Drule.arg_cong_rule lopr (polynomial_conv r)
       in Thm.transitive th1 (semiring_mul_conv (concl th1))
       end
     else
       if not(is_comb lopr) then Thm.reflexive tm
       else
         let val (opr,l) = Thm.dest_comb lopr
         in if opr aconvc pow_tm andalso is_numeral r
            then
              let val th1 = Drule.fun_cong_rule (Drule.arg_cong_rule opr (polynomial_conv l)) r
              in Thm.transitive th1 (polynomial_pow_conv (concl th1))
              end
         else if opr aconvc divide_tm 
            then
              let val th1 = Thm.combination (Drule.arg_cong_rule opr (polynomial_conv l)) 
                                        (polynomial_conv r)
                  val th2 = (Conv.rewr_conv divide_inverse then_conv polynomial_mul_conv)
                              (Thm.rhs_of th1)
              in Thm.transitive th1 th2
              end
            else
              if opr aconvc add_tm orelse opr aconvc mul_tm orelse opr aconvc sub_tm
              then
               let val th1 =
                    Thm.combination (Drule.arg_cong_rule opr (polynomial_conv l)) (polynomial_conv r)
                   val f = if opr aconvc add_tm then polynomial_add_conv
                      else if opr aconvc mul_tm then polynomial_mul_conv
                      else polynomial_sub_conv
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
  HOL_basic_ss addsimps (@{thms eval_nat_numeral} @ @{thms nat_arith} @ @{thms arith_simps} @ @{thms rel_simps})
    addsimps [@{thm Let_def}, @{thm if_False}, @{thm if_True}, @{thm Nat.add_0}, @{thm add_Suc}];

fun simple_cterm_ord t u = Term_Ord.term_ord (term_of t, term_of u) = LESS;


(* various normalizing conversions *)

fun semiring_normalizers_ord_wrapper ctxt ({vars, semiring, ring, field, idom, ideal}, 
                                     {conv, dest_const, mk_const, is_const}) ord =
  let
    val pow_conv =
      Conv.arg_conv (Simplifier.rewrite nat_exp_ss)
      then_conv Simplifier.rewrite
        (HOL_basic_ss addsimps [nth (snd semiring) 31, nth (snd semiring) 34])
      then_conv conv ctxt
    val dat = (is_const, conv ctxt, conv ctxt, pow_conv)
  in semiring_normalizers_conv vars semiring ring field dat ord end;

fun semiring_normalize_ord_wrapper ctxt ({vars, semiring, ring, field, idom, ideal}, {conv, dest_const, mk_const, is_const}) ord =
 #main (semiring_normalizers_ord_wrapper ctxt ({vars = vars, semiring = semiring, ring = ring, field = field, idom = idom, ideal = ideal},{conv = conv, dest_const = dest_const, mk_const = mk_const, is_const = is_const}) ord);

fun semiring_normalize_wrapper ctxt data = 
  semiring_normalize_ord_wrapper ctxt data simple_cterm_ord;

fun semiring_normalize_ord_conv ctxt ord tm =
  (case match ctxt tm of
    NONE => Thm.reflexive tm
  | SOME res => semiring_normalize_ord_wrapper ctxt res ord tm);
 
fun semiring_normalize_conv ctxt = semiring_normalize_ord_conv ctxt simple_cterm_ord;


(** Isar setup **)

local

fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();
fun keyword2 k1 k2 = Scan.lift (Args.$$$ k1 -- Args.$$$ k2 -- Args.colon) >> K ();
fun keyword3 k1 k2 k3 =
  Scan.lift (Args.$$$ k1 -- Args.$$$ k2 -- Args.$$$ k3 -- Args.colon) >> K ();

val opsN = "ops";
val rulesN = "rules";

val normN = "norm";
val constN = "const";
val delN = "del";

val any_keyword =
  keyword2 semiringN opsN || keyword2 semiringN rulesN ||
  keyword2 ringN opsN || keyword2 ringN rulesN ||
  keyword2 fieldN opsN || keyword2 fieldN rulesN ||
  keyword2 idomN rulesN || keyword2 idealN rulesN;

val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
val terms = thms >> map Drule.dest_term;

fun optional scan = Scan.optional scan [];

in

val setup =
  Attrib.setup @{binding normalizer}
    (Scan.lift (Args.$$$ delN >> K del) ||
      ((keyword2 semiringN opsN |-- terms) --
       (keyword2 semiringN rulesN |-- thms)) --
      (optional (keyword2 ringN opsN |-- terms) --
       optional (keyword2 ringN rulesN |-- thms)) --
      (optional (keyword2 fieldN opsN |-- terms) --
       optional (keyword2 fieldN rulesN |-- thms)) --
      optional (keyword2 idomN rulesN |-- thms) --
      optional (keyword2 idealN rulesN |-- thms)
      >> (fn ((((sr, r), f), id), idl) => 
             add {semiring = sr, ring = r, field = f, idom = id, ideal = idl}))
    "semiring normalizer data";

end;

end;
