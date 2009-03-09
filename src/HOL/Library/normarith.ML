(* A functor for finite mappings based on Tables *)
signature FUNC = 
sig
 type 'a T
 type key
 val apply : 'a T -> key -> 'a
 val applyd :'a T -> (key -> 'a) -> key -> 'a
 val combine : ('a -> 'a -> 'a) -> ('a -> bool) -> 'a T -> 'a T -> 'a T
 val defined : 'a T -> key -> bool
 val dom : 'a T -> key list
 val fold : (key * 'a -> 'b -> 'b) -> 'a T -> 'b -> 'b
 val graph : 'a T -> (key * 'a) list
 val is_undefined : 'a T -> bool
 val mapf : ('a -> 'b) -> 'a T -> 'b T
 val tryapplyd : 'a T -> key -> 'a -> 'a
 val undefine :  key -> 'a T -> 'a T
 val undefined : 'a T
 val update : key * 'a -> 'a T -> 'a T
 val updatep : (key * 'a -> bool) -> key * 'a -> 'a T -> 'a T
 val choose : 'a T -> key * 'a
 val onefunc : key * 'a -> 'a T
 val get_first: (key*'a -> 'a option) -> 'a T -> 'a option
 val fns: 
   {key_ord: key*key -> order,
    apply : 'a T -> key -> 'a,
    applyd :'a T -> (key -> 'a) -> key -> 'a,
    combine : ('a -> 'a -> 'a) -> ('a -> bool) -> 'a T -> 'a T -> 'a T,
    defined : 'a T -> key -> bool,
    dom : 'a T -> key list,
    fold : (key * 'a -> 'b -> 'b) -> 'a T -> 'b -> 'b,
    graph : 'a T -> (key * 'a) list,
    is_undefined : 'a T -> bool,
    mapf : ('a -> 'b) -> 'a T -> 'b T,
    tryapplyd : 'a T -> key -> 'a -> 'a,
    undefine :  key -> 'a T -> 'a T,
    undefined : 'a T,
    update : key * 'a -> 'a T -> 'a T,
    updatep : (key * 'a -> bool) -> key * 'a -> 'a T -> 'a T,
    choose : 'a T -> key * 'a,
    onefunc : key * 'a -> 'a T,
    get_first: (key*'a -> 'a option) -> 'a T -> 'a option}
end;

functor FuncFun(Key: KEY) : FUNC=
struct

type key = Key.key;
structure Tab = TableFun(Key);
type 'a T = 'a Tab.table;

val undefined = Tab.empty;
val is_undefined = Tab.is_empty;
val mapf = Tab.map;
val fold = Tab.fold;
val graph = Tab.dest;
val dom = Tab.keys;
fun applyd f d x = case Tab.lookup f x of 
   SOME y => y
 | NONE => d x;

fun apply f x = applyd f (fn _ => raise Tab.UNDEF x) x;
fun tryapplyd f a d = applyd f (K d) a;
val defined = Tab.defined;
fun undefine x t = (Tab.delete x t handle UNDEF => t);
val update = Tab.update;
fun updatep p (k,v) t = if p (k, v) then t else update (k,v) t
fun combine f z a b = 
 let
  fun h (k,v) t = case Tab.lookup t k of
     NONE => Tab.update (k,v) t
   | SOME v' => let val w = f v v'
     in if z w then Tab.delete k t else Tab.update (k,w) t end;
  in Tab.fold h a b end;

fun choose f = case Tab.max_key f of 
   SOME k => (k,valOf (Tab.lookup f k))
 | NONE => error "FuncFun.choose : Completely undefined function"

fun onefunc kv = update kv undefined

local
fun  find f (k,v) NONE = f (k,v)
   | find f (k,v) r = r
in
fun get_first f t = fold (find f) t NONE
end

val fns = 
   {key_ord = Key.ord,
    apply = apply,
    applyd = applyd,
    combine = combine,
    defined = defined,
    dom = dom,
    fold = fold,
    graph = graph,
    is_undefined = is_undefined,
    mapf = mapf,
    tryapplyd = tryapplyd,
    undefine = undefine,
    undefined = undefined,
    update = update,
    updatep = updatep,
    choose = choose,
    onefunc = onefunc,
    get_first = get_first}

end;

structure Intfunc = FuncFun(type key = int val ord = int_ord);
structure Symfunc = FuncFun(type key = string val ord = fast_string_ord);
structure Termfunc = FuncFun(type key = term val ord = TermOrd.fast_term_ord);
structure Ctermfunc = FuncFun(type key = cterm val ord = (fn (s,t) => TermOrd.fast_term_ord(term_of s, term_of t)));
structure Ratfunc = FuncFun(type key = Rat.rat val ord = Rat.ord);

    (* Some conversions-related stuff which has been forbidden entrance into Pure/conv.ML*)
structure Conv2 = 
struct
 open Conv
fun instantiate_cterm' ty tms = Drule.cterm_rule (Drule.instantiate' ty tms)
fun is_comb t = case (term_of t) of _$_ => true | _ => false;
fun is_abs t = case (term_of t) of Abs _ => true | _ => false;

fun end_itlist f l =
 case l of 
   []     => error "end_itlist"
 | [x]    => x
 | (h::t) => f h (end_itlist f t);

 fun absc cv ct = case term_of ct of 
 Abs (v,_, _) => 
  let val (x,t) = Thm.dest_abs (SOME v) ct
  in Thm.abstract_rule ((fst o dest_Free o term_of) x) x (cv t)
  end
 | _ => all_conv ct;

fun cache_conv conv =
 let 
  val tab = ref Termtab.empty
  fun cconv t =  
    case Termtab.lookup (!tab) (term_of t) of
     SOME th => th
   | NONE => let val th = conv t
             in ((tab := Termtab.insert Thm.eq_thm (term_of t, th) (!tab)); th) end
 in cconv end;
fun is_binop ct ct' = ct aconvc (Thm.dest_fun (Thm.dest_fun ct'))
  handle CTERM _ => false;

local
 fun thenqc conv1 conv2 tm =
   case try conv1 tm of
    SOME th1 => (case try conv2 (Thm.rhs_of th1) of SOME th2 => Thm.transitive th1 th2 | NONE => th1)
  | NONE => conv2 tm

 fun thencqc conv1 conv2 tm =
    let val th1 = conv1 tm 
    in (case try conv2 (Thm.rhs_of th1) of SOME th2 => Thm.transitive th1 th2 | NONE => th1)
    end
 fun comb_qconv conv tm =
   let val (l,r) = Thm.dest_comb tm 
   in (case try conv l of 
        SOME th1 => (case try conv r of SOME th2 => Thm.combination th1 th2 
                                      | NONE => Drule.fun_cong_rule th1 r)
      | NONE => Drule.arg_cong_rule l (conv r))
   end
 fun repeatqc conv tm = thencqc conv (repeatqc conv) tm 
 fun sub_qconv conv tm =  if is_abs tm then absc conv tm else comb_qconv conv tm 
 fun once_depth_qconv conv tm =
      (conv else_conv (sub_qconv (once_depth_qconv conv))) tm
 fun depth_qconv conv tm =
    thenqc (sub_qconv (depth_qconv conv))
           (repeatqc conv) tm
 fun redepth_qconv conv tm =
    thenqc (sub_qconv (redepth_qconv conv))
           (thencqc conv (redepth_qconv conv)) tm
 fun top_depth_qconv conv tm =
    thenqc (repeatqc conv)
           (thencqc (sub_qconv (top_depth_qconv conv))
                    (thencqc conv (top_depth_qconv conv))) tm
 fun top_sweep_qconv conv tm =
    thenqc (repeatqc conv)
           (sub_qconv (top_sweep_qconv conv)) tm
in 
val (once_depth_conv, depth_conv, rdepth_conv, top_depth_conv, top_sweep_conv) = 
  (fn c => try_conv (once_depth_qconv c),
   fn c => try_conv (depth_qconv c),
   fn c => try_conv (redepth_qconv c),
   fn c => try_conv (top_depth_qconv c),
   fn c => try_conv (top_sweep_qconv c));
end;
end;


    (* Some useful derived rules *)
fun deduct_antisym_rule tha thb = 
    equal_intr (implies_intr (cprop_of thb) tha) 
     (implies_intr (cprop_of tha) thb);

fun prove_hyp tha thb = 
  if exists (curry op aconv (concl_of tha)) (#hyps (rep_thm thb)) 
  then equal_elim (symmetric (deduct_antisym_rule tha thb)) tha else thb;



signature REAL_ARITH = 
sig
  datatype positivstellensatz =
   Axiom_eq of int
 | Axiom_le of int
 | Axiom_lt of int
 | Rational_eq of Rat.rat
 | Rational_le of Rat.rat
 | Rational_lt of Rat.rat
 | Square of cterm
 | Eqmul of cterm * positivstellensatz
 | Sum of positivstellensatz * positivstellensatz
 | Product of positivstellensatz * positivstellensatz;

val gen_gen_real_arith :
  Proof.context -> (Rat.rat -> Thm.cterm) * conv * conv * conv * 
   conv * conv * conv * conv * conv * conv * 
    ( (thm list * thm list * thm list -> positivstellensatz -> thm) ->
        thm list * thm list * thm list -> thm) -> conv
val real_linear_prover : 
  (thm list * thm list * thm list -> positivstellensatz -> thm) ->
   thm list * thm list * thm list -> thm

val gen_real_arith : Proof.context ->
   (Rat.rat -> cterm) * conv * conv * conv * conv * conv * conv * conv *
   ( (thm list * thm list * thm list -> positivstellensatz -> thm) ->
       thm list * thm list * thm list -> thm) -> conv
val gen_prover_real_arith : Proof.context ->
   ((thm list * thm list * thm list -> positivstellensatz -> thm) ->
     thm list * thm list * thm list -> thm) -> conv
val real_arith : Proof.context -> conv
end

structure RealArith (* : REAL_ARITH *)=
struct

 open Conv Thm Conv2;;
(* ------------------------------------------------------------------------- *)
(* Data structure for Positivstellensatz refutations.                        *)
(* ------------------------------------------------------------------------- *)

datatype positivstellensatz =
   Axiom_eq of int
 | Axiom_le of int
 | Axiom_lt of int
 | Rational_eq of Rat.rat
 | Rational_le of Rat.rat
 | Rational_lt of Rat.rat
 | Square of cterm
 | Eqmul of cterm * positivstellensatz
 | Sum of positivstellensatz * positivstellensatz
 | Product of positivstellensatz * positivstellensatz;
         (* Theorems used in the procedure *)

fun conjunctions th = case try Conjunction.elim th of
   SOME (th1,th2) => (conjunctions th1) @ conjunctions th2
 | NONE => [th];

val pth = @{lemma "(((x::real) < y) == (y - x > 0)) &&& ((x <= y) == (y - x >= 0)) 
     &&& ((x = y) == (x - y = 0)) &&& ((~(x < y)) == (x - y >= 0)) &&& ((~(x <= y)) == (x - y > 0))
     &&& ((~(x = y)) == (x - y > 0 | -(x - y) > 0))"
  by (atomize (full), auto simp add: less_diff_eq le_diff_eq not_less)} |> 
conjunctions;

val pth_final = @{lemma "(~p ==> False) ==> p" by blast}
val pth_add = 
 @{lemma "(x = (0::real) ==> y = 0 ==> x + y = 0 ) &&& ( x = 0 ==> y >= 0 ==> x + y >= 0) 
    &&& (x = 0 ==> y > 0 ==> x + y > 0) &&& (x >= 0 ==> y = 0 ==> x + y >= 0) 
    &&& (x >= 0 ==> y >= 0 ==> x + y >= 0) &&& (x >= 0 ==> y > 0 ==> x + y > 0) 
    &&& (x > 0 ==> y = 0 ==> x + y > 0) &&& (x > 0 ==> y >= 0 ==> x + y > 0) 
    &&& (x > 0 ==> y > 0 ==> x + y > 0)"  by simp_all} |> conjunctions ;

val pth_mul = 
  @{lemma "(x = (0::real) ==> y = 0 ==> x * y = 0) &&& (x = 0 ==> y >= 0 ==> x * y = 0) &&& 
           (x = 0 ==> y > 0 ==> x * y = 0) &&& (x >= 0 ==> y = 0 ==> x * y = 0) &&& 
           (x >= 0 ==> y >= 0 ==> x * y >= 0 ) &&& ( x >= 0 ==> y > 0 ==> x * y >= 0 ) &&&
           (x > 0 ==>  y = 0 ==> x * y = 0 ) &&& ( x > 0 ==> y >= 0 ==> x * y >= 0 ) &&&
           (x > 0 ==>  y > 0 ==> x * y > 0)"
  by (auto intro: mult_mono[where a="0::real" and b="x" and d="y" and c="0", simplified]
    mult_strict_mono[where b="x" and d="y" and a="0" and c="0", simplified])} |> conjunctions;

val pth_emul = @{lemma "y = (0::real) ==> x * y = 0"  by simp};
val pth_square = @{lemma "x * x >= (0::real)"  by simp};

val weak_dnf_simps = List.take (simp_thms, 34) 
    @ conjunctions @{lemma "((P & (Q | R)) = ((P&Q) | (P&R))) &&& ((Q | R) & P) = ((Q&P) | (R&P)) &&& (P & Q) = (Q & P) &&& ((P | Q) = (Q | P))" by blast+};

val nnfD_simps = conjunctions @{lemma "((~(P & Q)) = (~P | ~Q)) &&& ((~(P | Q)) = (~P & ~Q) ) &&& ((P --> Q) = (~P | Q) ) &&& ((P = Q) = ((P & Q) | (~P & ~ Q))) &&& ((~(P = Q)) = ((P & ~ Q) | (~P & Q)) ) &&& ((~ ~(P)) = P)" by blast+}

val choice_iff = @{lemma "(ALL x. EX y. P x y) = (EX f. ALL x. P x (f x))" by metis};
val prenex_simps = map (fn th => th RS sym) ([@{thm "all_conj_distrib"}, @{thm "ex_disj_distrib"}] @ @{thms "all_simps"(1-4)} @ @{thms "ex_simps"(1-4)});

val real_abs_thms1 = conjunctions @{lemma
  "((-1 * abs(x::real) >= r) = (-1 * x >= r & 1 * x >= r)) &&&
  ((-1 * abs(x) + a >= r) = (a + -1 * x >= r & a + 1 * x >= r)) &&&
  ((a + -1 * abs(x) >= r) = (a + -1 * x >= r & a + 1 * x >= r)) &&&
  ((a + -1 * abs(x) + b >= r) = (a + -1 * x + b >= r & a + 1 * x + b >= r)) &&&
  ((a + b + -1 * abs(x) >= r) = (a + b + -1 * x >= r & a + b + 1 * x >= r)) &&&
  ((a + b + -1 * abs(x) + c >= r) = (a + b + -1 * x + c >= r & a + b + 1 * x + c >= r)) &&&
  ((-1 * max x y >= r) = (-1 * x >= r & -1 * y >= r)) &&&
  ((-1 * max x y + a >= r) = (a + -1 * x >= r & a + -1 * y >= r)) &&&
  ((a + -1 * max x y >= r) = (a + -1 * x >= r & a + -1 * y >= r)) &&&
  ((a + -1 * max x y + b >= r) = (a + -1 * x + b >= r & a + -1 * y  + b >= r)) &&&
  ((a + b + -1 * max x y >= r) = (a + b + -1 * x >= r & a + b + -1 * y >= r)) &&&
  ((a + b + -1 * max x y + c >= r) = (a + b + -1 * x + c >= r & a + b + -1 * y  + c >= r)) &&&
  ((1 * min x y >= r) = (1 * x >= r & 1 * y >= r)) &&&
  ((1 * min x y + a >= r) = (a + 1 * x >= r & a + 1 * y >= r)) &&&
  ((a + 1 * min x y >= r) = (a + 1 * x >= r & a + 1 * y >= r)) &&&
  ((a + 1 * min x y + b >= r) = (a + 1 * x + b >= r & a + 1 * y  + b >= r) )&&&
  ((a + b + 1 * min x y >= r) = (a + b + 1 * x >= r & a + b + 1 * y >= r)) &&&
  ((a + b + 1 * min x y + c >= r) = (a + b + 1 * x + c >= r & a + b + 1 * y  + c >= r)) &&&
  ((min x y >= r) = (x >= r &  y >= r)) &&&
  ((min x y + a >= r) = (a + x >= r & a + y >= r)) &&&
  ((a + min x y >= r) = (a + x >= r & a + y >= r)) &&&
  ((a + min x y + b >= r) = (a + x + b >= r & a + y  + b >= r)) &&&
  ((a + b + min x y >= r) = (a + b + x >= r & a + b + y >= r) )&&&
  ((a + b + min x y + c >= r) = (a + b + x + c >= r & a + b + y + c >= r)) &&&
  ((-1 * abs(x) > r) = (-1 * x > r & 1 * x > r)) &&&
  ((-1 * abs(x) + a > r) = (a + -1 * x > r & a + 1 * x > r)) &&&
  ((a + -1 * abs(x) > r) = (a + -1 * x > r & a + 1 * x > r)) &&&
  ((a + -1 * abs(x) + b > r) = (a + -1 * x + b > r & a + 1 * x + b > r)) &&&
  ((a + b + -1 * abs(x) > r) = (a + b + -1 * x > r & a + b + 1 * x > r)) &&&
  ((a + b + -1 * abs(x) + c > r) = (a + b + -1 * x + c > r & a + b + 1 * x + c > r)) &&&
  ((-1 * max x y > r) = ((-1 * x > r) & -1 * y > r)) &&&
  ((-1 * max x y + a > r) = (a + -1 * x > r & a + -1 * y > r)) &&&
  ((a + -1 * max x y > r) = (a + -1 * x > r & a + -1 * y > r)) &&&
  ((a + -1 * max x y + b > r) = (a + -1 * x + b > r & a + -1 * y  + b > r)) &&&
  ((a + b + -1 * max x y > r) = (a + b + -1 * x > r & a + b + -1 * y > r)) &&&
  ((a + b + -1 * max x y + c > r) = (a + b + -1 * x + c > r & a + b + -1 * y  + c > r)) &&&
  ((min x y > r) = (x > r &  y > r)) &&&
  ((min x y + a > r) = (a + x > r & a + y > r)) &&&
  ((a + min x y > r) = (a + x > r & a + y > r)) &&&
  ((a + min x y + b > r) = (a + x + b > r & a + y  + b > r)) &&&
  ((a + b + min x y > r) = (a + b + x > r & a + b + y > r)) &&&
  ((a + b + min x y + c > r) = (a + b + x + c > r & a + b + y + c > r))"
  by auto};

val abs_split' = @{lemma "P (abs (x::'a::ordered_idom)) == (x >= 0 & P x | x < 0 & P (-x))"
  by (atomize (full)) (auto split add: abs_split)};

val max_split = @{lemma "P (max x y) == ((x::'a::linorder) <= y & P y | x > y & P x)"
  by (atomize (full)) (cases "x <= y", auto simp add: max_def)};

val min_split = @{lemma "P (min x y) == ((x::'a::linorder) <= y & P x | x > y & P y)"
  by (atomize (full)) (cases "x <= y", auto simp add: min_def)};


         (* Miscalineous *)
fun literals_conv bops uops cv = 
 let fun h t =
  case (term_of t) of 
   b$_$_ => if member (op aconv) bops b then binop_conv h t else cv t
 | u$_ => if member (op aconv) uops u then arg_conv h t else cv t
 | _ => cv t
 in h end;

fun cterm_of_rat x = 
let val (a, b) = Rat.quotient_of_rat x
in 
 if b = 1 then Numeral.mk_cnumber @{ctyp "real"} a
  else Thm.capply (Thm.capply @{cterm "op / :: real => _"} 
                   (Numeral.mk_cnumber @{ctyp "real"} a))
        (Numeral.mk_cnumber @{ctyp "real"} b)
end;

  fun dest_ratconst t = case term_of t of
   Const(@{const_name divide}, _)$a$b => Rat.rat_of_quotient(HOLogic.dest_number a |> snd, HOLogic.dest_number b |> snd)
 | _ => Rat.rat_of_int (HOLogic.dest_number (term_of t) |> snd)
 fun is_ratconst t = can dest_ratconst t

fun find_term p t = if p t then t else 
 case t of
  a$b => (find_term p a handle TERM _ => find_term p b)
 | Abs (_,_,t') => find_term p t'
 | _ => raise TERM ("find_term",[t]);

fun find_cterm p t = if p t then t else 
 case term_of t of
  a$b => (find_cterm p (Thm.dest_fun t) handle CTERM _ => find_cterm p (Thm.dest_arg t))
 | Abs (_,_,t') => find_cterm p (Thm.dest_abs NONE t |> snd)
 | _ => raise CTERM ("find_cterm",[t]);


    (* A general real arithmetic prover *)

fun gen_gen_real_arith ctxt (mk_numeric,
       numeric_eq_conv,numeric_ge_conv,numeric_gt_conv,
       poly_conv,poly_neg_conv,poly_add_conv,poly_mul_conv,
       absconv1,absconv2,prover) = 
let
 open Conv Thm; 
 val pre_ss = HOL_basic_ss addsimps simp_thms@ ex_simps@ all_simps@[@{thm not_all},@{thm not_ex},ex_disj_distrib, all_conj_distrib, @{thm if_bool_eq_disj}]
 val prenex_ss = HOL_basic_ss addsimps prenex_simps
 val skolemize_ss = HOL_basic_ss addsimps [choice_iff]
 val presimp_conv = Simplifier.rewrite (Simplifier.context ctxt pre_ss)
 val prenex_conv = Simplifier.rewrite (Simplifier.context ctxt prenex_ss)
 val skolemize_conv = Simplifier.rewrite (Simplifier.context ctxt skolemize_ss)
 val weak_dnf_ss = HOL_basic_ss addsimps weak_dnf_simps
 val weak_dnf_conv = Simplifier.rewrite (Simplifier.context ctxt weak_dnf_ss)
 fun eqT_elim th = equal_elim (symmetric th) @{thm TrueI}
 fun oprconv cv ct = 
  let val g = Thm.dest_fun2 ct
  in if g aconvc @{cterm "op <= :: real => _"} 
       orelse g aconvc @{cterm "op < :: real => _"} 
     then arg_conv cv ct else arg1_conv cv ct
  end

 fun real_ineq_conv th ct =
  let
   val th' = (instantiate (match (lhs_of th, ct)) th 
      handle MATCH => raise CTERM ("real_ineq_conv", [ct]))
  in transitive th' (oprconv poly_conv (Thm.rhs_of th'))
  end 
  val [real_lt_conv, real_le_conv, real_eq_conv,
       real_not_lt_conv, real_not_le_conv, _] =
       map real_ineq_conv pth
  fun match_mp_rule ths ths' = 
   let
     fun f ths ths' = case ths of [] => raise THM("match_mp_rule",0,ths)
      | th::ths => (ths' MRS th handle THM _ => f ths ths')
   in f ths ths' end
  fun mul_rule th th' = fconv_rule (arg_conv (oprconv poly_mul_conv))
         (match_mp_rule pth_mul [th, th'])
  fun add_rule th th' = fconv_rule (arg_conv (oprconv poly_add_conv))
         (match_mp_rule pth_add [th, th'])
  fun emul_rule ct th = fconv_rule (arg_conv (oprconv poly_mul_conv)) 
       (instantiate' [] [SOME ct] (th RS pth_emul)) 
  fun square_rule t = fconv_rule (arg_conv (oprconv poly_mul_conv))
       (instantiate' [] [SOME t] pth_square)

  fun hol_of_positivstellensatz(eqs,les,lts) =
   let 
    fun translate prf = case prf of
        Axiom_eq n => nth eqs n
      | Axiom_le n => nth les n
      | Axiom_lt n => nth lts n
      | Rational_eq x => eqT_elim(numeric_eq_conv(capply @{cterm Trueprop} 
                          (capply (capply @{cterm "op =::real => _"} (mk_numeric x)) 
                               @{cterm "0::real"})))
      | Rational_le x => eqT_elim(numeric_ge_conv(capply @{cterm Trueprop} 
                          (capply (capply @{cterm "op <=::real => _"} 
                                     @{cterm "0::real"}) (mk_numeric x))))
      | Rational_lt x => eqT_elim(numeric_gt_conv(capply @{cterm Trueprop} 
                      (capply (capply @{cterm "op <::real => _"} @{cterm "0::real"})
                        (mk_numeric x))))
      | Square t => square_rule t
      | Eqmul(t,p) => emul_rule t (translate p)
      | Sum(p1,p2) => add_rule (translate p1) (translate p2)
      | Product(p1,p2) => mul_rule (translate p1) (translate p2)
   in fn prf => 
      fconv_rule (first_conv [numeric_ge_conv, numeric_gt_conv, numeric_eq_conv, all_conv]) 
          (translate prf)
   end
  
  val init_conv = presimp_conv then_conv
      nnf_conv then_conv skolemize_conv then_conv prenex_conv then_conv
      weak_dnf_conv

  val concl = dest_arg o cprop_of
  fun is_binop opr ct = (dest_fun2 ct aconvc opr handle CTERM _ => false)
  val is_req = is_binop @{cterm "op =:: real => _"}
  val is_ge = is_binop @{cterm "op <=:: real => _"}
  val is_gt = is_binop @{cterm "op <:: real => _"}
  val is_conj = is_binop @{cterm "op &"}
  val is_disj = is_binop @{cterm "op |"}
  fun conj_pair th = (th RS @{thm conjunct1}, th RS @{thm conjunct2})
  fun disj_cases th th1 th2 = 
   let val (p,q) = dest_binop (concl th)
       val c = concl th1
       val _ = if c aconvc (concl th2) then () else error "disj_cases : conclusions not alpha convertible"
   in implies_elim (implies_elim (implies_elim (instantiate' [] (map SOME [p,q,c]) @{thm disjE}) th) (implies_intr (capply @{cterm Trueprop} p) th1)) (implies_intr (capply @{cterm Trueprop} q) th2)
   end
 fun overall dun ths = case ths of
  [] =>
   let 
    val (eq,ne) = List.partition (is_req o concl) dun
     val (le,nl) = List.partition (is_ge o concl) ne
     val lt = filter (is_gt o concl) nl 
    in prover hol_of_positivstellensatz (eq,le,lt) end
 | th::oths =>
   let 
    val ct = concl th 
   in 
    if is_conj ct  then
     let 
      val (th1,th2) = conj_pair th in
      overall dun (th1::th2::oths) end
    else if is_disj ct then
      let 
       val th1 = overall dun (assume (capply @{cterm Trueprop} (dest_arg1 ct))::oths)
       val th2 = overall dun (assume (capply @{cterm Trueprop} (dest_arg ct))::oths)
      in disj_cases th th1 th2 end
   else overall (th::dun) oths
  end
  fun dest_binary b ct = if is_binop b ct then dest_binop ct 
                         else raise CTERM ("dest_binary",[b,ct])
  val dest_eq = dest_binary @{cterm "op = :: real => _"}
  val neq_th = nth pth 5
  fun real_not_eq_conv ct = 
   let 
    val (l,r) = dest_eq (dest_arg ct)
    val th = instantiate ([],[(@{cpat "?x::real"},l),(@{cpat "?y::real"},r)]) neq_th
    val th_p = poly_conv(dest_arg(dest_arg1(Thm.rhs_of th)))
    val th_x = Drule.arg_cong_rule @{cterm "uminus :: real => _"} th_p
    val th_n = fconv_rule (arg_conv poly_neg_conv) th_x
    val th' = Drule.binop_cong_rule @{cterm "op |"} 
     (Drule.arg_cong_rule (capply @{cterm "op <::real=>_"} @{cterm "0::real"}) th_p)
     (Drule.arg_cong_rule (capply @{cterm "op <::real=>_"} @{cterm "0::real"}) th_n)
    in transitive th th' 
  end
 fun equal_implies_1_rule PQ = 
  let 
   val P = lhs_of PQ
  in implies_intr P (equal_elim PQ (assume P))
  end
 (* FIXME!!! Copied from groebner.ml *)
 val strip_exists =
  let fun h (acc, t) =
   case (term_of t) of
    Const("Ex",_)$Abs(x,T,p) => h (dest_abs NONE (dest_arg t) |>> (fn v => v::acc))
  | _ => (acc,t)
  in fn t => h ([],t)
  end
  fun name_of x = case term_of x of
   Free(s,_) => s
 | Var ((s,_),_) => s
 | _ => "x"

  fun mk_forall x th = Drule.arg_cong_rule (instantiate_cterm' [SOME (ctyp_of_term x)] [] @{cpat "All :: (?'a => bool) => _" }) (abstract_rule (name_of x) x th)

  val specl = fold_rev (fn x => fn th => instantiate' [] [SOME x] (th RS spec));

 fun ext T = Drule.cterm_rule (instantiate' [SOME T] []) @{cpat Ex}
 fun mk_ex v t = Thm.capply (ext (ctyp_of_term v)) (Thm.cabs v t)

 fun choose v th th' = case concl_of th of 
   @{term Trueprop} $ (Const("Ex",_)$_) => 
    let
     val p = (funpow 2 Thm.dest_arg o cprop_of) th
     val T = (hd o Thm.dest_ctyp o ctyp_of_term) p
     val th0 = fconv_rule (Thm.beta_conversion true)
         (instantiate' [SOME T] [SOME p, (SOME o Thm.dest_arg o cprop_of) th'] exE)
     val pv = (Thm.rhs_of o Thm.beta_conversion true) 
           (Thm.capply @{cterm Trueprop} (Thm.capply p v))
     val th1 = forall_intr v (implies_intr pv th')
    in implies_elim (implies_elim th0 th) th1  end
 | _ => raise THM ("choose",0,[th, th'])

  fun simple_choose v th = 
     choose v (assume ((Thm.capply @{cterm Trueprop} o mk_ex v) ((Thm.dest_arg o hd o #hyps o Thm.crep_thm) th))) th

 val strip_forall =
  let fun h (acc, t) =
   case (term_of t) of
    Const("All",_)$Abs(x,T,p) => h (dest_abs NONE (dest_arg t) |>> (fn v => v::acc))
  | _ => (acc,t)
  in fn t => h ([],t)
  end

 fun f ct =
  let 
   val nnf_norm_conv' = 
     nnf_conv then_conv 
     literals_conv [@{term "op &"}, @{term "op |"}] [] 
     (cache_conv 
       (first_conv [real_lt_conv, real_le_conv, 
                    real_eq_conv, real_not_lt_conv, 
                    real_not_le_conv, real_not_eq_conv, all_conv]))
  fun absremover ct = (literals_conv [@{term "op &"}, @{term "op |"}] [] 
                  (try_conv (absconv1 then_conv binop_conv (arg_conv poly_conv))) then_conv 
        try_conv (absconv2 then_conv nnf_norm_conv' then_conv binop_conv absremover)) ct
  val nct = capply @{cterm Trueprop} (capply @{cterm "Not"} ct)
  val th0 = (init_conv then_conv arg_conv nnf_norm_conv') nct
  val tm0 = dest_arg (Thm.rhs_of th0)
  val th = if tm0 aconvc @{cterm False} then equal_implies_1_rule th0 else
   let 
    val (evs,bod) = strip_exists tm0
    val (avs,ibod) = strip_forall bod
    val th1 = Drule.arg_cong_rule @{cterm Trueprop} (fold mk_forall avs (absremover ibod))
    val th2 = overall [] [specl avs (assume (Thm.rhs_of th1))]
    val th3 = fold simple_choose evs (prove_hyp (equal_elim th1 (assume (capply @{cterm Trueprop} bod))) th2)
   in  Drule.implies_intr_hyps (prove_hyp (equal_elim th0 (assume nct)) th3)
   end
  in implies_elim (instantiate' [] [SOME ct] pth_final) th
 end
in f
end;

(* A linear arithmetic prover *)
local
  val linear_add = Ctermfunc.combine (curry op +/) (fn z => z =/ Rat.zero)
  fun linear_cmul c = Ctermfunc.mapf (fn x => c */ x)
  val one_tm = @{cterm "1::real"}
  fun contradictory p (e,_) = ((Ctermfunc.is_undefined e) andalso not(p Rat.zero)) orelse
     ((gen_eq_set (op aconvc) (Ctermfunc.dom e, [one_tm])) andalso not(p(Ctermfunc.apply e one_tm)))

  fun linear_ineqs vars (les,lts) = 
   case find_first (contradictory (fn x => x >/ Rat.zero)) lts of
    SOME r => r
  | NONE => 
   (case find_first (contradictory (fn x => x >/ Rat.zero)) les of
     SOME r => r
   | NONE => 
     if null vars then error "linear_ineqs: no contradiction" else
     let 
      val ineqs = les @ lts
      fun blowup v =
       length(filter (fn (e,_) => Ctermfunc.tryapplyd e v Rat.zero =/ Rat.zero) ineqs) +
       length(filter (fn (e,_) => Ctermfunc.tryapplyd e v Rat.zero >/ Rat.zero) ineqs) *
       length(filter (fn (e,_) => Ctermfunc.tryapplyd e v Rat.zero </ Rat.zero) ineqs)
      val  v = fst(hd(sort (fn ((_,i),(_,j)) => int_ord (i,j))
                 (map (fn v => (v,blowup v)) vars)))
      fun addup (e1,p1) (e2,p2) acc =
       let 
        val c1 = Ctermfunc.tryapplyd e1 v Rat.zero 
        val c2 = Ctermfunc.tryapplyd e2 v Rat.zero
       in if c1 */ c2 >=/ Rat.zero then acc else
        let 
         val e1' = linear_cmul (Rat.abs c2) e1
         val e2' = linear_cmul (Rat.abs c1) e2
         val p1' = Product(Rational_lt(Rat.abs c2),p1)
         val p2' = Product(Rational_lt(Rat.abs c1),p2)
        in (linear_add e1' e2',Sum(p1',p2'))::acc
        end
       end
      val (les0,les1) = 
         List.partition (fn (e,_) => Ctermfunc.tryapplyd e v Rat.zero =/ Rat.zero) les
      val (lts0,lts1) = 
         List.partition (fn (e,_) => Ctermfunc.tryapplyd e v Rat.zero =/ Rat.zero) lts
      val (lesp,lesn) = 
         List.partition (fn (e,_) => Ctermfunc.tryapplyd e v Rat.zero >/ Rat.zero) les1
      val (ltsp,ltsn) = 
         List.partition (fn (e,_) => Ctermfunc.tryapplyd e v Rat.zero >/ Rat.zero) lts1
      val les' = fold_rev (fn ep1 => fold_rev (addup ep1) lesp) lesn les0
      val lts' = fold_rev (fn ep1 => fold_rev (addup ep1) (lesp@ltsp)) ltsn
                      (fold_rev (fn ep1 => fold_rev (addup ep1) (lesn@ltsn)) ltsp lts0)
     in linear_ineqs (remove (op aconvc) v vars) (les',lts')
     end)

  fun linear_eqs(eqs,les,lts) = 
   case find_first (contradictory (fn x => x =/ Rat.zero)) eqs of
    SOME r => r
  | NONE => (case eqs of 
    [] => 
     let val vars = remove (op aconvc) one_tm 
           (fold_rev (curry (gen_union (op aconvc)) o Ctermfunc.dom o fst) (les@lts) []) 
     in linear_ineqs vars (les,lts) end
   | (e,p)::es => 
     if Ctermfunc.is_undefined e then linear_eqs (es,les,lts) else
     let 
      val (x,c) = Ctermfunc.choose (Ctermfunc.undefine one_tm e)
      fun xform (inp as (t,q)) =
       let val d = Ctermfunc.tryapplyd t x Rat.zero in
        if d =/ Rat.zero then inp else
        let 
         val k = (Rat.neg d) */ Rat.abs c // c
         val e' = linear_cmul k e
         val t' = linear_cmul (Rat.abs c) t
         val p' = Eqmul(cterm_of_rat k,p)
         val q' = Product(Rational_lt(Rat.abs c),q) 
        in (linear_add e' t',Sum(p',q')) 
        end 
      end
     in linear_eqs(map xform es,map xform les,map xform lts)
     end)

  fun linear_prover (eq,le,lt) = 
   let 
    val eqs = map2 (fn p => fn n => (p,Axiom_eq n)) eq (0 upto (length eq - 1))
    val les = map2 (fn p => fn n => (p,Axiom_le n)) le (0 upto (length le - 1))
    val lts = map2 (fn p => fn n => (p,Axiom_lt n)) lt (0 upto (length lt - 1))
   in linear_eqs(eqs,les,lts)
   end 
  
  fun lin_of_hol ct = 
   if ct aconvc @{cterm "0::real"} then Ctermfunc.undefined
   else if not (is_comb ct) then Ctermfunc.onefunc (ct, Rat.one)
   else if is_ratconst ct then Ctermfunc.onefunc (one_tm, dest_ratconst ct)
   else
    let val (lop,r) = Thm.dest_comb ct 
    in if not (is_comb lop) then Ctermfunc.onefunc (ct, Rat.one)
       else
        let val (opr,l) = Thm.dest_comb lop 
        in if opr aconvc @{cterm "op + :: real =>_"} 
           then linear_add (lin_of_hol l) (lin_of_hol r)
           else if opr aconvc @{cterm "op * :: real =>_"} 
                   andalso is_ratconst l then Ctermfunc.onefunc (r, dest_ratconst l)
           else Ctermfunc.onefunc (ct, Rat.one)
        end
    end

  fun is_alien ct = case term_of ct of 
   Const(@{const_name "real"}, _)$ n => 
     if can HOLogic.dest_number n then false else true
  | _ => false
 open Thm
in 
fun real_linear_prover translator (eq,le,lt) = 
 let 
  val lhs = lin_of_hol o dest_arg1 o dest_arg o cprop_of
  val rhs = lin_of_hol o dest_arg o dest_arg o cprop_of
  val eq_pols = map lhs eq
  val le_pols = map rhs le
  val lt_pols = map rhs lt 
  val aliens =  filter is_alien
      (fold_rev (curry (gen_union (op aconvc)) o Ctermfunc.dom) 
          (eq_pols @ le_pols @ lt_pols) [])
  val le_pols' = le_pols @ map (fn v => Ctermfunc.onefunc (v,Rat.one)) aliens
  val (_,proof) = linear_prover (eq_pols,le_pols',lt_pols)
  val le' = le @ map (fn a => instantiate' [] [SOME (dest_arg a)] @{thm real_of_nat_ge_zero}) aliens 
 in (translator (eq,le',lt) proof) : thm
 end
end;

(* A less general generic arithmetic prover dealing with abs,max and min*)

local
 val absmaxmin_elim_ss1 = HOL_basic_ss addsimps real_abs_thms1
 fun absmaxmin_elim_conv1 ctxt = 
    Simplifier.rewrite (Simplifier.context ctxt absmaxmin_elim_ss1)

 val absmaxmin_elim_conv2 =
  let 
   val pth_abs = instantiate' [SOME @{ctyp real}] [] abs_split'
   val pth_max = instantiate' [SOME @{ctyp real}] [] max_split
   val pth_min = instantiate' [SOME @{ctyp real}] [] min_split
   val abs_tm = @{cterm "abs :: real => _"}
   val p_tm = @{cpat "?P :: real => bool"}
   val x_tm = @{cpat "?x :: real"}
   val y_tm = @{cpat "?y::real"}
   val is_max = is_binop @{cterm "max :: real => _"}
   val is_min = is_binop @{cterm "min :: real => _"} 
   fun is_abs t = is_comb t andalso dest_fun t aconvc abs_tm
   fun eliminate_construct p c tm =
    let 
     val t = find_cterm p tm
     val th0 = (symmetric o beta_conversion false) (capply (cabs t tm) t)
     val (p,ax) = (dest_comb o Thm.rhs_of) th0
    in fconv_rule(arg_conv(binop_conv (arg_conv (beta_conversion false))))
               (transitive th0 (c p ax))
   end

   val elim_abs = eliminate_construct is_abs
    (fn p => fn ax => 
       instantiate ([], [(p_tm,p), (x_tm, dest_arg ax)]) pth_abs)
   val elim_max = eliminate_construct is_max
    (fn p => fn ax => 
      let val (ax,y) = dest_comb ax 
      in  instantiate ([], [(p_tm,p), (x_tm, dest_arg ax), (y_tm,y)]) 
      pth_max end)
   val elim_min = eliminate_construct is_min
    (fn p => fn ax => 
      let val (ax,y) = dest_comb ax 
      in  instantiate ([], [(p_tm,p), (x_tm, dest_arg ax), (y_tm,y)]) 
      pth_min end)
   in first_conv [elim_abs, elim_max, elim_min, all_conv]
  end;
in fun gen_real_arith ctxt (mkconst,eq,ge,gt,norm,neg,add,mul,prover) =
        gen_gen_real_arith ctxt (mkconst,eq,ge,gt,norm,neg,add,mul,
                       absmaxmin_elim_conv1 ctxt,absmaxmin_elim_conv2,prover)
end;

(* An instance for reals*) 

fun gen_prover_real_arith ctxt prover = 
 let
  fun simple_cterm_ord t u = TermOrd.term_ord (term_of t, term_of u) = LESS
  val {add,mul,neg,pow,sub,main} = 
     Normalizer.semiring_normalizers_ord_wrapper ctxt
      (valOf (NormalizerData.match ctxt @{cterm "(0::real) + 1"})) 
     simple_cterm_ord
in gen_real_arith ctxt
   (cterm_of_rat, field_comp_conv, field_comp_conv,field_comp_conv,
    main,neg,add,mul, prover)
end;

fun real_arith ctxt = gen_prover_real_arith ctxt real_linear_prover;
end

  (* Now the norm procedure for euclidean spaces *)


signature NORM_ARITH = 
sig
 val norm_arith : Proof.context -> conv
 val norm_arith_tac : Proof.context -> int -> tactic
end

structure NormArith : NORM_ARITH = 
struct

 open Conv Thm Conv2;
 val bool_eq = op = : bool *bool -> bool
 fun dest_ratconst t = case term_of t of
   Const(@{const_name divide}, _)$a$b => Rat.rat_of_quotient(HOLogic.dest_number a |> snd, HOLogic.dest_number b |> snd)
 | _ => Rat.rat_of_int (HOLogic.dest_number (term_of t) |> snd)
 fun is_ratconst t = can dest_ratconst t
 fun augment_norm b t acc = case term_of t of 
     Const(@{const_name norm}, _) $ _ => insert (eq_pair bool_eq (op aconvc)) (b,dest_arg t) acc
   | _ => acc
 fun find_normedterms t acc = case term_of t of
    @{term "op + :: real => _"}$_$_ =>
            find_normedterms (dest_arg1 t) (find_normedterms (dest_arg t) acc)
      | @{term "op * :: real => _"}$_$n =>
            if not (is_ratconst (dest_arg1 t)) then acc else
            augment_norm (dest_ratconst (dest_arg1 t) >=/ Rat.zero) 
                      (dest_arg t) acc
      | _ => augment_norm true t acc 

 val cterm_lincomb_neg = Ctermfunc.mapf Rat.neg
 fun cterm_lincomb_cmul c t = 
    if c =/ Rat.zero then Ctermfunc.undefined else Ctermfunc.mapf (fn x => x */ c) t
 fun cterm_lincomb_add l r = Ctermfunc.combine (curry op +/) (fn x => x =/ Rat.zero) l r
 fun cterm_lincomb_sub l r = cterm_lincomb_add l (cterm_lincomb_neg r)
 fun cterm_lincomb_eq l r = Ctermfunc.is_undefined (cterm_lincomb_sub l r)

 val int_lincomb_neg = Intfunc.mapf Rat.neg
 fun int_lincomb_cmul c t = 
    if c =/ Rat.zero then Intfunc.undefined else Intfunc.mapf (fn x => x */ c) t
 fun int_lincomb_add l r = Intfunc.combine (curry op +/) (fn x => x =/ Rat.zero) l r
 fun int_lincomb_sub l r = int_lincomb_add l (int_lincomb_neg r)
 fun int_lincomb_eq l r = Intfunc.is_undefined (int_lincomb_sub l r)

fun vector_lincomb t = case term_of t of 
   Const(@{const_name plus},Type("fun",[Type("Finite_Cartesian_Product.^",_),_])) $ _ $ _ =>
    cterm_lincomb_add (vector_lincomb (dest_arg1 t)) (vector_lincomb (dest_arg t))
 | Const(@{const_name minus},Type("fun",[Type("Finite_Cartesian_Product.^",_),_])) $ _ $ _ =>
    cterm_lincomb_sub (vector_lincomb (dest_arg1 t)) (vector_lincomb (dest_arg t))
 | Const(@{const_name vector_scalar_mult},Type("fun",[Type("Finite_Cartesian_Product.^",_),_]))$_$_ =>
    cterm_lincomb_cmul (dest_ratconst (dest_arg1 t)) (vector_lincomb (dest_arg t))
 | Const(@{const_name uminus},Type("fun",[Type("Finite_Cartesian_Product.^",_),_]))$_ =>
     cterm_lincomb_neg (vector_lincomb (dest_arg t))
 | Const(@{const_name vec},_)$_ => 
   let 
     val b = ((snd o HOLogic.dest_number o term_of o dest_arg) t = 0 
               handle TERM _=> false)
   in if b then Ctermfunc.onefunc (t,Rat.one)
      else Ctermfunc.undefined
   end
 | _ => Ctermfunc.onefunc (t,Rat.one)

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

fun replacenegnorms cv t = case term_of t of 
  @{term "op + :: real => _"}$_$_ => binop_conv (replacenegnorms cv) t
| @{term "op * :: real => _"}$_$_ => 
    if dest_ratconst (dest_arg1 t) </ Rat.zero then arg_conv cv t else reflexive t
| _ => reflexive t
fun flip v eq = 
  if Ctermfunc.defined eq v 
  then Ctermfunc.update (v, Rat.neg (Ctermfunc.apply eq v)) eq else eq
fun allsubsets s = case s of 
  [] => [[]]
|(a::t) => let val res = allsubsets t in
               map (cons a) res @ res end
fun evaluate env lin =
 Intfunc.fold (fn (x,c) => fn s => s +/ c */ (Intfunc.apply env x)) 
   lin Rat.zero

fun solve (vs,eqs) = case (vs,eqs) of
  ([],[]) => SOME (Intfunc.onefunc (0,Rat.one))
 |(_,eq::oeqs) => 
   (case filter (member (op =) vs) (Intfunc.dom eq) of (*FIXME use find_first here*)
     [] => NONE
    | v::_ => 
       if Intfunc.defined eq v 
       then 
        let 
         val c = Intfunc.apply eq v
         val vdef = int_lincomb_cmul (Rat.neg (Rat.inv c)) eq
         fun eliminate eqn = if not (Intfunc.defined eqn v) then eqn 
                             else int_lincomb_add (int_lincomb_cmul (Intfunc.apply eqn v) vdef) eqn
        in (case solve (vs \ v,map eliminate oeqs) of
            NONE => NONE
          | SOME soln => SOME (Intfunc.update (v, evaluate soln (Intfunc.undefine v vdef)) soln))
        end
       else NONE)

fun combinations k l = if k = 0 then [[]] else
 case l of 
  [] => []
| h::t => map (cons h) (combinations (k - 1) t) @ combinations k t


fun forall2 p l1 l2 = case (l1,l2) of 
   ([],[]) => true
 | (h1::t1,h2::t2) => p h1 h2 andalso forall2 p t1 t2
 | _ => false;


fun vertices vs eqs =
 let 
  fun vertex cmb = case solve(vs,cmb) of
    NONE => NONE
   | SOME soln => SOME (map (fn v => Intfunc.tryapplyd soln v Rat.zero) vs)
  val rawvs = map_filter vertex (combinations (length vs) eqs)
  val unset = filter (forall (fn c => c >=/ Rat.zero)) rawvs 
 in fold_rev (insert (uncurry (forall2 (curry op =/)))) unset [] 
 end 

fun subsumes l m = forall2 (fn x => fn y => Rat.abs x <=/ Rat.abs y) l m 

fun subsume todo dun = case todo of
 [] => dun
|v::ovs => 
   let val dun' = if exists (fn w => subsumes w v) dun then dun
                  else v::(filter (fn w => not(subsumes v w)) dun) 
   in subsume ovs dun' 
   end;

fun match_mp PQ P = P RS PQ;

fun cterm_of_rat x = 
let val (a, b) = Rat.quotient_of_rat x
in 
 if b = 1 then Numeral.mk_cnumber @{ctyp "real"} a
  else Thm.capply (Thm.capply @{cterm "op / :: real => _"} 
                   (Numeral.mk_cnumber @{ctyp "real"} a))
        (Numeral.mk_cnumber @{ctyp "real"} b)
end;

fun norm_cmul_rule c th = instantiate' [] [SOME (cterm_of_rat c)] (th RS @{thm norm_cmul_rule_thm});

fun norm_add_rule th1 th2 = [th1, th2] MRS @{thm norm_add_rule_thm};

  (* I think here the static context should be sufficient!! *)
fun inequality_canon_rule ctxt = 
 let 
  (* FIXME : Should be computed statically!! *)
  val real_poly_conv = 
    Normalizer.semiring_normalize_wrapper ctxt
     (valOf (NormalizerData.match ctxt @{cterm "(0::real) + 1"}))
 in fconv_rule (arg_conv ((rewr_conv @{thm ge_iff_diff_ge_0}) then_conv arg_conv (field_comp_conv then_conv real_poly_conv)))
end;

 fun absc cv ct = case term_of ct of 
 Abs (v,_, _) => 
  let val (x,t) = Thm.dest_abs (SOME v) ct
  in Thm.abstract_rule ((fst o dest_Free o term_of) x) x (cv t)
  end
 | _ => all_conv ct;

fun sub_conv cv ct = (comb_conv cv else_conv absc cv) ct;
fun botc1 conv ct = 
  ((sub_conv (botc1 conv)) then_conv (conv else_conv all_conv)) ct;

 fun rewrs_conv eqs ct = first_conv (map rewr_conv eqs) ct;
 val apply_pth1 = rewr_conv @{thm pth_1};
 val apply_pth2 = rewr_conv @{thm pth_2};
 val apply_pth3 = rewr_conv @{thm pth_3};
 val apply_pth4 = rewrs_conv @{thms pth_4};
 val apply_pth5 = rewr_conv @{thm pth_5};
 val apply_pth6 = rewr_conv @{thm pth_6};
 val apply_pth7 = rewrs_conv @{thms pth_7};
 val apply_pth8 = rewr_conv @{thm pth_8} then_conv arg1_conv field_comp_conv then_conv (try_conv (rewr_conv (mk_meta_eq @{thm vector_smult_lzero})));
 val apply_pth9 = rewrs_conv @{thms pth_9} then_conv arg1_conv (arg1_conv field_comp_conv);
 val apply_ptha = rewr_conv @{thm pth_a};
 val apply_pthb = rewrs_conv @{thms pth_b};
 val apply_pthc = rewrs_conv @{thms pth_c};
 val apply_pthd = try_conv (rewr_conv @{thm pth_d});

fun headvector t = case t of 
  Const(@{const_name plus}, Type("fun",[Type("Finite_Cartesian_Product.^",_),_]))$
   (Const(@{const_name vector_scalar_mult}, _)$l$v)$r => v
 | Const(@{const_name vector_scalar_mult}, _)$l$v => v
 | _ => error "headvector: non-canonical term"

fun vector_cmul_conv ct =
   ((apply_pth5 then_conv arg1_conv field_comp_conv) else_conv
    (apply_pth6 then_conv binop_conv vector_cmul_conv)) ct

fun vector_add_conv ct = apply_pth7 ct 
 handle CTERM _ => 
  (apply_pth8 ct 
   handle CTERM _ => 
    (case term_of ct of 
     Const(@{const_name plus},_)$lt$rt =>
      let 
       val l = headvector lt 
       val r = headvector rt
      in (case TermOrd.fast_term_ord (l,r) of
         LESS => (apply_pthb then_conv arg_conv vector_add_conv 
                  then_conv apply_pthd) ct
        | GREATER => (apply_pthc then_conv arg_conv vector_add_conv 
                     then_conv apply_pthd) ct 
        | EQUAL => (apply_pth9 then_conv 
                ((apply_ptha then_conv vector_add_conv) else_conv 
              arg_conv vector_add_conv then_conv apply_pthd)) ct)
      end
     | _ => reflexive ct))

fun vector_canon_conv ct = case term_of ct of
 Const(@{const_name plus},_)$_$_ =>
  let 
   val ((p,l),r) = Thm.dest_comb ct |>> Thm.dest_comb
   val lth = vector_canon_conv l 
   val rth = vector_canon_conv r
   val th = Drule.binop_cong_rule p lth rth 
  in fconv_rule (arg_conv vector_add_conv) th end

| Const(@{const_name vector_scalar_mult}, _)$_$_ =>
  let 
   val (p,r) = Thm.dest_comb ct
   val rth = Drule.arg_cong_rule p (vector_canon_conv r) 
  in fconv_rule (arg_conv (apply_pth4 else_conv vector_cmul_conv)) rth
  end

| Const(@{const_name minus},_)$_$_ => (apply_pth2 then_conv vector_canon_conv) ct

| Const(@{const_name uminus},_)$_ => (apply_pth3 then_conv vector_canon_conv) ct

| Const(@{const_name vec},_)$n => 
  let val n = Thm.dest_arg ct
  in if is_ratconst n andalso not (dest_ratconst n =/ Rat.zero) 
     then reflexive ct else apply_pth1 ct
  end

| _ => apply_pth1 ct

fun norm_canon_conv ct = case term_of ct of
  Const(@{const_name norm},_)$_ => arg_conv vector_canon_conv ct
 | _ => raise CTERM ("norm_canon_conv", [ct])

fun fold_rev2 f [] [] z = z
 | fold_rev2 f (x::xs) (y::ys) z = f x y (fold_rev2 f xs ys z)
 | fold_rev2 f _ _ _ = raise UnequalLengths;

fun int_flip v eq = 
  if Intfunc.defined eq v 
  then Intfunc.update (v, Rat.neg (Intfunc.apply eq v)) eq else eq;

local
 val pth_zero = @{thm "norm_0"}
 val tv_n = (hd o tl o dest_ctyp o ctyp_of_term o dest_arg o dest_arg1 o dest_arg o cprop_of)
             pth_zero
 val concl = dest_arg o cprop_of 
 fun real_vector_combo_prover ctxt translator (nubs,ges,gts) = 
  let 
   (* FIXME: Should be computed statically!!*)
   val real_poly_conv = 
      Normalizer.semiring_normalize_wrapper ctxt
       (valOf (NormalizerData.match ctxt @{cterm "(0::real) + 1"}))
   val sources = map (dest_arg o dest_arg1 o concl) nubs
   val rawdests = fold_rev (find_normedterms o dest_arg o concl) (ges @ gts) [] 
   val _ = if not (forall fst rawdests) then error "real_vector_combo_prover: Sanity check" 
           else ()
   val dests = distinct (op aconvc) (map snd rawdests)
   val srcfuns = map vector_lincomb sources
   val destfuns = map vector_lincomb dests 
   val vvs = fold_rev (curry (gen_union op aconvc) o Ctermfunc.dom) (srcfuns @ destfuns) []
   val n = length srcfuns
   val nvs = 1 upto n
   val srccombs = srcfuns ~~ nvs
   fun consider d =
    let 
     fun coefficients x =
      let 
       val inp = if Ctermfunc.defined d x then Intfunc.onefunc (0, Rat.neg(Ctermfunc.apply d x))
                      else Intfunc.undefined 
      in fold_rev (fn (f,v) => fn g => if Ctermfunc.defined f x then Intfunc.update (v, Ctermfunc.apply f x) g else g) srccombs inp 
      end
     val equations = map coefficients vvs
     val inequalities = map (fn n => Intfunc.onefunc (n,Rat.one)) nvs
     fun plausiblevertices f =
      let 
       val flippedequations = map (fold_rev int_flip f) equations
       val constraints = flippedequations @ inequalities
       val rawverts = vertices nvs constraints
       fun check_solution v =
        let 
          val f = fold_rev2 (curry Intfunc.update) nvs v (Intfunc.onefunc (0, Rat.one))
        in forall (fn e => evaluate f e =/ Rat.zero) flippedequations
        end
       val goodverts = filter check_solution rawverts
       val signfixups = map (fn n => if n mem_int  f then ~1 else 1) nvs 
      in map (map2 (fn s => fn c => Rat.rat_of_int s */ c) signfixups) goodverts
      end
     val allverts = fold_rev append (map plausiblevertices (allsubsets nvs)) [] 
    in subsume allverts []
    end
   fun compute_ineq v =
    let 
     val ths = map_filter (fn (v,t) => if v =/ Rat.zero then NONE 
                                     else SOME(norm_cmul_rule v t))
                            (v ~~ nubs) 
    in inequality_canon_rule ctxt (end_itlist norm_add_rule ths)
    end
   val ges' = map_filter (try compute_ineq) (fold_rev (append o consider) destfuns []) @
                 map (inequality_canon_rule ctxt) nubs @ ges
   val zerodests = filter
        (fn t => null (Ctermfunc.dom (vector_lincomb t))) (map snd rawdests)

  in RealArith.real_linear_prover translator
        (map (fn t => instantiate ([(tv_n,(hd o tl o dest_ctyp o ctyp_of_term) t)],[]) pth_zero)
            zerodests,
        map (fconv_rule (once_depth_conv (norm_canon_conv) then_conv
                       arg_conv (arg_conv real_poly_conv))) ges',
        map (fconv_rule (once_depth_conv (norm_canon_conv) then_conv 
                       arg_conv (arg_conv real_poly_conv))) gts)
  end
in val real_vector_combo_prover = real_vector_combo_prover
end;

local
 val pth = @{thm norm_imp_pos_and_ge}
 val norm_mp = match_mp pth
 val concl = dest_arg o cprop_of
 fun conjunct1 th = th RS @{thm conjunct1}
 fun conjunct2 th = th RS @{thm conjunct2}
 fun C f x y = f y x
fun real_vector_ineq_prover ctxt translator (ges,gts) = 
 let 
(*   val _ = error "real_vector_ineq_prover: pause" *)
  val ntms = fold_rev find_normedterms (map (dest_arg o concl) (ges @ gts)) []
  val lctab = vector_lincombs (map snd (filter (not o fst) ntms))
  val (fxns, ctxt') = Variable.variant_fixes (replicate (length lctab) "x") ctxt
  fun mk_norm t = capply (instantiate_cterm' [SOME (ctyp_of_term t)] [] @{cpat "norm :: (?'a :: norm) => real"}) t
  fun mk_equals l r = capply (capply (instantiate_cterm' [SOME (ctyp_of_term l)] [] @{cpat "op == :: ?'a =>_"}) l) r
  val asl = map2 (fn (t,_) => fn n => assume (mk_equals (mk_norm t) (cterm_of (ProofContext.theory_of ctxt') (Free(n,@{typ real}))))) lctab fxns
  val replace_conv = try_conv (rewrs_conv asl)
  val replace_rule = fconv_rule (funpow 2 arg_conv (replacenegnorms replace_conv))
  val ges' =
       fold_rev (fn th => fn ths => conjunct1(norm_mp th)::ths)
              asl (map replace_rule ges)
  val gts' = map replace_rule gts
  val nubs = map (conjunct2 o norm_mp) asl
  val th1 = real_vector_combo_prover ctxt' translator (nubs,ges',gts')
  val shs = filter (member (fn (t,th) => t aconvc cprop_of th) asl) (#hyps (crep_thm th1)) 
  val th11 = hd (Variable.export ctxt' ctxt [fold implies_intr shs th1])
  val cps = map (swap o dest_equals) (cprems_of th11)
  val th12 = instantiate ([], cps) th11
  val th13 = fold (C implies_elim) (map (reflexive o snd) cps) th12;
 in hd (Variable.export ctxt' ctxt [th13])
 end 
in val real_vector_ineq_prover = real_vector_ineq_prover
end;

local
 val rawrule = fconv_rule (arg_conv (rewr_conv @{thm real_eq_0_iff_le_ge_0}))
 fun conj_pair th = (th RS @{thm conjunct1}, th RS @{thm conjunct2})
 fun simple_cterm_ord t u = TermOrd.term_ord (term_of t, term_of u) = LESS;
  (* FIXME: Lookup in the context every time!!! Fix this !!!*)
 fun splitequation ctxt th acc =
  let 
   val real_poly_neg_conv = #neg
       (Normalizer.semiring_normalizers_ord_wrapper ctxt
        (valOf (NormalizerData.match ctxt @{cterm "(0::real) + 1"})) simple_cterm_ord)
   val (th1,th2) = conj_pair(rawrule th)
  in th1::fconv_rule (arg_conv (arg_conv real_poly_neg_conv)) th2::acc
  end
in fun real_vector_prover ctxt translator (eqs,ges,gts) =
     real_vector_ineq_prover ctxt translator
         (fold_rev (splitequation ctxt) eqs ges,gts)
end;

  fun init_conv ctxt = 
   Simplifier.rewrite (Simplifier.context ctxt 
     (HOL_basic_ss addsimps ([@{thm vec_0}, @{thm vec_1}, @{thm dist_def}, @{thm diff_0_right}, @{thm right_minus}, @{thm diff_self}, @{thm norm_0}] @ @{thms arithmetic_simps} @ @{thms norm_pths})))
   then_conv field_comp_conv 
   then_conv nnf_conv

 fun pure ctxt = RealArith.gen_prover_real_arith ctxt (real_vector_prover ctxt);
 fun norm_arith ctxt ct = 
  let 
   val ctxt' = Variable.declare_term (term_of ct) ctxt
   val th = init_conv ctxt' ct
  in equal_elim (Drule.arg_cong_rule @{cterm Trueprop} (symmetric th)) 
                (pure ctxt' (rhs_of th))
 end

 fun norm_arith_tac ctxt = 
   clarify_tac HOL_cs THEN'
   ObjectLogic.full_atomize_tac THEN'
   CSUBGOAL ( fn (p,i) => rtac (norm_arith ctxt (Thm.dest_arg p )) i);

end;