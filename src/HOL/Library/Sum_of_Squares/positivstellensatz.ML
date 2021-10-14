(*  Title:      HOL/Library/positivstellensatz.ML
    Author:     Amine Chaieb, University of Cambridge

A generic arithmetic prover based on Positivstellensatz certificates
--- also implements Fourier-Motzkin elimination as a special case
Fourier-Motzkin elimination.
*)

(* A functor for finite mappings based on Tables *)

signature FUNC =
sig
  include TABLE
  val apply : 'a table -> key -> 'a
  val applyd :'a table -> (key -> 'a) -> key -> 'a
  val combine : ('a -> 'a -> 'a) -> ('a -> bool) -> 'a table -> 'a table -> 'a table
  val dom : 'a table -> key list
  val tryapplyd : 'a table -> key -> 'a -> 'a
  val updatep : (key * 'a -> bool) -> key * 'a -> 'a table -> 'a table
  val choose : 'a table -> key * 'a
  val onefunc : key * 'a -> 'a table
end;

functor FuncFun(Key: KEY) : FUNC =
struct

structure Tab = Table(Key);

open Tab;

fun dom a = sort Key.ord (Tab.keys a);
fun applyd f d x = case Tab.lookup f x of
   SOME y => y
 | NONE => d x;

fun apply f x = applyd f (fn _ => raise Tab.UNDEF x) x;
fun tryapplyd f a d = applyd f (K d) a;
fun updatep p (k,v) t = if p (k, v) then t else update (k,v) t
fun combine f z a b =
  let
    fun h (k,v) t = case Tab.lookup t k of
        NONE => Tab.update (k,v) t
      | SOME v' => let val w = f v v'
        in if z w then Tab.delete k t else Tab.update (k,w) t end;
  in Tab.fold h a b end;

fun choose f =
  (case Tab.min f of
    SOME entry => entry
  | NONE => error "FuncFun.choose : Completely empty function")

fun onefunc kv = update kv empty

end;

(* Some standard functors and utility functions for them *)

structure FuncUtil =
struct

structure Intfunc = FuncFun(type key = int val ord = int_ord);
structure Ratfunc = FuncFun(type key = Rat.rat val ord = Rat.ord);
structure Intpairfunc = FuncFun(type key = int*int val ord = prod_ord int_ord int_ord);
structure Symfunc = FuncFun(type key = string val ord = fast_string_ord);
structure Termfunc = FuncFun(type key = term val ord = Term_Ord.fast_term_ord);
structure Ctermfunc = FuncFun(type key = cterm val ord = Thm.fast_term_ord);

type monomial = int Ctermfunc.table;
val monomial_ord = list_ord (prod_ord Thm.fast_term_ord int_ord) o apply2 Ctermfunc.dest
structure Monomialfunc = FuncFun(type key = monomial val ord = monomial_ord)

type poly = Rat.rat Monomialfunc.table;

(* The ordering so we can create canonical HOL polynomials.                  *)

fun dest_monomial mon = sort (Thm.fast_term_ord o apply2 fst) (Ctermfunc.dest mon);

fun monomial_order (m1,m2) =
  if Ctermfunc.is_empty m2 then LESS
  else if Ctermfunc.is_empty m1 then GREATER
  else
    let
      val mon1 = dest_monomial m1
      val mon2 = dest_monomial m2
      val deg1 = fold (Integer.add o snd) mon1 0
      val deg2 = fold (Integer.add o snd) mon2 0
    in if deg1 < deg2 then GREATER
       else if deg1 > deg2 then LESS
       else list_ord (prod_ord Thm.fast_term_ord int_ord) (mon1,mon2)
    end;

end

(* positivstellensatz datatype and prover generation *)

signature REAL_ARITH =
sig

  datatype positivstellensatz =
    Axiom_eq of int
  | Axiom_le of int
  | Axiom_lt of int
  | Rational_eq of Rat.rat
  | Rational_le of Rat.rat
  | Rational_lt of Rat.rat
  | Square of FuncUtil.poly
  | Eqmul of FuncUtil.poly * positivstellensatz
  | Sum of positivstellensatz * positivstellensatz
  | Product of positivstellensatz * positivstellensatz;

  datatype pss_tree = Trivial | Cert of positivstellensatz | Branch of pss_tree * pss_tree

  datatype tree_choice = Left | Right

  type prover = tree_choice list ->
    (thm list * thm list * thm list -> positivstellensatz -> thm) ->
      thm list * thm list * thm list -> thm * pss_tree
  type cert_conv = cterm -> thm * pss_tree

  val gen_gen_real_arith :
    Proof.context -> (Rat.rat -> cterm) * conv * conv * conv *
     conv * conv * conv * conv * conv * conv * prover -> cert_conv
  val real_linear_prover : (thm list * thm list * thm list -> positivstellensatz -> thm) ->
    thm list * thm list * thm list -> thm * pss_tree

  val gen_real_arith : Proof.context ->
    (Rat.rat -> cterm) * conv * conv * conv * conv * conv * conv * conv * prover -> cert_conv

  val gen_prover_real_arith : Proof.context -> prover -> cert_conv

  val is_ratconst : cterm -> bool
  val dest_ratconst : cterm -> Rat.rat
  val cterm_of_rat : Rat.rat -> cterm

end

structure RealArith : REAL_ARITH =
struct

open Conv
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
  | Square of FuncUtil.poly
  | Eqmul of FuncUtil.poly * positivstellensatz
  | Sum of positivstellensatz * positivstellensatz
  | Product of positivstellensatz * positivstellensatz;
         (* Theorems used in the procedure *)

datatype pss_tree = Trivial | Cert of positivstellensatz | Branch of pss_tree * pss_tree
datatype tree_choice = Left | Right
type prover = tree_choice list ->
  (thm list * thm list * thm list -> positivstellensatz -> thm) ->
    thm list * thm list * thm list -> thm * pss_tree
type cert_conv = cterm -> thm * pss_tree


    (* Some useful derived rules *)
fun deduct_antisym_rule tha thb =
    Thm.equal_intr (Thm.implies_intr (Thm.cprop_of thb) tha)
     (Thm.implies_intr (Thm.cprop_of tha) thb);

fun prove_hyp tha thb =
  if exists (curry op aconv (Thm.concl_of tha)) (Thm.hyps_of thb)  (* FIXME !? *)
  then Thm.equal_elim (Thm.symmetric (deduct_antisym_rule tha thb)) tha else thb;

val pth = @{lemma "(((x::real) < y) \<equiv> (y - x > 0))" and "((x \<le> y) \<equiv> (y - x \<ge> 0))" and
     "((x = y) \<equiv> (x - y = 0))" and "((\<not>(x < y)) \<equiv> (x - y \<ge> 0))" and
     "((\<not>(x \<le> y)) \<equiv> (x - y > 0))" and "((\<not>(x = y)) \<equiv> (x - y > 0 \<or> -(x - y) > 0))"
  by (atomize (full), auto simp add: less_diff_eq le_diff_eq not_less)};

val pth_final = @{lemma "(\<not>p \<Longrightarrow> False) \<Longrightarrow> p" by blast}
val pth_add =
  @{lemma "(x = (0::real) \<Longrightarrow> y = 0 \<Longrightarrow> x + y = 0 )" and "( x = 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> x + y \<ge> 0)" and
    "(x = 0 \<Longrightarrow> y > 0 \<Longrightarrow> x + y > 0)" and "(x \<ge> 0 \<Longrightarrow> y = 0 \<Longrightarrow> x + y \<ge> 0)" and
    "(x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> x + y \<ge> 0)" and "(x \<ge> 0 \<Longrightarrow> y > 0 \<Longrightarrow> x + y > 0)" and
    "(x > 0 \<Longrightarrow> y = 0 \<Longrightarrow> x + y > 0)" and "(x > 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> x + y > 0)" and
    "(x > 0 \<Longrightarrow> y > 0 \<Longrightarrow> x + y > 0)" by simp_all};

val pth_mul =
  @{lemma "(x = (0::real) \<Longrightarrow> y = 0 \<Longrightarrow> x * y = 0)" and "(x = 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> x * y = 0)" and
    "(x = 0 \<Longrightarrow> y > 0 \<Longrightarrow> x * y = 0)" and "(x \<ge> 0 \<Longrightarrow> y = 0 \<Longrightarrow> x * y = 0)" and
    "(x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> x * y \<ge> 0)" and "(x \<ge> 0 \<Longrightarrow> y > 0 \<Longrightarrow> x * y \<ge> 0)" and
    "(x > 0 \<Longrightarrow>  y = 0 \<Longrightarrow> x * y = 0)" and "(x > 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> x * y \<ge> 0)" and
    "(x > 0 \<Longrightarrow>  y > 0 \<Longrightarrow> x * y > 0)"
  by (auto intro: mult_mono[where a="0::real" and b="x" and d="y" and c="0", simplified]
    mult_strict_mono[where b="x" and d="y" and a="0" and c="0", simplified])};

val pth_emul = @{lemma "y = (0::real) \<Longrightarrow> x * y = 0"  by simp};
val pth_square = @{lemma "x * x \<ge> (0::real)"  by simp};

val weak_dnf_simps =
  List.take (@{thms simp_thms}, 34) @
    @{lemma "((P \<and> (Q \<or> R)) = ((P\<and>Q) \<or> (P\<and>R)))" and "((Q \<or> R) \<and> P) = ((Q\<and>P) \<or> (R\<and>P))" and
      "(P \<and> Q) = (Q \<and> P)" and "((P \<or> Q) = (Q \<or> P))" by blast+};

(*
val nnfD_simps =
  @{lemma "((~(P & Q)) = (~P | ~Q))" and "((~(P | Q)) = (~P & ~Q) )" and
    "((P --> Q) = (~P | Q) )" and "((P = Q) = ((P & Q) | (~P & ~ Q)))" and
    "((~(P = Q)) = ((P & ~ Q) | (~P & Q)) )" and "((~ ~(P)) = P)" by blast+};
*)

val choice_iff = @{lemma "(\<forall>x. \<exists>y. P x y) = (\<exists>f. \<forall>x. P x (f x))" by metis};
val prenex_simps =
  map (fn th => th RS sym)
    ([@{thm "all_conj_distrib"}, @{thm "ex_disj_distrib"}] @
      @{thms "HOL.all_simps"(1-4)} @ @{thms "ex_simps"(1-4)});

val real_abs_thms1 = @{lemma
  "((-1 * \<bar>x::real\<bar> \<ge> r) = (-1 * x \<ge> r \<and> 1 * x \<ge> r))" and
  "((-1 * \<bar>x\<bar> + a \<ge> r) = (a + -1 * x \<ge> r \<and> a + 1 * x \<ge> r))" and
  "((a + -1 * \<bar>x\<bar> \<ge> r) = (a + -1 * x \<ge> r \<and> a + 1 * x \<ge> r))" and
  "((a + -1 * \<bar>x\<bar> + b \<ge> r) = (a + -1 * x + b \<ge> r \<and> a + 1 * x + b \<ge> r))" and
  "((a + b + -1 * \<bar>x\<bar> \<ge> r) = (a + b + -1 * x \<ge> r \<and> a + b + 1 * x \<ge> r))" and
  "((a + b + -1 * \<bar>x\<bar> + c \<ge> r) = (a + b + -1 * x + c \<ge> r \<and> a + b + 1 * x + c \<ge> r))" and
  "((-1 * max x y \<ge> r) = (-1 * x \<ge> r \<and> -1 * y \<ge> r))" and
  "((-1 * max x y + a \<ge> r) = (a + -1 * x \<ge> r \<and> a + -1 * y \<ge> r))" and
  "((a + -1 * max x y \<ge> r) = (a + -1 * x \<ge> r \<and> a + -1 * y \<ge> r))" and
  "((a + -1 * max x y + b \<ge> r) = (a + -1 * x + b \<ge> r \<and> a + -1 * y  + b \<ge> r))" and
  "((a + b + -1 * max x y \<ge> r) = (a + b + -1 * x \<ge> r \<and> a + b + -1 * y \<ge> r))" and
  "((a + b + -1 * max x y + c \<ge> r) = (a + b + -1 * x + c \<ge> r \<and> a + b + -1 * y  + c \<ge> r))" and
  "((1 * min x y \<ge> r) = (1 * x \<ge> r \<and> 1 * y \<ge> r))" and
  "((1 * min x y + a \<ge> r) = (a + 1 * x \<ge> r \<and> a + 1 * y \<ge> r))" and
  "((a + 1 * min x y \<ge> r) = (a + 1 * x \<ge> r \<and> a + 1 * y \<ge> r))" and
  "((a + 1 * min x y + b \<ge> r) = (a + 1 * x + b \<ge> r \<and> a + 1 * y  + b \<ge> r))" and
  "((a + b + 1 * min x y \<ge> r) = (a + b + 1 * x \<ge> r \<and> a + b + 1 * y \<ge> r))" and
  "((a + b + 1 * min x y + c \<ge> r) = (a + b + 1 * x + c \<ge> r \<and> a + b + 1 * y  + c \<ge> r))" and
  "((min x y \<ge> r) = (x \<ge> r \<and> y \<ge> r))" and
  "((min x y + a \<ge> r) = (a + x \<ge> r \<and> a + y \<ge> r))" and
  "((a + min x y \<ge> r) = (a + x \<ge> r \<and> a + y \<ge> r))" and
  "((a + min x y + b \<ge> r) = (a + x + b \<ge> r \<and> a + y  + b \<ge> r))" and
  "((a + b + min x y \<ge> r) = (a + b + x \<ge> r \<and> a + b + y \<ge> r))" and
  "((a + b + min x y + c \<ge> r) = (a + b + x + c \<ge> r \<and> a + b + y + c \<ge> r))" and
  "((-1 * \<bar>x\<bar> > r) = (-1 * x > r \<and> 1 * x > r))" and
  "((-1 * \<bar>x\<bar> + a > r) = (a + -1 * x > r \<and> a + 1 * x > r))" and
  "((a + -1 * \<bar>x\<bar> > r) = (a + -1 * x > r \<and> a + 1 * x > r))" and
  "((a + -1 * \<bar>x\<bar> + b > r) = (a + -1 * x + b > r \<and> a + 1 * x + b > r))" and
  "((a + b + -1 * \<bar>x\<bar> > r) = (a + b + -1 * x > r \<and> a + b + 1 * x > r))" and
  "((a + b + -1 * \<bar>x\<bar> + c > r) = (a + b + -1 * x + c > r \<and> a + b + 1 * x + c > r))" and
  "((-1 * max x y > r) = ((-1 * x > r) \<and> -1 * y > r))" and
  "((-1 * max x y + a > r) = (a + -1 * x > r \<and> a + -1 * y > r))" and
  "((a + -1 * max x y > r) = (a + -1 * x > r \<and> a + -1 * y > r))" and
  "((a + -1 * max x y + b > r) = (a + -1 * x + b > r \<and> a + -1 * y  + b > r))" and
  "((a + b + -1 * max x y > r) = (a + b + -1 * x > r \<and> a + b + -1 * y > r))" and
  "((a + b + -1 * max x y + c > r) = (a + b + -1 * x + c > r \<and> a + b + -1 * y  + c > r))" and
  "((min x y > r) = (x > r \<and> y > r))" and
  "((min x y + a > r) = (a + x > r \<and> a + y > r))" and
  "((a + min x y > r) = (a + x > r \<and> a + y > r))" and
  "((a + min x y + b > r) = (a + x + b > r \<and> a + y  + b > r))" and
  "((a + b + min x y > r) = (a + b + x > r \<and> a + b + y > r))" and
  "((a + b + min x y + c > r) = (a + b + x + c > r \<and> a + b + y + c > r))"
  by auto};

val abs_split' = @{lemma "P \<bar>x::'a::linordered_idom\<bar> == (x \<ge> 0 \<and> P x \<or> x < 0 \<and> P (-x))"
  by (atomize (full)) (auto split: abs_split)};

val max_split = @{lemma "P (max x y) \<equiv> ((x::'a::linorder) \<le> y \<and> P y \<or> x > y \<and> P x)"
  by (atomize (full)) (cases "x \<le> y", auto simp add: max_def)};

val min_split = @{lemma "P (min x y) \<equiv> ((x::'a::linorder) \<le> y \<and> P x \<or> x > y \<and> P y)"
  by (atomize (full)) (cases "x \<le> y", auto simp add: min_def)};


         (* Miscellaneous *)
fun literals_conv bops uops cv =
  let
    fun h t =
      (case Thm.term_of t of
        b$_$_ => if member (op aconv) bops b then binop_conv h t else cv t
      | u$_ => if member (op aconv) uops u then arg_conv h t else cv t
      | _ => cv t)
  in h end;

fun cterm_of_rat x =
  let
    val (a, b) = Rat.dest x
  in
    if b = 1 then Numeral.mk_cnumber \<^ctyp>\<open>real\<close> a
    else Thm.apply (Thm.apply \<^cterm>\<open>(/) :: real \<Rightarrow> _\<close>
      (Numeral.mk_cnumber \<^ctyp>\<open>real\<close> a))
      (Numeral.mk_cnumber \<^ctyp>\<open>real\<close> b)
  end;

fun dest_ratconst t =
  case Thm.term_of t of
    Const(\<^const_name>\<open>divide\<close>, _)$a$b => Rat.make(HOLogic.dest_number a |> snd, HOLogic.dest_number b |> snd)
  | _ => Rat.of_int (HOLogic.dest_number (Thm.term_of t) |> snd)
fun is_ratconst t = can dest_ratconst t

(*
fun find_term p t = if p t then t else
 case t of
  a$b => (find_term p a handle TERM _ => find_term p b)
 | Abs (_,_,t') => find_term p t'
 | _ => raise TERM ("find_term",[t]);
*)

fun find_cterm p t =
  if p t then t else
  case Thm.term_of t of
    _$_ => (find_cterm p (Thm.dest_fun t) handle CTERM _ => find_cterm p (Thm.dest_arg t))
  | Abs (_,_,_) => find_cterm p (Thm.dest_abs t |> snd)
  | _ => raise CTERM ("find_cterm",[t]);

fun is_comb t = (case Thm.term_of t of _ $ _ => true | _ => false);

fun is_binop ct ct' = ct aconvc (Thm.dest_fun (Thm.dest_fun ct'))
  handle CTERM _ => false;


(* Map back polynomials to HOL.                         *)

fun cterm_of_varpow x k = if k = 1 then x else Thm.apply (Thm.apply \<^cterm>\<open>(^) :: real \<Rightarrow> _\<close> x)
  (Numeral.mk_cnumber \<^ctyp>\<open>nat\<close> k)

fun cterm_of_monomial m =
  if FuncUtil.Ctermfunc.is_empty m then \<^cterm>\<open>1::real\<close>
  else
    let
      val m' = FuncUtil.dest_monomial m
      val vps = fold_rev (fn (x,k) => cons (cterm_of_varpow x k)) m' []
    in foldr1 (fn (s, t) => Thm.apply (Thm.apply \<^cterm>\<open>(*) :: real \<Rightarrow> _\<close> s) t) vps
    end

fun cterm_of_cmonomial (m,c) =
  if FuncUtil.Ctermfunc.is_empty m then cterm_of_rat c
  else if c = @1 then cterm_of_monomial m
  else Thm.apply (Thm.apply \<^cterm>\<open>(*)::real \<Rightarrow> _\<close> (cterm_of_rat c)) (cterm_of_monomial m);

fun cterm_of_poly p =
  if FuncUtil.Monomialfunc.is_empty p then \<^cterm>\<open>0::real\<close>
  else
    let
      val cms = map cterm_of_cmonomial
        (sort (prod_ord FuncUtil.monomial_order (K EQUAL)) (FuncUtil.Monomialfunc.dest p))
    in foldr1 (fn (t1, t2) => Thm.apply(Thm.apply \<^cterm>\<open>(+) :: real \<Rightarrow> _\<close> t1) t2) cms
    end;

(* A general real arithmetic prover *)

fun gen_gen_real_arith ctxt (mk_numeric,
       numeric_eq_conv,numeric_ge_conv,numeric_gt_conv,
       poly_conv,poly_neg_conv,poly_add_conv,poly_mul_conv,
       absconv1,absconv2,prover) =
  let
    val pre_ss = put_simpset HOL_basic_ss ctxt addsimps
      @{thms simp_thms ex_simps all_simps not_all not_ex ex_disj_distrib
          all_conj_distrib if_bool_eq_disj}
    val prenex_ss = put_simpset HOL_basic_ss ctxt addsimps prenex_simps
    val skolemize_ss = put_simpset HOL_basic_ss ctxt addsimps [choice_iff]
    val presimp_conv = Simplifier.rewrite pre_ss
    val prenex_conv = Simplifier.rewrite prenex_ss
    val skolemize_conv = Simplifier.rewrite skolemize_ss
    val weak_dnf_ss = put_simpset HOL_basic_ss ctxt addsimps weak_dnf_simps
    val weak_dnf_conv = Simplifier.rewrite weak_dnf_ss
    fun eqT_elim th = Thm.equal_elim (Thm.symmetric th) @{thm TrueI}
    fun oprconv cv ct =
      let val g = Thm.dest_fun2 ct
      in if g aconvc \<^cterm>\<open>(\<le>) :: real \<Rightarrow> _\<close>
            orelse g aconvc \<^cterm>\<open>(<) :: real \<Rightarrow> _\<close>
         then arg_conv cv ct else arg1_conv cv ct
      end

    fun real_ineq_conv th ct =
      let
        val th' = (Thm.instantiate (Thm.match (Thm.lhs_of th, ct)) th
          handle Pattern.MATCH => raise CTERM ("real_ineq_conv", [ct]))
      in Thm.transitive th' (oprconv poly_conv (Thm.rhs_of th'))
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
       (Thm.instantiate' [] [SOME ct] (th RS pth_emul))
    fun square_rule t = fconv_rule (arg_conv (oprconv poly_conv))
       (Thm.instantiate' [] [SOME t] pth_square)

    fun hol_of_positivstellensatz(eqs,les,lts) proof =
      let
        fun translate prf =
          case prf of
            Axiom_eq n => nth eqs n
          | Axiom_le n => nth les n
          | Axiom_lt n => nth lts n
          | Rational_eq x => eqT_elim(numeric_eq_conv(Thm.apply \<^cterm>\<open>Trueprop\<close>
                          (Thm.apply (Thm.apply \<^cterm>\<open>(=)::real \<Rightarrow> _\<close> (mk_numeric x))
                               \<^cterm>\<open>0::real\<close>)))
          | Rational_le x => eqT_elim(numeric_ge_conv(Thm.apply \<^cterm>\<open>Trueprop\<close>
                          (Thm.apply (Thm.apply \<^cterm>\<open>(\<le>)::real \<Rightarrow> _\<close>
                                     \<^cterm>\<open>0::real\<close>) (mk_numeric x))))
          | Rational_lt x => eqT_elim(numeric_gt_conv(Thm.apply \<^cterm>\<open>Trueprop\<close>
                      (Thm.apply (Thm.apply \<^cterm>\<open>(<)::real \<Rightarrow> _\<close> \<^cterm>\<open>0::real\<close>)
                        (mk_numeric x))))
          | Square pt => square_rule (cterm_of_poly pt)
          | Eqmul(pt,p) => emul_rule (cterm_of_poly pt) (translate p)
          | Sum(p1,p2) => add_rule (translate p1) (translate p2)
          | Product(p1,p2) => mul_rule (translate p1) (translate p2)
      in fconv_rule (first_conv [numeric_ge_conv, numeric_gt_conv, numeric_eq_conv, all_conv])
          (translate proof)
      end

    val init_conv = presimp_conv then_conv
        nnf_conv ctxt then_conv skolemize_conv then_conv prenex_conv then_conv
        weak_dnf_conv

    val concl = Thm.dest_arg o Thm.cprop_of
    fun is_binop opr ct = (Thm.dest_fun2 ct aconvc opr handle CTERM _ => false)
    val is_req = is_binop \<^cterm>\<open>(=):: real \<Rightarrow> _\<close>
    val is_ge = is_binop \<^cterm>\<open>(\<le>):: real \<Rightarrow> _\<close>
    val is_gt = is_binop \<^cterm>\<open>(<):: real \<Rightarrow> _\<close>
    val is_conj = is_binop \<^cterm>\<open>HOL.conj\<close>
    val is_disj = is_binop \<^cterm>\<open>HOL.disj\<close>
    fun conj_pair th = (th RS @{thm conjunct1}, th RS @{thm conjunct2})
    fun disj_cases th th1 th2 =
      let
        val (p,q) = Thm.dest_binop (concl th)
        val c = concl th1
        val _ =
          if c aconvc (concl th2) then ()
          else error "disj_cases : conclusions not alpha convertible"
      in Thm.implies_elim (Thm.implies_elim
          (Thm.implies_elim (Thm.instantiate' [] (map SOME [p,q,c]) @{thm disjE}) th)
          (Thm.implies_intr (Thm.apply \<^cterm>\<open>Trueprop\<close> p) th1))
        (Thm.implies_intr (Thm.apply \<^cterm>\<open>Trueprop\<close> q) th2)
      end
    fun overall cert_choice dun ths =
      case ths of
        [] =>
        let
          val (eq,ne) = List.partition (is_req o concl) dun
          val (le,nl) = List.partition (is_ge o concl) ne
          val lt = filter (is_gt o concl) nl
        in prover (rev cert_choice) hol_of_positivstellensatz (eq,le,lt) end
      | th::oths =>
        let
          val ct = concl th
        in
          if is_conj ct then
            let
              val (th1,th2) = conj_pair th
            in overall cert_choice dun (th1::th2::oths) end
          else if is_disj ct then
            let
              val (th1, cert1) =
                overall (Left::cert_choice) dun
                  (Thm.assume (Thm.apply \<^cterm>\<open>Trueprop\<close> (Thm.dest_arg1 ct))::oths)
              val (th2, cert2) =
                overall (Right::cert_choice) dun
                  (Thm.assume (Thm.apply \<^cterm>\<open>Trueprop\<close> (Thm.dest_arg ct))::oths)
            in (disj_cases th th1 th2, Branch (cert1, cert2)) end
          else overall cert_choice (th::dun) oths
        end
    fun dest_binary b ct =
        if is_binop b ct then Thm.dest_binop ct
        else raise CTERM ("dest_binary",[b,ct])
    val dest_eq = dest_binary \<^cterm>\<open>(=) :: real \<Rightarrow> _\<close>
    val neq_th = nth pth 5
    fun real_not_eq_conv ct =
      let
        val (l,r) = dest_eq (Thm.dest_arg ct)
        val th = Thm.instantiate (TVars.empty, Vars.make [(\<^var>\<open>?x::real\<close>,l),(\<^var>\<open>?y::real\<close>,r)]) neq_th
        val th_p = poly_conv(Thm.dest_arg(Thm.dest_arg1(Thm.rhs_of th)))
        val th_x = Drule.arg_cong_rule \<^cterm>\<open>uminus :: real \<Rightarrow> _\<close> th_p
        val th_n = fconv_rule (arg_conv poly_neg_conv) th_x
        val th' = Drule.binop_cong_rule \<^cterm>\<open>HOL.disj\<close>
          (Drule.arg_cong_rule (Thm.apply \<^cterm>\<open>(<)::real \<Rightarrow> _\<close> \<^cterm>\<open>0::real\<close>) th_p)
          (Drule.arg_cong_rule (Thm.apply \<^cterm>\<open>(<)::real \<Rightarrow> _\<close> \<^cterm>\<open>0::real\<close>) th_n)
      in Thm.transitive th th'
      end
    fun equal_implies_1_rule PQ =
      let
        val P = Thm.lhs_of PQ
      in Thm.implies_intr P (Thm.equal_elim PQ (Thm.assume P))
      end
    (*FIXME!!! Copied from groebner.ml*)
    val strip_exists =
      let
        fun h (acc, t) =
          case Thm.term_of t of
            Const(\<^const_name>\<open>Ex\<close>,_)$Abs(_,_,_) =>
              h (Thm.dest_abs (Thm.dest_arg t) |>> (fn v => v::acc))
          | _ => (acc,t)
      in fn t => h ([],t)
      end
    fun name_of x =
      case Thm.term_of x of
        Free(s,_) => s
      | Var ((s,_),_) => s
      | _ => "x"

    fun mk_forall x th =
      let
        val T = Thm.typ_of_cterm x
        val all = Thm.cterm_of ctxt (Const (\<^const_name>\<open>All\<close>, (T --> \<^typ>\<open>bool\<close>) --> \<^typ>\<open>bool\<close>))
      in Drule.arg_cong_rule all (Thm.abstract_rule (name_of x) x th) end

    val specl = fold_rev (fn x => fn th => Thm.instantiate' [] [SOME x] (th RS spec));

    fun ext T = Thm.cterm_of ctxt (Const (\<^const_name>\<open>Ex\<close>, (T --> \<^typ>\<open>bool\<close>) --> \<^typ>\<open>bool\<close>))
    fun mk_ex v t = Thm.apply (ext (Thm.typ_of_cterm v)) (Thm.lambda v t)

    fun choose v th th' =
      case Thm.concl_of th of
        \<^term>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>Ex\<close>,_)$_) =>
        let
          val p = (funpow 2 Thm.dest_arg o Thm.cprop_of) th
          val T = Thm.dest_ctyp0 (Thm.ctyp_of_cterm p)
          val th0 = fconv_rule (Thm.beta_conversion true)
            (Thm.instantiate' [SOME T] [SOME p, (SOME o Thm.dest_arg o Thm.cprop_of) th'] exE)
          val pv = (Thm.rhs_of o Thm.beta_conversion true)
            (Thm.apply \<^cterm>\<open>Trueprop\<close> (Thm.apply p v))
          val th1 = Thm.forall_intr v (Thm.implies_intr pv th')
        in Thm.implies_elim (Thm.implies_elim th0 th) th1  end
      | _ => raise THM ("choose",0,[th, th'])

    fun simple_choose v th =
      choose v
        (Thm.assume
          ((Thm.apply \<^cterm>\<open>Trueprop\<close> o mk_ex v) (Thm.dest_arg (hd (Thm.chyps_of th))))) th

    val strip_forall =
      let
        fun h (acc, t) =
          case Thm.term_of t of
            Const(\<^const_name>\<open>All\<close>,_)$Abs(_,_,_) =>
              h (Thm.dest_abs (Thm.dest_arg t) |>> (fn v => v::acc))
          | _ => (acc,t)
      in fn t => h ([],t)
      end

    fun f ct =
      let
        val nnf_norm_conv' =
          nnf_conv ctxt then_conv
          literals_conv [\<^term>\<open>HOL.conj\<close>, \<^term>\<open>HOL.disj\<close>] []
          (Conv.cache_conv
            (first_conv [real_lt_conv, real_le_conv,
                         real_eq_conv, real_not_lt_conv,
                         real_not_le_conv, real_not_eq_conv, all_conv]))
        fun absremover ct = (literals_conv [\<^term>\<open>HOL.conj\<close>, \<^term>\<open>HOL.disj\<close>] []
                  (try_conv (absconv1 then_conv binop_conv (arg_conv poly_conv))) then_conv
                  try_conv (absconv2 then_conv nnf_norm_conv' then_conv binop_conv absremover)) ct
        val nct = Thm.apply \<^cterm>\<open>Trueprop\<close> (Thm.apply \<^cterm>\<open>Not\<close> ct)
        val th0 = (init_conv then_conv arg_conv nnf_norm_conv') nct
        val tm0 = Thm.dest_arg (Thm.rhs_of th0)
        val (th, certificates) =
          if tm0 aconvc \<^cterm>\<open>False\<close> then (equal_implies_1_rule th0, Trivial) else
          let
            val (evs,bod) = strip_exists tm0
            val (avs,ibod) = strip_forall bod
            val th1 = Drule.arg_cong_rule \<^cterm>\<open>Trueprop\<close> (fold mk_forall avs (absremover ibod))
            val (th2, certs) = overall [] [] [specl avs (Thm.assume (Thm.rhs_of th1))]
            val th3 =
              fold simple_choose evs
                (prove_hyp (Thm.equal_elim th1 (Thm.assume (Thm.apply \<^cterm>\<open>Trueprop\<close> bod))) th2)
          in (Drule.implies_intr_hyps (prove_hyp (Thm.equal_elim th0 (Thm.assume nct)) th3), certs)
          end
      in (Thm.implies_elim (Thm.instantiate' [] [SOME ct] pth_final) th, certificates)
      end
  in f
  end;

(* A linear arithmetic prover *)
local
  val linear_add = FuncUtil.Ctermfunc.combine (curry op +) (fn z => z = @0)
  fun linear_cmul c = FuncUtil.Ctermfunc.map (fn _ => fn x => c * x)
  val one_tm = \<^cterm>\<open>1::real\<close>
  fun contradictory p (e,_) = ((FuncUtil.Ctermfunc.is_empty e) andalso not(p @0)) orelse
     ((eq_set (op aconvc) (FuncUtil.Ctermfunc.dom e, [one_tm])) andalso
       not(p(FuncUtil.Ctermfunc.apply e one_tm)))

  fun linear_ineqs vars (les,lts) =
    case find_first (contradictory (fn x => x > @0)) lts of
      SOME r => r
    | NONE =>
      (case find_first (contradictory (fn x => x > @0)) les of
         SOME r => r
       | NONE =>
         if null vars then error "linear_ineqs: no contradiction" else
         let
           val ineqs = les @ lts
           fun blowup v =
             length(filter (fn (e,_) => FuncUtil.Ctermfunc.tryapplyd e v @0 = @0) ineqs) +
             length(filter (fn (e,_) => FuncUtil.Ctermfunc.tryapplyd e v @0 > @0) ineqs) *
             length(filter (fn (e,_) => FuncUtil.Ctermfunc.tryapplyd e v @0 < @0) ineqs)
           val v = fst(hd(sort (fn ((_,i),(_,j)) => int_ord (i,j))
             (map (fn v => (v,blowup v)) vars)))
           fun addup (e1,p1) (e2,p2) acc =
             let
               val c1 = FuncUtil.Ctermfunc.tryapplyd e1 v @0
               val c2 = FuncUtil.Ctermfunc.tryapplyd e2 v @0
             in
               if c1 * c2 >= @0 then acc else
               let
                 val e1' = linear_cmul (abs c2) e1
                 val e2' = linear_cmul (abs c1) e2
                 val p1' = Product(Rational_lt (abs c2), p1)
                 val p2' = Product(Rational_lt (abs c1), p2)
               in (linear_add e1' e2',Sum(p1',p2'))::acc
               end
             end
           val (les0,les1) =
             List.partition (fn (e,_) => FuncUtil.Ctermfunc.tryapplyd e v @0 = @0) les
           val (lts0,lts1) =
             List.partition (fn (e,_) => FuncUtil.Ctermfunc.tryapplyd e v @0 = @0) lts
           val (lesp,lesn) =
             List.partition (fn (e,_) => FuncUtil.Ctermfunc.tryapplyd e v @0 > @0) les1
           val (ltsp,ltsn) =
             List.partition (fn (e,_) => FuncUtil.Ctermfunc.tryapplyd e v @0 > @0) lts1
           val les' = fold_rev (fn ep1 => fold_rev (addup ep1) lesp) lesn les0
           val lts' = fold_rev (fn ep1 => fold_rev (addup ep1) (lesp@ltsp)) ltsn
                      (fold_rev (fn ep1 => fold_rev (addup ep1) (lesn@ltsn)) ltsp lts0)
         in linear_ineqs (remove (op aconvc) v vars) (les',lts')
         end)

  fun linear_eqs(eqs,les,lts) =
    case find_first (contradictory (fn x => x = @0)) eqs of
      SOME r => r
    | NONE =>
      (case eqs of
         [] =>
         let val vars = remove (op aconvc) one_tm
             (fold_rev (union (op aconvc) o FuncUtil.Ctermfunc.dom o fst) (les@lts) [])
         in linear_ineqs vars (les,lts) end
       | (e,p)::es =>
         if FuncUtil.Ctermfunc.is_empty e then linear_eqs (es,les,lts) else
         let
           val (x,c) = FuncUtil.Ctermfunc.choose (FuncUtil.Ctermfunc.delete_safe one_tm e)
           fun xform (inp as (t,q)) =
             let val d = FuncUtil.Ctermfunc.tryapplyd t x @0 in
               if d = @0 then inp else
               let
                 val k = ~ d * abs c / c
                 val e' = linear_cmul k e
                 val t' = linear_cmul (abs c) t
                 val p' = Eqmul(FuncUtil.Monomialfunc.onefunc (FuncUtil.Ctermfunc.empty, k),p)
                 val q' = Product(Rational_lt (abs c), q)
               in (linear_add e' t',Sum(p',q'))
               end
             end
         in linear_eqs(map xform es,map xform les,map xform lts)
         end)

  fun linear_prover (eq,le,lt) =
    let
      val eqs = map_index (fn (n, p) => (p,Axiom_eq n)) eq
      val les = map_index (fn (n, p) => (p,Axiom_le n)) le
      val lts = map_index (fn (n, p) => (p,Axiom_lt n)) lt
    in linear_eqs(eqs,les,lts)
    end

  fun lin_of_hol ct =
    if ct aconvc \<^cterm>\<open>0::real\<close> then FuncUtil.Ctermfunc.empty
    else if not (is_comb ct) then FuncUtil.Ctermfunc.onefunc (ct, @1)
    else if is_ratconst ct then FuncUtil.Ctermfunc.onefunc (one_tm, dest_ratconst ct)
    else
      let val (lop,r) = Thm.dest_comb ct
      in
        if not (is_comb lop) then FuncUtil.Ctermfunc.onefunc (ct, @1)
        else
          let val (opr,l) = Thm.dest_comb lop
          in
            if opr aconvc \<^cterm>\<open>(+) :: real \<Rightarrow> _\<close>
            then linear_add (lin_of_hol l) (lin_of_hol r)
            else if opr aconvc \<^cterm>\<open>(*) :: real \<Rightarrow> _\<close>
                    andalso is_ratconst l then FuncUtil.Ctermfunc.onefunc (r, dest_ratconst l)
            else FuncUtil.Ctermfunc.onefunc (ct, @1)
          end
      end

  fun is_alien ct =
    case Thm.term_of ct of
      Const(\<^const_name>\<open>of_nat\<close>, _)$ n => not (can HOLogic.dest_number n)
    | Const(\<^const_name>\<open>of_int\<close>, _)$ n => not (can HOLogic.dest_number n)
    | _ => false
in
fun real_linear_prover translator (eq,le,lt) =
  let
    val lhs = lin_of_hol o Thm.dest_arg1 o Thm.dest_arg o Thm.cprop_of
    val rhs = lin_of_hol o Thm.dest_arg o Thm.dest_arg o Thm.cprop_of
    val eq_pols = map lhs eq
    val le_pols = map rhs le
    val lt_pols = map rhs lt
    val aliens = filter is_alien
      (fold_rev (union (op aconvc) o FuncUtil.Ctermfunc.dom)
                (eq_pols @ le_pols @ lt_pols) [])
    val le_pols' = le_pols @ map (fn v => FuncUtil.Ctermfunc.onefunc (v,@1)) aliens
    val (_,proof) = linear_prover (eq_pols,le_pols',lt_pols)
    val le' = le @ map (fn a => Thm.instantiate' [] [SOME (Thm.dest_arg a)] @{thm of_nat_0_le_iff}) aliens
  in ((translator (eq,le',lt) proof), Trivial)
  end
end;

(* A less general generic arithmetic prover dealing with abs,max and min*)

local
  val absmaxmin_elim_ss1 =
    simpset_of (put_simpset HOL_basic_ss \<^context> addsimps real_abs_thms1)
  fun absmaxmin_elim_conv1 ctxt =
    Simplifier.rewrite (put_simpset absmaxmin_elim_ss1 ctxt)

  val absmaxmin_elim_conv2 =
    let
      val pth_abs = Thm.instantiate' [SOME \<^ctyp>\<open>real\<close>] [] abs_split'
      val pth_max = Thm.instantiate' [SOME \<^ctyp>\<open>real\<close>] [] max_split
      val pth_min = Thm.instantiate' [SOME \<^ctyp>\<open>real\<close>] [] min_split
      val abs_tm = \<^cterm>\<open>abs :: real \<Rightarrow> _\<close>
      val p_v = (("P", 0), \<^typ>\<open>real \<Rightarrow> bool\<close>)
      val x_v = (("x", 0), \<^typ>\<open>real\<close>)
      val y_v = (("y", 0), \<^typ>\<open>real\<close>)
      val is_max = is_binop \<^cterm>\<open>max :: real \<Rightarrow> _\<close>
      val is_min = is_binop \<^cterm>\<open>min :: real \<Rightarrow> _\<close>
      fun is_abs t = is_comb t andalso Thm.dest_fun t aconvc abs_tm
      fun eliminate_construct p c tm =
        let
          val t = find_cterm p tm
          val th0 = (Thm.symmetric o Thm.beta_conversion false) (Thm.apply (Thm.lambda t tm) t)
          val (p,ax) = (Thm.dest_comb o Thm.rhs_of) th0
        in fconv_rule(arg_conv(binop_conv (arg_conv (Thm.beta_conversion false))))
                     (Thm.transitive th0 (c p ax))
        end

      val elim_abs = eliminate_construct is_abs
        (fn p => fn ax =>
          Thm.instantiate (TVars.empty, Vars.make [(p_v,p), (x_v, Thm.dest_arg ax)]) pth_abs)
      val elim_max = eliminate_construct is_max
        (fn p => fn ax =>
          let val (ax,y) = Thm.dest_comb ax
          in Thm.instantiate (TVars.empty, Vars.make [(p_v,p), (x_v, Thm.dest_arg ax), (y_v,y)])
                             pth_max end)
      val elim_min = eliminate_construct is_min
        (fn p => fn ax =>
          let val (ax,y) = Thm.dest_comb ax
          in Thm.instantiate (TVars.empty, Vars.make [(p_v,p), (x_v, Thm.dest_arg ax), (y_v,y)])
                             pth_min end)
    in first_conv [elim_abs, elim_max, elim_min, all_conv]
    end;
in
fun gen_real_arith ctxt (mkconst,eq,ge,gt,norm,neg,add,mul,prover) =
  gen_gen_real_arith ctxt
    (mkconst,eq,ge,gt,norm,neg,add,mul,
     absmaxmin_elim_conv1 ctxt,absmaxmin_elim_conv2,prover)
end;

(* An instance for reals*)

fun gen_prover_real_arith ctxt prover =
  let
    val {add, mul, neg, pow = _, sub = _, main} =
        Semiring_Normalizer.semiring_normalizers_ord_wrapper ctxt
        (the (Semiring_Normalizer.match ctxt \<^cterm>\<open>(0::real) + 1\<close>))
        Thm.term_ord
  in gen_real_arith ctxt
     (cterm_of_rat,
      Numeral_Simprocs.field_comp_conv ctxt,
      Numeral_Simprocs.field_comp_conv ctxt,
      Numeral_Simprocs.field_comp_conv ctxt,
      main ctxt, neg ctxt, add ctxt, mul ctxt, prover)
  end;

end
