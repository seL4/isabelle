(*  Title:      HOL/Tools/Qelim/cooper.ML
    Author:     Amine Chaieb, TU Muenchen

Presburger arithmetic by Cooper's algorithm.
*)

signature COOPER =
sig
  type entry
  val get: Proof.context -> entry
  val del: term list -> attribute
  val add: term list -> attribute
  exception COOPER of string
  val conv: Proof.context -> conv
  val tac: bool -> thm list -> thm list -> Proof.context -> int -> tactic
end;

structure Cooper: COOPER =
struct

type entry = simpset * term list;

val allowed_consts =
  [\<^term>\<open>(+) :: int => _\<close>, \<^term>\<open>(+) :: nat => _\<close>,
   \<^term>\<open>(-) :: int => _\<close>, \<^term>\<open>(-) :: nat => _\<close>,
   \<^term>\<open>(*) :: int => _\<close>, \<^term>\<open>(*) :: nat => _\<close>,
   \<^term>\<open>(div) :: int => _\<close>, \<^term>\<open>(div) :: nat => _\<close>,
   \<^term>\<open>(mod) :: int => _\<close>, \<^term>\<open>(mod) :: nat => _\<close>,
   \<^term>\<open>HOL.conj\<close>, \<^term>\<open>HOL.disj\<close>, \<^term>\<open>HOL.implies\<close>,
   \<^term>\<open>(=) :: int => _\<close>, \<^term>\<open>(=) :: nat => _\<close>, \<^term>\<open>(=) :: bool => _\<close>,
   \<^term>\<open>(<) :: int => _\<close>, \<^term>\<open>(<) :: nat => _\<close>,
   \<^term>\<open>(<=) :: int => _\<close>, \<^term>\<open>(<=) :: nat => _\<close>,
   \<^term>\<open>(dvd) :: int => _\<close>, \<^term>\<open>(dvd) :: nat => _\<close>,
   \<^term>\<open>abs :: int => _\<close>,
   \<^term>\<open>max :: int => _\<close>, \<^term>\<open>max :: nat => _\<close>,
   \<^term>\<open>min :: int => _\<close>, \<^term>\<open>min :: nat => _\<close>,
   \<^term>\<open>uminus :: int => _\<close>, (*@ {term "uminus :: nat => _"},*)
   \<^term>\<open>Not\<close>, \<^term>\<open>Suc\<close>,
   \<^term>\<open>Ex :: (int => _) => _\<close>, \<^term>\<open>Ex :: (nat => _) => _\<close>,
   \<^term>\<open>All :: (int => _) => _\<close>, \<^term>\<open>All :: (nat => _) => _\<close>,
   \<^term>\<open>nat\<close>, \<^term>\<open>int\<close>,
   \<^term>\<open>Num.One\<close>, \<^term>\<open>Num.Bit0\<close>, \<^term>\<open>Num.Bit1\<close>,
   \<^term>\<open>Num.numeral :: num => int\<close>, \<^term>\<open>Num.numeral :: num => nat\<close>,
   \<^term>\<open>0::int\<close>, \<^term>\<open>1::int\<close>, \<^term>\<open>0::nat\<close>, \<^term>\<open>1::nat\<close>,
   \<^term>\<open>True\<close>, \<^term>\<open>False\<close>];

structure Data = Generic_Data
(
  type T = simpset * term list;
  val empty = (HOL_ss, allowed_consts);
  val extend = I;
  fun merge ((ss1, ts1), (ss2, ts2)) =
    (merge_ss (ss1, ss2), Library.merge (op aconv) (ts1, ts2));
);

val get = Data.get o Context.Proof;

fun add ts = Thm.declaration_attribute (fn th => fn context =>
  context |> Data.map (fn (ss, ts') =>
     (simpset_map (Context.proof_of context) (fn ctxt => ctxt addsimps [th]) ss,
      merge (op aconv) (ts', ts))))

fun del ts = Thm.declaration_attribute (fn th => fn context =>
  context |> Data.map (fn (ss, ts') =>
     (simpset_map (Context.proof_of context) (fn ctxt => ctxt delsimps [th]) ss,
      subtract (op aconv) ts' ts)))

fun simp_thms_conv ctxt =
  Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps @{thms simp_thms});
val FWD = Drule.implies_elim_list;

val true_tm = \<^cterm>\<open>True\<close>;
val false_tm = \<^cterm>\<open>False\<close>;
val presburger_ss = simpset_of (\<^context> addsimps @{thms zdvd1_eq});
val lin_ss =
  simpset_of (put_simpset presburger_ss \<^context>
    addsimps (@{thms dvd_eq_mod_eq_0 add.assoc [where 'a = int] add.commute [where 'a = int] add.left_commute [where 'a = int]
  mult.assoc [where 'a = int] mult.commute [where 'a = int] mult.left_commute [where 'a = int]
}));

val iT = HOLogic.intT
val bT = HOLogic.boolT;
val dest_number = HOLogic.dest_number #> snd;
val perhaps_number = try dest_number;
val is_number = can dest_number;

val [miconj, midisj, mieq, mineq, milt, mile, migt, mige, midvd, mindvd, miP] =
    map (Thm.instantiate' [SOME \<^ctyp>\<open>int\<close>] []) @{thms "minf"};

val [infDconj, infDdisj, infDdvd,infDndvd,infDP] =
    map (Thm.instantiate' [SOME \<^ctyp>\<open>int\<close>] []) @{thms "inf_period"};

val [piconj, pidisj, pieq,pineq,pilt,pile,pigt,pige,pidvd,pindvd,piP] =
    map (Thm.instantiate' [SOME \<^ctyp>\<open>int\<close>] []) @{thms "pinf"};

val [miP, piP] = map (Thm.instantiate' [SOME \<^ctyp>\<open>bool\<close>] []) [miP, piP];

val infDP = Thm.instantiate' (map SOME [\<^ctyp>\<open>int\<close>, \<^ctyp>\<open>bool\<close>]) [] infDP;

val [[asetconj, asetdisj, aseteq, asetneq, asetlt, asetle,
      asetgt, asetge, asetdvd, asetndvd,asetP],
     [bsetconj, bsetdisj, bseteq, bsetneq, bsetlt, bsetle,
      bsetgt, bsetge, bsetdvd, bsetndvd,bsetP]]  = [@{thms "aset"}, @{thms "bset"}];

val [cpmi, cppi] = [@{thm "cpmi"}, @{thm "cppi"}];

val unity_coeff_ex = Thm.instantiate' [SOME \<^ctyp>\<open>int\<close>] [] @{thm "unity_coeff_ex"};

val [zdvd_mono,simp_from_to,all_not_ex] =
     [@{thm "zdvd_mono"}, @{thm "simp_from_to"}, @{thm "all_not_ex"}];

val [dvd_uminus, dvd_uminus'] = @{thms "uminus_dvd_conv"};

val eval_ss =
  simpset_of (put_simpset presburger_ss \<^context>
    addsimps [simp_from_to] delsimps [insert_iff, bex_triv]);
fun eval_conv ctxt = Simplifier.rewrite (put_simpset eval_ss ctxt);

(* recognising cterm without moving to terms *)

datatype fm = And of cterm*cterm| Or of cterm*cterm| Eq of cterm | NEq of cterm
            | Lt of cterm | Le of cterm | Gt of cterm | Ge of cterm
            | Dvd of cterm*cterm | NDvd of cterm*cterm | Nox

fun whatis x ct =
( case Thm.term_of ct of
  Const(\<^const_name>\<open>HOL.conj\<close>,_)$_$_ => And (Thm.dest_binop ct)
| Const (\<^const_name>\<open>HOL.disj\<close>,_)$_$_ => Or (Thm.dest_binop ct)
| Const (\<^const_name>\<open>HOL.eq\<close>,_)$y$_ => if Thm.term_of x aconv y then Eq (Thm.dest_arg ct) else Nox
| Const (\<^const_name>\<open>Not\<close>,_) $ (Const (\<^const_name>\<open>HOL.eq\<close>,_)$y$_) =>
  if Thm.term_of x aconv y then NEq (funpow 2 Thm.dest_arg ct) else Nox
| Const (\<^const_name>\<open>Orderings.less\<close>, _) $ y$ z =>
   if Thm.term_of x aconv y then Lt (Thm.dest_arg ct)
   else if Thm.term_of x aconv z then Gt (Thm.dest_arg1 ct) else Nox
| Const (\<^const_name>\<open>Orderings.less_eq\<close>, _) $ y $ z =>
   if Thm.term_of x aconv y then Le (Thm.dest_arg ct)
   else if Thm.term_of x aconv z then Ge (Thm.dest_arg1 ct) else Nox
| Const (\<^const_name>\<open>Rings.dvd\<close>,_)$_$(Const(\<^const_name>\<open>Groups.plus\<close>,_)$y$_) =>
   if Thm.term_of x aconv y then Dvd (Thm.dest_binop ct ||> Thm.dest_arg) else Nox
| Const (\<^const_name>\<open>Not\<close>,_) $ (Const (\<^const_name>\<open>Rings.dvd\<close>,_)$_$(Const(\<^const_name>\<open>Groups.plus\<close>,_)$y$_)) =>
   if Thm.term_of x aconv y then
   NDvd (Thm.dest_binop (Thm.dest_arg ct) ||> Thm.dest_arg) else Nox
| _ => Nox)
  handle CTERM _ => Nox;

fun get_pmi_term t =
  let val (x,eq) =
     (Thm.dest_abs_global o Thm.dest_arg o snd o Thm.dest_abs_global o Thm.dest_arg)
        (Thm.dest_arg t)
in (Thm.lambda x o Thm.dest_arg o Thm.dest_arg) eq end;

val get_pmi = get_pmi_term o Thm.cprop_of;

val p_v' = (("P'", 0), \<^typ>\<open>int \<Rightarrow> bool\<close>);
val q_v' = (("Q'", 0), \<^typ>\<open>int \<Rightarrow> bool\<close>);
val p_v = (("P", 0), \<^typ>\<open>int \<Rightarrow> bool\<close>);
val q_v = (("Q", 0), \<^typ>\<open>int \<Rightarrow> bool\<close>);

fun myfwd (th1, th2, th3) p q
      [(th_1,th_2,th_3), (th_1',th_2',th_3')] =
  let
   val (mp', mq') = (get_pmi th_1, get_pmi th_1')
   val mi_th =
    FWD (Drule.instantiate_normalize
          (TVars.empty, Vars.make [(p_v,p),(q_v,q), (p_v',mp'),(q_v',mq')]) th1) [th_1, th_1']
   val infD_th =
    FWD (Drule.instantiate_normalize (TVars.empty, Vars.make [(p_v,mp'), (q_v, mq')]) th3) [th_3,th_3']
   val set_th =
    FWD (Drule.instantiate_normalize (TVars.empty, Vars.make [(p_v,p), (q_v,q)]) th2) [th_2, th_2']
  in (mi_th, set_th, infD_th)
  end;

val inst' = fn cts => Thm.instantiate' [] (map SOME cts);
val infDTrue = Thm.instantiate' [] [SOME true_tm] infDP;
val infDFalse = Thm.instantiate' [] [SOME false_tm] infDP;

val cadd =  \<^cterm>\<open>(+) :: int => _\<close>
val cmulC =  \<^cterm>\<open>(*) :: int => _\<close>
val cminus =  \<^cterm>\<open>(-) :: int => _\<close>
val cone =  \<^cterm>\<open>1 :: int\<close>
val [addC, mulC, subC] = map Thm.term_of [cadd, cmulC, cminus]
val [zero, one] = [\<^term>\<open>0 :: int\<close>, \<^term>\<open>1 :: int\<close>];

fun numeral1 f n = HOLogic.mk_number iT (f (dest_number n));
fun numeral2 f m n = HOLogic.mk_number iT (f (dest_number m) (dest_number n));

val [minus1,plus1] =
    map (fn c => fn t => Thm.apply (Thm.apply c t) cone) [cminus,cadd];

fun decomp_pinf x dvd inS [aseteq, asetneq, asetlt, asetle,
                           asetgt, asetge,asetdvd,asetndvd,asetP,
                           infDdvd, infDndvd, asetconj,
                           asetdisj, infDconj, infDdisj] cp =
 case (whatis x cp) of
  And (p,q) => ([p,q], myfwd (piconj, asetconj, infDconj) (Thm.lambda x p) (Thm.lambda x q))
| Or (p,q) => ([p,q], myfwd (pidisj, asetdisj, infDdisj) (Thm.lambda x p) (Thm.lambda x q))
| Eq t => ([], K (inst' [t] pieq, FWD (inst' [t] aseteq) [inS (plus1 t)], infDFalse))
| NEq t => ([], K (inst' [t] pineq, FWD (inst' [t] asetneq) [inS t], infDTrue))
| Lt t => ([], K (inst' [t] pilt, FWD (inst' [t] asetlt) [inS t], infDFalse))
| Le t => ([], K (inst' [t] pile, FWD (inst' [t] asetle) [inS (plus1 t)], infDFalse))
| Gt t => ([], K (inst' [t] pigt, (inst' [t] asetgt), infDTrue))
| Ge t => ([], K (inst' [t] pige, (inst' [t] asetge), infDTrue))
| Dvd (d,s) =>
   ([],let val dd = dvd d
       in K (inst' [d,s] pidvd, FWD (inst' [d,s] asetdvd) [dd],FWD (inst' [d,s] infDdvd) [dd]) end)
| NDvd(d,s) => ([],let val dd = dvd d
        in K (inst' [d,s] pindvd, FWD (inst' [d,s] asetndvd) [dd], FWD (inst' [d,s] infDndvd) [dd]) end)
| _ => ([], K (inst' [cp] piP, inst' [cp] asetP, inst' [cp] infDP));

fun decomp_minf x dvd inS [bseteq,bsetneq,bsetlt, bsetle, bsetgt,
                           bsetge,bsetdvd,bsetndvd,bsetP,
                           infDdvd, infDndvd, bsetconj,
                           bsetdisj, infDconj, infDdisj] cp =
 case (whatis x cp) of
  And (p,q) => ([p,q], myfwd (miconj, bsetconj, infDconj) (Thm.lambda x p) (Thm.lambda x q))
| Or (p,q) => ([p,q], myfwd (midisj, bsetdisj, infDdisj) (Thm.lambda x p) (Thm.lambda x q))
| Eq t => ([], K (inst' [t] mieq, FWD (inst' [t] bseteq) [inS (minus1 t)], infDFalse))
| NEq t => ([], K (inst' [t] mineq, FWD (inst' [t] bsetneq) [inS t], infDTrue))
| Lt t => ([], K (inst' [t] milt, (inst' [t] bsetlt), infDTrue))
| Le t => ([], K (inst' [t] mile, (inst' [t] bsetle), infDTrue))
| Gt t => ([], K (inst' [t] migt, FWD (inst' [t] bsetgt) [inS t], infDFalse))
| Ge t => ([], K (inst' [t] mige,FWD (inst' [t] bsetge) [inS (minus1 t)], infDFalse))
| Dvd (d,s) => ([],let val dd = dvd d
        in K (inst' [d,s] midvd, FWD (inst' [d,s] bsetdvd) [dd] , FWD (inst' [d,s] infDdvd) [dd]) end)
| NDvd (d,s) => ([],let val dd = dvd d
        in K (inst' [d,s] mindvd, FWD (inst' [d,s] bsetndvd) [dd], FWD (inst' [d,s] infDndvd) [dd]) end)
| _ => ([], K (inst' [cp] miP, inst' [cp] bsetP, inst' [cp] infDP))

    (* Canonical linear form for terms, formulae etc.. *)
fun provelin ctxt t = Goal.prove ctxt [] [] t
  (fn _ => EVERY [simp_tac (put_simpset lin_ss ctxt) 1, TRY (Lin_Arith.tac ctxt 1)]);
fun linear_cmul 0 tm = zero
  | linear_cmul n tm = case tm of
      Const (\<^const_name>\<open>Groups.plus\<close>, _) $ a $ b => addC $ linear_cmul n a $ linear_cmul n b
    | Const (\<^const_name>\<open>Groups.times\<close>, _) $ c $ x => mulC $ numeral1 (fn m => n * m) c $ x
    | Const (\<^const_name>\<open>Groups.minus\<close>, _) $ a $ b => subC $ linear_cmul n a $ linear_cmul n b
    | (m as Const (\<^const_name>\<open>Groups.uminus\<close>, _)) $ a => m $ linear_cmul n a
    | _ => numeral1 (fn m => n * m) tm;
fun earlier [] x y = false
  | earlier (h::t) x y =
    if h aconv y then false else if h aconv x then true else earlier t x y;

fun linear_add vars tm1 tm2 = case (tm1, tm2) of
    (Const (\<^const_name>\<open>Groups.plus\<close>, _) $ (Const (\<^const_name>\<open>Groups.times\<close>, _) $ c1 $ x1) $ r1,
    Const (\<^const_name>\<open>Groups.plus\<close>, _) $ (Const (\<^const_name>\<open>Groups.times\<close>, _) $ c2 $ x2) $ r2) =>
   if x1 = x2 then
     let val c = numeral2 Integer.add c1 c2
      in if c = zero then linear_add vars r1 r2
         else addC$(mulC$c$x1)$(linear_add vars r1 r2)
     end
     else if earlier vars x1 x2 then addC $ (mulC $ c1 $ x1) $ linear_add vars r1 tm2
   else addC $ (mulC $ c2 $ x2) $ linear_add vars tm1 r2
 | (Const (\<^const_name>\<open>Groups.plus\<close>, _) $ (Const (\<^const_name>\<open>Groups.times\<close>, _) $ c1 $ x1) $ r1, _) =>
      addC $ (mulC $ c1 $ x1) $ linear_add vars r1 tm2
 | (_, Const (\<^const_name>\<open>Groups.plus\<close>, _) $ (Const (\<^const_name>\<open>Groups.times\<close>, _) $ c2 $ x2) $ r2) =>
      addC $ (mulC $ c2 $ x2) $ linear_add vars tm1 r2
 | (_, _) => numeral2 Integer.add tm1 tm2;

fun linear_neg tm = linear_cmul ~1 tm;
fun linear_sub vars tm1 tm2 = linear_add vars tm1 (linear_neg tm2);

exception COOPER of string;

fun lint vars tm =  if is_number tm then tm  else case tm of
  Const (\<^const_name>\<open>Groups.uminus\<close>, _) $ t => linear_neg (lint vars t)
| Const (\<^const_name>\<open>Groups.plus\<close>, _) $ s $ t => linear_add vars (lint vars s) (lint vars t)
| Const (\<^const_name>\<open>Groups.minus\<close>, _) $ s $ t => linear_sub vars (lint vars s) (lint vars t)
| Const (\<^const_name>\<open>Groups.times\<close>, _) $ s $ t =>
  let val s' = lint vars s
      val t' = lint vars t
  in case perhaps_number s' of SOME n => linear_cmul n t'
   | NONE => (case perhaps_number t' of SOME n => linear_cmul n s'
   | NONE => raise COOPER "lint: not linear")
  end
 | _ => addC $ (mulC $ one $ tm) $ zero;

fun lin (vs as _::_) (Const (\<^const_name>\<open>Not\<close>, _) $ (Const (\<^const_name>\<open>Orderings.less\<close>, T) $ s $ t)) =
    lin vs (Const (\<^const_name>\<open>Orderings.less_eq\<close>, T) $ t $ s)
  | lin (vs as _::_) (Const (\<^const_name>\<open>Not\<close>,_) $ (Const(\<^const_name>\<open>Orderings.less_eq\<close>, T) $ s $ t)) =
    lin vs (Const (\<^const_name>\<open>Orderings.less\<close>, T) $ t $ s)
  | lin vs (Const (\<^const_name>\<open>Not\<close>,T)$t) = Const (\<^const_name>\<open>Not\<close>,T)$ (lin vs t)
  | lin (vs as _::_) (Const(\<^const_name>\<open>Rings.dvd\<close>,_)$d$t) =
    HOLogic.mk_binrel \<^const_name>\<open>Rings.dvd\<close> (numeral1 abs d, lint vs t)
  | lin (vs as x::_) ((b as Const(\<^const_name>\<open>HOL.eq\<close>,_))$s$t) =
     (case lint vs (subC$t$s) of
      (t as _$(m$c$y)$r) =>
        if x <> y then b$zero$t
        else if dest_number c < 0 then b$(m$(numeral1 ~ c)$y)$r
        else b$(m$c$y)$(linear_neg r)
      | t => b$zero$t)
  | lin (vs as x::_) (b$s$t) =
     (case lint vs (subC$t$s) of
      (t as _$(m$c$y)$r) =>
        if x <> y then b$zero$t
        else if dest_number c < 0 then b$(m$(numeral1 ~ c)$y)$r
        else b$(linear_neg r)$(m$c$y)
      | t => b$zero$t)
  | lin vs fm = fm;

fun lint_conv ctxt vs ct =
let val t = Thm.term_of ct
in (provelin ctxt ((HOLogic.eq_const iT)$t$(lint vs t) |> HOLogic.mk_Trueprop))
             RS eq_reflection
end;

fun is_intrel_type T = T = \<^typ>\<open>int => int => bool\<close>;

fun is_intrel (b$_$_) = is_intrel_type (fastype_of b)
  | is_intrel (\<^term>\<open>Not\<close>$(b$_$_)) = is_intrel_type (fastype_of b)
  | is_intrel _ = false;

fun linearize_conv ctxt vs ct = case Thm.term_of ct of
  Const(\<^const_name>\<open>Rings.dvd\<close>,_)$_$_ =>
  let
    val th = Conv.binop_conv (lint_conv ctxt vs) ct
    val (d',t') = Thm.dest_binop (Thm.rhs_of th)
    val (dt',tt') = (Thm.term_of d', Thm.term_of t')
  in if is_number dt' andalso is_number tt'
     then Conv.fconv_rule (Conv.arg_conv (Simplifier.rewrite (put_simpset presburger_ss ctxt))) th
     else
     let
       val dth =
         case perhaps_number (Thm.term_of d') of
           SOME d => if d < 0 then
             (Conv.fconv_rule (Conv.arg_conv (Conv.arg1_conv (lint_conv ctxt vs)))
                              (Thm.transitive th (inst' [d',t'] dvd_uminus))
              handle TERM _ => th)
            else th
         | NONE => raise COOPER "linearize_conv: not linear"
      val d'' = Thm.rhs_of dth |> Thm.dest_arg1
     in
      case tt' of
        Const(\<^const_name>\<open>Groups.plus\<close>,_)$(Const(\<^const_name>\<open>Groups.times\<close>,_)$c$_)$_ =>
        let val x = dest_number c
        in if x < 0 then Conv.fconv_rule (Conv.arg_conv (Conv.arg_conv (lint_conv ctxt vs)))
                                       (Thm.transitive dth (inst' [d'',t'] dvd_uminus'))
        else dth end
      | _ => dth
     end
  end
| Const (\<^const_name>\<open>Not\<close>,_)$(Const(\<^const_name>\<open>Rings.dvd\<close>,_)$_$_) => Conv.arg_conv (linearize_conv ctxt vs) ct
| t => if is_intrel t
      then (provelin ctxt ((HOLogic.eq_const bT)$t$(lin vs t) |> HOLogic.mk_Trueprop))
       RS eq_reflection
      else Thm.reflexive ct;

val dvdc = \<^cterm>\<open>(dvd) :: int => _\<close>;

fun unify ctxt q =
 let
  val (e,(cx,p)) = q |> Thm.dest_comb ||> Thm.dest_abs_global
  val x = Thm.term_of cx
  val ins = insert (op = : int * int -> bool)
  fun h (acc,dacc) t =
   case Thm.term_of t of
    Const(s,_)$(Const(\<^const_name>\<open>Groups.times\<close>,_)$c$y)$ _ =>
    if x aconv y andalso member (op =)
      [\<^const_name>\<open>HOL.eq\<close>, \<^const_name>\<open>Orderings.less\<close>, \<^const_name>\<open>Orderings.less_eq\<close>] s
    then (ins (dest_number c) acc,dacc) else (acc,dacc)
  | Const(s,_)$_$(Const(\<^const_name>\<open>Groups.times\<close>,_)$c$y) =>
    if x aconv y andalso member (op =)
       [\<^const_name>\<open>Orderings.less\<close>, \<^const_name>\<open>Orderings.less_eq\<close>] s
    then (ins (dest_number c) acc, dacc) else (acc,dacc)
  | Const(\<^const_name>\<open>Rings.dvd\<close>,_)$_$(Const(\<^const_name>\<open>Groups.plus\<close>,_)$(Const(\<^const_name>\<open>Groups.times\<close>,_)$c$y)$_) =>
    if x aconv y then (acc,ins (dest_number c) dacc) else (acc,dacc)
  | Const(\<^const_name>\<open>HOL.conj\<close>,_)$_$_ => h (h (acc,dacc) (Thm.dest_arg1 t)) (Thm.dest_arg t)
  | Const(\<^const_name>\<open>HOL.disj\<close>,_)$_$_ => h (h (acc,dacc) (Thm.dest_arg1 t)) (Thm.dest_arg t)
  | Const (\<^const_name>\<open>Not\<close>,_)$_ => h (acc,dacc) (Thm.dest_arg t)
  | _ => (acc, dacc)
  val (cs,ds) = h ([],[]) p
  val l = Integer.lcms (union (op =) cs ds)
  fun cv k ct =
    let val (tm as b$s$t) = Thm.term_of ct
    in ((HOLogic.eq_const bT)$tm$(b$(linear_cmul k s)$(linear_cmul k t))
         |> HOLogic.mk_Trueprop |> provelin ctxt) RS eq_reflection end
  fun nzprop x =
   let
    val th =
     Simplifier.rewrite (put_simpset lin_ss ctxt)
      (Thm.apply \<^cterm>\<open>Trueprop\<close> (Thm.apply \<^cterm>\<open>Not\<close>
           (Thm.apply (Thm.apply \<^cterm>\<open>(=) :: int => _\<close> (Numeral.mk_cnumber \<^ctyp>\<open>int\<close> x))
           \<^cterm>\<open>0::int\<close>)))
   in Thm.equal_elim (Thm.symmetric th) TrueI end;
  val notz =
    let val tab = fold Inttab.update
          (ds ~~ (map (fn x => nzprop (l div x)) ds)) Inttab.empty
    in
      fn ct => the (Inttab.lookup tab (ct |> Thm.term_of |> dest_number))
        handle Option.Option =>
          (writeln ("noz: Theorems-Table contains no entry for " ^
              Syntax.string_of_term ctxt (Thm.term_of ct)); raise Option.Option)
    end
  fun unit_conv t =
   case Thm.term_of t of
   Const(\<^const_name>\<open>HOL.conj\<close>,_)$_$_ => Conv.binop_conv unit_conv t
  | Const(\<^const_name>\<open>HOL.disj\<close>,_)$_$_ => Conv.binop_conv unit_conv t
  | Const (\<^const_name>\<open>Not\<close>,_)$_ => Conv.arg_conv unit_conv t
  | Const(s,_)$(Const(\<^const_name>\<open>Groups.times\<close>,_)$c$y)$ _ =>
    if x=y andalso member (op =)
      [\<^const_name>\<open>HOL.eq\<close>, \<^const_name>\<open>Orderings.less\<close>, \<^const_name>\<open>Orderings.less_eq\<close>] s
    then cv (l div dest_number c) t else Thm.reflexive t
  | Const(s,_)$_$(Const(\<^const_name>\<open>Groups.times\<close>,_)$c$y) =>
    if x=y andalso member (op =)
      [\<^const_name>\<open>Orderings.less\<close>, \<^const_name>\<open>Orderings.less_eq\<close>] s
    then cv (l div dest_number c) t else Thm.reflexive t
  | Const(\<^const_name>\<open>Rings.dvd\<close>,_)$d$(r as (Const(\<^const_name>\<open>Groups.plus\<close>,_)$(Const(\<^const_name>\<open>Groups.times\<close>,_)$c$y)$_)) =>
    if x=y then
      let
       val k = l div dest_number c
       val kt = HOLogic.mk_number iT k
       val th1 = inst' [Thm.dest_arg1 t, Thm.dest_arg t]
             ((Thm.dest_arg t |> funpow 2 Thm.dest_arg1 |> notz) RS zdvd_mono)
       val (d',t') = (mulC$kt$d, mulC$kt$r)
       val thc = (provelin ctxt ((HOLogic.eq_const iT)$d'$(lint [] d') |> HOLogic.mk_Trueprop))
                   RS eq_reflection
       val tht = (provelin ctxt ((HOLogic.eq_const iT)$t'$(linear_cmul k r) |> HOLogic.mk_Trueprop))
                 RS eq_reflection
      in Thm.transitive th1 (Thm.combination (Drule.arg_cong_rule dvdc thc) tht) end
    else Thm.reflexive t
  | _ => Thm.reflexive t
  val uth = unit_conv p
  val clt =  Numeral.mk_cnumber \<^ctyp>\<open>int\<close> l
  val ltx = Thm.apply (Thm.apply cmulC clt) cx
  val th = Drule.arg_cong_rule e (Thm.abstract_rule (fst (dest_Free x )) cx uth)
  val th' = inst' [Thm.lambda ltx (Thm.rhs_of uth), clt] unity_coeff_ex
  val thf = Thm.transitive th
      (Thm.transitive (Thm.symmetric (Thm.beta_conversion true (Thm.cprop_of th' |> Thm.dest_arg1))) th')
  val (lth,rth) = Thm.dest_comb (Thm.cprop_of thf) |>> Thm.dest_arg |>> Thm.beta_conversion true
                  ||> Thm.beta_conversion true |>> Thm.symmetric
 in Thm.transitive (Thm.transitive lth thf) rth end;


val emptyIS = \<^cterm>\<open>{}::int set\<close>;
val insert_tm = \<^cterm>\<open>insert :: int => _\<close>;
fun mkISet cts = fold_rev (Thm.apply insert_tm #> Thm.apply) cts emptyIS;
val eqelem_imp_imp = @{thm eqelem_imp_iff} RS iffD1;
val [A_v,B_v] =
  map (fn th => Thm.cprop_of th |> funpow 2 Thm.dest_arg
    |> Thm.dest_abs_global |> snd |> Thm.dest_arg1 |> Thm.dest_arg
    |> Thm.dest_abs_global |> snd |> Thm.dest_fun |> Thm.dest_arg
    |> Thm.term_of |> dest_Var) [asetP, bsetP];

val D_v = (("D", 0), \<^typ>\<open>int\<close>);

fun cooperex_conv ctxt vs q =
let

 val uth = unify ctxt q
 val (x,p) = Thm.dest_abs_global (Thm.dest_arg (Thm.rhs_of uth))
 val ins = insert (op aconvc)
 fun h t (bacc,aacc,dacc) =
  case (whatis x t) of
    And (p,q) => h q (h p (bacc,aacc,dacc))
  | Or (p,q) => h q  (h p (bacc,aacc,dacc))
  | Eq t => (ins (minus1 t) bacc,
             ins (plus1 t) aacc,dacc)
  | NEq t => (ins t bacc,
              ins t aacc, dacc)
  | Lt t => (bacc, ins t aacc, dacc)
  | Le t => (bacc, ins (plus1 t) aacc,dacc)
  | Gt t => (ins t bacc, aacc,dacc)
  | Ge t => (ins (minus1 t) bacc, aacc,dacc)
  | Dvd (d,_) => (bacc,aacc,insert (op =) (Thm.term_of d |> dest_number) dacc)
  | NDvd (d,_) => (bacc,aacc,insert (op =) (Thm.term_of d|> dest_number) dacc)
  | _ => (bacc, aacc, dacc)
 val (b0,a0,ds) = h p ([],[],[])
 val d = Integer.lcms ds
 val cd = Numeral.mk_cnumber \<^ctyp>\<open>int\<close> d
 fun divprop x =
   let
    val th =
     Simplifier.rewrite (put_simpset lin_ss ctxt)
      (Thm.apply \<^cterm>\<open>Trueprop\<close>
           (Thm.apply (Thm.apply dvdc (Numeral.mk_cnumber \<^ctyp>\<open>int\<close> x)) cd))
   in Thm.equal_elim (Thm.symmetric th) TrueI end;
 val dvd =
   let val tab = fold Inttab.update (ds ~~ (map divprop ds)) Inttab.empty in
     fn ct => the (Inttab.lookup tab (Thm.term_of ct |> dest_number))
       handle Option.Option =>
        (writeln ("dvd: Theorems-Table contains no entry for" ^
            Syntax.string_of_term ctxt (Thm.term_of ct)); raise Option.Option)
   end
 val dp =
   let val th = Simplifier.rewrite (put_simpset lin_ss ctxt)
      (Thm.apply \<^cterm>\<open>Trueprop\<close>
           (Thm.apply (Thm.apply \<^cterm>\<open>(<) :: int => _\<close> \<^cterm>\<open>0::int\<close>) cd))
   in Thm.equal_elim (Thm.symmetric th) TrueI end;
    (* A and B set *)
   local
     val insI1 = Thm.instantiate' [SOME \<^ctyp>\<open>int\<close>] [] @{thm "insertI1"}
     val insI2 = Thm.instantiate' [SOME \<^ctyp>\<open>int\<close>] [] @{thm "insertI2"}
   in
    fun provein x S =
     case Thm.term_of S of
        Const(\<^const_name>\<open>Orderings.bot\<close>, _) => error "Unexpected error in Cooper, please email Amine Chaieb"
      | Const(\<^const_name>\<open>insert\<close>, _) $ y $ _ =>
         let val (cy,S') = Thm.dest_binop S
         in if Thm.term_of x aconv y then Thm.instantiate' [] [SOME x, SOME S'] insI1
         else Thm.implies_elim (Thm.instantiate' [] [SOME x, SOME S', SOME cy] insI2)
                           (provein x S')
         end
   end

 val al = map (lint vs o Thm.term_of) a0
 val bl = map (lint vs o Thm.term_of) b0
 val (sl,s0,f,abths,cpth) =
   if length (distinct (op aconv) bl) <= length (distinct (op aconv) al)
   then
    (bl,b0,decomp_minf,
     fn B => (map (fn th =>
       Thm.implies_elim (Thm.instantiate (TVars.empty, Vars.make [(B_v,B), (D_v,cd)]) th) dp)
                     [bseteq,bsetneq,bsetlt, bsetle, bsetgt,bsetge])@
                   (map (Thm.instantiate (TVars.empty, Vars.make [(B_v,B), (D_v,cd)]))
                        [bsetdvd,bsetndvd,bsetP,infDdvd, infDndvd,bsetconj,
                         bsetdisj,infDconj, infDdisj]),
                       cpmi)
     else (al,a0,decomp_pinf,fn A =>
          (map (fn th =>
            Thm.implies_elim (Thm.instantiate (TVars.empty, Vars.make [(A_v,A), (D_v,cd)]) th) dp)
                   [aseteq,asetneq,asetlt, asetle, asetgt,asetge])@
                   (map (Thm.instantiate (TVars.empty, Vars.make [(A_v,A), (D_v,cd)]))
                   [asetdvd,asetndvd, asetP, infDdvd, infDndvd,asetconj,
                         asetdisj,infDconj, infDdisj]),cppi)
 val cpth =
  let
   val sths = map (fn (tl,t0) =>
                      if tl = Thm.term_of t0
                      then Thm.instantiate' [SOME \<^ctyp>\<open>int\<close>] [SOME t0] refl
                      else provelin ctxt ((HOLogic.eq_const iT)$tl$(Thm.term_of t0)
                                 |> HOLogic.mk_Trueprop))
                   (sl ~~ s0)
   val csl = distinct (op aconvc) (map (Thm.cprop_of #> Thm.dest_arg #> Thm.dest_arg1) sths)
   val S = mkISet csl
   val inStab = fold (fn ct => fn tab => Termtab.update (Thm.term_of ct, provein ct S) tab)
                    csl Termtab.empty
   val eqelem_th = Thm.instantiate' [SOME \<^ctyp>\<open>int\<close>] [NONE,NONE, SOME S] eqelem_imp_imp
   val inS =
     let
      val tab = fold Termtab.update
        (map (fn eq =>
                let val (s,t) = Thm.cprop_of eq |> Thm.dest_arg |> Thm.dest_binop
                    val th =
                      if s aconvc t
                      then the (Termtab.lookup inStab (Thm.term_of s))
                      else FWD (Thm.instantiate' [] [SOME s, SOME t] eqelem_th)
                        [eq, the (Termtab.lookup inStab (Thm.term_of s))]
                 in (Thm.term_of t, th) end) sths) Termtab.empty
        in
          fn ct => the (Termtab.lookup tab (Thm.term_of ct))
            handle Option.Option =>
              (writeln ("inS: No theorem for " ^ Syntax.string_of_term ctxt (Thm.term_of ct));
                raise Option.Option)
        end
       val (inf, nb, pd) = divide_and_conquer (f x dvd inS (abths S)) p
   in [dp, inf, nb, pd] MRS cpth
   end
 val cpth' = Thm.transitive uth (cpth RS eq_reflection)
in Thm.transitive cpth' ((simp_thms_conv ctxt then_conv eval_conv ctxt) (Thm.rhs_of cpth'))
end;

fun literals_conv bops uops env cv =
 let fun h t =
  case Thm.term_of t of
   b$_$_ => if member (op aconv) bops b then Conv.binop_conv h t else cv env t
 | u$_ => if member (op aconv) uops u then Conv.arg_conv h t else cv env t
 | _ => cv env t
 in h end;

fun integer_nnf_conv ctxt env =
  nnf_conv ctxt then_conv literals_conv [HOLogic.conj, HOLogic.disj] [] env (linearize_conv ctxt);

val conv_ss =
  simpset_of (put_simpset HOL_basic_ss \<^context>
    addsimps (@{thms simp_thms} @ take 4 @{thms ex_simps} @
      [not_all, all_not_ex, @{thm ex_disj_distrib}]));

fun conv ctxt p =
  Qelim.gen_qelim_conv ctxt
    (Simplifier.rewrite (put_simpset conv_ss ctxt))
    (Simplifier.rewrite (put_simpset presburger_ss ctxt))
    (Simplifier.rewrite (put_simpset conv_ss ctxt))
    (cons o Thm.term_of) (Misc_Legacy.term_frees (Thm.term_of p))
    (linearize_conv ctxt) (integer_nnf_conv ctxt)
    (cooperex_conv ctxt) p
  handle CTERM _ => raise COOPER "bad cterm"
       | THM _ => raise COOPER "bad thm"
       | TYPE _ => raise COOPER "bad type"

fun add_bools t =
  let
    val ops = [\<^term>\<open>(=) :: int => _\<close>, \<^term>\<open>(<) :: int => _\<close>, \<^term>\<open>(<=) :: int => _\<close>,
      \<^term>\<open>HOL.conj\<close>, \<^term>\<open>HOL.disj\<close>, \<^term>\<open>HOL.implies\<close>, \<^term>\<open>(=) :: bool => _\<close>,
      \<^term>\<open>Not\<close>, \<^term>\<open>All :: (int => _) => _\<close>,
      \<^term>\<open>Ex :: (int => _) => _\<close>, \<^term>\<open>True\<close>, \<^term>\<open>False\<close>];
    val is_op = member (op =) ops;
    val skip = not (fastype_of t = HOLogic.boolT)
  in case t of
      (l as f $ a) $ b => if skip orelse is_op f then add_bools b o add_bools l
              else insert (op aconv) t
    | f $ a => if skip orelse is_op f then add_bools a o add_bools f
              else insert (op aconv) t
    | Abs _ => add_bools (snd (Term.dest_abs_global t))
    | _ => if skip orelse is_op t then I else insert (op aconv) t
  end;

fun descend vs (abs as (_, xT, _)) =
  let val ((xn', _), p') = Term.dest_abs_global (Abs abs)
  in ((xn', xT) :: vs, p') end;

local structure Proc = Cooper_Procedure in

fun num_of_term vs (Free vT) = Proc.Bound (Proc.nat_of_integer (find_index (fn vT' => vT' = vT) vs))
  | num_of_term vs (Term.Bound i) = Proc.Bound (Proc.nat_of_integer i)
  | num_of_term vs \<^term>\<open>0::int\<close> = Proc.C (Proc.Int_of_integer 0)
  | num_of_term vs \<^term>\<open>1::int\<close> = Proc.C (Proc.Int_of_integer 1)
  | num_of_term vs (t as Const (\<^const_name>\<open>numeral\<close>, _) $ _) =
      Proc.C (Proc.Int_of_integer (dest_number t))
  | num_of_term vs (Const (\<^const_name>\<open>Groups.uminus\<close>, _) $ t') =
      Proc.Neg (num_of_term vs t')
  | num_of_term vs (Const (\<^const_name>\<open>Groups.plus\<close>, _) $ t1 $ t2) =
      Proc.Add (num_of_term vs t1, num_of_term vs t2)
  | num_of_term vs (Const (\<^const_name>\<open>Groups.minus\<close>, _) $ t1 $ t2) =
      Proc.Sub (num_of_term vs t1, num_of_term vs t2)
  | num_of_term vs (Const (\<^const_name>\<open>Groups.times\<close>, _) $ t1 $ t2) =
     (case perhaps_number t1
       of SOME n => Proc.Mul (Proc.Int_of_integer n, num_of_term vs t2)
        | NONE => (case perhaps_number t2
           of SOME n => Proc.Mul (Proc.Int_of_integer n, num_of_term vs t1)
            | NONE => raise COOPER "reification: unsupported kind of multiplication"))
  | num_of_term _ _ = raise COOPER "reification: bad term";

fun fm_of_term ps vs (Const (\<^const_name>\<open>True\<close>, _)) = Proc.T
  | fm_of_term ps vs (Const (\<^const_name>\<open>False\<close>, _)) = Proc.F
  | fm_of_term ps vs (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ t1 $ t2) =
      Proc.And (fm_of_term ps vs t1, fm_of_term ps vs t2)
  | fm_of_term ps vs (Const (\<^const_name>\<open>HOL.disj\<close>, _) $ t1 $ t2) =
      Proc.Or (fm_of_term ps vs t1, fm_of_term ps vs t2)
  | fm_of_term ps vs (Const (\<^const_name>\<open>HOL.implies\<close>, _) $ t1 $ t2) =
      Proc.Imp (fm_of_term ps vs t1, fm_of_term ps vs t2)
  | fm_of_term ps vs (\<^term>\<open>(=) :: bool => _ \<close> $ t1 $ t2) =
      Proc.Iff (fm_of_term ps vs t1, fm_of_term ps vs t2)
  | fm_of_term ps vs (Const (\<^const_name>\<open>Not\<close>, _) $ t') =
      Proc.NOT (fm_of_term ps vs t')
  | fm_of_term ps vs (Const (\<^const_name>\<open>Ex\<close>, _) $ Abs abs) =
      Proc.E (uncurry (fm_of_term ps) (descend vs abs))
  | fm_of_term ps vs (Const (\<^const_name>\<open>All\<close>, _) $ Abs abs) =
      Proc.A (uncurry (fm_of_term ps) (descend vs abs))
  | fm_of_term ps vs (\<^term>\<open>(=) :: int => _\<close> $ t1 $ t2) =
      Proc.Eq (Proc.Sub (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term ps vs (Const (\<^const_name>\<open>Orderings.less_eq\<close>, _) $ t1 $ t2) =
      Proc.Le (Proc.Sub (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term ps vs (Const (\<^const_name>\<open>Orderings.less\<close>, _) $ t1 $ t2) =
      Proc.Lt (Proc.Sub (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term ps vs (Const (\<^const_name>\<open>Rings.dvd\<close>, _) $ t1 $ t2) =
     (case perhaps_number t1
       of SOME n => Proc.Dvd (Proc.Int_of_integer n, num_of_term vs t2)
        | NONE => raise COOPER "reification: unsupported dvd")
  | fm_of_term ps vs t = let val n = find_index (fn t' => t aconv t') ps
      in if n > 0 then Proc.Closed (Proc.nat_of_integer n) else raise COOPER "reification: unknown term" end;

fun term_of_num vs (Proc.C i) = HOLogic.mk_number HOLogic.intT (Proc.integer_of_int i)
  | term_of_num vs (Proc.Bound n) = Free (nth vs (Proc.integer_of_nat n))
  | term_of_num vs (Proc.Neg t') =
      \<^term>\<open>uminus :: int => _\<close> $ term_of_num vs t'
  | term_of_num vs (Proc.Add (t1, t2)) =
      \<^term>\<open>(+) :: int => _\<close> $ term_of_num vs t1 $ term_of_num vs t2
  | term_of_num vs (Proc.Sub (t1, t2)) =
      \<^term>\<open>(-) :: int => _\<close> $ term_of_num vs t1 $ term_of_num vs t2
  | term_of_num vs (Proc.Mul (i, t2)) =
      \<^term>\<open>(*) :: int => _\<close> $ HOLogic.mk_number HOLogic.intT (Proc.integer_of_int i) $ term_of_num vs t2
  | term_of_num vs (Proc.CN (n, i, t')) =
      term_of_num vs (Proc.Add (Proc.Mul (i, Proc.Bound n), t'));

fun term_of_fm ps vs Proc.T = \<^term>\<open>True\<close>
  | term_of_fm ps vs Proc.F = \<^term>\<open>False\<close>
  | term_of_fm ps vs (Proc.And (t1, t2)) = HOLogic.conj $ term_of_fm ps vs t1 $ term_of_fm ps vs t2
  | term_of_fm ps vs (Proc.Or (t1, t2)) = HOLogic.disj $ term_of_fm ps vs t1 $ term_of_fm ps vs t2
  | term_of_fm ps vs (Proc.Imp (t1, t2)) = HOLogic.imp $ term_of_fm ps vs t1 $ term_of_fm ps vs t2
  | term_of_fm ps vs (Proc.Iff (t1, t2)) = \<^term>\<open>(=) :: bool => _\<close> $ term_of_fm ps vs t1 $ term_of_fm ps vs t2
  | term_of_fm ps vs (Proc.NOT t') = HOLogic.Not $ term_of_fm ps vs t'
  | term_of_fm ps vs (Proc.Eq t') = \<^term>\<open>(=) :: int => _ \<close> $ term_of_num vs t'$ \<^term>\<open>0::int\<close>
  | term_of_fm ps vs (Proc.NEq t') = term_of_fm ps vs (Proc.NOT (Proc.Eq t'))
  | term_of_fm ps vs (Proc.Lt t') = \<^term>\<open>(<) :: int => _ \<close> $ term_of_num vs t' $ \<^term>\<open>0::int\<close>
  | term_of_fm ps vs (Proc.Le t') = \<^term>\<open>(<=) :: int => _ \<close> $ term_of_num vs t' $ \<^term>\<open>0::int\<close>
  | term_of_fm ps vs (Proc.Gt t') = \<^term>\<open>(<) :: int => _ \<close> $ \<^term>\<open>0::int\<close> $ term_of_num vs t'
  | term_of_fm ps vs (Proc.Ge t') = \<^term>\<open>(<=) :: int => _ \<close> $ \<^term>\<open>0::int\<close> $ term_of_num vs t'
  | term_of_fm ps vs (Proc.Dvd (i, t')) = \<^term>\<open>(dvd) :: int => _ \<close> $
      HOLogic.mk_number HOLogic.intT (Proc.integer_of_int i) $ term_of_num vs t'
  | term_of_fm ps vs (Proc.NDvd (i, t')) = term_of_fm ps vs (Proc.NOT (Proc.Dvd (i, t')))
  | term_of_fm ps vs (Proc.Closed n) = nth ps (Proc.integer_of_nat n)
  | term_of_fm ps vs (Proc.NClosed n) = term_of_fm ps vs (Proc.NOT (Proc.Closed n));

fun procedure t =
  let
    val vs = Term.add_frees t [];
    val ps = add_bools t [];
  in (term_of_fm ps vs o Proc.pa o fm_of_term ps vs) t end;

end;

val (_, oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (\<^binding>\<open>cooper\<close>,
    (fn (ctxt, t) =>
      (Thm.cterm_of ctxt o Logic.mk_equals o apply2 HOLogic.mk_Trueprop)
        (t, procedure t)))));

val comp_ss =
  simpset_of (put_simpset HOL_ss \<^context> addsimps @{thms semiring_norm});

fun strip_objimp ct =
  (case Thm.term_of ct of
    Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
      let val (A, B) = Thm.dest_binop ct
      in A :: strip_objimp B end
  | _ => [ct]);

fun strip_objall ct =
 case Thm.term_of ct of
  Const (\<^const_name>\<open>All\<close>, _) $ Abs _ =>
   let val (a,(v,t')) = (apsnd Thm.dest_abs_global o Thm.dest_comb) ct
   in apfst (cons (a,v)) (strip_objall t')
   end
| _ => ([],ct);

local
  val all_maxscope_ss =
    simpset_of (put_simpset HOL_basic_ss \<^context>
      addsimps map (fn th => th RS sym) @{thms "all_simps"})
in
fun thin_prems_tac ctxt P =
  simp_tac (put_simpset all_maxscope_ss ctxt) THEN'
  CSUBGOAL (fn (p', i) =>
    let
     val (qvs, p) = strip_objall (Thm.dest_arg p')
     val (ps, c) = split_last (strip_objimp p)
     val qs = filter P ps
     val q = if P c then c else \<^cterm>\<open>False\<close>
     val ng = fold_rev (fn (a,v) => fn t => Thm.apply a (Thm.lambda v t)) qvs
         (fold_rev (fn p => fn q => Thm.apply (Thm.apply \<^cterm>\<open>HOL.implies\<close> p) q) qs q)
     val g = Thm.apply (Thm.apply \<^cterm>\<open>(==>)\<close> (Thm.apply \<^cterm>\<open>Trueprop\<close> ng)) p'
     val ntac = (case qs of [] => q aconvc \<^cterm>\<open>False\<close>
                         | _ => false)
    in
      if ntac then no_tac
      else
        (case \<^try>\<open>Goal.prove_internal ctxt [] g
            (fn {context = goal_ctxt, ...} => blast_tac (put_claset HOL_cs goal_ctxt) 1)\<close> of
          NONE => no_tac
        | SOME r => resolve_tac ctxt [r] i)
    end)
end;

local
 fun isnum t = case t of
   Const(\<^const_name>\<open>Groups.zero\<close>,_) => true
 | Const(\<^const_name>\<open>Groups.one\<close>,_) => true
 | \<^term>\<open>Suc\<close>$s => isnum s
 | \<^term>\<open>nat\<close>$s => isnum s
 | \<^term>\<open>int\<close>$s => isnum s
 | Const(\<^const_name>\<open>Groups.uminus\<close>,_)$s => isnum s
 | Const(\<^const_name>\<open>Groups.plus\<close>,_)$l$r => isnum l andalso isnum r
 | Const(\<^const_name>\<open>Groups.times\<close>,_)$l$r => isnum l andalso isnum r
 | Const(\<^const_name>\<open>Groups.minus\<close>,_)$l$r => isnum l andalso isnum r
 | Const(\<^const_name>\<open>Power.power\<close>,_)$l$r => isnum l andalso isnum r
 | Const(\<^const_name>\<open>Rings.modulo\<close>,_)$l$r => isnum l andalso isnum r
 | Const(\<^const_name>\<open>Rings.divide\<close>,_)$l$r => isnum l andalso isnum r
 | _ => is_number t orelse can HOLogic.dest_nat t

 fun ty cts t =
  if not (member (op =) [HOLogic.intT, HOLogic.natT, HOLogic.boolT] (Thm.typ_of_cterm t))
  then false
  else case Thm.term_of t of
    c$l$r => if member (op =) [\<^term>\<open>(*)::int => _\<close>, \<^term>\<open>(*)::nat => _\<close>] c
             then not (isnum l orelse isnum r)
             else not (member (op aconv) cts c)
  | c$_ => not (member (op aconv) cts c)
  | c => not (member (op aconv) cts c)

 val term_constants =
  let fun h acc t = case t of
    Const _ => insert (op aconv) t acc
  | a$b => h (h acc a) b
  | Abs (_,_,t) => h acc t
  | _ => acc
 in h [] end;
in
fun is_relevant ctxt ct =
 subset (op aconv) (term_constants (Thm.term_of ct), snd (get ctxt))
 andalso
  forall (fn Free (_, T) => member (op =) [\<^typ>\<open>int\<close>, \<^typ>\<open>nat\<close>] T)
    (Misc_Legacy.term_frees (Thm.term_of ct))
 andalso
  forall (fn Var (_, T) => member (op =) [\<^typ>\<open>int\<close>, \<^typ>\<open>nat\<close>] T)
    (Misc_Legacy.term_vars (Thm.term_of ct));

fun int_nat_terms ctxt ct =
 let
  val cts = snd (get ctxt)
  fun h acc t = if ty cts t then insert (op aconvc) t acc else
   case Thm.term_of t of
    _$_ => h (h acc (Thm.dest_arg t)) (Thm.dest_fun t)
  | Abs _ => Thm.dest_abs_global t ||> h acc |> uncurry (remove (op aconvc))
  | _ => acc
 in h [] ct end
end;

fun generalize_tac ctxt f = CSUBGOAL (fn (p, _) => PRIMITIVE (fn st =>
 let
   fun all x t =
    Thm.apply (Thm.cterm_of ctxt (Logic.all_const (Thm.typ_of_cterm x))) (Thm.lambda x t)
   val ts = sort Thm.fast_term_ord (f p)
   val p' = fold_rev all ts p
 in Thm.implies_intr p' (Thm.implies_elim st (fold Thm.forall_elim ts (Thm.assume p'))) end));

local
val ss1 =
  simpset_of (put_simpset comp_ss \<^context>
    addsimps @{thms simp_thms} @
            [@{thm "nat_numeral"} RS sym, @{thm int_dvd_int_iff [symmetric]}, @{thm "of_nat_add"}, @{thm "of_nat_mult"}]
        @ map (fn r => r RS sym) [@{thm "int_int_eq"}, @{thm "zle_int"}, @{thm "of_nat_less_iff" [where ?'a = int]}]
    |> Splitter.add_split @{thm "zdiff_int_split"})

val ss2 =
  simpset_of (put_simpset HOL_basic_ss \<^context>
    addsimps [@{thm "nat_0_le"}, @{thm "of_nat_numeral"},
              @{thm "all_nat"}, @{thm "ex_nat"}, @{thm "zero_le_numeral"},
              @{thm "le_numeral_extra"(3)}, @{thm "of_nat_0"}, @{thm "of_nat_1"}, @{thm "Suc_eq_plus1"}]
    |> fold Simplifier.add_cong [@{thm "conj_le_cong"}, @{thm "imp_le_cong"}])
val div_mod_ss =
  simpset_of (put_simpset HOL_basic_ss \<^context>
    addsimps @{thms simp_thms
      mod_eq_0_iff_dvd mod_add_left_eq mod_add_right_eq
      mod_add_eq div_add1_eq [symmetric] div_add1_eq [symmetric]
      mod_self mod_by_0 div_by_0
      div_0 mod_0 div_by_1 mod_by_1
      div_by_Suc_0 mod_by_Suc_0 Suc_eq_plus1
      ac_simps}
   addsimprocs [\<^simproc>\<open>cancel_div_mod_nat\<close>, \<^simproc>\<open>cancel_div_mod_int\<close>])
val splits_ss =
  simpset_of (put_simpset comp_ss \<^context>
    addsimps [@{thm minus_div_mult_eq_mod [symmetric]}]
    |> fold Splitter.add_split
      [@{thm "split_zdiv"}, @{thm "split_zmod"}, @{thm "split_div'"},
       @{thm "split_min"}, @{thm "split_max"}, @{thm "abs_split"}])
in

fun nat_to_int_tac ctxt =
  simp_tac (put_simpset ss1 ctxt) THEN_ALL_NEW
  simp_tac (put_simpset ss2 ctxt) THEN_ALL_NEW
  simp_tac (put_simpset comp_ss ctxt);

fun div_mod_tac ctxt = simp_tac (put_simpset div_mod_ss ctxt);
fun splits_tac ctxt = simp_tac (put_simpset splits_ss ctxt);

end;

fun core_tac ctxt = CSUBGOAL (fn (p, i) =>
   let
     val cpth =
       if Config.get ctxt quick_and_dirty
       then oracle (ctxt, Envir.beta_norm (Envir.eta_long [] (Thm.term_of (Thm.dest_arg p))))
       else Conv.arg_conv (conv ctxt) p
     val p' = Thm.rhs_of cpth
     val th = Thm.implies_intr p' (Thm.equal_elim (Thm.symmetric cpth) (Thm.assume p'))
   in resolve_tac ctxt [th] i end
   handle COOPER _ => no_tac);

fun finish_tac ctxt q = SUBGOAL (fn (_, i) =>
  (if q then I else TRY) (resolve_tac ctxt [TrueI] i));

fun tac elim add_ths del_ths = Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
  let
    val simpset_ctxt =
      put_simpset (fst (get ctxt)) ctxt delsimps del_ths addsimps add_ths
  in
    Method.insert_tac ctxt (rev (Named_Theorems.get ctxt \<^named_theorems>\<open>arith\<close>))
    THEN_ALL_NEW Object_Logic.full_atomize_tac ctxt
    THEN_ALL_NEW CONVERSION Thm.eta_long_conversion
    THEN_ALL_NEW simp_tac simpset_ctxt
    THEN_ALL_NEW (TRY o generalize_tac ctxt (int_nat_terms ctxt))
    THEN_ALL_NEW Object_Logic.full_atomize_tac ctxt
    THEN_ALL_NEW (thin_prems_tac ctxt (is_relevant ctxt))
    THEN_ALL_NEW Object_Logic.full_atomize_tac ctxt
    THEN_ALL_NEW div_mod_tac ctxt
    THEN_ALL_NEW splits_tac ctxt
    THEN_ALL_NEW simp_tac simpset_ctxt
    THEN_ALL_NEW CONVERSION Thm.eta_long_conversion
    THEN_ALL_NEW nat_to_int_tac ctxt
    THEN_ALL_NEW core_tac ctxt
    THEN_ALL_NEW finish_tac ctxt elim
  end 1);


(* attribute syntax *)

local

fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();

val constsN = "consts";
val any_keyword = keyword constsN
val thms = Scan.repeats (Scan.unless any_keyword Attrib.multi_thm);
val terms = thms >> map (Thm.term_of o Drule.dest_term);

fun optional scan = Scan.optional scan [];

in

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>presburger\<close>
      ((Scan.lift (Args.$$$ "del") |-- optional (keyword constsN |-- terms)) >> del ||
        optional (keyword constsN |-- terms) >> add) "data for Cooper's algorithm"
    #> Arith_Data.add_tactic "Presburger arithmetic" (tac true [] []));

end;

end;
