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
  val setup: theory -> theory
end;

structure Cooper: COOPER =
struct

type entry = simpset * term list;

val allowed_consts = 
  [@{term "op + :: int => _"}, @{term "op + :: nat => _"},
   @{term "op - :: int => _"}, @{term "op - :: nat => _"},
   @{term "op * :: int => _"}, @{term "op * :: nat => _"},
   @{term "op div :: int => _"}, @{term "op div :: nat => _"},
   @{term "op mod :: int => _"}, @{term "op mod :: nat => _"},
   @{term HOL.conj}, @{term HOL.disj}, @{term HOL.implies}, 
   @{term "op = :: int => _"}, @{term "op = :: nat => _"}, @{term "op = :: bool => _"},
   @{term "op < :: int => _"}, @{term "op < :: nat => _"},
   @{term "op <= :: int => _"}, @{term "op <= :: nat => _"},
   @{term "op dvd :: int => _"}, @{term "op dvd :: nat => _"},
   @{term "abs :: int => _"},
   @{term "max :: int => _"}, @{term "max :: nat => _"},
   @{term "min :: int => _"}, @{term "min :: nat => _"},
   @{term "uminus :: int => _"}, (*@ {term "uminus :: nat => _"},*)
   @{term "Not"}, @{term Suc},
   @{term "Ex :: (int => _) => _"}, @{term "Ex :: (nat => _) => _"},
   @{term "All :: (int => _) => _"}, @{term "All :: (nat => _) => _"},
   @{term "nat"}, @{term "int"},
   @{term "Num.One"}, @{term "Num.Bit0"}, @{term "Num.Bit1"},
   @{term "Num.numeral :: num => int"}, @{term "Num.numeral :: num => nat"},
   @{term "Num.neg_numeral :: num => int"},
   @{term "0::int"}, @{term "1::int"}, @{term "0::nat"}, @{term "1::nat"},
   @{term "True"}, @{term "False"}];

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
  context |> Data.map (fn (ss,ts') => 
     (ss addsimps [th], merge (op aconv) (ts',ts) ))) 

fun del ts = Thm.declaration_attribute (fn th => fn context => 
  context |> Data.map (fn (ss,ts') => 
     (ss delsimps [th], subtract (op aconv) ts' ts ))) 

fun simp_thms_conv ctxt =
  Simplifier.rewrite (Simplifier.context ctxt HOL_basic_ss addsimps @{thms simp_thms});
val FWD = Drule.implies_elim_list;

val true_tm = @{cterm "True"};
val false_tm = @{cterm "False"};
val zdvd1_eq = @{thm "zdvd1_eq"};
val presburger_ss = @{simpset} addsimps [zdvd1_eq];
val lin_ss =
  presburger_ss addsimps (@{thm dvd_eq_mod_eq_0} :: zdvd1_eq :: @{thms add_ac [where 'a=int]});

val iT = HOLogic.intT
val bT = HOLogic.boolT;
val dest_number = HOLogic.dest_number #> snd;
val perhaps_number = try dest_number;
val is_number = can dest_number;

val [miconj, midisj, mieq, mineq, milt, mile, migt, mige, midvd, mindvd, miP] =
    map(instantiate' [SOME @{ctyp "int"}] []) @{thms "minf"};

val [infDconj, infDdisj, infDdvd,infDndvd,infDP] =
    map(instantiate' [SOME @{ctyp "int"}] []) @{thms "inf_period"};

val [piconj, pidisj, pieq,pineq,pilt,pile,pigt,pige,pidvd,pindvd,piP] =
    map (instantiate' [SOME @{ctyp "int"}] []) @{thms "pinf"};

val [miP, piP] = map (instantiate' [SOME @{ctyp "bool"}] []) [miP, piP];

val infDP = instantiate' (map SOME [@{ctyp "int"}, @{ctyp "bool"}]) [] infDP;

val [[asetconj, asetdisj, aseteq, asetneq, asetlt, asetle,
      asetgt, asetge, asetdvd, asetndvd,asetP],
     [bsetconj, bsetdisj, bseteq, bsetneq, bsetlt, bsetle,
      bsetgt, bsetge, bsetdvd, bsetndvd,bsetP]]  = [@{thms "aset"}, @{thms "bset"}];

val [cpmi, cppi] = [@{thm "cpmi"}, @{thm "cppi"}];

val unity_coeff_ex = instantiate' [SOME @{ctyp "int"}] [] @{thm "unity_coeff_ex"};

val [zdvd_mono,simp_from_to,all_not_ex] =
     [@{thm "zdvd_mono"}, @{thm "simp_from_to"}, @{thm "all_not_ex"}];

val [dvd_uminus, dvd_uminus'] = @{thms "uminus_dvd_conv"};

val eval_ss = presburger_ss addsimps [simp_from_to] delsimps [insert_iff,bex_triv];
val eval_conv = Simplifier.rewrite eval_ss;

(* recognising cterm without moving to terms *)

datatype fm = And of cterm*cterm| Or of cterm*cterm| Eq of cterm | NEq of cterm
            | Lt of cterm | Le of cterm | Gt of cterm | Ge of cterm
            | Dvd of cterm*cterm | NDvd of cterm*cterm | Nox

fun whatis x ct =
( case (term_of ct) of
  Const(@{const_name HOL.conj},_)$_$_ => And (Thm.dest_binop ct)
| Const (@{const_name HOL.disj},_)$_$_ => Or (Thm.dest_binop ct)
| Const (@{const_name HOL.eq},_)$y$_ => if term_of x aconv y then Eq (Thm.dest_arg ct) else Nox
| Const (@{const_name Not},_) $ (Const (@{const_name HOL.eq},_)$y$_) =>
  if term_of x aconv y then NEq (funpow 2 Thm.dest_arg ct) else Nox
| Const (@{const_name Orderings.less}, _) $ y$ z =>
   if term_of x aconv y then Lt (Thm.dest_arg ct)
   else if term_of x aconv z then Gt (Thm.dest_arg1 ct) else Nox
| Const (@{const_name Orderings.less_eq}, _) $ y $ z =>
   if term_of x aconv y then Le (Thm.dest_arg ct)
   else if term_of x aconv z then Ge (Thm.dest_arg1 ct) else Nox
| Const (@{const_name Rings.dvd},_)$_$(Const(@{const_name Groups.plus},_)$y$_) =>
   if term_of x aconv y then Dvd (Thm.dest_binop ct ||> Thm.dest_arg) else Nox
| Const (@{const_name Not},_) $ (Const (@{const_name Rings.dvd},_)$_$(Const(@{const_name Groups.plus},_)$y$_)) =>
   if term_of x aconv y then
   NDvd (Thm.dest_binop (Thm.dest_arg ct) ||> Thm.dest_arg) else Nox
| _ => Nox)
  handle CTERM _ => Nox;

fun get_pmi_term t =
  let val (x,eq) =
     (Thm.dest_abs NONE o Thm.dest_arg o snd o Thm.dest_abs NONE o Thm.dest_arg)
        (Thm.dest_arg t)
in (Thm.lambda x o Thm.dest_arg o Thm.dest_arg) eq end;

val get_pmi = get_pmi_term o cprop_of;

val p_v' = @{cpat "?P' :: int => bool"};
val q_v' = @{cpat "?Q' :: int => bool"};
val p_v = @{cpat "?P:: int => bool"};
val q_v = @{cpat "?Q:: int => bool"};

fun myfwd (th1, th2, th3) p q
      [(th_1,th_2,th_3), (th_1',th_2',th_3')] =
  let
   val (mp', mq') = (get_pmi th_1, get_pmi th_1')
   val mi_th = FWD (Drule.instantiate_normalize ([],[(p_v,p),(q_v,q), (p_v',mp'),(q_v',mq')]) th1)
                   [th_1, th_1']
   val infD_th = FWD (Drule.instantiate_normalize ([],[(p_v,mp'), (q_v, mq')]) th3) [th_3,th_3']
   val set_th = FWD (Drule.instantiate_normalize ([],[(p_v,p), (q_v,q)]) th2) [th_2, th_2']
  in (mi_th, set_th, infD_th)
  end;

val inst' = fn cts => instantiate' [] (map SOME cts);
val infDTrue = instantiate' [] [SOME true_tm] infDP;
val infDFalse = instantiate' [] [SOME false_tm] infDP;

val cadd =  @{cterm "op + :: int => _"}
val cmulC =  @{cterm "op * :: int => _"}
val cminus =  @{cterm "op - :: int => _"}
val cone =  @{cterm "1 :: int"}
val [addC, mulC, subC] = map term_of [cadd, cmulC, cminus]
val [zero, one] = [@{term "0 :: int"}, @{term "1 :: int"}];

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
  (fn _ => EVERY [simp_tac lin_ss 1, TRY (Lin_Arith.tac ctxt 1)]);
fun linear_cmul 0 tm = zero
  | linear_cmul n tm = case tm of
      Const (@{const_name Groups.plus}, _) $ a $ b => addC $ linear_cmul n a $ linear_cmul n b
    | Const (@{const_name Groups.times}, _) $ c $ x => mulC $ numeral1 (fn m => n * m) c $ x
    | Const (@{const_name Groups.minus}, _) $ a $ b => subC $ linear_cmul n a $ linear_cmul n b
    | (m as Const (@{const_name Groups.uminus}, _)) $ a => m $ linear_cmul n a
    | _ => numeral1 (fn m => n * m) tm;
fun earlier [] x y = false
  | earlier (h::t) x y =
    if h aconv y then false else if h aconv x then true else earlier t x y;

fun linear_add vars tm1 tm2 = case (tm1, tm2) of
    (Const (@{const_name Groups.plus}, _) $ (Const (@{const_name Groups.times}, _) $ c1 $ x1) $ r1,
    Const (@{const_name Groups.plus}, _) $ (Const (@{const_name Groups.times}, _) $ c2 $ x2) $ r2) =>
   if x1 = x2 then
     let val c = numeral2 Integer.add c1 c2
      in if c = zero then linear_add vars r1 r2
         else addC$(mulC$c$x1)$(linear_add vars r1 r2)
     end
     else if earlier vars x1 x2 then addC $ (mulC $ c1 $ x1) $ linear_add vars r1 tm2
   else addC $ (mulC $ c2 $ x2) $ linear_add vars tm1 r2
 | (Const (@{const_name Groups.plus}, _) $ (Const (@{const_name Groups.times}, _) $ c1 $ x1) $ r1, _) =>
      addC $ (mulC $ c1 $ x1) $ linear_add vars r1 tm2
 | (_, Const (@{const_name Groups.plus}, _) $ (Const (@{const_name Groups.times}, _) $ c2 $ x2) $ r2) =>
      addC $ (mulC $ c2 $ x2) $ linear_add vars tm1 r2
 | (_, _) => numeral2 Integer.add tm1 tm2;

fun linear_neg tm = linear_cmul ~1 tm;
fun linear_sub vars tm1 tm2 = linear_add vars tm1 (linear_neg tm2);

exception COOPER of string;

fun lint vars tm =  if is_number tm then tm  else case tm of
  Const (@{const_name Groups.uminus}, _) $ t => linear_neg (lint vars t)
| Const (@{const_name Groups.plus}, _) $ s $ t => linear_add vars (lint vars s) (lint vars t)
| Const (@{const_name Groups.minus}, _) $ s $ t => linear_sub vars (lint vars s) (lint vars t)
| Const (@{const_name Groups.times}, _) $ s $ t =>
  let val s' = lint vars s
      val t' = lint vars t
  in case perhaps_number s' of SOME n => linear_cmul n t'
   | NONE => (case perhaps_number t' of SOME n => linear_cmul n s'
   | NONE => raise COOPER "lint: not linear")
  end
 | _ => addC $ (mulC $ one $ tm) $ zero;

fun lin (vs as x::_) (Const (@{const_name Not}, _) $ (Const (@{const_name Orderings.less}, T) $ s $ t)) =
    lin vs (Const (@{const_name Orderings.less_eq}, T) $ t $ s)
  | lin (vs as x::_) (Const (@{const_name Not},_) $ (Const(@{const_name Orderings.less_eq}, T) $ s $ t)) =
    lin vs (Const (@{const_name Orderings.less}, T) $ t $ s)
  | lin vs (Const (@{const_name Not},T)$t) = Const (@{const_name Not},T)$ (lin vs t)
  | lin (vs as x::_) (Const(@{const_name Rings.dvd},_)$d$t) =
    HOLogic.mk_binrel @{const_name Rings.dvd} (numeral1 abs d, lint vs t)
  | lin (vs as x::_) ((b as Const(@{const_name HOL.eq},_))$s$t) =
     (case lint vs (subC$t$s) of
      (t as a$(m$c$y)$r) =>
        if x <> y then b$zero$t
        else if dest_number c < 0 then b$(m$(numeral1 ~ c)$y)$r
        else b$(m$c$y)$(linear_neg r)
      | t => b$zero$t)
  | lin (vs as x::_) (b$s$t) =
     (case lint vs (subC$t$s) of
      (t as a$(m$c$y)$r) =>
        if x <> y then b$zero$t
        else if dest_number c < 0 then b$(m$(numeral1 ~ c)$y)$r
        else b$(linear_neg r)$(m$c$y)
      | t => b$zero$t)
  | lin vs fm = fm;

fun lint_conv ctxt vs ct =
let val t = term_of ct
in (provelin ctxt ((HOLogic.eq_const iT)$t$(lint vs t) |> HOLogic.mk_Trueprop))
             RS eq_reflection
end;

fun is_intrel_type T = T = @{typ "int => int => bool"};

fun is_intrel (b$_$_) = is_intrel_type (fastype_of b)
  | is_intrel (@{term "Not"}$(b$_$_)) = is_intrel_type (fastype_of b)
  | is_intrel _ = false;

fun linearize_conv ctxt vs ct = case term_of ct of
  Const(@{const_name Rings.dvd},_)$d$t =>
  let
    val th = Conv.binop_conv (lint_conv ctxt vs) ct
    val (d',t') = Thm.dest_binop (Thm.rhs_of th)
    val (dt',tt') = (term_of d', term_of t')
  in if is_number dt' andalso is_number tt'
     then Conv.fconv_rule (Conv.arg_conv (Simplifier.rewrite presburger_ss)) th
     else
     let
      val dth =
      ((if dest_number (term_of d') < 0 then
          Conv.fconv_rule (Conv.arg_conv (Conv.arg1_conv (lint_conv ctxt vs)))
                           (Thm.transitive th (inst' [d',t'] dvd_uminus))
        else th) handle TERM _ => th)
      val d'' = Thm.rhs_of dth |> Thm.dest_arg1
     in
      case tt' of
        Const(@{const_name Groups.plus},_)$(Const(@{const_name Groups.times},_)$c$_)$_ =>
        let val x = dest_number c
        in if x < 0 then Conv.fconv_rule (Conv.arg_conv (Conv.arg_conv (lint_conv ctxt vs)))
                                       (Thm.transitive dth (inst' [d'',t'] dvd_uminus'))
        else dth end
      | _ => dth
     end
  end
| Const (@{const_name Not},_)$(Const(@{const_name Rings.dvd},_)$_$_) => Conv.arg_conv (linearize_conv ctxt vs) ct
| t => if is_intrel t
      then (provelin ctxt ((HOLogic.eq_const bT)$t$(lin vs t) |> HOLogic.mk_Trueprop))
       RS eq_reflection
      else Thm.reflexive ct;

val dvdc = @{cterm "op dvd :: int => _"};

fun unify ctxt q =
 let
  val (e,(cx,p)) = q |> Thm.dest_comb ||> Thm.dest_abs NONE
  val x = term_of cx
  val ins = insert (op = : int * int -> bool)
  fun h (acc,dacc) t =
   case (term_of t) of
    Const(s,_)$(Const(@{const_name Groups.times},_)$c$y)$ _ =>
    if x aconv y andalso member (op =)
      [@{const_name HOL.eq}, @{const_name Orderings.less}, @{const_name Orderings.less_eq}] s
    then (ins (dest_number c) acc,dacc) else (acc,dacc)
  | Const(s,_)$_$(Const(@{const_name Groups.times},_)$c$y) =>
    if x aconv y andalso member (op =)
       [@{const_name Orderings.less}, @{const_name Orderings.less_eq}] s
    then (ins (dest_number c) acc, dacc) else (acc,dacc)
  | Const(@{const_name Rings.dvd},_)$_$(Const(@{const_name Groups.plus},_)$(Const(@{const_name Groups.times},_)$c$y)$_) =>
    if x aconv y then (acc,ins (dest_number c) dacc) else (acc,dacc)
  | Const(@{const_name HOL.conj},_)$_$_ => h (h (acc,dacc) (Thm.dest_arg1 t)) (Thm.dest_arg t)
  | Const(@{const_name HOL.disj},_)$_$_ => h (h (acc,dacc) (Thm.dest_arg1 t)) (Thm.dest_arg t)
  | Const (@{const_name Not},_)$_ => h (acc,dacc) (Thm.dest_arg t)
  | _ => (acc, dacc)
  val (cs,ds) = h ([],[]) p
  val l = Integer.lcms (union (op =) cs ds)
  fun cv k ct =
    let val (tm as b$s$t) = term_of ct
    in ((HOLogic.eq_const bT)$tm$(b$(linear_cmul k s)$(linear_cmul k t))
         |> HOLogic.mk_Trueprop |> provelin ctxt) RS eq_reflection end
  fun nzprop x =
   let
    val th =
     Simplifier.rewrite lin_ss
      (Thm.apply @{cterm Trueprop} (Thm.apply @{cterm "Not"}
           (Thm.apply (Thm.apply @{cterm "op = :: int => _"} (Numeral.mk_cnumber @{ctyp "int"} x))
           @{cterm "0::int"})))
   in Thm.equal_elim (Thm.symmetric th) TrueI end;
  val notz =
    let val tab = fold Inttab.update
          (ds ~~ (map (fn x => nzprop (l div x)) ds)) Inttab.empty
    in
      fn ct => the (Inttab.lookup tab (ct |> term_of |> dest_number))
        handle Option =>
          (writeln ("noz: Theorems-Table contains no entry for " ^
              Syntax.string_of_term ctxt (Thm.term_of ct)); raise Option)
    end
  fun unit_conv t =
   case (term_of t) of
   Const(@{const_name HOL.conj},_)$_$_ => Conv.binop_conv unit_conv t
  | Const(@{const_name HOL.disj},_)$_$_ => Conv.binop_conv unit_conv t
  | Const (@{const_name Not},_)$_ => Conv.arg_conv unit_conv t
  | Const(s,_)$(Const(@{const_name Groups.times},_)$c$y)$ _ =>
    if x=y andalso member (op =)
      [@{const_name HOL.eq}, @{const_name Orderings.less}, @{const_name Orderings.less_eq}] s
    then cv (l div dest_number c) t else Thm.reflexive t
  | Const(s,_)$_$(Const(@{const_name Groups.times},_)$c$y) =>
    if x=y andalso member (op =)
      [@{const_name Orderings.less}, @{const_name Orderings.less_eq}] s
    then cv (l div dest_number c) t else Thm.reflexive t
  | Const(@{const_name Rings.dvd},_)$d$(r as (Const(@{const_name Groups.plus},_)$(Const(@{const_name Groups.times},_)$c$y)$_)) =>
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
  val clt =  Numeral.mk_cnumber @{ctyp "int"} l
  val ltx = Thm.apply (Thm.apply cmulC clt) cx
  val th = Drule.arg_cong_rule e (Thm.abstract_rule (fst (dest_Free x )) cx uth)
  val th' = inst' [Thm.lambda ltx (Thm.rhs_of uth), clt] unity_coeff_ex
  val thf = Thm.transitive th
      (Thm.transitive (Thm.symmetric (Thm.beta_conversion true (cprop_of th' |> Thm.dest_arg1))) th')
  val (lth,rth) = Thm.dest_comb (cprop_of thf) |>> Thm.dest_arg |>> Thm.beta_conversion true
                  ||> Thm.beta_conversion true |>> Thm.symmetric
 in Thm.transitive (Thm.transitive lth thf) rth end;


val emptyIS = @{cterm "{}::int set"};
val insert_tm = @{cterm "insert :: int => _"};
fun mkISet cts = fold_rev (Thm.apply insert_tm #> Thm.apply) cts emptyIS;
val eqelem_imp_imp = @{thm eqelem_imp_iff} RS iffD1;
val [A_tm,B_tm] = map (fn th => cprop_of th |> funpow 2 Thm.dest_arg |> Thm.dest_abs NONE |> snd |> Thm.dest_arg1 |> Thm.dest_arg
                                      |> Thm.dest_abs NONE |> snd |> Thm.dest_fun |> Thm.dest_arg)
                      [asetP,bsetP];

val D_tm = @{cpat "?D::int"};

fun cooperex_conv ctxt vs q =
let

 val uth = unify ctxt q
 val (x,p) = Thm.dest_abs NONE (Thm.dest_arg (Thm.rhs_of uth))
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
  | Dvd (d,_) => (bacc,aacc,insert (op =) (term_of d |> dest_number) dacc)
  | NDvd (d,_) => (bacc,aacc,insert (op =) (term_of d|> dest_number) dacc)
  | _ => (bacc, aacc, dacc)
 val (b0,a0,ds) = h p ([],[],[])
 val d = Integer.lcms ds
 val cd = Numeral.mk_cnumber @{ctyp "int"} d
 fun divprop x =
   let
    val th =
     Simplifier.rewrite lin_ss
      (Thm.apply @{cterm Trueprop}
           (Thm.apply (Thm.apply dvdc (Numeral.mk_cnumber @{ctyp "int"} x)) cd))
   in Thm.equal_elim (Thm.symmetric th) TrueI end;
 val dvd =
   let val tab = fold Inttab.update (ds ~~ (map divprop ds)) Inttab.empty in
     fn ct => the (Inttab.lookup tab (term_of ct |> dest_number))
       handle Option =>
        (writeln ("dvd: Theorems-Table contains no entry for" ^
            Syntax.string_of_term ctxt (Thm.term_of ct)); raise Option)
   end
 val dp =
   let val th = Simplifier.rewrite lin_ss
      (Thm.apply @{cterm Trueprop}
           (Thm.apply (Thm.apply @{cterm "op < :: int => _"} @{cterm "0::int"}) cd))
   in Thm.equal_elim (Thm.symmetric th) TrueI end;
    (* A and B set *)
   local
     val insI1 = instantiate' [SOME @{ctyp "int"}] [] @{thm "insertI1"}
     val insI2 = instantiate' [SOME @{ctyp "int"}] [] @{thm "insertI2"}
   in
    fun provein x S =
     case term_of S of
        Const(@{const_name Orderings.bot}, _) => error "Unexpected error in Cooper, please email Amine Chaieb"
      | Const(@{const_name insert}, _) $ y $ _ =>
         let val (cy,S') = Thm.dest_binop S
         in if term_of x aconv y then instantiate' [] [SOME x, SOME S'] insI1
         else Thm.implies_elim (instantiate' [] [SOME x, SOME S', SOME cy] insI2)
                           (provein x S')
         end
   end

 val al = map (lint vs o term_of) a0
 val bl = map (lint vs o term_of) b0
 val (sl,s0,f,abths,cpth) =
   if length (distinct (op aconv) bl) <= length (distinct (op aconv) al)
   then
    (bl,b0,decomp_minf,
     fn B => (map (fn th => Thm.implies_elim (Thm.instantiate ([],[(B_tm,B), (D_tm,cd)]) th) dp)
                     [bseteq,bsetneq,bsetlt, bsetle, bsetgt,bsetge])@
                   (map (Thm.instantiate ([],[(B_tm,B), (D_tm,cd)]))
                        [bsetdvd,bsetndvd,bsetP,infDdvd, infDndvd,bsetconj,
                         bsetdisj,infDconj, infDdisj]),
                       cpmi)
     else (al,a0,decomp_pinf,fn A =>
          (map (fn th => Thm.implies_elim (Thm.instantiate ([],[(A_tm,A), (D_tm,cd)]) th) dp)
                   [aseteq,asetneq,asetlt, asetle, asetgt,asetge])@
                   (map (Thm.instantiate ([],[(A_tm,A), (D_tm,cd)]))
                   [asetdvd,asetndvd, asetP, infDdvd, infDndvd,asetconj,
                         asetdisj,infDconj, infDdisj]),cppi)
 val cpth =
  let
   val sths = map (fn (tl,t0) =>
                      if tl = term_of t0
                      then instantiate' [SOME @{ctyp "int"}] [SOME t0] refl
                      else provelin ctxt ((HOLogic.eq_const iT)$tl$(term_of t0)
                                 |> HOLogic.mk_Trueprop))
                   (sl ~~ s0)
   val csl = distinct (op aconvc) (map (cprop_of #> Thm.dest_arg #> Thm.dest_arg1) sths)
   val S = mkISet csl
   val inStab = fold (fn ct => fn tab => Termtab.update (term_of ct, provein ct S) tab)
                    csl Termtab.empty
   val eqelem_th = instantiate' [SOME @{ctyp "int"}] [NONE,NONE, SOME S] eqelem_imp_imp
   val inS =
     let
      val tab = fold Termtab.update
        (map (fn eq =>
                let val (s,t) = cprop_of eq |> Thm.dest_arg |> Thm.dest_binop
                    val th = if term_of s = term_of t
                             then the (Termtab.lookup inStab (term_of s))
                             else FWD (instantiate' [] [SOME s, SOME t] eqelem_th)
                                [eq, the (Termtab.lookup inStab (term_of s))]
                 in (term_of t, th) end)
                  sths) Termtab.empty
        in
          fn ct => the (Termtab.lookup tab (term_of ct))
            handle Option =>
              (writeln ("inS: No theorem for " ^ Syntax.string_of_term ctxt (Thm.term_of ct));
                raise Option)
        end
       val (inf, nb, pd) = divide_and_conquer (f x dvd inS (abths S)) p
   in [dp, inf, nb, pd] MRS cpth
   end
 val cpth' = Thm.transitive uth (cpth RS eq_reflection)
in Thm.transitive cpth' ((simp_thms_conv ctxt then_conv eval_conv) (Thm.rhs_of cpth'))
end;

fun literals_conv bops uops env cv =
 let fun h t =
  case (term_of t) of
   b$_$_ => if member (op aconv) bops b then Conv.binop_conv h t else cv env t
 | u$_ => if member (op aconv) uops u then Conv.arg_conv h t else cv env t
 | _ => cv env t
 in h end;

fun integer_nnf_conv ctxt env =
 nnf_conv then_conv literals_conv [HOLogic.conj, HOLogic.disj] [] env (linearize_conv ctxt);

val conv_ss = HOL_basic_ss addsimps
  (@{thms simp_thms} @ take 4 @{thms ex_simps} @ [not_all, all_not_ex, @{thm ex_disj_distrib}]);

fun conv ctxt p =
  Qelim.gen_qelim_conv (Simplifier.rewrite conv_ss) (Simplifier.rewrite presburger_ss) (Simplifier.rewrite conv_ss)
    (cons o term_of) (Misc_Legacy.term_frees (term_of p)) (linearize_conv ctxt) (integer_nnf_conv ctxt)
    (cooperex_conv ctxt) p
  handle CTERM s => raise COOPER "bad cterm"
       | THM s => raise COOPER "bad thm"
       | TYPE s => raise COOPER "bad type"

fun add_bools t =
  let
    val ops = [@{term "op = :: int => _"}, @{term "op < :: int => _"}, @{term "op <= :: int => _"},
      @{term HOL.conj}, @{term HOL.disj}, @{term HOL.implies}, @{term "op = :: bool => _"},
      @{term "Not"}, @{term "All :: (int => _) => _"},
      @{term "Ex :: (int => _) => _"}, @{term "True"}, @{term "False"}];
    val is_op = member (op =) ops;
    val skip = not (fastype_of t = HOLogic.boolT)
  in case t of
      (l as f $ a) $ b => if skip orelse is_op f then add_bools b o add_bools l
              else insert (op aconv) t
    | f $ a => if skip orelse is_op f then add_bools a o add_bools f
              else insert (op aconv) t
    | Abs p => add_bools (snd (Syntax_Trans.variant_abs p))  (* FIXME !? *)
    | _ => if skip orelse is_op t then I else insert (op aconv) t
  end;

fun descend vs (abs as (_, xT, _)) =
  let
    val (xn', p') = Syntax_Trans.variant_abs abs;  (* FIXME !? *)
  in ((xn', xT) :: vs, p') end;

local structure Proc = Cooper_Procedure in

fun num_of_term vs (Free vT) = Proc.Bound (find_index (fn vT' => vT' = vT) vs)
  | num_of_term vs (Term.Bound i) = Proc.Bound i
  | num_of_term vs @{term "0::int"} = Proc.C 0
  | num_of_term vs @{term "1::int"} = Proc.C 1
  | num_of_term vs (t as Const (@{const_name numeral}, _) $ _) =
      Proc.C (dest_number t)
  | num_of_term vs (t as Const (@{const_name neg_numeral}, _) $ _) =
      Proc.Neg (Proc.C (dest_number t))
  | num_of_term vs (Const (@{const_name Groups.uminus}, _) $ t') =
      Proc.Neg (num_of_term vs t')
  | num_of_term vs (Const (@{const_name Groups.plus}, _) $ t1 $ t2) =
      Proc.Add (num_of_term vs t1, num_of_term vs t2)
  | num_of_term vs (Const (@{const_name Groups.minus}, _) $ t1 $ t2) =
      Proc.Sub (num_of_term vs t1, num_of_term vs t2)
  | num_of_term vs (Const (@{const_name Groups.times}, _) $ t1 $ t2) =
     (case perhaps_number t1
       of SOME n => Proc.Mul (n, num_of_term vs t2)
        | NONE => (case perhaps_number t2
           of SOME n => Proc.Mul (n, num_of_term vs t1)
            | NONE => raise COOPER "reification: unsupported kind of multiplication"))
  | num_of_term _ _ = raise COOPER "reification: bad term";

fun fm_of_term ps vs (Const (@{const_name True}, _)) = Proc.T
  | fm_of_term ps vs (Const (@{const_name False}, _)) = Proc.F
  | fm_of_term ps vs (Const (@{const_name HOL.conj}, _) $ t1 $ t2) =
      Proc.And (fm_of_term ps vs t1, fm_of_term ps vs t2)
  | fm_of_term ps vs (Const (@{const_name HOL.disj}, _) $ t1 $ t2) =
      Proc.Or (fm_of_term ps vs t1, fm_of_term ps vs t2)
  | fm_of_term ps vs (Const (@{const_name HOL.implies}, _) $ t1 $ t2) =
      Proc.Imp (fm_of_term ps vs t1, fm_of_term ps vs t2)
  | fm_of_term ps vs (@{term "op = :: bool => _ "} $ t1 $ t2) =
      Proc.Iff (fm_of_term ps vs t1, fm_of_term ps vs t2)
  | fm_of_term ps vs (Const (@{const_name Not}, _) $ t') =
      Proc.Not (fm_of_term ps vs t')
  | fm_of_term ps vs (Const (@{const_name Ex}, _) $ Abs abs) =
      Proc.E (uncurry (fm_of_term ps) (descend vs abs))
  | fm_of_term ps vs (Const (@{const_name All}, _) $ Abs abs) =
      Proc.A (uncurry (fm_of_term ps) (descend vs abs))
  | fm_of_term ps vs (@{term "op = :: int => _"} $ t1 $ t2) =
      Proc.Eq (Proc.Sub (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term ps vs (Const (@{const_name Orderings.less_eq}, _) $ t1 $ t2) =
      Proc.Le (Proc.Sub (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term ps vs (Const (@{const_name Orderings.less}, _) $ t1 $ t2) =
      Proc.Lt (Proc.Sub (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term ps vs (Const (@{const_name Rings.dvd}, _) $ t1 $ t2) =
     (case perhaps_number t1
       of SOME n => Proc.Dvd (n, num_of_term vs t2)
        | NONE => raise COOPER "reification: unsupported dvd")
  | fm_of_term ps vs t = let val n = find_index (fn t' => t aconv t') ps
      in if n > 0 then Proc.Closed n else raise COOPER "reification: unknown term" end;

fun term_of_num vs (Proc.C i) = HOLogic.mk_number HOLogic.intT i
  | term_of_num vs (Proc.Bound n) = Free (nth vs n)
  | term_of_num vs (Proc.Neg t') =
      @{term "uminus :: int => _"} $ term_of_num vs t'
  | term_of_num vs (Proc.Add (t1, t2)) =
      @{term "op + :: int => _"} $ term_of_num vs t1 $ term_of_num vs t2
  | term_of_num vs (Proc.Sub (t1, t2)) =
      @{term "op - :: int => _"} $ term_of_num vs t1 $ term_of_num vs t2
  | term_of_num vs (Proc.Mul (i, t2)) =
      @{term "op * :: int => _"} $ HOLogic.mk_number HOLogic.intT i $ term_of_num vs t2
  | term_of_num vs (Proc.Cn (n, i, t')) =
      term_of_num vs (Proc.Add (Proc.Mul (i, Proc.Bound n), t'));

fun term_of_fm ps vs Proc.T = @{term True}
  | term_of_fm ps vs Proc.F = @{term False}
  | term_of_fm ps vs (Proc.And (t1, t2)) = HOLogic.conj $ term_of_fm ps vs t1 $ term_of_fm ps vs t2
  | term_of_fm ps vs (Proc.Or (t1, t2)) = HOLogic.disj $ term_of_fm ps vs t1 $ term_of_fm ps vs t2
  | term_of_fm ps vs (Proc.Imp (t1, t2)) = HOLogic.imp $ term_of_fm ps vs t1 $ term_of_fm ps vs t2
  | term_of_fm ps vs (Proc.Iff (t1, t2)) = @{term "op = :: bool => _"} $ term_of_fm ps vs t1 $ term_of_fm ps vs t2
  | term_of_fm ps vs (Proc.Not t') = HOLogic.Not $ term_of_fm ps vs t'
  | term_of_fm ps vs (Proc.Eq t') = @{term "op = :: int => _ "} $ term_of_num vs t'$ @{term "0::int"}
  | term_of_fm ps vs (Proc.NEq t') = term_of_fm ps vs (Proc.Not (Proc.Eq t'))
  | term_of_fm ps vs (Proc.Lt t') = @{term "op < :: int => _ "} $ term_of_num vs t' $ @{term "0::int"}
  | term_of_fm ps vs (Proc.Le t') = @{term "op <= :: int => _ "} $ term_of_num vs t' $ @{term "0::int"}
  | term_of_fm ps vs (Proc.Gt t') = @{term "op < :: int => _ "} $ @{term "0::int"} $ term_of_num vs t'
  | term_of_fm ps vs (Proc.Ge t') = @{term "op <= :: int => _ "} $ @{term "0::int"} $ term_of_num vs t'
  | term_of_fm ps vs (Proc.Dvd (i, t')) = @{term "op dvd :: int => _ "} $
      HOLogic.mk_number HOLogic.intT i $ term_of_num vs t'
  | term_of_fm ps vs (Proc.NDvd (i, t')) = term_of_fm ps vs (Proc.Not (Proc.Dvd (i, t')))
  | term_of_fm ps vs (Proc.Closed n) = nth ps n
  | term_of_fm ps vs (Proc.NClosed n) = term_of_fm ps vs (Proc.Not (Proc.Closed n));

fun procedure t =
  let
    val vs = Term.add_frees t [];
    val ps = add_bools t [];
  in (term_of_fm ps vs o Proc.pa o fm_of_term ps vs) t end;

end;

val (_, oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (@{binding cooper},
    (fn (ctxt, t) =>
      (Thm.cterm_of (Proof_Context.theory_of ctxt) o Logic.mk_equals o pairself HOLogic.mk_Trueprop)
        (t, procedure t)))));

val comp_ss = HOL_ss addsimps @{thms semiring_norm};

fun strip_objimp ct =
  (case Thm.term_of ct of
    Const (@{const_name HOL.implies}, _) $ _ $ _ =>
      let val (A, B) = Thm.dest_binop ct
      in A :: strip_objimp B end
  | _ => [ct]);

fun strip_objall ct = 
 case term_of ct of 
  Const (@{const_name All}, _) $ Abs (xn,xT,p) => 
   let val (a,(v,t')) = (apsnd (Thm.dest_abs (SOME xn)) o Thm.dest_comb) ct
   in apfst (cons (a,v)) (strip_objall t')
   end
| _ => ([],ct);

local
  val all_maxscope_ss = 
     HOL_basic_ss addsimps map (fn th => th RS sym) @{thms "all_simps"}
in
fun thin_prems_tac ctxt P = simp_tac all_maxscope_ss THEN'
  CSUBGOAL (fn (p', i) =>
    let
     val (qvs, p) = strip_objall (Thm.dest_arg p')
     val (ps, c) = split_last (strip_objimp p)
     val qs = filter P ps
     val q = if P c then c else @{cterm "False"}
     val ng = fold_rev (fn (a,v) => fn t => Thm.apply a (Thm.lambda v t)) qvs 
         (fold_rev (fn p => fn q => Thm.apply (Thm.apply @{cterm HOL.implies} p) q) qs q)
     val g = Thm.apply (Thm.apply @{cterm "op ==>"} (Thm.apply @{cterm "Trueprop"} ng)) p'
     val ntac = (case qs of [] => q aconvc @{cterm "False"}
                         | _ => false)
    in 
    if ntac then no_tac
      else rtac (Goal.prove_internal [] g (K (blast_tac (put_claset HOL_cs ctxt) 1))) i
    end)
end;

local
 fun isnum t = case t of 
   Const(@{const_name Groups.zero},_) => true
 | Const(@{const_name Groups.one},_) => true
 | @{term Suc}$s => isnum s
 | @{term "nat"}$s => isnum s
 | @{term "int"}$s => isnum s
 | Const(@{const_name Groups.uminus},_)$s => isnum s
 | Const(@{const_name Groups.plus},_)$l$r => isnum l andalso isnum r
 | Const(@{const_name Groups.times},_)$l$r => isnum l andalso isnum r
 | Const(@{const_name Groups.minus},_)$l$r => isnum l andalso isnum r
 | Const(@{const_name Power.power},_)$l$r => isnum l andalso isnum r
 | Const(@{const_name Divides.mod},_)$l$r => isnum l andalso isnum r
 | Const(@{const_name Divides.div},_)$l$r => isnum l andalso isnum r
 | _ => is_number t orelse can HOLogic.dest_nat t

 fun ty cts t = 
 if not (member (op =) [HOLogic.intT, HOLogic.natT, HOLogic.boolT] (typ_of (ctyp_of_term t))) then false 
    else case term_of t of 
      c$l$r => if member (op =) [@{term"op *::int => _"}, @{term"op *::nat => _"}] c
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
 subset (op aconv) (term_constants (term_of ct) , snd (get ctxt))
 andalso forall (fn Free (_,T) => member (op =) [@{typ int}, @{typ nat}] T) (Misc_Legacy.term_frees (term_of ct))
 andalso forall (fn Var (_,T) => member (op =) [@{typ int}, @{typ nat}] T) (Misc_Legacy.term_vars (term_of ct));

fun int_nat_terms ctxt ct =
 let 
  val cts = snd (get ctxt)
  fun h acc t = if ty cts t then insert (op aconvc) t acc else
   case (term_of t) of
    _$_ => h (h acc (Thm.dest_arg t)) (Thm.dest_fun t)
  | Abs(_,_,_) => Thm.dest_abs NONE t ||> h acc |> uncurry (remove (op aconvc))
  | _ => acc
 in h [] ct end
end;

fun generalize_tac f = CSUBGOAL (fn (p, i) => PRIMITIVE (fn st =>
 let 
   fun all T = Drule.cterm_rule (instantiate' [SOME T] []) @{cpat "all"}
   fun gen x t = Thm.apply (all (ctyp_of_term x)) (Thm.lambda x t)
   val ts = sort (fn (a,b) => Term_Ord.fast_term_ord (term_of a, term_of b)) (f p)
   val p' = fold_rev gen ts p
 in Thm.implies_intr p' (Thm.implies_elim st (fold Thm.forall_elim ts (Thm.assume p'))) end));

local
val ss1 = comp_ss
  addsimps @{thms simp_thms} @ [@{thm "nat_numeral"} RS sym, @{thm "zdvd_int"}] 
      @ map (fn r => r RS sym) 
        [@{thm "int_int_eq"}, @{thm "zle_int"}, @{thm "zless_int"}, @{thm "zadd_int"}, 
         @{thm "zmult_int"}]
  |> Splitter.add_split @{thm "zdiff_int_split"}

val ss2 = HOL_basic_ss
  addsimps [@{thm "nat_0_le"}, @{thm "int_numeral"},
            @{thm "all_nat"}, @{thm "ex_nat"}, @{thm "zero_le_numeral"}, 
            @{thm "le_numeral_extra"(3)}, @{thm "int_0"}, @{thm "int_1"}, @{thm "Suc_eq_plus1"}]
  |> fold Simplifier.add_cong [@{thm "conj_le_cong"}, @{thm "imp_le_cong"}]
val div_mod_ss = HOL_basic_ss addsimps @{thms simp_thms}
  @ map (Thm.symmetric o mk_meta_eq) 
    [@{thm "dvd_eq_mod_eq_0"},
     @{thm "mod_add_left_eq"}, @{thm "mod_add_right_eq"}, 
     @{thm "mod_add_eq"}, @{thm "div_add1_eq"}, @{thm "zdiv_zadd1_eq"}]
  @ [@{thm "mod_self"}, @{thm "mod_by_0"}, @{thm "div_by_0"},
     @{thm "div_0"}, @{thm "mod_0"}, @{thm "div_by_1"}, @{thm "mod_by_1"}, @{thm "div_1"}, 
     @{thm "mod_1"}, @{thm "Suc_eq_plus1"}]
  @ @{thms add_ac}
 addsimprocs [@{simproc cancel_div_mod_nat}, @{simproc cancel_div_mod_int}]
val splits_ss =
  comp_ss addsimps [@{thm "mod_div_equality'"}]
  |> fold Splitter.add_split
    [@{thm "split_zdiv"}, @{thm "split_zmod"}, @{thm "split_div'"}, 
     @{thm "split_min"}, @{thm "split_max"}, @{thm "abs_split"}]
in
fun nat_to_int_tac ctxt = 
  simp_tac (Simplifier.context ctxt ss1) THEN_ALL_NEW
  simp_tac (Simplifier.context ctxt ss2) THEN_ALL_NEW
  simp_tac (Simplifier.context ctxt comp_ss);

fun div_mod_tac ctxt i = simp_tac (Simplifier.context ctxt div_mod_ss) i;
fun splits_tac ctxt i = simp_tac (Simplifier.context ctxt splits_ss) i;
end;

fun core_tac ctxt = CSUBGOAL (fn (p, i) =>
   let
    val cpth = 
       if !quick_and_dirty 
       then oracle (ctxt, Envir.beta_norm (Pattern.eta_long [] (term_of (Thm.dest_arg p))))
       else Conv.arg_conv (conv ctxt) p
    val p' = Thm.rhs_of cpth
    val th = Thm.implies_intr p' (Thm.equal_elim (Thm.symmetric cpth) (Thm.assume p'))
   in rtac th i end
   handle COOPER _ => no_tac);

fun finish_tac q = SUBGOAL (fn (_, i) =>
  (if q then I else TRY) (rtac TrueI i));

fun tac elim add_ths del_ths ctxt =
let val ss = Simplifier.context ctxt (fst (get ctxt)) delsimps del_ths addsimps add_ths
    val aprems = Arith_Data.get_arith_facts ctxt
in
  Method.insert_tac aprems
  THEN_ALL_NEW Object_Logic.full_atomize_tac
  THEN_ALL_NEW CONVERSION Thm.eta_long_conversion
  THEN_ALL_NEW simp_tac ss
  THEN_ALL_NEW (TRY o generalize_tac (int_nat_terms ctxt))
  THEN_ALL_NEW Object_Logic.full_atomize_tac
  THEN_ALL_NEW (thin_prems_tac ctxt (is_relevant ctxt))
  THEN_ALL_NEW Object_Logic.full_atomize_tac
  THEN_ALL_NEW div_mod_tac ctxt
  THEN_ALL_NEW splits_tac ctxt
  THEN_ALL_NEW simp_tac ss
  THEN_ALL_NEW CONVERSION Thm.eta_long_conversion
  THEN_ALL_NEW nat_to_int_tac ctxt
  THEN_ALL_NEW (core_tac ctxt)
  THEN_ALL_NEW finish_tac elim
end;


(* theory setup *)

local

fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();

val constsN = "consts";
val any_keyword = keyword constsN
val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
val terms = thms >> map (term_of o Drule.dest_term);

fun optional scan = Scan.optional scan [];

in

val setup =
  Attrib.setup @{binding presburger}
    ((Scan.lift (Args.$$$ "del") |-- optional (keyword constsN |-- terms)) >> del ||
      optional (keyword constsN |-- terms) >> add) "data for Cooper's algorithm"
  #> Arith_Data.add_tactic "Presburger arithmetic" (K (tac true [] []));

end;

end;
