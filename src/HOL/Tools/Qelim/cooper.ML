(*  Title:      HOL/Tools/Qelim/cooper.ML
    Author:     Amine Chaieb, TU Muenchen
*)

signature COOPER =
 sig
  val cooper_conv : Proof.context -> conv
  exception COOPER of string * exn
end;

structure Cooper: COOPER =
struct

open Conv;
open Normalizer;

exception COOPER of string * exn;
fun simp_thms_conv ctxt =
  Simplifier.rewrite (Simplifier.context ctxt HOL_basic_ss addsimps simp_thms);
val FWD = Drule.implies_elim_list;

val true_tm = @{cterm "True"};
val false_tm = @{cterm "False"};
val zdvd1_eq = @{thm "zdvd1_eq"};
val presburger_ss = @{simpset} addsimps [zdvd1_eq];
val lin_ss = presburger_ss addsimps (@{thm dvd_eq_mod_eq_0} :: zdvd1_eq :: @{thms zadd_ac});

val iT = HOLogic.intT
val bT = HOLogic.boolT;
val dest_numeral = HOLogic.dest_number #> snd;

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

val [miex, cpmi, piex, cppi] = [@{thm "minusinfinity"}, @{thm "cpmi"}, 
                                @{thm "plusinfinity"}, @{thm "cppi"}];

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
  Const("op &",_)$_$_ => And (Thm.dest_binop ct)
| Const ("op |",_)$_$_ => Or (Thm.dest_binop ct)
| Const ("op =",ty)$y$_ => if term_of x aconv y then Eq (Thm.dest_arg ct) else Nox
| Const (@{const_name Not},_) $ (Const ("op =",_)$y$_) => 
  if term_of x aconv y then NEq (funpow 2 Thm.dest_arg ct) else Nox
| Const (@{const_name HOL.less}, _) $ y$ z =>
   if term_of x aconv y then Lt (Thm.dest_arg ct) 
   else if term_of x aconv z then Gt (Thm.dest_arg1 ct) else Nox
| Const (@{const_name HOL.less_eq}, _) $ y $ z => 
   if term_of x aconv y then Le (Thm.dest_arg ct) 
   else if term_of x aconv z then Ge (Thm.dest_arg1 ct) else Nox
| Const (@{const_name Ring_and_Field.dvd},_)$_$(Const(@{const_name HOL.plus},_)$y$_) =>
   if term_of x aconv y then Dvd (Thm.dest_binop ct ||> Thm.dest_arg) else Nox 
| Const (@{const_name Not},_) $ (Const (@{const_name Ring_and_Field.dvd},_)$_$(Const(@{const_name "HOL.plus"},_)$y$_)) =>
   if term_of x aconv y then 
   NDvd (Thm.dest_binop (Thm.dest_arg ct) ||> Thm.dest_arg) else Nox 
| _ => Nox)
  handle CTERM _ => Nox; 

fun get_pmi_term t = 
  let val (x,eq) = 
     (Thm.dest_abs NONE o Thm.dest_arg o snd o Thm.dest_abs NONE o Thm.dest_arg)
        (Thm.dest_arg t)
in (Thm.cabs x o Thm.dest_arg o Thm.dest_arg) eq end;

val get_pmi = get_pmi_term o cprop_of;

val p_v' = @{cpat "?P' :: int => bool"}; 
val q_v' = @{cpat "?Q' :: int => bool"};
val p_v = @{cpat "?P:: int => bool"};
val q_v = @{cpat "?Q:: int => bool"};

fun myfwd (th1, th2, th3) p q 
      [(th_1,th_2,th_3), (th_1',th_2',th_3')] = 
  let  
   val (mp', mq') = (get_pmi th_1, get_pmi th_1')
   val mi_th = FWD (instantiate ([],[(p_v,p),(q_v,q), (p_v',mp'),(q_v',mq')]) th1) 
                   [th_1, th_1']
   val infD_th = FWD (instantiate ([],[(p_v,mp'), (q_v, mq')]) th3) [th_3,th_3']
   val set_th = FWD (instantiate ([],[(p_v,p), (q_v,q)]) th2) [th_2, th_2']
  in (mi_th, set_th, infD_th)
  end;

val inst' = fn cts => instantiate' [] (map SOME cts);
val infDTrue = instantiate' [] [SOME true_tm] infDP;
val infDFalse = instantiate' [] [SOME false_tm] infDP;

val cadd =  @{cterm "op + :: int => _"}
val cmulC =  @{cterm "op * :: int => _"}
val cminus =  @{cterm "op - :: int => _"}
val cone =  @{cterm "1 :: int"}
val cneg = @{cterm "uminus :: int => _"}
val [addC, mulC, subC, negC] = map term_of [cadd, cmulC, cminus, cneg]
val [zero, one] = [@{term "0 :: int"}, @{term "1 :: int"}];

val is_numeral = can dest_numeral; 

fun numeral1 f n = HOLogic.mk_number iT (f (dest_numeral n)); 
fun numeral2 f m n = HOLogic.mk_number iT (f (dest_numeral m) (dest_numeral n));

val [minus1,plus1] = 
    map (fn c => fn t => Thm.capply (Thm.capply c t) cone) [cminus,cadd];

fun decomp_pinf x dvd inS [aseteq, asetneq, asetlt, asetle, 
                           asetgt, asetge,asetdvd,asetndvd,asetP,
                           infDdvd, infDndvd, asetconj,
                           asetdisj, infDconj, infDdisj] cp =
 case (whatis x cp) of
  And (p,q) => ([p,q], myfwd (piconj, asetconj, infDconj) (Thm.cabs x p) (Thm.cabs x q))
| Or (p,q) => ([p,q], myfwd (pidisj, asetdisj, infDdisj) (Thm.cabs x p) (Thm.cabs x q))
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
  And (p,q) => ([p,q], myfwd (miconj, bsetconj, infDconj) (Thm.cabs x p) (Thm.cabs x q))
| Or (p,q) => ([p,q], myfwd (midisj, bsetdisj, infDdisj) (Thm.cabs x p) (Thm.cabs x q))
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
      Const (@{const_name HOL.plus}, _) $ a $ b => addC $ linear_cmul n a $ linear_cmul n b
    | Const (@{const_name HOL.times}, _) $ c $ x => mulC $ numeral1 (fn m => n * m) c $ x
    | Const (@{const_name HOL.minus}, _) $ a $ b => subC $ linear_cmul n a $ linear_cmul n b
    | (m as Const (@{const_name HOL.uminus}, _)) $ a => m $ linear_cmul n a
    | _ => numeral1 (fn m => n * m) tm;
fun earlier [] x y = false 
	| earlier (h::t) x y = 
    if h aconv y then false else if h aconv x then true else earlier t x y; 

fun linear_add vars tm1 tm2 = case (tm1, tm2) of 
    (Const (@{const_name HOL.plus}, _) $ (Const (@{const_name HOL.times}, _) $ c1 $ x1) $ r1,
    Const (@{const_name HOL.plus}, _) $ (Const (@{const_name HOL.times}, _) $ c2 $ x2) $ r2) =>
   if x1 = x2 then 
     let val c = numeral2 (curry op +) c1 c2
      in if c = zero then linear_add vars r1 r2
         else addC$(mulC$c$x1)$(linear_add vars r1 r2)
     end 
     else if earlier vars x1 x2 then addC $ (mulC $ c1 $ x1) $ linear_add vars r1 tm2
   else addC $ (mulC $ c2 $ x2) $ linear_add vars tm1 r2
 | (Const (@{const_name HOL.plus}, _) $ (Const (@{const_name HOL.times}, _) $ c1 $ x1) $ r1, _) =>
      addC $ (mulC $ c1 $ x1) $ linear_add vars r1 tm2
 | (_, Const (@{const_name HOL.plus}, _) $ (Const (@{const_name HOL.times}, _) $ c2 $ x2) $ r2) => 
      addC $ (mulC $ c2 $ x2) $ linear_add vars tm1 r2
 | (_, _) => numeral2 (curry op +) tm1 tm2;
 
fun linear_neg tm = linear_cmul ~1 tm; 
fun linear_sub vars tm1 tm2 = linear_add vars tm1 (linear_neg tm2); 


fun lint vars tm =  if is_numeral tm then tm  else case tm of 
  Const (@{const_name HOL.uminus}, _) $ t => linear_neg (lint vars t)
| Const (@{const_name HOL.plus}, _) $ s $ t => linear_add vars (lint vars s) (lint vars t)
| Const (@{const_name HOL.minus}, _) $ s $ t => linear_sub vars (lint vars s) (lint vars t)
| Const (@{const_name HOL.times}, _) $ s $ t =>
  let val s' = lint vars s  
      val t' = lint vars t  
  in if is_numeral s' then (linear_cmul (dest_numeral s') t') 
     else if is_numeral t' then (linear_cmul (dest_numeral t') s') 
     else raise COOPER ("Cooper Failed", TERM ("lint: not linear",[tm]))
  end 
 | _ => addC $ (mulC $ one $ tm) $ zero;

fun lin (vs as x::_) (Const (@{const_name Not}, _) $ (Const (@{const_name HOL.less}, T) $ s $ t)) = 
    lin vs (Const (@{const_name HOL.less_eq}, T) $ t $ s)
  | lin (vs as x::_) (Const (@{const_name Not},_) $ (Const(@{const_name HOL.less_eq}, T) $ s $ t)) = 
    lin vs (Const (@{const_name HOL.less}, T) $ t $ s)
  | lin vs (Const (@{const_name Not},T)$t) = Const (@{const_name Not},T)$ (lin vs t)
  | lin (vs as x::_) (Const(@{const_name Ring_and_Field.dvd},_)$d$t) = 
    HOLogic.mk_binrel @{const_name Ring_and_Field.dvd} (numeral1 abs d, lint vs t)
  | lin (vs as x::_) ((b as Const("op =",_))$s$t) = 
     (case lint vs (subC$t$s) of 
      (t as a$(m$c$y)$r) => 
        if x <> y then b$zero$t
        else if dest_numeral c < 0 then b$(m$(numeral1 ~ c)$y)$r
        else b$(m$c$y)$(linear_neg r)
      | t => b$zero$t)
  | lin (vs as x::_) (b$s$t) = 
     (case lint vs (subC$t$s) of 
      (t as a$(m$c$y)$r) => 
        if x <> y then b$zero$t
        else if dest_numeral c < 0 then b$(m$(numeral1 ~ c)$y)$r
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
  Const(@{const_name Ring_and_Field.dvd},_)$d$t => 
  let 
    val th = binop_conv (lint_conv ctxt vs) ct
    val (d',t') = Thm.dest_binop (Thm.rhs_of th)
    val (dt',tt') = (term_of d', term_of t')
  in if is_numeral dt' andalso is_numeral tt' 
     then Conv.fconv_rule (arg_conv (Simplifier.rewrite presburger_ss)) th
     else 
     let 
      val dth = 
      ((if dest_numeral (term_of d') < 0 then 
          Conv.fconv_rule (arg_conv (arg1_conv (lint_conv ctxt vs)))
                           (Thm.transitive th (inst' [d',t'] dvd_uminus))
        else th) handle TERM _ => th)
      val d'' = Thm.rhs_of dth |> Thm.dest_arg1
     in
      case tt' of 
        Const(@{const_name HOL.plus},_)$(Const(@{const_name HOL.times},_)$c$_)$_ => 
        let val x = dest_numeral c
        in if x < 0 then Conv.fconv_rule (arg_conv (arg_conv (lint_conv ctxt vs)))
                                       (Thm.transitive dth (inst' [d'',t'] dvd_uminus'))
        else dth end
      | _ => dth
     end
  end
| Const (@{const_name Not},_)$(Const(@{const_name Ring_and_Field.dvd},_)$_$_) => arg_conv (linearize_conv ctxt vs) ct
| t => if is_intrel t 
      then (provelin ctxt ((HOLogic.eq_const bT)$t$(lin vs t) |> HOLogic.mk_Trueprop))
       RS eq_reflection
      else reflexive ct;

val dvdc = @{cterm "op dvd :: int => _"};

fun unify ctxt q = 
 let
  val (e,(cx,p)) = q |> Thm.dest_comb ||> Thm.dest_abs NONE
  val x = term_of cx 
  val ins = insert (op = : int * int -> bool)
  fun h (acc,dacc) t = 
   case (term_of t) of
    Const(s,_)$(Const(@{const_name HOL.times},_)$c$y)$ _ => 
    if x aconv y andalso member (op =)
      ["op =", @{const_name HOL.less}, @{const_name HOL.less_eq}] s
    then (ins (dest_numeral c) acc,dacc) else (acc,dacc)
  | Const(s,_)$_$(Const(@{const_name HOL.times},_)$c$y) => 
    if x aconv y andalso member (op =)
       [@{const_name HOL.less}, @{const_name HOL.less_eq}] s 
    then (ins (dest_numeral c) acc, dacc) else (acc,dacc)
  | Const(@{const_name Ring_and_Field.dvd},_)$_$(Const(@{const_name HOL.plus},_)$(Const(@{const_name HOL.times},_)$c$y)$_) => 
    if x aconv y then (acc,ins (dest_numeral c) dacc) else (acc,dacc)
  | Const("op &",_)$_$_ => h (h (acc,dacc) (Thm.dest_arg1 t)) (Thm.dest_arg t)
  | Const("op |",_)$_$_ => h (h (acc,dacc) (Thm.dest_arg1 t)) (Thm.dest_arg t)
  | Const (@{const_name Not},_)$_ => h (acc,dacc) (Thm.dest_arg t)
  | _ => (acc, dacc)
  val (cs,ds) = h ([],[]) p
  val l = Integer.lcms (cs union ds)
  fun cv k ct = 
    let val (tm as b$s$t) = term_of ct 
    in ((HOLogic.eq_const bT)$tm$(b$(linear_cmul k s)$(linear_cmul k t))
         |> HOLogic.mk_Trueprop |> provelin ctxt) RS eq_reflection end
  fun nzprop x = 
   let 
    val th = 
     Simplifier.rewrite lin_ss 
      (Thm.capply @{cterm Trueprop} (Thm.capply @{cterm "Not"} 
           (Thm.capply (Thm.capply @{cterm "op = :: int => _"} (Numeral.mk_cnumber @{ctyp "int"} x)) 
           @{cterm "0::int"})))
   in equal_elim (Thm.symmetric th) TrueI end;
  val notz = let val tab = fold Inttab.update 
                               (ds ~~ (map (fn x => nzprop (l div x)) ds)) Inttab.empty 
            in 
             (fn ct => (valOf (Inttab.lookup tab (ct |> term_of |> dest_numeral)) 
                handle Option => (writeln "noz: Theorems-Table contains no entry for"; 
                                    Display.print_cterm ct ; raise Option)))
           end
  fun unit_conv t = 
   case (term_of t) of
   Const("op &",_)$_$_ => binop_conv unit_conv t
  | Const("op |",_)$_$_ => binop_conv unit_conv t
  | Const (@{const_name Not},_)$_ => arg_conv unit_conv t
  | Const(s,_)$(Const(@{const_name HOL.times},_)$c$y)$ _ => 
    if x=y andalso member (op =)
      ["op =", @{const_name HOL.less}, @{const_name HOL.less_eq}] s
    then cv (l div dest_numeral c) t else Thm.reflexive t
  | Const(s,_)$_$(Const(@{const_name HOL.times},_)$c$y) => 
    if x=y andalso member (op =)
      [@{const_name HOL.less}, @{const_name HOL.less_eq}] s
    then cv (l div dest_numeral c) t else Thm.reflexive t
  | Const(@{const_name Ring_and_Field.dvd},_)$d$(r as (Const(@{const_name HOL.plus},_)$(Const(@{const_name HOL.times},_)$c$y)$_)) => 
    if x=y then 
      let 
       val k = l div dest_numeral c
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
  val ltx = Thm.capply (Thm.capply cmulC clt) cx
  val th = Drule.arg_cong_rule e (Thm.abstract_rule (fst (dest_Free x )) cx uth)
  val th' = inst' [Thm.cabs ltx (Thm.rhs_of uth), clt] unity_coeff_ex
  val thf = transitive th 
      (transitive (symmetric (beta_conversion true (cprop_of th' |> Thm.dest_arg1))) th')
  val (lth,rth) = Thm.dest_comb (cprop_of thf) |>> Thm.dest_arg |>> Thm.beta_conversion true
                  ||> beta_conversion true |>> Thm.symmetric
 in transitive (transitive lth thf) rth end;


val emptyIS = @{cterm "{}::int set"};
val insert_tm = @{cterm "insert :: int => _"};
val mem_tm = Const("op :",[iT , HOLogic.mk_setT iT] ---> bT);
fun mkISet cts = fold_rev (Thm.capply insert_tm #> Thm.capply) cts emptyIS;
val cTrp = @{cterm "Trueprop"};
val eqelem_imp_imp = (thm"eqelem_imp_iff") RS iffD1;
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
  | Dvd (d,s) => (bacc,aacc,insert (op =) (term_of d |> dest_numeral) dacc)
  | NDvd (d,s) => (bacc,aacc,insert (op =) (term_of d|> dest_numeral) dacc)
  | _ => (bacc, aacc, dacc)
 val (b0,a0,ds) = h p ([],[],[])
 val d = Integer.lcms ds
 val cd = Numeral.mk_cnumber @{ctyp "int"} d
 val dt = term_of cd
 fun divprop x = 
   let 
    val th = 
     Simplifier.rewrite lin_ss 
      (Thm.capply @{cterm Trueprop} 
           (Thm.capply (Thm.capply dvdc (Numeral.mk_cnumber @{ctyp "int"} x)) cd))
   in equal_elim (Thm.symmetric th) TrueI end;
 val dvd = let val tab = fold Inttab.update
                               (ds ~~ (map divprop ds)) Inttab.empty in 
           (fn ct => (valOf (Inttab.lookup tab (term_of ct |> dest_numeral)) 
                    handle Option => (writeln "dvd: Theorems-Table contains no entry for"; 
                                      Display.print_cterm ct ; raise Option)))
           end
 val dp = 
   let val th = Simplifier.rewrite lin_ss 
      (Thm.capply @{cterm Trueprop} 
           (Thm.capply (Thm.capply @{cterm "op < :: int => _"} @{cterm "0::int"}) cd))
   in equal_elim (Thm.symmetric th) TrueI end;
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
         else implies_elim (instantiate' [] [SOME x, SOME S', SOME cy] insI2) 
                           (provein x S')
         end
   end
 
 val al = map (lint vs o term_of) a0
 val bl = map (lint vs o term_of) b0
 val (sl,s0,f,abths,cpth) = 
   if length (distinct (op aconv) bl) <= length (distinct (op aconv) al) 
   then  
    (bl,b0,decomp_minf,
     fn B => (map (fn th => implies_elim (Thm.instantiate ([],[(B_tm,B), (D_tm,cd)]) th) dp) 
                     [bseteq,bsetneq,bsetlt, bsetle, bsetgt,bsetge])@
                   (map (Thm.instantiate ([],[(B_tm,B), (D_tm,cd)])) 
                        [bsetdvd,bsetndvd,bsetP,infDdvd, infDndvd,bsetconj,
                         bsetdisj,infDconj, infDdisj]),
                       cpmi) 
     else (al,a0,decomp_pinf,fn A => 
          (map (fn th => implies_elim (Thm.instantiate ([],[(A_tm,A), (D_tm,cd)]) th) dp)
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
      fun transmem th0 th1 = 
       Thm.equal_elim 
        (Drule.arg_cong_rule cTrp (Drule.fun_cong_rule (Drule.arg_cong_rule 
               ((Thm.dest_fun o Thm.dest_fun o Thm.dest_arg o cprop_of) th1) th0) S)) th1
      val tab = fold Termtab.update
        (map (fn eq => 
                let val (s,t) = cprop_of eq |> Thm.dest_arg |> Thm.dest_binop 
                    val th = if term_of s = term_of t 
                             then valOf(Termtab.lookup inStab (term_of s))
                             else FWD (instantiate' [] [SOME s, SOME t] eqelem_th) 
                                [eq, valOf(Termtab.lookup inStab (term_of s))]
                 in (term_of t, th) end)
                  sths) Termtab.empty
        in fn ct => 
          (valOf (Termtab.lookup tab (term_of ct))
           handle Option => (writeln "inS: No theorem for " ; Display.print_cterm ct ; raise Option))
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
   b$_$_ => if member (op aconv) bops b then binop_conv h t else cv env t
 | u$_ => if member (op aconv) uops u then arg_conv h t else cv env t
 | _ => cv env t
 in h end;

fun integer_nnf_conv ctxt env =
 nnf_conv then_conv literals_conv [HOLogic.conj, HOLogic.disj] [] env (linearize_conv ctxt);

local
 val pcv = Simplifier.rewrite 
     (HOL_basic_ss addsimps (simp_thms @ (List.take(ex_simps,4)) 
                      @ [not_all,all_not_ex, ex_disj_distrib]))
 val postcv = Simplifier.rewrite presburger_ss
 fun conv ctxt p = 
  let val _ = ()
  in
   Qelim.gen_qelim_conv pcv postcv pcv (cons o term_of) 
      (OldTerm.term_frees (term_of p)) (linearize_conv ctxt) (integer_nnf_conv ctxt) 
      (cooperex_conv ctxt) p 
  end
  handle  CTERM s => raise COOPER ("Cooper Failed", CTERM s)
        | THM s => raise COOPER ("Cooper Failed", THM s) 
        | TYPE s => raise COOPER ("Cooper Failed", TYPE s) 
in val cooper_conv = conv 
end;
end;



structure Coopereif =
struct

open GeneratedCooper;

fun cooper s = raise Cooper.COOPER ("Cooper oracle failed", ERROR s);
fun i_of_term vs t = case t
 of Free (xn, xT) => (case AList.lookup (op aconv) vs t
     of NONE   => cooper "Variable not found in the list!"
      | SOME n => Bound n)
  | @{term "0::int"} => C 0
  | @{term "1::int"} => C 1
  | Term.Bound i => Bound i
  | Const(@{const_name HOL.uminus},_)$t' => Neg (i_of_term vs t')
  | Const(@{const_name HOL.plus},_)$t1$t2 => Add (i_of_term vs t1,i_of_term vs t2)
  | Const(@{const_name HOL.minus},_)$t1$t2 => Sub (i_of_term vs t1,i_of_term vs t2)
  | Const(@{const_name HOL.times},_)$t1$t2 => 
     (Mul (HOLogic.dest_number t1 |> snd, i_of_term vs t2)
    handle TERM _ => 
       (Mul (HOLogic.dest_number t2 |> snd, i_of_term vs t1)
        handle TERM _ => cooper "Reification: Unsupported kind of multiplication"))
  | _ => (C (HOLogic.dest_number t |> snd) 
           handle TERM _ => cooper "Reification: unknown term");

fun qf_of_term ps vs t =  case t
 of Const("True",_) => T
  | Const("False",_) => F
  | Const(@{const_name HOL.less},_)$t1$t2 => Lt (Sub (i_of_term vs t1,i_of_term vs t2))
  | Const(@{const_name HOL.less_eq},_)$t1$t2 => Le (Sub(i_of_term vs t1,i_of_term vs t2))
  | Const(@{const_name Ring_and_Field.dvd},_)$t1$t2 => 
      (Dvd(HOLogic.dest_number t1 |> snd, i_of_term vs t2) handle _ => cooper "Reification: unsupported dvd")  (* FIXME avoid handle _ *)
  | @{term "op = :: int => _"}$t1$t2 => Eq (Sub (i_of_term vs t1,i_of_term vs t2))
  | @{term "op = :: bool => _ "}$t1$t2 => Iff(qf_of_term ps vs t1,qf_of_term ps vs t2)
  | Const("op &",_)$t1$t2 => And(qf_of_term ps vs t1,qf_of_term ps vs t2)
  | Const("op |",_)$t1$t2 => Or(qf_of_term ps vs t1,qf_of_term ps vs t2)
  | Const("op -->",_)$t1$t2 => Imp(qf_of_term ps vs t1,qf_of_term ps vs t2)
  | Const (@{const_name Not},_)$t' => Not(qf_of_term ps vs t')
  | Const("Ex",_)$Abs(xn,xT,p) => 
     let val (xn',p') = variant_abs (xn,xT,p)
         val vs' = (Free (xn',xT), 0) :: (map (fn(v,n) => (v,1+ n)) vs)
     in E (qf_of_term ps vs' p')
     end
  | Const("All",_)$Abs(xn,xT,p) => 
     let val (xn',p') = variant_abs (xn,xT,p)
         val vs' = (Free (xn',xT), 0) :: (map (fn(v,n) => (v,1+ n)) vs)
     in A (qf_of_term ps vs' p')
     end
  | _ =>(case AList.lookup (op aconv) ps t of 
           NONE => cooper "Reification: unknown term!"
         | SOME n => Closed n);

local
 val ops = [@{term "op &"}, @{term "op |"}, @{term "op -->"}, @{term "op = :: bool => _"},
             @{term "op = :: int => _"}, @{term "op < :: int => _"}, 
             @{term "op <= :: int => _"}, @{term "Not"}, @{term "All:: (int => _) => _"}, 
             @{term "Ex:: (int => _) => _"}, @{term "True"}, @{term "False"}]
fun ty t = Bool.not (fastype_of t = HOLogic.boolT)
in
fun term_bools acc t =
case t of 
    (l as f $ a) $ b => if ty t orelse f mem ops then term_bools (term_bools acc l)b 
            else insert (op aconv) t acc
  | f $ a => if ty t orelse f mem ops then term_bools (term_bools acc f) a  
            else insert (op aconv) t acc
  | Abs p => term_bools acc (snd (variant_abs p))
  | _ => if ty t orelse t mem ops then acc else insert (op aconv) t acc
end;
 
fun myassoc2 l v =
    case l of
	[] => NONE
      | (x,v')::xs => if v = v' then SOME x
		      else myassoc2 xs v;

fun term_of_i vs t = case t
 of C i => HOLogic.mk_number HOLogic.intT i
  | Bound n => the (myassoc2 vs n)
  | Neg t' => @{term "uminus :: int => _"} $ term_of_i vs t'
  | Add (t1, t2) => @{term "op + :: int => _"} $ term_of_i vs t1 $ term_of_i vs t2
  | Sub (t1, t2) => @{term "op - :: int => _"} $ term_of_i vs t1 $ term_of_i vs t2
  | Mul (i, t2) => @{term "op * :: int => _"} $
      HOLogic.mk_number HOLogic.intT i $ term_of_i vs t2
  | Cn (n, i, t') => term_of_i vs (Add (Mul (i, Bound n), t'));

fun term_of_qf ps vs t = 
 case t of 
   T => HOLogic.true_const 
 | F => HOLogic.false_const
 | Lt t' => @{term "op < :: int => _ "}$ term_of_i vs t'$ @{term "0::int"}
 | Le t' => @{term "op <= :: int => _ "}$ term_of_i vs t' $ @{term "0::int"}
 | Gt t' => @{term "op < :: int => _ "}$ @{term "0::int"}$ term_of_i vs t'
 | Ge t' => @{term "op <= :: int => _ "}$ @{term "0::int"}$ term_of_i vs t'
 | Eq t' => @{term "op = :: int => _ "}$ term_of_i vs t'$ @{term "0::int"}
 | NEq t' => term_of_qf ps vs (Not (Eq t'))
 | Dvd(i,t') => @{term "op dvd :: int => _ "} $ 
    HOLogic.mk_number HOLogic.intT i $ term_of_i vs t'
 | NDvd(i,t')=> term_of_qf ps vs (Not(Dvd(i,t')))
 | Not t' => HOLogic.Not$(term_of_qf ps vs t')
 | And(t1,t2) => HOLogic.conj$(term_of_qf ps vs t1)$(term_of_qf ps vs t2)
 | Or(t1,t2) => HOLogic.disj$(term_of_qf ps vs t1)$(term_of_qf ps vs t2)
 | Imp(t1,t2) => HOLogic.imp$(term_of_qf ps vs t1)$(term_of_qf ps vs t2)
 | Iff(t1,t2) => @{term "op = :: bool => _"} $ term_of_qf ps vs t1 $ term_of_qf ps vs t2
 | Closed n => the (myassoc2 ps n)
 | NClosed n => term_of_qf ps vs (Not (Closed n))
 | _ => cooper "If this is raised, Isabelle/HOL or code generator is inconsistent!";

fun cooper_oracle ct =
  let
    val thy = Thm.theory_of_cterm ct;
    val t = Thm.term_of ct;
    val (vs, ps) = pairself (map_index swap) (OldTerm.term_frees t, term_bools [] t);
  in
    Thm.cterm_of thy (Logic.mk_equals (HOLogic.mk_Trueprop t,
      HOLogic.mk_Trueprop (term_of_qf ps vs (pa (qf_of_term ps vs t)))))
  end;

end;
