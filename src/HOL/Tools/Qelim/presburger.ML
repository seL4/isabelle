(*  Title:      HOL/Tools/Qelim/presburger.ML
    Author:     Amine Chaieb, TU Muenchen
*)

signature PRESBURGER =
sig
  val cooper_tac: bool -> thm list -> thm list -> Proof.context -> int -> tactic
end;

structure Presburger : PRESBURGER = 
struct

open Conv;
val comp_ss = HOL_ss addsimps @{thms "Groebner_Basis.comp_arith"};

fun strip_objimp ct =
  (case Thm.term_of ct of
    Const ("op -->", _) $ _ $ _ =>
      let val (A, B) = Thm.dest_binop ct
      in A :: strip_objimp B end
  | _ => [ct]);

fun strip_objall ct = 
 case term_of ct of 
  Const ("All", _) $ Abs (xn,xT,p) => 
   let val (a,(v,t')) = (apsnd (Thm.dest_abs (SOME xn)) o Thm.dest_comb) ct
   in apfst (cons (a,v)) (strip_objall t')
   end
| _ => ([],ct);

local
  val all_maxscope_ss = 
     HOL_basic_ss addsimps map (fn th => th RS sym) @{thms "all_simps"}
in
fun thin_prems_tac P = simp_tac all_maxscope_ss THEN'
  CSUBGOAL (fn (p', i) =>
    let
     val (qvs, p) = strip_objall (Thm.dest_arg p')
     val (ps, c) = split_last (strip_objimp p)
     val qs = filter P ps
     val q = if P c then c else @{cterm "False"}
     val ng = fold_rev (fn (a,v) => fn t => Thm.capply a (Thm.cabs v t)) qvs 
         (fold_rev (fn p => fn q => Thm.capply (Thm.capply @{cterm "op -->"} p) q) qs q)
     val g = Thm.capply (Thm.capply @{cterm "op ==>"} (Thm.capply @{cterm "Trueprop"} ng)) p'
     val ntac = (case qs of [] => q aconvc @{cterm "False"}
                         | _ => false)
    in 
    if ntac then no_tac
      else rtac (Goal.prove_internal [] g (K (blast_tac HOL_cs 1))) i
    end)
end;

local
 fun isnum t = case t of 
   Const(@{const_name "HOL.zero"},_) => true
 | Const(@{const_name "HOL.one"},_) => true
 | @{term "Suc"}$s => isnum s
 | @{term "nat"}$s => isnum s
 | @{term "int"}$s => isnum s
 | Const(@{const_name "HOL.uminus"},_)$s => isnum s
 | Const(@{const_name "HOL.plus"},_)$l$r => isnum l andalso isnum r
 | Const(@{const_name "HOL.times"},_)$l$r => isnum l andalso isnum r
 | Const(@{const_name "HOL.minus"},_)$l$r => isnum l andalso isnum r
 | Const(@{const_name "Power.power"},_)$l$r => isnum l andalso isnum r
 | Const(@{const_name "Divides.mod"},_)$l$r => isnum l andalso isnum r
 | Const(@{const_name "Divides.div"},_)$l$r => isnum l andalso isnum r
 | _ => can HOLogic.dest_number t orelse can HOLogic.dest_nat t

 fun ty cts t = 
 if not (typ_of (ctyp_of_term t) mem [HOLogic.intT, HOLogic.natT, HOLogic.boolT]) then false 
    else case term_of t of 
      c$l$r => if c mem [@{term"op *::int => _"}, @{term"op *::nat => _"}] 
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
 gen_subset (op aconv) (term_constants (term_of ct) , snd (CooperData.get ctxt))
 andalso forall (fn Free (_,T) => T mem [@{typ "int"}, @{typ nat}]) (OldTerm.term_frees (term_of ct))
 andalso forall (fn Var (_,T) => T mem [@{typ "int"}, @{typ nat}]) (OldTerm.term_vars (term_of ct));

fun int_nat_terms ctxt ct =
 let 
  val cts = snd (CooperData.get ctxt)
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
   fun gen x t = Thm.capply (all (ctyp_of_term x)) (Thm.cabs x t)
   val ts = sort (fn (a,b) => TermOrd.fast_term_ord (term_of a, term_of b)) (f p)
   val p' = fold_rev gen ts p
 in implies_intr p' (implies_elim st (fold forall_elim ts (assume p'))) end));

local
val ss1 = comp_ss
  addsimps simp_thms @ [@{thm "nat_number_of_def"}, @{thm "zdvd_int"}] 
      @ map (fn r => r RS sym) 
        [@{thm "int_int_eq"}, @{thm "zle_int"}, @{thm "zless_int"}, @{thm "zadd_int"}, 
         @{thm "zmult_int"}]
    addsplits [@{thm "zdiff_int_split"}]

val ss2 = HOL_basic_ss
  addsimps [@{thm "nat_0_le"}, @{thm "int_nat_number_of"},
            @{thm "all_nat"}, @{thm "ex_nat"}, @{thm "number_of1"}, 
            @{thm "number_of2"}, @{thm "int_0"}, @{thm "int_1"}, @{thm "Suc_plus1"}]
  addcongs [@{thm "conj_le_cong"}, @{thm "imp_le_cong"}]
val div_mod_ss = HOL_basic_ss addsimps simp_thms 
  @ map (symmetric o mk_meta_eq) 
    [@{thm "dvd_eq_mod_eq_0"},
     @{thm "mod_add_left_eq"}, @{thm "mod_add_right_eq"}, 
     @{thm "mod_add_eq"}, @{thm "div_add1_eq"}, @{thm "zdiv_zadd1_eq"}]
  @ [@{thm "mod_self"}, @{thm "zmod_self"}, @{thm "mod_by_0"}, 
     @{thm "div_by_0"}, @{thm "DIVISION_BY_ZERO"} RS conjunct1, 
     @{thm "DIVISION_BY_ZERO"} RS conjunct2, @{thm "zdiv_zero"}, @{thm "zmod_zero"}, 
     @{thm "div_0"}, @{thm "mod_0"}, @{thm "div_by_1"}, @{thm "mod_by_1"}, @{thm "div_1"}, 
     @{thm "mod_1"}, @{thm "Suc_plus1"}]
  @ @{thms add_ac}
 addsimprocs [cancel_div_mod_proc]
 val splits_ss = comp_ss addsimps [@{thm "mod_div_equality'"}] addsplits 
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


fun core_cooper_tac ctxt = CSUBGOAL (fn (p, i) =>
   let 
    val cpth = 
       if !quick_and_dirty 
       then linzqe_oracle (Thm.cterm_of (ProofContext.theory_of ctxt)
             (Envir.beta_norm (Pattern.eta_long [] (term_of (Thm.dest_arg p)))))
       else arg_conv (Cooper.cooper_conv ctxt) p
    val p' = Thm.rhs_of cpth
    val th = implies_intr p' (equal_elim (symmetric cpth) (assume p'))
   in rtac th i end
   handle Cooper.COOPER _ => no_tac);

fun finish_tac q = SUBGOAL (fn (_, i) =>
  (if q then I else TRY) (rtac TrueI i));

fun cooper_tac elim add_ths del_ths ctxt =
let val ss = Simplifier.context ctxt (fst (CooperData.get ctxt)) delsimps del_ths addsimps add_ths
    val aprems = Arith_Data.get_arith_facts ctxt
in
  Method.insert_tac aprems
  THEN_ALL_NEW ObjectLogic.full_atomize_tac
  THEN_ALL_NEW CONVERSION Thm.eta_long_conversion
  THEN_ALL_NEW simp_tac ss
  THEN_ALL_NEW (TRY o generalize_tac (int_nat_terms ctxt))
  THEN_ALL_NEW ObjectLogic.full_atomize_tac
  THEN_ALL_NEW (thin_prems_tac (is_relevant ctxt))
  THEN_ALL_NEW ObjectLogic.full_atomize_tac
  THEN_ALL_NEW div_mod_tac ctxt
  THEN_ALL_NEW splits_tac ctxt
  THEN_ALL_NEW simp_tac ss
  THEN_ALL_NEW CONVERSION Thm.eta_long_conversion
  THEN_ALL_NEW nat_to_int_tac ctxt
  THEN_ALL_NEW (core_cooper_tac ctxt)
  THEN_ALL_NEW finish_tac elim
end;

end;
