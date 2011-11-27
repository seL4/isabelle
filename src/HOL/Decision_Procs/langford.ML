(*  Title:      HOL/Decision_Procs/langford.ML
    Author:     Amine Chaieb, TU Muenchen
*)

signature LANGFORD_QE = 
sig
  val dlo_tac : Proof.context -> int -> tactic
  val dlo_conv : Proof.context -> cterm -> thm
end

structure LangfordQE :LANGFORD_QE = 
struct

val dest_set =
 let 
  fun h acc ct = 
   case term_of ct of
     Const (@{const_name Orderings.bot}, _) => acc
   | Const (@{const_name insert}, _) $ _ $ t => h (Thm.dest_arg1 ct :: acc) (Thm.dest_arg ct)
in h [] end;

fun prove_finite cT u = 
let val [th0,th1] = map (instantiate' [SOME cT] []) @{thms "finite.intros"}
    fun ins x th =
     Thm.implies_elim (instantiate' [] [(SOME o Thm.dest_arg o Thm.dest_arg)
                                     (Thm.cprop_of th), SOME x] th1) th
in fold ins u th0 end;

val simp_rule =
  Conv.fconv_rule
    (Conv.arg_conv (Simplifier.rewrite (HOL_basic_ss addsimps @{thms ball_simps simp_thms})));

fun basic_dloqe ctxt stupid dlo_qeth dlo_qeth_nolb dlo_qeth_noub gather ep = 
 case term_of ep of 
  Const(@{const_name Ex},_)$_ => 
   let 
     val p = Thm.dest_arg ep
     val ths = simplify (HOL_basic_ss addsimps gather) (instantiate' [] [SOME p] stupid)
     val (L,U) = 
       let 
         val (x,q) = Thm.dest_abs NONE (Thm.dest_arg (Thm.rhs_of ths))
       in (Thm.dest_arg1 q |> Thm.dest_arg1, Thm.dest_arg q |> Thm.dest_arg1)
       end
     fun proveneF S =         
       let val (a,A) = Thm.dest_comb S |>> Thm.dest_arg
           val cT = ctyp_of_term a
           val ne = instantiate' [SOME cT] [SOME a, SOME A] 
                    @{thm insert_not_empty}
           val f = prove_finite cT (dest_set S)
       in (ne, f) end

     val qe = case (term_of L, term_of U) of 
      (Const (@{const_name Orderings.bot}, _),_) =>  
        let
          val (neU,fU) = proveneF U 
        in simp_rule (Thm.transitive ths (dlo_qeth_nolb OF [neU, fU])) end
    | (_,Const (@{const_name Orderings.bot}, _)) =>  
        let
          val (neL,fL) = proveneF L
        in simp_rule (Thm.transitive ths (dlo_qeth_noub OF [neL, fL])) end

    | (_,_) =>  
      let 
       val (neL,fL) = proveneF L
       val (neU,fU) = proveneF U
      in simp_rule (Thm.transitive ths (dlo_qeth OF [neL, neU, fL, fU])) 
      end
   in qe end 
 | _ => error "dlo_qe : Not an existential formula";

val all_conjuncts = 
 let fun h acc ct = 
  case term_of ct of
   @{term HOL.conj}$_$_ => h (h acc (Thm.dest_arg ct)) (Thm.dest_arg1 ct)
  | _ => ct::acc
in h [] end;

fun conjuncts ct =
 case term_of ct of
  @{term HOL.conj}$_$_ => (Thm.dest_arg1 ct)::(conjuncts (Thm.dest_arg ct))
| _ => [ct];

fun fold1 f = foldr1 (uncurry f);

val list_conj = fold1 (fn c => fn c' => Thm.capply (Thm.capply @{cterm HOL.conj} c) c') ;

fun mk_conj_tab th = 
 let fun h acc th = 
   case prop_of th of
   @{term "Trueprop"}$(@{term HOL.conj}$p$q) => 
     h (h acc (th RS conjunct2)) (th RS conjunct1)
  | @{term "Trueprop"}$p => (p,th)::acc
in fold (Termtab.insert Thm.eq_thm) (h [] th) Termtab.empty end;

fun is_conj (@{term HOL.conj}$_$_) = true
  | is_conj _ = false;

fun prove_conj tab cjs = 
 case cjs of 
   [c] => if is_conj (term_of c) then prove_conj tab (conjuncts c) else tab c
 | c::cs => conjI OF [prove_conj tab [c], prove_conj tab cs];

fun conj_aci_rule eq = 
 let 
  val (l,r) = Thm.dest_equals eq
  fun tabl c = the (Termtab.lookup (mk_conj_tab (Thm.assume l)) (term_of c))
  fun tabr c = the (Termtab.lookup (mk_conj_tab (Thm.assume r)) (term_of c))
  val ll = Thm.dest_arg l
  val rr = Thm.dest_arg r
  
  val thl  = prove_conj tabl (conjuncts rr) 
                |> Drule.implies_intr_hyps
  val thr  = prove_conj tabr (conjuncts ll) 
                |> Drule.implies_intr_hyps
  val eqI = instantiate' [] [SOME ll, SOME rr] @{thm iffI}
 in Thm.implies_elim (Thm.implies_elim eqI thl) thr |> mk_meta_eq end;

fun contains x ct = member (op aconv) (Misc_Legacy.term_frees (term_of ct)) (term_of x);

fun is_eqx x eq = case term_of eq of
   Const(@{const_name HOL.eq},_)$l$r => l aconv term_of x orelse r aconv term_of x
 | _ => false ;

local 
fun proc ct = 
 case term_of ct of
  Const(@{const_name Ex},_)$Abs (xn,_,_) => 
   let 
    val e = Thm.dest_fun ct
    val (x,p) = Thm.dest_abs (SOME xn) (Thm.dest_arg ct)
    val Pp = Thm.capply @{cterm "Trueprop"} p 
    val (eqs,neqs) = List.partition (is_eqx x) (all_conjuncts p)
   in case eqs of
      [] => 
        let 
         val (dx,ndx) = List.partition (contains x) neqs
         in case ndx of [] => NONE
                      | _ =>
            conj_aci_rule (Thm.mk_binop @{cterm "op == :: prop => _"} Pp 
                 (Thm.capply @{cterm Trueprop} (list_conj (ndx @dx))))
           |> Thm.abstract_rule xn x |> Drule.arg_cong_rule e 
           |> Conv.fconv_rule (Conv.arg_conv 
                   (Simplifier.rewrite (HOL_basic_ss addsimps @{thms simp_thms ex_simps})))
           |> SOME
          end
    | _ => conj_aci_rule (Thm.mk_binop @{cterm "op == :: prop => _"} Pp 
                 (Thm.capply @{cterm Trueprop} (list_conj (eqs@neqs))))
           |> Thm.abstract_rule xn x |> Drule.arg_cong_rule e 
           |> Conv.fconv_rule (Conv.arg_conv 
                   (Simplifier.rewrite (HOL_basic_ss addsimps @{thms simp_thms ex_simps})))
           |> SOME
   end
 | _ => NONE;
in val reduce_ex_simproc = 
  Simplifier.make_simproc 
  {lhss = [@{cpat "EX x. ?P x"}] , name = "reduce_ex_simproc",
   proc = K (K proc) , identifier = []}
end;

fun raw_dlo_conv dlo_ss 
          ({qe_bnds, qe_nolb, qe_noub, gst, gs, atoms}:Langford_Data.entry) = 
 let 
  val ss = dlo_ss addsimps @{thms "dnf_simps"} addsimprocs [reduce_ex_simproc]
  val dnfex_conv = Simplifier.rewrite ss
  val pcv =
    Simplifier.rewrite
      (dlo_ss addsimps @{thms simp_thms ex_simps all_simps all_not_ex not_all ex_disj_distrib})
 in fn p => 
   Qelim.gen_qelim_conv pcv pcv dnfex_conv cons 
                  (Thm.add_cterm_frees p [])  (K Thm.reflexive) (K Thm.reflexive)
                  (K (basic_dloqe () gst qe_bnds qe_nolb qe_noub gs)) p
 end;


val grab_atom_bop =
 let
  fun h bounds tm =
   (case term_of tm of
     Const (@{const_name HOL.eq}, T) $ _ $ _ =>
       if domain_type T = HOLogic.boolT then find_args bounds tm
       else Thm.dest_fun2 tm
   | Const (@{const_name Not}, _) $ _ => h bounds (Thm.dest_arg tm)
   | Const (@{const_name All}, _) $ _ => find_body bounds (Thm.dest_arg tm)
   | Const ("all", _) $ _ => find_body bounds (Thm.dest_arg tm)
   | Const (@{const_name Ex}, _) $ _ => find_body bounds (Thm.dest_arg tm)
   | Const (@{const_name HOL.conj}, _) $ _ $ _ => find_args bounds tm
   | Const (@{const_name HOL.disj}, _) $ _ $ _ => find_args bounds tm
   | Const (@{const_name HOL.implies}, _) $ _ $ _ => find_args bounds tm
   | Const ("==>", _) $ _ $ _ => find_args bounds tm
   | Const ("==", _) $ _ $ _ => find_args bounds tm
   | Const (@{const_name Trueprop}, _) $ _ => h bounds (Thm.dest_arg tm)
   | _ => Thm.dest_fun2 tm)
  and find_args bounds tm =
    (h bounds (Thm.dest_arg tm) handle CTERM _ => h bounds (Thm.dest_arg1 tm))
 and find_body bounds b =
   let val (_, b') = Thm.dest_abs (SOME (Name.bound bounds)) b
   in h (bounds + 1) b' end;
in h end;

fun dlo_instance ctxt tm =
  (fst (Langford_Data.get ctxt), 
   Langford_Data.match ctxt (grab_atom_bop 0 tm));

fun dlo_conv ctxt tm =
  (case dlo_instance ctxt tm of
    (_, NONE) => raise CTERM ("dlo_conv (langford): no corresponding instance in context!", [tm])
  | (ss, SOME instance) => raw_dlo_conv ss instance tm);

fun generalize_tac f = CSUBGOAL (fn (p, i) => PRIMITIVE (fn st =>
 let 
   fun all T = Drule.cterm_rule (instantiate' [SOME T] []) @{cpat "all"}
   fun gen x t = Thm.capply (all (ctyp_of_term x)) (Thm.cabs x t)
   val ts = sort (fn (a,b) => Term_Ord.fast_term_ord (term_of a, term_of b)) (f p)
   val p' = fold_rev gen ts p
 in Thm.implies_intr p' (Thm.implies_elim st (fold Thm.forall_elim ts (Thm.assume p'))) end));


fun cfrees ats ct =
 let 
  val ins = insert (op aconvc)
  fun h acc t = 
   case (term_of t) of
    b$_$_ => if member (op aconvc) ats (Thm.dest_fun2 t) 
                then ins (Thm.dest_arg t) (ins (Thm.dest_arg1 t) acc) 
                else h (h acc (Thm.dest_arg t)) (Thm.dest_fun t)
  | _$_ => h (h acc (Thm.dest_arg t)) (Thm.dest_fun t)
  | Abs(_,_,_) => Thm.dest_abs NONE t ||> h acc |> uncurry (remove (op aconvc))
  | Free _ => if member (op aconvc) ats t then acc else ins t acc
  | Var _ => if member (op aconvc) ats t then acc else ins t acc
  | _ => acc
 in h [] ct end

fun dlo_tac ctxt = CSUBGOAL (fn (p, i) =>
  (case dlo_instance ctxt p of
    (ss, NONE) => simp_tac ss i
  | (ss,  SOME instance) =>
      Object_Logic.full_atomize_tac i THEN
      simp_tac ss i
      THEN (CONVERSION Thm.eta_long_conversion) i
      THEN (TRY o generalize_tac (cfrees (#atoms instance))) i
      THEN Object_Logic.full_atomize_tac i
      THEN CONVERSION (Object_Logic.judgment_conv (raw_dlo_conv ss instance)) i
      THEN (simp_tac ss i)));  
end;