(*
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

LCF proof synthesis for Ferrante and Rackoff.
*)

structure Ferrante_Rackoff_Proof:
sig
  val qelim: cterm -> thm
  exception FAILURE of string
end =
struct

    (* Some certified types *)
val cbT = ctyp_of (the_context()) HOLogic.boolT;
val rT = Type("RealDef.real",[]);
val crT = ctyp_of (the_context()) (Type("RealDef.real",[]));
    (* Normalization*)


	(* Computation of uset *)
fun uset x fm = 
    case fm of
	Const("op &",_)$p$q => (uset x p) union (uset x q)
      | Const("op |",_)$p$q => (uset x p) union (uset x q)
      | Const("Orderings.less",_)$s$t => if s=x then [t] 
			       else if t = x then [s]
			       else []
      | Const("Orderings.less_eq",_)$s$t => if s=x then [t] 
			       else if t = x then [s]
			       else []
      | Const("op =",_)$s$t => if s=x then [t] 
			       else []
      | Const("Not",_)$ (Const("op =",_)$s$t) => if s=x then [t] 
						 else []
      | _ => [];
val rsT = Type("set",[rT]);
fun holrealset [] = Const("{}",rsT)
  | holrealset (x::xs) = Const("insert",[rT,rsT] ---> rsT)$x$(holrealset xs);
fun prove_bysimp thy ss t = Goal.prove thy [] [] 
		       (HOLogic.mk_Trueprop t) (fn _ => simp_tac ss 1);

fun inusetthms sg x fm = 
    let val U = uset x fm
	val hU = holrealset U
	fun inC T = Const("op :",[T,Type("set",[T])] ---> HOLogic.boolT);
	val ss = simpset_of sg
	fun proveinU t = prove_bysimp sg ss ((inC rT)$t$hU)
	val uf = prove_bysimp sg ss ((inC rsT)$hU$Const("Finite_Set.Finites",Type("set",[rsT])))
    in (U,cterm_of sg hU,map proveinU U,uf)
    end;

	(* Theorems for minus/plusinfinity *)
val [minf_lt,minf_gt,minf_le,minf_ge,minf_eq,minf_neq,minf_fm,minf_conj,minf_disj] = thms"minf";
val [pinf_lt,pinf_gt,pinf_le,pinf_ge,pinf_eq,pinf_neq,pinf_fm,pinf_conj,pinf_disj] = thms"pinf";
    (* Theorems for boundedness from below/above *)
val [nmilbnd_lt,nmilbnd_gt,nmilbnd_le,nmilbnd_ge,nmilbnd_eq,nmilbnd_neq,nmilbnd_fm,nmilbnd_conj,nmilbnd_disj] = thms"nmilbnd";
val [npiubnd_lt,npiubnd_gt,npiubnd_le,npiubnd_ge,npiubnd_eq,npiubnd_neq,npiubnd_fm,npiubnd_conj,npiubnd_disj] = thms"npiubnd";

    (* Theorems for no changes over smallest intervals in U *)
val lin_dense_lt = thm "lin_dense_lt";
val lin_dense_le = thm "lin_dense_le";
val lin_dense_gt = thm "lin_dense_gt";
val lin_dense_ge = thm "lin_dense_ge";
val lin_dense_eq = thm "lin_dense_eq";
val lin_dense_neq = thm "lin_dense_neq";
val lin_dense_conj = thm "lin_dense_conj";
val lin_dense_disj = thm "lin_dense_disj";
val lin_dense_fm = thm "lin_dense_fm";
val fr_eq = thm "fr_eq";
val fr_simps = thms "fr_simps";

fun dest5 [] = ([],[],[],[],[])
  | dest5 ((x,y,z,w,v)::xs) = 
    let val (x',y',z',w',v') = dest5 xs 
    in (x::x',y::y',z::z',w::w',v::v') end ;

fun dest2 [] = ([],[])
  | dest2 ((x,y)::xs) = let val (x',y') = dest2 xs 
			    in (x::x',y::y') end ;
fun myfwd (th1,th2,th3,th4,th5) xs =
    let val (ths1,ths2,ths3,ths4,ths5) = dest5 xs
    in (ths1 MRS th1,ths2 MRS th2,ths3 MRS th3,ths4 MRS th4, ths5 MRS th5)
    end;

fun myfwd2 (th1,th2) xs =
    let val (ths1,ths2) = dest2 xs
    in (ths1 MRS th1,ths2 MRS th2)
    end;

fun decomp_mpinf sg x (U,CU,uths) fm = 
    let val cx = cterm_of sg x in
	(case fm of
	    Const("op &",_)$p$q => 
	    ([p,q],myfwd (minf_conj,pinf_conj, nmilbnd_conj, npiubnd_conj,lin_dense_conj))	
	  | Const("op |",_)$p$q => 
	    ([p,q],myfwd (minf_disj,pinf_disj, nmilbnd_disj,npiubnd_disj,lin_dense_disj))
	  | Const("Orderings.less",_)$s$t => 
	    if s= x then 
		let val ct = cterm_of sg t
		    val tinU = nth uths (find_index (fn a => a=t) U)
		    val mith = instantiate' [] [SOME ct] minf_lt
		    val pith = instantiate' [] [SOME ct] pinf_lt
		    val nmilth = tinU RS nmilbnd_lt
		    val npiuth = tinU RS npiubnd_lt
		    val lindth = tinU RS lin_dense_lt
		in ([],myfwd (mith,pith,nmilth,npiuth,lindth))
		end 
	    else if t = x then 
		let val ct = cterm_of sg s
		    val tinU = nth uths (find_index (fn a => a=s) U)
		    val mith = instantiate' [] [SOME ct] minf_gt
		    val pith = instantiate' [] [SOME ct] pinf_gt
		    val nmilth = tinU RS nmilbnd_gt
		    val npiuth = tinU RS npiubnd_gt
		    val lindth = tinU RS lin_dense_gt
		in ([],myfwd (mith,pith,nmilth,npiuth,lindth))
		end 

	    else
		let val cfm = cterm_of sg fm 
		    val mith = instantiate' [] [SOME cfm] minf_fm
		    val pith = instantiate' [] [SOME cfm] pinf_fm
		    val nmilth = instantiate' [] [SOME cfm, SOME CU] nmilbnd_fm
		    val npiuth = instantiate' [] [SOME cfm, SOME CU] npiubnd_fm
		    val lindth = instantiate' [] [SOME CU, SOME cfm] lin_dense_fm
		in ([], myfwd (mith,pith,nmilth,npiuth,lindth))
		end
	  | Const("Orderings.less_eq",_)$s$t => 
	    if s= x then 
		let val ct = cterm_of sg t
		    val tinU = nth uths (find_index (fn a => a=t) U)
		    val mith = instantiate' [] [SOME ct] minf_le
		    val pith = instantiate' [] [SOME ct] pinf_le
		    val nmilth = tinU RS nmilbnd_le
		    val npiuth = tinU RS npiubnd_le
		    val lindth = tinU RS lin_dense_le
		in ([],myfwd (mith,pith,nmilth,npiuth,lindth))
		end 
	    else if t = x then 
		let val ct = cterm_of sg s
		    val tinU = nth uths (find_index (fn a => a=s) U)
		    val mith = instantiate' [] [SOME ct] minf_ge
		    val pith = instantiate' [] [SOME ct] pinf_ge
		    val nmilth = tinU RS nmilbnd_ge
		    val npiuth = tinU RS npiubnd_ge
		    val lindth = tinU RS lin_dense_ge
		in ([],myfwd (mith,pith,nmilth,npiuth,lindth))
		end 

	    else
		let val cfm = cterm_of sg fm 
		    val mith = instantiate' [] [SOME cfm] minf_fm
		    val pith = instantiate' [] [SOME cfm] pinf_fm
		    val nmilth = instantiate' [] [SOME cfm, SOME CU] nmilbnd_fm
		    val npiuth = instantiate' [] [SOME cfm, SOME CU] npiubnd_fm
		    val lindth = instantiate' [] [SOME CU, SOME cfm] lin_dense_fm
		in ([], myfwd (mith,pith,nmilth,npiuth,lindth))
		end
	  | Const("op =",_)$s$t => 
	    if s= x then 
		let val ct = cterm_of sg t
		    val tinU = nth uths (find_index (fn a => a=t) U)
		    val mith = instantiate' [] [SOME ct] minf_eq
		    val pith = instantiate' [] [SOME ct] pinf_eq
		    val nmilth = tinU RS nmilbnd_eq
		    val npiuth = tinU RS npiubnd_eq
		    val lindth = tinU RS lin_dense_eq
		in ([],myfwd (mith,pith,nmilth,npiuth,lindth))
		end 
	    else
		let val cfm = cterm_of sg fm 
		    val mith = instantiate' [] [SOME cfm] minf_fm
		    val pith = instantiate' [] [SOME cfm] pinf_fm
		    val nmilth = instantiate' [] [SOME cfm, SOME CU] nmilbnd_fm
		    val npiuth = instantiate' [] [SOME cfm, SOME CU] npiubnd_fm
		    val lindth = instantiate' [] [SOME CU, SOME cfm] lin_dense_fm
		in ([], myfwd (mith,pith,nmilth,npiuth,lindth))
		end

	  | Const("Not",_)$(Const("op =",_)$s$t) => 
	    if s= x then 
		let val ct = cterm_of sg t
		    val tinU = nth uths (find_index (fn a => a=t) U)
		    val mith = instantiate' [] [SOME ct] minf_neq
		    val pith = instantiate' [] [SOME ct] pinf_neq
		    val nmilth = tinU RS nmilbnd_neq
		    val npiuth = tinU RS npiubnd_neq
		    val lindth = tinU RS lin_dense_neq
		in ([],myfwd (mith,pith,nmilth,npiuth,lindth))
		end 
	    else
		let val cfm = cterm_of sg fm 
		    val mith = instantiate' [] [SOME cfm] minf_fm
		    val pith = instantiate' [] [SOME cfm] pinf_fm
		    val nmilth = instantiate' [] [SOME cfm, SOME CU] nmilbnd_fm
		    val npiuth = instantiate' [] [SOME cfm, SOME CU] npiubnd_fm
		    val lindth = instantiate' [] [SOME CU, SOME cfm] lin_dense_fm
		in ([], myfwd (mith,pith,nmilth,npiuth,lindth))
		end
	  | _ => let val cfm = cterm_of sg fm 
		     val mith = instantiate' [] [SOME cfm] minf_fm
		     val pith = instantiate' [] [SOME cfm] pinf_fm
		     val nmilth = instantiate' [] [SOME cfm, SOME CU] nmilbnd_fm
		     val npiuth = instantiate' [] [SOME cfm, SOME CU] npiubnd_fm
		     val lindth = instantiate' [] [SOME CU, SOME cfm] lin_dense_fm
		 in ([], myfwd (mith,pith,nmilth,npiuth,lindth))
		 end)
    end;

fun ferrack_eq thy p = 
    case p of
	Const("Ex",_)$Abs(x1,T,p1) => 
	let val (xn,fm) = variant_abs(x1,T,p1)
	    val x = Free(xn,T)
	    val (u,cu,uths,uf) = inusetthms thy x fm
	    val (mi,pi,nmi,npi,lind) = divide_and_conquer (decomp_mpinf thy x (u,cu,uths)) fm
	    val frth = [uf,lind,nmi,npi,mi,pi] MRS fr_eq
	    val (cTp,ceq) = Thm.dest_comb (cprop_of frth)
	    val qth = (Simplifier.rewrite (HOL_basic_ss addsimps fr_simps addsimps [refl]) 
					  (snd (Thm.dest_comb ceq))) RS meta_eq_to_obj_eq
	in [frth,qth] MRS trans
	end
      | _ => instantiate' [SOME cbT] [SOME (cterm_of thy p)] refl;

(* Code for normalization of terms and Formulae *)
    (* For NNF reuse the CooperProof methods*)
    (*FIXME:: This is copied from cooper_proof.ML *)
val FWD = fn th => fn ths => ths MRS th;

val qe_Not = thm "qe_Not";
val qe_conjI = thm "qe_conjI";
val qe_disjI = thm "qe_disjI";
val qe_impI = thm "qe_impI";
val qe_eqI = thm "qe_eqI";
val qe_exI = thm "qe_exI";
val qe_ALLI = thm "qe_ALLI";

val nnf_nn = thm "nnf_nn";
val nnf_im = thm "nnf_im";
val nnf_eq = thm "nnf_eq";
val nnf_sdj = thm "nnf_sdj";
val nnf_ncj = thm "nnf_ncj";
val nnf_nim = thm "nnf_nim";
val nnf_neq = thm "nnf_neq";
val nnf_ndj = thm "nnf_ndj";

fun decomp_cnnf lfnp P = 
    case P of 
	Const ("op &",_) $ p $q => ([p,q] , FWD qe_conjI )
      | Const ("op |",_) $ p $q => ([p,q] , FWD qe_disjI)
      | Const ("Not",_) $ (Const("Not",_) $ p) => ([p], FWD nnf_nn)
      | Const("Not",_) $ (Const(opn,T) $ p $ q) => 
	if opn = "op |" 
	then 
	    (case (p,q) of 
		 (A as (Const ("op &",_) $ r $ s),B as (Const ("op &",_) $ r1 $ t)) =>
		 if r1 = CooperDec.negate r 
		 then  ([r,HOLogic.Not$s,r1,HOLogic.Not$t],
			fn [th1_1,th1_2,th2_1,th2_2] => 
			   [[th1_1,th1_1] MRS qe_conjI,[th2_1,th2_2] MRS qe_conjI] MRS nnf_sdj)
		       
		 else ([HOLogic.Not $ p,HOLogic.Not $ q ], FWD nnf_ndj)
               | (_,_) => ([HOLogic.Not $ p,HOLogic.Not $ q ], FWD nnf_ndj))
	else (
              case (opn,T) of 
		  ("op &",_) => ([HOLogic.Not $ p,HOLogic.Not $ q ], FWD nnf_ncj )
		| ("op -->",_) => ([p,HOLogic.Not $ q ], FWD nnf_nim )
		| ("op =",Type ("fun",[Type ("bool", []),_])) => 
		  ([HOLogic.conj $ p $ (HOLogic.Not $ q),HOLogic.conj $ (HOLogic.Not $ p) $ q], 
		   FWD nnf_neq)
		| (_,_) => ([], fn [] => lfnp P))
      | (Const ("op -->",_) $ p $ q) => ([HOLogic.Not$p,q], FWD nnf_im)
      | (Const ("op =", Type ("fun",[Type ("bool", []),_])) $ p $ q) =>
	([HOLogic.conj $ p $ q,HOLogic.conj $ (HOLogic.Not $ p) $ (HOLogic.Not $ q) ], FWD nnf_eq )
      | _ => ([], fn [] => lfnp P);

fun nnfp afnp vs p = 
    let val th = divide_and_conquer (decomp_cnnf (afnp vs)) p
	val Pth = (Simplifier.rewrite 
		       (HOL_basic_ss addsimps fr_simps addsimps [refl]) 
		       (snd(Thm.dest_comb(snd(Thm.dest_comb (cprop_of th))))))
		      RS meta_eq_to_obj_eq
    in [th,Pth] MRS trans
    end;


    (* Normalization of arithmetical expressions *)
val rzero = Const("0",rT);
val rone = Const("1",rT);
fun mk_real i = 
    case i of 
	0 => rzero
      | 1 => rone
      | _ => (HOLogic.number_of_const rT)$(HOLogic.mk_binum i); 

fun dest_real (Const("0",_)) = 0
  | dest_real (Const("1",_)) = 1
  | dest_real (Const("Numeral.number_of",_)$b) = HOLogic.dest_binum b;

	(* Normal form for terms is: 
	 (c0*x0 + ... + cn*xn + k) / c , where ci!=0 and x0<..<xn ordered according to vs*)
	(* functions to prove trivial properties about numbers *)
fun proveq thy n m = prove_bysimp thy (simpset_of thy) (HOLogic.mk_eq(mk_real n,mk_real m));
fun provenz thy n = 
    prove_bysimp thy (simpset_of thy) (HOLogic.Not$(HOLogic.mk_eq(mk_real n,rzero)));

fun proveprod thy m n = 
    prove_bysimp thy (simpset_of thy) 
		 (HOLogic.mk_eq(HOLogic.mk_binop "HOL.times" (mk_real m,mk_real n),mk_real (m*n)));
fun proveadd thy m n = 
    prove_bysimp thy (simpset_of thy) 
		 (HOLogic.mk_eq(HOLogic.mk_binop "HOL.plus" (mk_real m,mk_real n),mk_real (m+n)));
fun provediv thy m n = 
    let val g = gcd (m,n) 
	val m' = m div g
	val n'= n div g
    in
	(prove_bysimp thy (simpset_of thy) 
		     (HOLogic.mk_eq(HOLogic.mk_binop "HOL.divide" (mk_real m,mk_real n),
				    HOLogic.mk_binop "HOL.divide" 
						     (mk_real m',mk_real n'))),m')
    end;
		 (* Multiplication of a normal term by a constant *)
val ncmul_congh = thm "ncmul_congh";
val ncmul_cong = thm "ncmul_cong";
fun decomp_ncmulh thy c t = 
    if c = 0 then ([],fn _ => instantiate' [SOME crT] [SOME (cterm_of thy t)] mult_zero_left) else 
    case t of 
	Const("HOL.plus",_)$(Const("HOL.times",_)$c'$v)$b => 
	([b],FWD (instantiate' [] [NONE, NONE, SOME (cterm_of thy v)] 
			       ((proveprod thy c (dest_real c')) RS ncmul_congh)))
      | _ => ([],fn _ => proveprod thy c (dest_real t));

fun prove_ncmulh thy c = divide_and_conquer (decomp_ncmulh thy c);

    (* prove_ncmul thy n t n = a theorem : "c*(t/n) = (t'/n')*)
fun prove_ncmul thy c (t,m) = 
    let val (eq1,c') = provediv thy c m
	val tt' = prove_ncmulh thy c' t
    in [eq1,tt'] MRS ncmul_cong
    end;

    (* prove_nneg returns "-(t/n) = t'/n'" ; normally t'=t and n' = -n*)
val nneg_cong = thm "nneg_cong";
fun prove_nneg thy (t,m) = (prove_ncmul thy ~1 (t, m)) RS nneg_cong;

(* Addition of 2 expressions in normal form*)
val naddh_cong_same = thm "naddh_cong_same";
val naddh_cong_same0 = thm "naddh_cong_same0";
val naddh_cong_ts = thm "naddh_cong_ts";
val naddh_cong_st = thm "naddh_cong_st";

fun earlier [] x y = false 
  | earlier (h::t) x y =
    if h = y then false 
    else if h = x then true 
    else earlier t x y ; 

fun decomp_naddh thy vs (t,s) = 
    case (t,s) of 
	(Const("HOL.plus",_)$(ctv as Const("HOL.times",_)$tc$tv)$tr, 
	 Const("HOL.plus",_)$(csv as Const("HOL.times",_)$sc$sv)$sr) =>
	if tv = sv then 
	    let val ntc = dest_real tc
		val nsc = dest_real sc
		val addth = proveadd thy ntc nsc
	    in if ntc + nsc = 0 
	       then ([(tr,sr)], FWD (instantiate' [] [NONE,NONE,NONE,SOME (cterm_of thy tv)] 
						  (addth RS naddh_cong_same0)))
	       else ([(tr,sr)], FWD (instantiate' [] [NONE,NONE,NONE,SOME (cterm_of thy tv)] 
						  (addth RS naddh_cong_same)))
	    end
	else if earlier vs tv sv 
	then ([(tr,s)],FWD (instantiate' [] [NONE,NONE,NONE,SOME(cterm_of thy ctv)] naddh_cong_ts))
	else ([(t,sr)],FWD (instantiate' [] [NONE,NONE,NONE,SOME(cterm_of thy csv)] naddh_cong_st))
      | (Const("HOL.plus",_)$(ctv as Const("HOL.times",_)$tc$tv)$tr,_) => 
	([(tr,s)],FWD (instantiate' [] [NONE,NONE,NONE,SOME(cterm_of thy ctv)] naddh_cong_ts))
      | (_,Const("HOL.plus",_)$(csv as Const("HOL.times",_)$sc$sv)$sr) => 
	([(t,sr)],FWD (instantiate' [] [NONE,NONE,NONE,SOME(cterm_of thy csv)] naddh_cong_st))
      | (_,_) => ([], fn _ => proveadd thy (dest_real t) (dest_real s));

    (* prove_naddh returns "t + s = t'*) 
fun prove_naddh thy vs = divide_and_conquer (decomp_naddh thy vs);

val nadd_cong_same = thm "nadd_cong_same";
val nadd_cong = thm "nadd_cong";
val plus_cong = thm "plus_cong";
    (* prove_nadd resturns: "t/m + s/n = t'/m'"*)
fun prove_nadd thy vs (t,m) (s,n) = 
    if n=m then 
	let val nm = proveq thy n m
	    val ts = prove_naddh thy vs (t,s)
	in [nm,ts] MRS nadd_cong_same
	end
    else let val l = lcm (m,n)
	     val m' = l div m
	     val n' = l div n
	     val mml = proveprod thy m' m
	     val nnl = proveprod thy n' n
	     val mnz = provenz thy m
	     val nnz = provenz thy n
	     val lnz = provenz thy l
	     val mt = prove_ncmulh thy m' t
	     val ns = prove_ncmulh thy n' s
	     val _$(_$_$t') = prop_of mt
	     val _$(_$_$s') = prop_of ns
	 in [mml,nnl,mnz,nnz,lnz,[mt,ns,prove_naddh thy vs (t',s')] MRS plus_cong] 
		MRS nadd_cong
	 end;

    (* prove_nsub returns: "t/m - s/n = t'/m'"*)
val nsub_cong = thm "nsub_cong";
fun prove_nsub thy vs (t,m) (s,n) = 
    let val nsm = prove_nneg thy (s,n)
	val _$(_$_$(_$s'$n')) = prop_of nsm
	val ts = prove_nadd thy vs (t,m) (s',dest_real n')
    in [nsm,ts] MRS nsub_cong
    end;

val ndivide_cong = thm "ndivide_cong";
fun prove_ndivide thy (t,m) n = instantiate' [] [SOME(cterm_of thy t)] 
					     ((proveprod thy m n) RS ndivide_cong);

exception FAILURE of string;

val divide_cong = thm"divide_cong";
val diff_cong = thm"diff_cong";
val uminus_cong = thm"uminus_cong";
val mult_cong = thm"mult_cong";
val mult_cong2 = thm"mult_cong2";
val normalizeh_var = thm "normalizeh_var";
val nrefl = thm "nrefl";

fun decomp_normalizeh thy vs t =
    case t of
	Free _ => ([], fn _ => instantiate' [] [SOME(cterm_of thy t)] normalizeh_var)
      | Const("HOL.uminus",_)$a => 
	([a], 
	 fn [tha] => let val _$(_$_$(_$a'$n')) = prop_of tha
			 in [tha,prove_nneg thy (a',dest_real n')] 
				MRS uminus_cong
			 end )
      | Const("HOL.plus",_)$a$b => 
	([a,b], 
	 fn [tha,thb] => let val _$(_$_$(_$a'$n')) = prop_of tha
			     val _$(_$_$(_$b'$m')) = prop_of thb
			 in [tha,thb,prove_nadd thy vs (a',dest_real n') (b',dest_real m')] 
				MRS plus_cong
			 end )
      | Const("HOL.minus",_)$a$b => 
	([a,b], 
	 fn [tha,thb] => let val _$(_$_$(_$a'$n')) = prop_of tha
			     val _$(_$_$(_$b'$m')) = prop_of thb
			 in [tha,thb,prove_nsub thy vs (a',dest_real n') (b',dest_real m')] 
				MRS diff_cong
			 end )
      | Const("HOL.times",_)$a$b => 
	if can dest_real a 
	then ([b], fn [thb] => 
		      let val _$(_$_$(_$b'$m')) = prop_of thb
		      in [thb, prove_ncmul thy (dest_real a) (b',dest_real m')] MRS mult_cong
		      end )
	else if can dest_real b
	then ([a], fn [tha] => 
		      let val _$(_$_$(_$a'$m')) = prop_of tha
		      in [tha, prove_ncmul thy (dest_real b) (a',dest_real m')] MRS mult_cong2
		      end )
	else raise FAILURE "decomp_normalizeh: non linear term"
      | Const("HOL.divide",_)$a$b => 
	if can dest_real b
	then ([a], fn [tha] => 
		      let val _$(_$_$(_$a'$m')) = prop_of tha
		      in [tha, prove_ndivide thy (a',dest_real m') (dest_real b)] MRS divide_cong
		      end )
	else raise FAILURE "decomp_normalizeh: non linear term"
      | _ => ([], fn _ => instantiate' [] [SOME (cterm_of thy t)] nrefl);
fun prove_normalizeh thy vs = divide_and_conquer (decomp_normalizeh thy vs);
fun dest_xth vs th = 
    let val _$(_$_$(_$t$n)) = prop_of th
    in (case t of 
	    Const("HOL.plus",_)$(Const("HOL.times",_)$c$y)$r => 
	    if vs = [] then (0,t,dest_real n)
	    else if hd vs = y then (dest_real c, r,dest_real n)
	    else (0,t,dest_real n)
	  | _ => (0,t,dest_real n))
    end;

fun prove_strictsign thy n = 
    prove_bysimp thy (simpset_of thy) 
		 (HOLogic.mk_binrel "Orderings.less" 
				    (if n > 0 then (rzero, mk_real n) else (mk_real n, rzero))); 
fun prove_fracsign thy (m,n) = 
    let val mn = HOLogic.mk_binop "HOL.divide" (mk_real m, mk_real n)
    in prove_bysimp thy (simpset_of thy) 
		 (HOLogic.mk_binrel "Orderings.less" 
				    (if m*n > 0 then (rzero, mn) else (mn, rzero)))
    end; 

fun holbool_of true = HOLogic.true_const
  | holbool_of false = HOLogic.false_const;

fun prove_fracsign_eq thy s (m,n) = 
    let fun f s = the (AList.lookup (op =) [("Orderings.less", op <),("Orderings.less_eq", op <=),("op =", op =)] s)
    in 
    prove_bysimp thy (simpset_of thy) (HOLogic.mk_eq
		 (HOLogic.mk_binrel s 
				    (HOLogic.mk_binop "HOL.divide" (mk_real m, mk_real n),rzero), 
				    holbool_of (f s (m*n,0))))
    end;

fun proveq_eq thy n m = 
    prove_bysimp thy (simpset_of thy) 
		 (HOLogic.mk_eq 
		      (HOLogic.mk_eq(mk_real n, mk_real m),holbool_of (n = m)));

val sum_of_same_denoms = thm "sum_of_same_denoms";
val sum_of_opposite_denoms = thm "sum_of_opposite_denoms";
val trivial_sum_of_opposites = thm "trivial_sum_of_opposites";
val normalize_ltground_cong = thm "normalize_ltground_cong";
val normalize_ltnoxpos_cong = thm "normalize_ltnoxpos_cong";
val normalize_ltnoxneg_cong = thm "normalize_ltnoxneg_cong";
val normalize_ltxpos_cong = thm "normalize_ltxpos_cong";
val normalize_ltxneg_cong = thm "normalize_ltxneg_cong";

val normalize_leground_cong = thm "normalize_leground_cong";
val normalize_lenoxpos_cong = thm "normalize_lenoxpos_cong";
val normalize_lenoxneg_cong = thm "normalize_lenoxneg_cong";
val normalize_lexpos_cong = thm "normalize_lexpos_cong";
val normalize_lexneg_cong = thm "normalize_lexneg_cong";

val normalize_eqground_cong = thm "normalize_eqground_cong";
val normalize_eqnox_cong = thm "normalize_eqnox_cong";
val normalize_eqxpos_cong = thm "normalize_eqxpos_cong";
val normalize_eqxneg_cong = thm "normalize_eqxneg_cong";

val normalize_not_lt = thm "normalize_not_lt";
val normalize_not_le = thm "normalize_not_le";
val normalize_not_eq = thm "normalize_not_eq";

fun prove_normalize thy vs at = 
    case at of 
	Const("Orderings.less",_)$s$t => 
	let val smtth = prove_normalizeh thy vs (HOLogic.mk_binop "HOL.minus" (s,t))
	    val (cx,r,n) = dest_xth vs smtth
	in if cx = 0 then if can dest_real r 
			  then [smtth, prove_fracsign_eq thy "Orderings.less" (dest_real r, n)]
				   MRS normalize_ltground_cong
			  else [smtth, prove_strictsign thy n] 
				   MRS (if n > 0 then normalize_ltnoxpos_cong 
					else normalize_ltnoxneg_cong)
	   else let val srn = prove_fracsign thy (n,cx)
		    val rr' = if cx < 0 
			      then instantiate' [] [SOME (cterm_of thy r)]
						((proveadd thy cx (~cx)) RS sum_of_opposite_denoms)
			      else instantiate' [] [SOME (cterm_of thy (mk_real cx))] 
						(((prove_ncmulh thy ~1 r) RS nneg_cong) 
							   RS sum_of_same_denoms)
		in [smtth,srn,rr'] MRS (if n*cx < 0 then normalize_ltxneg_cong 
					else normalize_ltxpos_cong)
		end
	end
      | Const("Orderings.less_eq",_)$s$t => 
	let val smtth = prove_normalizeh thy vs (HOLogic.mk_binop "HOL.minus" (s,t))
	    val (cx,r,n) = dest_xth vs smtth
	in if cx = 0 then if can dest_real r 
			  then [smtth, prove_fracsign_eq thy "Orderings.less_eq" (dest_real r, n)]
				   MRS normalize_leground_cong
			  else [smtth, prove_strictsign thy n] 
				   MRS (if n > 0 then normalize_lenoxpos_cong 
					else normalize_lenoxneg_cong)
	   else let val srn = prove_fracsign thy (n,cx)
		    val rr' = if cx < 0 
			      then instantiate' [] [SOME (cterm_of thy r)]
						((proveadd thy cx (~cx)) RS sum_of_opposite_denoms)
			      else instantiate' [] [SOME (cterm_of thy (mk_real cx))] 
						(((prove_ncmulh thy ~1 r) RS nneg_cong) 
							   RS sum_of_same_denoms)
		in [smtth,srn,rr'] MRS (if n*cx < 0 then normalize_lexneg_cong 
					else normalize_lexpos_cong)
		end
	end
      | Const("op =",_)$s$t => 
	let val smtth = prove_normalizeh thy vs (HOLogic.mk_binop "HOL.minus" (s,t))
	    val (cx,r,n) = dest_xth vs smtth
	in if cx = 0 then if can dest_real r 
			  then [smtth, provenz thy n, 
				proveq_eq thy (dest_real r) 0]
				   MRS normalize_eqground_cong
			  else [smtth, provenz thy n] 
				   MRS normalize_eqnox_cong
	   else let val scx = prove_strictsign thy cx
		    val nnz = provenz thy n
		    val rr' = if cx < 0 
			      then proveadd thy cx (~cx)
			      else ((prove_ncmulh thy ~1 r) RS nneg_cong) 
				       RS trivial_sum_of_opposites
		in [smtth,scx,nnz,rr'] MRS (if cx < 0 then normalize_eqxneg_cong 
					else normalize_eqxpos_cong)
		end
	end
      | Const("Not",_)$(Const("Orderings.less",T)$s$t) => 
	(prove_normalize thy vs (Const("Orderings.less_eq",T)$t$s)) RS normalize_not_lt
      | Const("Not",_)$(Const("Orderings.less_eq",T)$s$t) => 
	(prove_normalize thy vs (Const("Orderings.less",T)$t$s)) RS normalize_not_le
      | (nt as Const("Not",_))$(Const("op =",T)$s$t) => 
	(prove_normalize thy vs (Const("op =",T)$s$t)) RS qe_Not
      | _ => instantiate' [SOME cbT] [SOME (cterm_of thy at)] refl;

     (* Generic quantifier elimination *)


val qe_ex_conj = thm "qe_ex_conj";
val qe_ex_nconj = thm "qe_ex_nconj";
val qe_ALL = thm "qe_ALL";
val ex_eq_cong = thm "ex_eq_cong";

fun decomp_genqelim thy afnp nfnp qfnp (P,vs) = 
    case P of
	(Const("op &",_)$A$B) => ([(A,vs),(B,vs)], fn [th1,th2] => [th1,th2] MRS qe_conjI)
      | (Const("op |",_)$A$B) => ([(A,vs),(B,vs)], fn [th1,th2] => [th1,th2] MRS qe_disjI)
      | (Const("op -->",_)$A$B) => ([(A,vs),(B,vs)], fn [th1,th2] => [th1,th2] MRS qe_impI)
      | (Const("op =", Type ("fun",[Type ("bool", []),_]))$A$B) => 
	([(A,vs),(B,vs)], fn [th1,th2] => [th1,th2] MRS qe_eqI)
      | (Const("Not",_)$p) => ([(p,vs)],fn [th] => th RS qe_Not)
      | (Const("Ex",_)$Abs(xn,xT,p)) => 
	let val (xn1,p1) = variant_abs(xn,xT,p)
	    val x= Free(xn1,xT)
	in ([(p1,x::vs)],
            fn [th1_1] => 
               let val th2 = [th1_1,nfnp (x::vs) (snd (CooperProof.qe_get_terms th1_1))] MRS trans
		   val eth1 = (forall_intr (cterm_of thy (Free(xn1,xT))) th2) COMP  ex_eq_cong
		   val th3 = qfnp (snd(CooperProof.qe_get_terms eth1))
               in [eth1,th3] MRS trans
               end )
	end
      | (Const("All",_)$Abs(xn,xT,p)) => 
	([((HOLogic.exists_const xT)$Abs(xn,xT,HOLogic.Not $ p),vs)], fn [th] => th RS qe_ALL)
      | _ => ([], fn [] => afnp vs P);

val fr_prepqelim = thms "fr_prepqelim";
val prepare_qelim_ss = HOL_basic_ss 
			   addsimps simp_thms 
			   addsimps (List.take(ex_simps,4))
			   addsimps fr_prepqelim
			   addsimps [not_all,ex_disj_distrib];

fun prove_genqelim thy afnp nfnp qfnp P = 
    let val thP = (Simplifier.rewrite prepare_qelim_ss P) RS meta_eq_to_obj_eq
	val _$(_$_$P') = prop_of thP
	val vs = term_frees P'
	val qeth = divide_and_conquer (decomp_genqelim thy afnp nfnp qfnp) (Pattern.eta_long [] P',vs)
	val _$(_$_$p'') = prop_of qeth
	val thp' = nfnp vs p''
    in [[thP, qeth] MRS trans, thp'] MRS trans
    end;

fun qelim P =
  let val {thy, ...} = Thm.rep_cterm P
  in prove_genqelim thy (prove_normalize thy) (nnfp (prove_normalize thy)) (ferrack_eq thy) P end;


    (* Just for testing!! *)
(*
val thy = the_context();
fun parseb s = term_of (read_cterm thy (s,HOLogic.boolT));
fun parser s = term_of (read_cterm thy (s,rT));
val fm = parseb "(x::real) < y + t & (y - 5 < x | 34 < y + t) & (x = s + 3*y) | (x ~= y - s)";

provediv thy 4 2;
provediv thy ~4 2;
provediv thy 4 ~2;
provediv thy 44 32;
provediv thy ~34 20000;
provediv thy ~4000000 ~27676;

val vs = [Free("x",rT),Free("y",rT),Free("z",rT)] ;
prove_nsub thy vs
		    (parser "4*(x::real) + (3*y + 5)" ,54) (parser "3*(y::real) + (4*z + 5)",9);

prove_ndivide thy (parser "4*(x::real) + (3*y + 5)" ,5) 4;
prove_normalizeh thy [Free("x",rT),Free("y",rT),Free("z",rT)] 
		    (parser "4*(x::real) + 3* ((3*y + 5) + x)");
prove_normalizeh thy [Free("x",rT),Free("y",rT),Free("z",rT)] 
		    (parser "4*(x::real) - 3* ((3*y + 5)*9 + x)");
prove_normalizeh thy [Free("x",rT),Free("y",rT),Free("z",rT)] 
		    (parser "- x");
prove_normalizeh thy [Free("x",rT),Free("y",rT),Free("z",rT)] 
		    (parser "4*(x::real) +3* ((3*y + 5) / 3 - (- x))");






fun test xn s = ferrack_eq thy (parseb ("EX (" ^ xn ^ "::real)." ^ s));
test "x" "(x::real) < y + t & (y - 5 < x | 34 < y + t) & (x = s + 3*y) | (x ~= y - s) & (x::real) <= y + t & (y - 5 <= x)";
test "x" "(x::real) < y + t & y - 5 < x & (x ~= y - s)";
test "x" "(x::real) < y + t";
test "x" "(x::real) > y + t";
test "x" "(x::real) = y + t";
test "x" "(x::real) ~= y + t";
test "x" "34 < y + (t::real)";
test "x" "(x::real) ~= y + t & 34 < y + (t::real)";
test "x" "(x::real) ~= y + t & (x::real) < y + t";

prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 <= x + y"); 
prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 <= 3*x + y"); 
prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 <= (-1)*x + y"); 
prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 <= x + 3 + 4* (y - 15*z) / 3 "); 

prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 < x + y"); 
prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 < 3*x + y"); 
prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 < (-1)*x + y"); 
prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 < x + 3 + 4* (y - 15*z) / 3 "); 

prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 = x + y"); 
prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 = 3*x + y"); 
prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 = (-1)*x + y"); 
prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 = x + 3 + 4* (y - 15*z) / 3 "); 

prove_normalize thy vs (parseb "~ ((x::real) + 4* (y - 15*z) / 3 <= x + y)"); 
prove_normalize thy vs (parseb "~ ((x::real) + 4* (y - 15*z) / 3 <= 3*x + y)"); 
prove_normalize thy vs (parseb "~ ((x::real) + 4* (y - 15*z) / 3 <= (-1)*x + y)"); 
prove_normalize thy vs (parseb "~ ((x::real) + 4* (y - 15*z) / 3 <= x + 3 + 4* (y - 15*z) / 3 )"); 

prove_normalize thy vs (parseb "~((x::real) + 4* (y - 15*z) / 3 < x + y)"); 
prove_normalize thy vs (parseb "~((x::real) + 4* (y - 15*z) / 3 < 3*x + y)"); 
prove_normalize thy vs (parseb "~((x::real) + 4* (y - 15*z) / 3 < (-1)*x + y)"); 
prove_normalize thy vs (parseb "~((x::real) + 4* (y - 15*z) / 3 < x + 3 + 4* (y - 15*z) / 3 )"); 

prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 ~= x + y"); 
prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 ~= 3*x + y"); 
prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 ~= (-1)*x + y"); 
prove_normalize thy vs (parseb "(x::real) + 4* (y - 15*z) / 3 ~= x + 3 + 4* (y - 15*z) / 3 "); 


nnfp (prove_normalize thy) vs
     (parseb "~((x::real) + 4* (y - 15*z) / 3 ~= x + 3 + 4* (y - 15*z) / 3 | (~ (~((x::real) + 4* (y - 15*z) / 3 < x + 3 + 4* (y - 15*z) / 3 ) & (x::real) + 4* (y - 15*z) / 3 <= x + y)))");
nnfp (prove_normalize thy) vs
     (parseb "~ ~((x::real) + 4* (y - 15*z) / 3 ~= x + 3 + 4* (y - 15*z) / 3 | (~ (~((x::real) + 4* (y - 15*z) / 3 < x + 3 + 4* (y - 15*z) / 3 ) & (x::real) + 4* (y - 15*z) / 3 <= x + y)))");

fun frtest s = frqelim thy (read_cterm thy (s,HOLogic.boolT));
frtest "~ (ALL (x::real) y. x < y --> 10*x < 11*y)";
frtest "ALL (x::real) y. x < y --> (10*(x + 5*y + -1) < 60*y)";
frtest "EX (x::real) y. x ~= y --> x < y";
frtest "EX (x::real) y. (x ~= y & 10*x ~= 9*y & 10*x < y) --> x < y";
frtest "ALL (x::real) y. (x ~= y & 5*x <= y) --> 500*x <= 100*y";
*)
  (* 1 Alternations *)
(*
frtest "ALL (x::real). (EX (y::real). 4*x + 3*y <= 0 & 4*x + 3*y >= -1)";
frtest "ALL (x::real) < 0. (EX (y::real) > 0. 7*x + y > 0 & x - y <= 9)";
frtest "EX (x::real). (0 < x & x < 1) --> (ALL y > 1. x + y ~= 1)";
frtest "EX (x::real). 0 < x & x < 1 & (ALL y. (1 < y & y < 2) --> (1 < 2*(y - x) & 2*(y - x) <3))";
frtest "ALL (x::real). x < 10 | x > 20 | (EX y. y>= 0 & y <= 10 & x+y = 20)";
*)
    (* Formulae with 3 quantifiers *)
  (* 0 Alternations *)
(*
frtest "ALL (x::real) y z. x + y < z --> y >= z --> x < 0";
frtest "EX (x::real) y z. x + 7*y < 5* z & 5*y >= 7*z & x < 0";
frtest "ALL (x::real) y z. abs (x + y) <= z --> (abs z = z)";
frtest "EX (x::real) y z. x + 7*y - 5* z < 0 & 5*y + 7*z + 3*x < 0";
frtest "ALL (x::real) y z. (abs (5*x+3*y+z) <= 5*x+3*y+z & abs (5*x+3*y+z) >= - (5*x+3*y+z)) | (abs (5*x+3*y+z) >= 5*x+3*y+z & abs (5*x+3*y+z) <= - (5*x+3*y+z))";
*)
  (* 1 Alternations *)
(*
frtest "ALL (x::real) y. x < y --> (EX z>0. x+z = y)";
frtest "ALL (x::real) y. (EX z>0. abs (x - y) <= z )";
frtest "EX (x::real) y. (ALL z>0. (z < x --> z <= 5) & (z > y --> z >= x))";
frtest "EX (x::real) y. (ALL z<0. (z < x --> z <= y) & (z > y --> z >= x))";
frtest "EX (x::real) y. (ALL z>0. abs (3*x - 7*y) >= 5 & abs (3*x+7*y) <= 2*z + 1)";
*)
  (* 2 Alternations *)
(*
frtest "EX (x::real)>0. (ALL y >0. (EX z>7. 5*x - 3*y <= 7*z))";
frtest "EX (x::real). abs x < 4 & (ALL y > 0. (EX z. 5*x - 3*y <= 7*z))";
frtest "ALL (x::real). (EX y > x. (ALL z < y. x+z < 2*y))" ;
frtest "ALL (x::real). (EX y<(3*x - 1). (ALL z >= (3*x - 1). x - y + z > x ))" ;
frtest "EX (x::real). abs x < 100 & (ALL y > x. (EX z<2*y - x. 5*x - 3*y <= 7*z))";
*)
    (* Formulae with 4 quantifiers *)
    (* 0 Alternations *)
(*
frtest "ALL (x::real) y z w. 7*x<3*y --> 5*y < 7*z --> z < 2*w --> 7*(2*w-x) > 2*y";
frtest "ALL (x::real) y. ALL z >x. ALL w > y. abs (z-x) + abs (y-w + x) <= z - x + w-y+abs x";
frtest "EX (x::real) y z w. 5*x + 3*z - 17*w + abs (y - 8*x + z) <= 89";
frtest "EX (x::real) y z w. abs (5*x + 3*z - 17*w) + 7* abs (y - 8*x + z) <= max y (7*z - x + w)";
frtest "EX (x::real) y z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w)";
*)
    (* 1 Alternations *)
(*
frtest "ALL (x::real) y z. (EX w >= abs (x+y+z). w <= abs x + abs y + abs z)";
frtest "ALL (x::real). (EX y z w. x< y & x < z & x> w & 3*x < w + y)";
frtest "ALL (x::real) y. (EX z w. abs (x-y) = abs (z-w) & z < x & w ~= y)";
frtest "ALL (x::real). (EX y z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w))";
frtest "EX (x::real) y z. (ALL w >= abs (x+y+z). w >= abs x + abs y + abs z)";
*)
    (* 2 Alternations *)
(*
frtest "EX z. (ALL (x::real) y. (EX w >= abs (x+y+z). w <= abs x + abs y + abs z))";
frtest "EX z. (ALL (x::real) < z. (EX y w. x< y & x < z & x> w & 3*x < w + y))";
frtest "ALL (x::real) y. (EX z. (ALL w. abs (x-y) = abs (z-w) --> z < x & w ~= y))";
frtest "EX y. (ALL (x::real). (EX z w. min (5*x + 3*z) (17*w) + 5* abs (y - 8*x + z) <= max y (7*z - x + w)))";
frtest "EX (x::real) z. (ALL w >= abs (x+z). (EX y. w >= abs x + abs y + abs z))";
*)
    (* 3 Alternations *)
(*
frtest "EX (x::real). (ALL y < x. (EX z > (x+y). (ALL w. 5*w + 10*x - z >= y --> w + 7*x + 3*z >= 2*y)))";
frtest "EX (x::real). (ALL y < 3*x. (EX z > max x y. 
  (ALL w . abs w < 13 --> w + 10*x - z >= y --> 5*w + 7*x + 13*z >= 2*y)))";
frtest "ALL (x::real). (EX y. (ALL z>19. y <= x + z & (EX w. abs (y - x) < w)))";
frtest "ALL (x::real). (EX y. (ALL z>19. abs (y) <= abs (x + z) & (EX w. abs (x + z) < w - y)))";
frtest "ALL (x::real). (EX y. abs y ~= abs x & (ALL z> max x y. (EX w. w ~= y & w ~= z & 3*w - z >= x + y)))";
*)
end
