(*  Title:      HOL/Import/shuffler.ML
    ID:         $Id$
    Author:     Sebastian Skalberg, TU Muenchen

Package for proving two terms equal by normalizing (hence the
"shuffler" name).  Uses the simplifier for the normalization.
*)

signature Shuffler =
sig
    val debug      : bool ref

    val norm_term  : theory -> term -> thm
    val make_equal : theory -> term -> term -> thm option
    val set_prop   : theory -> term -> (string * thm) list -> (string * thm) option

    val find_potential: theory -> term -> (string * thm) list

    val gen_shuffle_tac: theory -> bool -> (string * thm) list -> int -> tactic

    val shuffle_tac: (string * thm) list -> int -> tactic
    val search_tac : (string * thm) list -> int -> tactic

    val print_shuffles: theory -> unit

    val add_shuffle_rule: thm -> theory -> theory
    val shuffle_attr: theory attribute

    val setup      : (theory -> theory) list
end

structure Shuffler :> Shuffler =
struct

val debug = ref false

fun if_debug f x = if !debug then f x else ()
val message = if_debug writeln

(*Prints exceptions readably to users*)
fun print_sign_exn_unit sign e = 
  case e of
     THM (msg,i,thms) =>
	 (writeln ("Exception THM " ^ string_of_int i ^ " raised:\n" ^ msg);
	  seq print_thm thms)
   | THEORY (msg,thys) =>
	 (writeln ("Exception THEORY raised:\n" ^ msg);
	  seq (Pretty.writeln o Display.pretty_theory) thys)
   | TERM (msg,ts) =>
	 (writeln ("Exception TERM raised:\n" ^ msg);
	  seq (writeln o Sign.string_of_term sign) ts)
   | TYPE (msg,Ts,ts) =>
	 (writeln ("Exception TYPE raised:\n" ^ msg);
	  seq (writeln o Sign.string_of_typ sign) Ts;
	  seq (writeln o Sign.string_of_term sign) ts)
   | e => raise e

(*Prints an exception, then fails*)
fun print_sign_exn sign e = (print_sign_exn_unit sign e; raise e)

val string_of_thm = Library.setmp print_mode [] string_of_thm;
val string_of_cterm = Library.setmp print_mode [] string_of_cterm;

fun mk_meta_eq th =
    (case concl_of th of
	 Const("Trueprop",_) $ (Const("op =",_) $ _ $ _) => th RS eq_reflection
       | Const("==",_) $ _ $ _ => th
       | _ => raise THM("Not an equality",0,[th]))
    handle _ => raise THM("Couldn't make meta equality",0,[th])
				   
fun mk_obj_eq th =
    (case concl_of th of
	 Const("Trueprop",_) $ (Const("op =",_) $ _ $ _) => th
       | Const("==",_) $ _ $ _ => th RS meta_eq_to_obj_eq
       | _ => raise THM("Not an equality",0,[th]))
    handle _ => raise THM("Couldn't make object equality",0,[th])

structure ShuffleDataArgs: THEORY_DATA_ARGS =
struct
val name = "HOL/shuffles"
type T = thm list
val empty = []
val copy = I
val prep_ext = I
val merge = Library.gen_union Thm.eq_thm
fun print sg thms =
    Pretty.writeln (Pretty.big_list "Shuffle theorems:"
				    (map Display.pretty_thm thms))
end

structure ShuffleData = TheoryDataFun(ShuffleDataArgs)

val weaken =
    let
	val cert = cterm_of (sign_of ProtoPure.thy)
	val P = Free("P",propT)
	val Q = Free("Q",propT)
	val PQ = Logic.mk_implies(P,Q)
	val PPQ = Logic.mk_implies(P,PQ)
	val cP = cert P
	val cQ = cert Q
	val cPQ = cert PQ
	val cPPQ = cert PPQ
	val th1 = assume cPQ |> implies_intr_list [cPQ,cP]
	val th3 = assume cP
	val th4 = implies_elim_list (assume cPPQ) [th3,th3]
				    |> implies_intr_list [cPPQ,cP]
    in
	equal_intr th4 th1 |> standard
    end

val imp_comm =
    let
	val cert = cterm_of (sign_of ProtoPure.thy)
	val P = Free("P",propT)
	val Q = Free("Q",propT)
	val R = Free("R",propT)
	val PQR = Logic.mk_implies(P,Logic.mk_implies(Q,R))
	val QPR = Logic.mk_implies(Q,Logic.mk_implies(P,R))
	val cP = cert P
	val cQ = cert Q
	val cPQR = cert PQR
	val cQPR = cert QPR
	val th1 = implies_elim_list (assume cPQR) [assume cP,assume cQ]
				    |> implies_intr_list [cPQR,cQ,cP]
	val th2 = implies_elim_list (assume cQPR) [assume cQ,assume cP]
				    |> implies_intr_list [cQPR,cP,cQ]
    in
	equal_intr th1 th2 |> standard
    end

val def_norm =
    let
	val cert = cterm_of (sign_of ProtoPure.thy)
	val aT = TFree("'a",logicS)
	val bT = TFree("'b",logicS)
	val v = Free("v",aT)
	val P = Free("P",aT-->bT)
	val Q = Free("Q",aT-->bT)
	val cvPQ = cert (list_all ([("v",aT)],Logic.mk_equals(P $ Bound 0,Q $ Bound 0)))
	val cPQ = cert (Logic.mk_equals(P,Q))
	val cv = cert v
	val rew = assume cvPQ
			 |> forall_elim cv
			 |> abstract_rule "v" cv
	val (lhs,rhs) = Logic.dest_equals(concl_of rew)
	val th1 = transitive (transitive
				  (eta_conversion (cert lhs) |> symmetric)
				  rew)
			     (eta_conversion (cert rhs))
			     |> implies_intr cvPQ
	val th2 = combination (assume cPQ) (reflexive cv)
			      |> forall_intr cv
			      |> implies_intr cPQ
    in
	equal_intr th1 th2 |> standard
    end

val all_comm =
    let
	val cert = cterm_of (sign_of ProtoPure.thy)
	val xT = TFree("'a",logicS)
	val yT = TFree("'b",logicS)
	val P = Free("P",xT-->yT-->propT)
	val lhs = all xT $ (Abs("x",xT,all yT $ (Abs("y",yT,P $ Bound 1 $ Bound 0))))
	val rhs = all yT $ (Abs("y",yT,all xT $ (Abs("x",xT,P $ Bound 0 $ Bound 1))))
	val cl = cert lhs
	val cr = cert rhs
	val cx = cert (Free("x",xT))
	val cy = cert (Free("y",yT))
	val th1 = assume cr
			 |> forall_elim_list [cy,cx]
			 |> forall_intr_list [cx,cy]
			 |> implies_intr cr
	val th2 = assume cl
			 |> forall_elim_list [cx,cy]
			 |> forall_intr_list [cy,cx]
			 |> implies_intr cl
    in
	equal_intr th1 th2 |> standard
    end

val equiv_comm =
    let
	val cert = cterm_of (sign_of ProtoPure.thy)
	val T    = TFree("'a",[])
	val t    = Free("t",T)
	val u    = Free("u",T)
	val ctu  = cert (Logic.mk_equals(t,u))
	val cut  = cert (Logic.mk_equals(u,t))
	val th1  = assume ctu |> symmetric |> implies_intr ctu
	val th2  = assume cut |> symmetric |> implies_intr cut
    in
	equal_intr th1 th2 |> standard
    end

(* This simplification procedure rewrites !!x y. P x y
deterministicly, in order for the normalization function, defined
below, to handle nested quantifiers robustly *)

local

exception RESULT of int

fun find_bound n (Bound i) = if i = n then raise RESULT 0
			     else if i = n+1 then raise RESULT 1
			     else ()
  | find_bound n (t $ u) = (find_bound n t; find_bound n u)
  | find_bound n (Abs(_,_,t)) = find_bound (n+1) t
  | find_bound _ _ = ()

fun swap_bound n (Bound i) = if i = n then Bound (n+1)
			     else if i = n+1 then Bound n
			     else Bound i
  | swap_bound n (t $ u) = (swap_bound n t $ swap_bound n u)
  | swap_bound n (Abs(x,xT,t)) = Abs(x,xT,swap_bound (n+1) t)
  | swap_bound n t = t

fun rew_th sg (xv as (x,xT)) (yv as (y,yT)) t =
    let
	val lhs = list_all ([xv,yv],t)
	val rhs = list_all ([yv,xv],swap_bound 0 t)
	val rew = Logic.mk_equals (lhs,rhs)
	val init = trivial (cterm_of sg rew)
    in
	(all_comm RS init handle e => (message "rew_th"; print_exn e))
    end

fun quant_rewrite sg assumes (t as Const("all",T1) $ (Abs(x,xT,Const("all",T2) $ Abs(y,yT,body)))) =
    let
	val res = (find_bound 0 body;2) handle RESULT i => i
    in
	case res of
	    0 => Some (rew_th sg (x,xT) (y,yT) body)
	  | 1 => if string_ord(y,x) = LESS
		 then
		     let
			 val newt = Const("all",T1) $ (Abs(y,xT,Const("all",T2) $ Abs(x,yT,body)))
			 val t_th    = reflexive (cterm_of sg t)
			 val newt_th = reflexive (cterm_of sg newt)
		     in
			 Some (transitive t_th newt_th)
		     end
		 else None
	  | _ => error "norm_term (quant_rewrite) internal error"
     end
  | quant_rewrite _ _ _ = (warning "quant_rewrite: Unknown lhs"; None)

fun freeze_thaw_term t =
    let
	val tvars = term_tvars t
	val tfree_names = add_term_tfree_names(t,[])
	val (type_inst,_) =
	    foldl (fn ((inst,used),(w as (v,_),S)) =>
		      let
			  val v' = variant used v
		      in
			  ((w,TFree(v',S))::inst,v'::used)
		      end)
		  (([],tfree_names),tvars)
	val t' = subst_TVars type_inst t
    in
	(t',map (fn (w,TFree(v,S)) => (v,TVar(w,S))
		  | _ => error "Internal error in Shuffler.freeze_thaw") type_inst)
    end

fun inst_tfrees sg [] thm = thm
  | inst_tfrees sg ((name,U)::rest) thm = 
    let
	val cU = ctyp_of sg U
	val tfree_names = add_term_tfree_names (prop_of thm,[])
	val (thm',rens) = varifyT' (tfree_names \ name) thm
	val mid = 
	    case rens of
		[] => thm'
	      | [(_,idx)] => instantiate ([(idx,cU)],[]) thm'
	      | _ => error "Shuffler.inst_tfrees internal error"
    in
	inst_tfrees sg rest mid
    end

fun is_Abs (Abs _) = true
  | is_Abs _ = false

fun eta_redex (t $ Bound 0) =
    let
	fun free n (Bound i) = i = n
	  | free n (t $ u) = free n t orelse free n u
	  | free n (Abs(_,_,t)) = free (n+1) t
	  | free n _ = false
    in
	not (free 0 t)
    end
  | eta_redex _ = false

fun eta_contract sg assumes origt =
    let
	val (typet,Tinst) = freeze_thaw_term origt
	val (init,thaw) = freeze_thaw (reflexive (cterm_of sg typet))
	val final = inst_tfrees sg Tinst o thaw
	val t = #1 (Logic.dest_equals (prop_of init))
	val _ =
	    let
		val lhs = #1 (Logic.dest_equals (prop_of (final init)))
	    in
		if not (lhs aconv origt)
		then (writeln "Something is utterly wrong: (orig,lhs,frozen type,t,tinst)";
		      writeln (string_of_cterm (cterm_of sg origt));
		      writeln (string_of_cterm (cterm_of sg lhs));
		      writeln (string_of_cterm (cterm_of sg typet));
		      writeln (string_of_cterm (cterm_of sg t));
		      app (fn (n,T) => writeln (n ^ ": " ^ (string_of_ctyp (ctyp_of sg T)))) Tinst;
		      writeln "done")
		else ()
	    end
    in
	case t of
	    Const("all",_) $ (Abs(x,xT,Const("==",eqT) $ P $ Q)) =>
	    ((if eta_redex P andalso eta_redex Q
	      then
		  let
		      val cert = cterm_of sg
		      val v = Free(variant (add_term_free_names(t,[])) "v",xT)
		      val cv = cert v
		      val ct = cert t
		      val th = (assume ct)
				   |> forall_elim cv
				   |> abstract_rule x cv
		      val ext_th = eta_conversion (cert (Abs(x,xT,P)))
		      val th' = transitive (symmetric ext_th) th
		      val cu = cert (prop_of th')
		      val uth = combination (assume cu) (reflexive cv)
		      val uth' = (beta_conversion false (cert (Abs(x,xT,Q) $ v)))
				     |> transitive uth
				     |> forall_intr cv
				     |> implies_intr cu
		      val rew_th = equal_intr (th' |> implies_intr ct) uth'
		      val res = final rew_th
		      val lhs = (#1 (Logic.dest_equals (prop_of res)))
		  in
		       Some res
		  end
	      else None)
	     handle e => (writeln "eta_contract:";print_exn e))
	  | _ => (error ("Bad eta_contract argument" ^ (string_of_cterm (cterm_of sg t))); None)
    end

fun beta_fun sg assume t =
    Some (beta_conversion true (cterm_of sg t))

fun eta_expand sg assumes origt =
    let
	val (typet,Tinst) = freeze_thaw_term origt
	val (init,thaw) = freeze_thaw (reflexive (cterm_of sg typet))
	val final = inst_tfrees sg Tinst o thaw
	val t = #1 (Logic.dest_equals (prop_of init))
	val _ =
	    let
		val lhs = #1 (Logic.dest_equals (prop_of (final init)))
	    in
		if not (lhs aconv origt)
		then (writeln "Something is utterly wrong: (orig,lhs,frozen type,t,tinst)";
		      writeln (string_of_cterm (cterm_of sg origt));
		      writeln (string_of_cterm (cterm_of sg lhs));
		      writeln (string_of_cterm (cterm_of sg typet));
		      writeln (string_of_cterm (cterm_of sg t));
		      app (fn (n,T) => writeln (n ^ ": " ^ (string_of_ctyp (ctyp_of sg T)))) Tinst;
		      writeln "done")
		else ()
	    end
    in
	case t of
	    Const("==",T) $ P $ Q =>
	    if is_Abs P orelse is_Abs Q
	    then (case domain_type T of
		      Type("fun",[aT,bT]) =>
		      let
			  val cert = cterm_of sg
			  val vname = variant (add_term_free_names(t,[])) "v"
			  val v = Free(vname,aT)
			  val cv = cert v
			  val ct = cert t
			  val th1 = (combination (assume ct) (reflexive cv))
					|> forall_intr cv
					|> implies_intr ct
			  val concl = cert (concl_of th1)
			  val th2 = (assume concl)
					|> forall_elim cv
					|> abstract_rule vname cv
			  val (lhs,rhs) = Logic.dest_equals (prop_of th2)
			  val elhs = eta_conversion (cert lhs)
			  val erhs = eta_conversion (cert rhs)
			  val th2' = transitive
					 (transitive (symmetric elhs) th2)
					 erhs
			  val res = equal_intr th1 (th2' |> implies_intr concl)
			  val res' = final res
		      in
			  Some res'
		      end
		    | _ => None)
	    else None
	  | _ => (error ("Bad eta_expand argument" ^ (string_of_cterm (cterm_of sg t))); None)
    end
    handle e => (writeln "eta_expand internal error";print_exn e)

fun mk_tfree s = TFree("'"^s,logicS)
val xT = mk_tfree "a"
val yT = mk_tfree "b"
val P  = Var(("P",0),xT-->yT-->propT)
val Q  = Var(("Q",0),xT-->yT)
val R  = Var(("R",0),xT-->yT)
val S  = Var(("S",0),xT)
in
fun beta_simproc sg = Simplifier.simproc_i
		      sg
		      "Beta-contraction"
		      [Abs("x",xT,Q) $ S]
		      beta_fun

fun quant_simproc sg = Simplifier.simproc_i
			   sg
			   "Ordered rewriting of nested quantifiers"
			   [all xT $ (Abs("x",xT,all yT $ (Abs("y",yT,P $ Bound 1 $ Bound 0))))]
			   quant_rewrite
fun eta_expand_simproc sg = Simplifier.simproc_i
			 sg
			 "Smart eta-expansion by equivalences"
			 [Logic.mk_equals(Q,R)]
			 eta_expand
fun eta_contract_simproc sg = Simplifier.simproc_i
			 sg
			 "Smart handling of eta-contractions"
			 [all xT $ (Abs("x",xT,Logic.mk_equals(Q $ Bound 0,R $ Bound 0)))]
			 eta_contract
end

(* Disambiguates the names of bound variables in a term, returning t
== t' where all the names of bound variables in t' are unique *)

fun disamb_bound sg t =
    let
	
	fun F (t $ u,idx) =
	    let
		val (t',idx') = F (t,idx)
		val (u',idx'') = F (u,idx')
	    in
		(t' $ u',idx'')
	    end
	  | F (Abs(x,xT,t),idx) =
	    let
		val x' = "x" ^ (LargeInt.toString idx) (* amazing *)
		val (t',idx') = F (t,idx+1)
	    in
		(Abs(x',xT,t'),idx')
	    end
	  | F arg = arg
	val (t',_) = F (t,0)
	val ct = cterm_of sg t
	val ct' = cterm_of sg t'
	val res = transitive (reflexive ct) (reflexive ct')
	val _ = message ("disamb_term: " ^ (string_of_thm res))
    in
	res
    end

(* Transforms a term t to some normal form t', returning the theorem t
== t'.  This is originally a help function for make_equal, but might
be handy in its own right, for example for indexing terms. *)

fun norm_term thy t =
    let
	val sg = sign_of thy

	val norms = ShuffleData.get thy
	val ss = empty_ss setmksimps single
			  addsimps (map (transfer_sg sg) norms)
	fun chain f th =
	    let
		val rhs = snd (dest_equals (cprop_of th))
	    in
		transitive th (f rhs)
	    end

	val th =
	    t |> disamb_bound sg
	      |> chain (Simplifier.full_rewrite
			    (ss addsimprocs [quant_simproc sg,eta_expand_simproc sg,eta_contract_simproc sg]))
	      |> chain eta_conversion
	      |> strip_shyps
	val _ = message ("norm_term: " ^ (string_of_thm th))
    in
	th
    end
    handle e => (writeln "norm_term internal error"; print_sign_exn (sign_of thy) e)

fun is_logic_var sg v =
    Type.of_sort (Sign.tsig_of sg) (type_of v,logicS)

(* Closes a theorem with respect to free and schematic variables (does
not touch type variables, though). *)

fun close_thm th =
    let
	val sg = sign_of_thm th
	val c = prop_of th
	val all_vars = add_term_frees (c,add_term_vars(c,[]))
	val all_rel_vars = filter (is_logic_var sg) all_vars
    in
	Drule.forall_intr_list (map (cterm_of sg) all_rel_vars) th
    end
    handle e => (writeln "close_thm internal error"; print_exn e)

(* Normalizes a theorem's conclusion using norm_term. *)

fun norm_thm thy th =
    let
	val c = prop_of th
    in
	equal_elim (norm_term thy c) th
    end

(* make_equal sg t u tries to construct the theorem t == u under the
signature sg.  If it succeeds, Some (t == u) is returned, otherwise
None is returned. *)

fun make_equal sg t u =
    let
	val t_is_t' = norm_term sg t
	val u_is_u' = norm_term sg u
	val th = transitive t_is_t' (symmetric u_is_u')
	val _ = message ("make_equal: Some " ^ (string_of_thm th))
    in
	Some th
    end
    handle e as THM _ => (message "make_equal: None";None)
			 
fun match_consts ignore t (* th *) =
    let
	fun add_consts (Const (c, _), cs) =
	    if c mem_string ignore
	    then cs
	    else c ins_string cs
	  | add_consts (t $ u, cs) = add_consts (t, add_consts (u, cs))
	  | add_consts (Abs (_, _, t), cs) = add_consts (t, cs)
	  | add_consts (_, cs) = cs
	val t_consts = add_consts(t,[])
    in
     fn (name,th) =>
	let
	    val th_consts = add_consts(prop_of th,[])
	in
	    eq_set(t_consts,th_consts)
	end
    end
    
val collect_ignored =
    foldr (fn (thm,cs) =>
	      let
		  val (lhs,rhs) = Logic.dest_equals (prop_of thm)
		  val ignore_lhs = term_consts lhs \\ term_consts rhs
		  val ignore_rhs = term_consts rhs \\ term_consts lhs
	      in
		  foldr (op ins_string) (ignore_lhs @ ignore_rhs,cs)
	      end)

(* set_prop t thms tries to make a theorem with the proposition t from
one of the theorems thms, by shuffling the propositions around.  If it
succeeds, Some theorem is returned, otherwise None.  *)

fun set_prop thy t =
    let
	val sg = sign_of thy
	val all_vars = add_term_frees (t,add_term_vars (t,[]))
	val all_rel_vars = filter (is_logic_var sg) all_vars
	val closed_t = foldr (fn (v,body) => let val vT = type_of v
					     in all vT $ (Abs("x",vT,abstract_over(v,body))) end) (all_rel_vars,t)
	val rew_th = norm_term thy closed_t
	val rhs = snd (dest_equals (cprop_of rew_th))

	val shuffles = ShuffleData.get thy
	fun process [] = None
	  | process ((name,th)::thms) =
	    let
		val norm_th = varifyT (norm_thm thy (close_thm (transfer_sg sg th)))
		val triv_th = trivial rhs
		val _ = message ("Shuffler.set_prop: Gluing together " ^ (string_of_thm norm_th) ^ " and " ^ (string_of_thm triv_th))
		val mod_th = case Seq.pull (bicompose true (false,norm_th,0) 1 triv_th) of
				 Some(th,_) => Some th
			       | None => None
	    in
		case mod_th of
		    Some mod_th =>
		    let
			val closed_th = equal_elim (symmetric rew_th) mod_th
		    in
			message ("Shuffler.set_prop succeeded by " ^ name);
			Some (name,forall_elim_list (map (cterm_of sg) all_rel_vars) closed_th)
		    end
		  | None => process thms
	    end
	    handle e as THM _ => process thms
    in
	fn thms =>
	   case process thms of
	       res as Some (name,th) => if (prop_of th) aconv t
					then res
					else error "Internal error in set_prop"
	     | None => None
    end
    handle e => (writeln "set_prop internal error"; print_exn e)

fun find_potential thy t =
    let
	val shuffles = ShuffleData.get thy
	val ignored = collect_ignored(shuffles,[])
	val rel_consts = term_consts t \\ ignored
	val pot_thms = PureThy.thms_containing_consts thy rel_consts
    in
	filter (match_consts ignored t) pot_thms
    end

fun gen_shuffle_tac thy search thms i st =
    let
	val _ = message ("Shuffling " ^ (string_of_thm st))
	val t = nth_elem(i-1,prems_of st)
	val set = set_prop thy t
	fun process_tac thms st =
	    case set thms of
		Some (_,th) => Seq.of_list (compose (th,i,st))
	      | None => Seq.empty
    in
	(process_tac thms APPEND (if search
				  then process_tac (find_potential thy t)
				  else no_tac)) st
    end

fun shuffle_tac thms i st =
    gen_shuffle_tac (the_context()) false thms i st

fun search_tac thms i st =
    gen_shuffle_tac (the_context()) true thms i st

fun shuffle_meth (thms:thm list) ctxt =
    let
	val thy = ProofContext.theory_of ctxt
    in
	Method.SIMPLE_METHOD' HEADGOAL (gen_shuffle_tac thy false (map (pair "") thms))
    end

fun search_meth ctxt =
    let
	val thy = ProofContext.theory_of ctxt
	val prems = ProofContext.prems_of ctxt
    in
	Method.SIMPLE_METHOD' HEADGOAL (gen_shuffle_tac thy true (map (pair "premise") prems))
    end

val print_shuffles = ShuffleData.print

fun add_shuffle_rule thm thy =
    let
	val shuffles = ShuffleData.get thy
    in
	if exists (curry Thm.eq_thm thm) shuffles
	then (warning ((string_of_thm thm) ^ " already known to the shuffler");
	      thy)
	else ShuffleData.put (thm::shuffles) thy
    end

fun shuffle_attr (thy,thm) = (add_shuffle_rule thm thy,thm)

val setup = [Method.add_method ("shuffle_tac",Method.thms_ctxt_args shuffle_meth,"solve goal by shuffling terms around"),
	     Method.add_method ("search_tac",Method.ctxt_args search_meth,"search for suitable theorems"),
	     ShuffleData.init,
	     add_shuffle_rule weaken,
	     add_shuffle_rule equiv_comm,
	     add_shuffle_rule imp_comm,
	     add_shuffle_rule Drule.norm_hhf_eq,
	     add_shuffle_rule Drule.triv_forall_equality,
	     Attrib.add_attributes [("shuffle_rule",(Attrib.no_args shuffle_attr,K Attrib.undef_local_attribute),"tell the shuffler about the theorem")]]
end
