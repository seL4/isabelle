(*  Title:      Provers/simp
    Author:     Tobias Nipkow
    Copyright   1993  University of Cambridge

Generic simplifier, suitable for most logics.  The only known exception is
Constructive Type Theory.  The reflexivity axiom must be unconditional,
namely a=a not a:A ==> a=a:A.  Used typedsimp.ML otherwise.  
*)

signature SIMP_DATA =
sig
  val dest_red     : term -> term * term * term
  val mk_rew_rules : thm -> thm list
  val norm_thms    : (thm*thm) list (* [(?x>>norm(?x), norm(?x)>>?x), ...] *)
  val red1         : thm        (*  ?P>>?Q  ==>  ?P  ==>  ?Q  *)
  val red2         : thm        (*  ?P>>?Q  ==>  ?Q  ==>  ?P  *)
  val refl_thms    : thm list
  val subst_thms   : thm list   (* [ ?a>>?b ==> ?P(?a) ==> ?P(?b), ...] *)
  val trans_thms   : thm list
end;


infix 4 addrews addcongs addsplits delrews delcongs setauto;

signature SIMP =
sig
  type simpset
  val empty_ss  : simpset
  val addcongs  : simpset * thm list -> simpset
  val addrews   : simpset * thm list -> simpset
  val addsplits : simpset * thm list -> simpset
  val delcongs  : simpset * thm list -> simpset
  val delrews   : simpset * thm list -> simpset
  val dest_ss   : simpset -> thm list * thm list
  val print_ss  : simpset -> unit
  val setauto   : simpset * (thm list -> int -> tactic) -> simpset
  val ASM_SIMP_TAC      : simpset -> int -> tactic
  val SPLIT_TAC          : simpset -> int -> tactic
  val SIMP_SPLIT2_TAC    : simpset -> int -> tactic
  val SIMP_THM          : simpset -> thm -> thm
  val SIMP_TAC          : simpset -> int -> tactic
  val mk_congs          : theory -> string list -> thm list
  val mk_typed_congs    : theory -> (string * string) list -> thm list
(* temporarily disabled:
  val extract_free_congs        : unit -> thm list
*)
  val tracing   : bool ref
end;

functor SimpFun (Simp_data: SIMP_DATA) : SIMP = 
struct

local open Simp_data Logic in

(*For taking apart reductions into left, right hand sides*)
val lhs_of = #2 o dest_red;
val rhs_of = #3 o dest_red;

(*** Indexing and filtering of theorems ***)

fun eq_brl ((b1,th1),(b2,th2)) = b1=b2 andalso eq_thm(th1,th2);

(*insert a thm in a discrimination net by its lhs*)
fun lhs_insert_thm (th,net) =
    Net.insert_term((lhs_of (concl_of th), (false,th)), net, eq_brl)
    handle  Net.INSERT => net;

(*match subgoal i against possible theorems in the net.
  Similar to match_from_nat_tac, but the net does not contain numbers;
  rewrite rules are not ordered.*)
fun net_tac net =
  SUBGOAL(fn (prem,i) => 
	  match_tac (Net.match_term net (strip_assums_concl prem)) i);

(*match subgoal i against possible theorems indexed by lhs in the net*)
fun lhs_net_tac net =
  SUBGOAL(fn (prem,i) => 
	  bimatch_tac (Net.match_term net
		       (lhs_of (strip_assums_concl prem))) i);

fun nth_subgoal i thm = nth_elem(i-1,prems_of thm);

fun goal_concl i thm = strip_assums_concl(nth_subgoal i thm);

fun lhs_of_eq i thm = lhs_of(goal_concl i thm)
and rhs_of_eq i thm = rhs_of(goal_concl i thm);

fun var_lhs(thm,i) =
let fun var(Var _) = true
      | var(Abs(_,_,t)) = var t
      | var(f$_) = var f
      | var _ = false;
in var(lhs_of_eq i thm) end;

fun contains_op opns =
    let fun contains(Const(s,_)) = s mem opns |
            contains(s$t) = contains s orelse contains t |
            contains(Abs(_,_,t)) = contains t |
            contains _ = false;
    in contains end;

fun may_match(match_ops,i) = contains_op match_ops o lhs_of_eq i;

val (normI_thms,normE_thms) = split_list norm_thms;

(*Get the norm constants from norm_thms*)
val norms =
  let fun norm thm = 
      case lhs_of(concl_of thm) of
	  Const(n,_)$_ => n
	| _ => (prths normE_thms; error"No constant in lhs of a norm_thm")
  in map norm normE_thms end;

fun lhs_is_NORM(thm,i) = case lhs_of_eq i thm of
	Const(s,_)$_ => s mem norms | _ => false;

val refl_tac = resolve_tac refl_thms;

fun find_res thms thm =
    let fun find [] = (prths thms; error"Check Simp_Data")
          | find(th::thms) = thm RS th handle _ => find thms
    in find thms end;

val mk_trans = find_res trans_thms;

fun mk_trans2 thm =
let fun mk[] = error"Check transitivity"
      | mk(t::ts) = (thm RSN (2,t))  handle _  => mk ts
in mk trans_thms end;

(*Applies tactic and returns the first resulting state, FAILS if none!*)
fun one_result(tac,thm) = case Sequence.pull(tac thm) of
	Some(thm',_) => thm'
      | None => raise THM("Simplifier: could not continue", 0, [thm]);

fun res1(thm,thms,i) = one_result(resolve_tac thms i,thm);


(**** Adding "NORM" tags ****)

(*get name of the constant from conclusion of a congruence rule*)
fun cong_const cong = 
    case head_of (lhs_of (concl_of cong)) of
	Const(c,_) => c
      | _ => ""			(*a placeholder distinct from const names*);

(*true if the term is an atomic proposition (no ==> signs) *)
val atomic = null o strip_assums_hyp;

(*ccs contains the names of the constants possessing congruence rules*)
fun add_hidden_vars ccs =
  let fun add_hvars(tm,hvars) = case tm of
	      Abs(_,_,body) => add_term_vars(body,hvars)
	    | _$_ => let val (f,args) = strip_comb tm 
		     in case f of
			    Const(c,T) => 
				if c mem ccs
				then foldr add_hvars (args,hvars)
				else add_term_vars(tm,hvars)
			  | _ => add_term_vars(tm,hvars)
		     end
	    | _ => hvars;
  in add_hvars end;

fun add_new_asm_vars new_asms =
    let fun itf((tm,at),vars) =
		if at then vars else add_term_vars(tm,vars)
	fun add_list(tm,al,vars) = let val (_,tml) = strip_comb tm
		in if length(tml)=length(al)
		   then foldr itf (tml~~al,vars)
		   else vars
		end
	fun add_vars (tm,vars) = case tm of
		  Abs (_,_,body) => add_vars(body,vars)
		| r$s => (case head_of tm of
			  Const(c,T) => (case assoc(new_asms,c) of
				  None => add_vars(r,add_vars(s,vars))
				| Some(al) => add_list(tm,al,vars))
			| _ => add_vars(r,add_vars(s,vars)))
		| _ => vars
    in add_vars end;


fun add_norms(congs,ccs,new_asms) thm =
let val thm' = mk_trans2 thm;
(* thm': [?z -> l; Prems; r -> ?t] ==> ?z -> ?t *)
    val nops = nprems_of thm'
    val lhs = rhs_of_eq 1 thm'
    val rhs = lhs_of_eq nops thm'
    val asms = tl(rev(tl(prems_of thm')))
    val hvars = foldr (add_hidden_vars ccs) (lhs::rhs::asms,[])
    val hvars = add_new_asm_vars new_asms (rhs,hvars)
    fun it_asms (asm,hvars) =
	if atomic asm then add_new_asm_vars new_asms (asm,hvars)
	else add_term_frees(asm,hvars)
    val hvars = foldr it_asms (asms,hvars)
    val hvs = map (#1 o dest_Var) hvars
    val refl1_tac = refl_tac 1
    val add_norm_tac = DEPTH_FIRST (has_fewer_prems nops)
	      (STATE(fn thm =>
		case head_of(rhs_of_eq 1 thm) of
		  Var(ixn,_) => if ixn mem hvs then refl1_tac
				else resolve_tac normI_thms 1 ORELSE refl1_tac
		| Const _ => resolve_tac normI_thms 1 ORELSE
			     resolve_tac congs 1 ORELSE refl1_tac
		| Free _ => resolve_tac congs 1 ORELSE refl1_tac
		| _ => refl1_tac))
    val Some(thm'',_) = Sequence.pull(add_norm_tac thm')
in thm'' end;

fun add_norm_tags congs =
    let val ccs = map cong_const congs
	val new_asms = filter (exists not o #2)
		(ccs ~~ (map (map atomic o prems_of) congs));
    in add_norms(congs,ccs,new_asms) end;

fun normed_rews congs =
  let val add_norms = add_norm_tags congs;
  in fn thm => map (varifyT o add_norms o mk_trans) (mk_rew_rules(freezeT thm))
  end;

fun NORM norm_lhs_tac = EVERY'[resolve_tac [red2], norm_lhs_tac, refl_tac];

val trans_norms = map mk_trans normE_thms;


(* SIMPSET *)

datatype simpset =
	SS of {auto_tac: thm list -> int -> tactic,
	       congs: thm list,
	       cong_net: thm Net.net,
	       mk_simps: thm -> thm list,
	       simps: (thm * thm list) list,
	       simp_net: thm Net.net,
               splits: thm list,
               split_consts: string list}

val empty_ss = SS{auto_tac= K (K no_tac), congs=[], cong_net=Net.empty,
		  mk_simps=normed_rews[], simps=[], simp_net=Net.empty,
                  splits=[], split_consts=[]};

(** Insertion of congruences, rewrites and case splits **)

(*insert a thm in a thm net*)
fun insert_thm_warn (th,net) = 
  Net.insert_term((concl_of th, th), net, eq_thm)
  handle Net.INSERT => 
    (writeln"\nDuplicate rewrite or congruence rule:"; print_thm th;
     net);

val insert_thms = foldr insert_thm_warn;

fun addrew(SS{auto_tac,congs,cong_net,mk_simps,simps,simp_net,
              splits,split_consts}, thm) =
let val thms = mk_simps thm
in SS{auto_tac=auto_tac,congs=congs, cong_net=cong_net, mk_simps=mk_simps,
      simps = (thm,thms)::simps, simp_net = insert_thms(thms,simp_net),
      splits=splits,split_consts=split_consts}
end;

val op addrews = foldl addrew;

fun op addcongs(SS{auto_tac,congs,cong_net,mk_simps,simps,simp_net,
                   splits,split_consts}, thms) =
let val congs' = thms @ congs;
in SS{auto_tac=auto_tac, congs= congs',
      cong_net= insert_thms (map mk_trans thms,cong_net),
      mk_simps= normed_rews congs', simps=simps, simp_net=simp_net,
      splits=splits,split_consts=split_consts}
end;

fun split_err() = error("split rule not of the form ?P(c(...)) = ...");

fun split_const(_ $ t) =
       (case head_of t of Const(a,_) => a | _ => split_err())
  | split_const _ = split_err();

fun addsplit(SS{auto_tac,congs,cong_net,mk_simps,simps,simp_net,
                splits,split_consts}, thm) =
let val a = split_const(lhs_of(concl_of thm))
in SS{auto_tac=auto_tac,congs=congs,cong_net=cong_net,
      mk_simps=mk_simps,simps=simps,simp_net=simp_net,
      splits=splits@[mk_trans thm],split_consts=split_consts@[a]} end;

val op addsplits = foldl addsplit;

(** Deletion of congruences and rewrites **)

(*delete a thm from a thm net*)
fun delete_thm_warn (th,net) = 
  Net.delete_term((concl_of th, th), net, eq_thm)
  handle Net.DELETE => 
    (writeln"\nNo such rewrite or congruence rule:";  print_thm th;
     net);

val delete_thms = foldr delete_thm_warn;

fun op delcongs(SS{auto_tac,congs,cong_net,mk_simps,simps,simp_net,
                   splits,split_consts}, thms) =
let val congs' = foldl (gen_rem eq_thm) (congs,thms)
in SS{auto_tac=auto_tac, congs= congs',
      cong_net= delete_thms(map mk_trans thms,cong_net),
      mk_simps= normed_rews congs', simps=simps, simp_net=simp_net,
      splits=splits,split_consts=split_consts}
end;

fun delrew(SS{auto_tac,congs,cong_net,mk_simps,simps,simp_net,
              splits,split_consts}, thm) =
let fun find((p as (th,ths))::ps',ps) =
	  if eq_thm(thm,th) then (ths,ps@ps') else find(ps',p::ps)
      | find([],simps') = (writeln"\nNo such rewrite or congruence rule:";
			   print_thm thm;
			   ([],simps'))
    val (thms,simps') = find(simps,[])
in SS{auto_tac=auto_tac, congs=congs, cong_net=cong_net, mk_simps=mk_simps,
      simps = simps', simp_net = delete_thms(thms,simp_net),
      splits=splits,split_consts=split_consts}
end;

val op delrews = foldl delrew;


fun op setauto(SS{congs,cong_net,mk_simps,simps,simp_net,
                  splits,split_consts,...}, auto_tac) =
    SS{auto_tac=auto_tac, congs=congs, cong_net=cong_net, mk_simps=mk_simps,
       simps=simps, simp_net=simp_net,splits=splits,split_consts=split_consts};


(** Inspection of a simpset **)

fun dest_ss(SS{congs,simps,...}) = (congs, map #1 simps);

fun print_ss(SS{congs,simps,splits,...}) =
	(writeln"Congruences:"; prths congs;
         writeln"Case Splits"; prths splits;
	 writeln"Rewrite Rules:"; prths (map #1 simps); ());


(* Rewriting with case splits *)

fun splittable a i thm =
    let val tm = goal_concl i thm
	fun nobound(Abs(_,_,tm),j,k) = nobound(tm,j,k+1)
	  | nobound(s$t,j,k) = nobound(s,j,k) andalso nobound(t,j,k)
	  | nobound(Bound n,j,k) = n < k orelse k+j <= n
	  | nobound(_) = true;
	fun check_args(al,j) = forall (fn t => nobound(t,j,0)) al
	fun find_if(Abs(_,_,tm),j) = find_if(tm,j+1)
	  | find_if(tm as s$t,j) = let val (f,al) = strip_comb tm in
		case f of Const(c,_) =>	if c=a then check_args(al,j)
			else find_if(s,j) orelse find_if(t,j)
		| _ => find_if(s,j) orelse find_if(t,j) end
	  | find_if(_) = false;
    in find_if(tm,0) end;

fun split_tac (cong_tac,splits,split_consts) i =
    let fun seq_try (split::splits,a::bs) thm = tapply(
		COND (splittable a i) (DETERM(resolve_tac[split]i))
			((seq_try(splits,bs))), thm)
	      | seq_try([],_) thm = no_tac thm
	and try_rew thm = tapply((seq_try(splits,split_consts))
				 ORELSE one_subt, thm)
	and one_subt thm =
		let val test = has_fewer_prems (nprems_of thm + 1)
		    fun loop thm = tapply(COND test no_tac
			((try_rew THEN DEPTH_FIRST test (refl_tac i))
			 ORELSE (refl_tac i THEN loop)), thm)
		in (cong_tac THEN loop) thm end
    in if null splits then no_tac
       else COND (may_match(split_consts,i)) try_rew no_tac
    end;

fun SPLIT_TAC (SS{cong_net,splits,split_consts,...}) i =
let val cong_tac = net_tac cong_net i
in NORM (split_tac (cong_tac,splits,split_consts)) i end;

(* Rewriting Automaton *)

datatype cntrl = STOP | MK_EQ | ASMS of int | SIMP_LHS | REW | REFL | TRUE
	       | PROVE | POP_CS | POP_ARTR | SPLIT;
(*
fun pr_cntrl c = case c of STOP => prs("STOP") | MK_EQ => prs("MK_EQ") |
ASMS i => print_int i | POP_ARTR => prs("POP_ARTR") |
SIMP_LHS => prs("SIMP_LHS") | REW => prs("REW") | REFL => prs("REFL") |
TRUE => prs("TRUE") | PROVE => prs("PROVE") | POP_CS => prs("POP_CS") | SPLIT
=> prs("SPLIT");
*)
fun simp_refl([],_,ss) = ss
  | simp_refl(a'::ns,a,ss) = if a'=a then simp_refl(ns,a,SIMP_LHS::REFL::ss)
	else simp_refl(ns,a,ASMS(a)::SIMP_LHS::REFL::POP_ARTR::ss);

(** Tracing **)

val tracing = ref false;

(*Replace parameters by Free variables in P*)
fun variants_abs ([],P) = P
  | variants_abs ((a,T)::aTs, P) =
      variants_abs (aTs, #2 (variant_abs(a,T,P)));

(*Select subgoal i from proof state; substitute parameters, for printing*)
fun prepare_goal i st =
    let val subgi = nth_subgoal i st
	val params = rev(strip_params subgi)
    in variants_abs (params, strip_assums_concl subgi) end;

(*print lhs of conclusion of subgoal i*)
fun pr_goal_lhs i st =
    writeln (Sign.string_of_term (#sign(rep_thm st)) 
	     (lhs_of (prepare_goal i st)));

(*print conclusion of subgoal i*)
fun pr_goal_concl i st =
    writeln (Sign.string_of_term (#sign(rep_thm st)) (prepare_goal i st)) 

(*print subgoals i to j (inclusive)*)
fun pr_goals (i,j) st =
    if i>j then ()
    else (pr_goal_concl i st;  pr_goals (i+1,j) st);

(*Print rewrite for tracing; i=subgoal#, n=number of new subgoals,
  thm=old state, thm'=new state *)
fun pr_rew (i,n,thm,thm',not_asms) =
    if !tracing
    then (if not_asms then () else writeln"Assumption used in";
          pr_goal_lhs i thm; writeln"->"; pr_goal_lhs (i+n) thm';
	  if n>0 then (writeln"Conditions:"; pr_goals (i, i+n-1) thm')
          else ();
          writeln"" )
    else ();

(* Skip the first n hyps of a goal, and return the rest in generalized form *)
fun strip_varify(Const("==>", _) $ H $ B, n, vs) =
	if n=0 then subst_bounds(vs,H)::strip_varify(B,0,vs)
	else strip_varify(B,n-1,vs)
  | strip_varify(Const("all",_)$Abs(_,T,t), n, vs) =
	strip_varify(t,n,Var(("?",length vs),T)::vs)
  | strip_varify  _  = [];

fun execute(ss,if_fl,auto_tac,cong_tac,splits,split_consts,net,i) thm = let

fun simp_lhs(thm,ss,anet,ats,cs) =
    if var_lhs(thm,i) then (ss,thm,anet,ats,cs) else
    if lhs_is_NORM(thm,i) then (ss, res1(thm,trans_norms,i), anet,ats,cs)
    else case Sequence.pull(cong_tac i thm) of
	    Some(thm',_) =>
		    let val ps = prems_of thm and ps' = prems_of thm';
			val n = length(ps')-length(ps);
			val a = length(strip_assums_hyp(nth_elem(i-1,ps)))
			val l = map (fn p => length(strip_assums_hyp(p)))
				    (take(n,drop(i-1,ps')));
		    in (simp_refl(rev(l),a,REW::ss),thm',anet,ats,cs) end
	  | None => (REW::ss,thm,anet,ats,cs);

(*NB: the "Adding rewrites:" trace will look strange because assumptions
      are represented by rules, generalized over their parameters*)
fun add_asms(ss,thm,a,anet,ats,cs) =
    let val As = strip_varify(nth_subgoal i thm, a, []);
	val thms = map (trivial o cterm_of(#sign(rep_thm(thm))))As;
	val new_rws = flat(map mk_rew_rules thms);
	val rwrls = map mk_trans (flat(map mk_rew_rules thms));
	val anet' = foldr lhs_insert_thm (rwrls,anet)
    in  if !tracing andalso not(null new_rws)
	then (writeln"Adding rewrites:";  prths new_rws;  ())
	else ();
	(ss,thm,anet',anet::ats,cs) 
    end;

fun rew(seq,thm,ss,anet,ats,cs, more) = case Sequence.pull seq of
      Some(thm',seq') =>
	    let val n = (nprems_of thm') - (nprems_of thm)
	    in pr_rew(i,n,thm,thm',more);
	       if n=0 then (SIMP_LHS::ss, thm', anet, ats, cs)
	       else ((replicate n PROVE) @ (POP_CS::SIMP_LHS::ss),
		     thm', anet, ats, (ss,thm,anet,ats,seq',more)::cs)
	    end
    | None => if more
	    then rew(tapply(lhs_net_tac anet i THEN assume_tac i,thm),
		     thm,ss,anet,ats,cs,false)
	    else (ss,thm,anet,ats,cs);

fun try_true(thm,ss,anet,ats,cs) =
    case Sequence.pull(auto_tac i thm) of
      Some(thm',_) => (ss,thm',anet,ats,cs)
    | None => let val (ss0,thm0,anet0,ats0,seq,more)::cs0 = cs
	      in if !tracing
		 then (writeln"*** Failed to prove precondition. Normal form:";
		       pr_goal_concl i thm;  writeln"")
		 else ();
		 rew(seq,thm0,ss0,anet0,ats0,cs0,more)
	      end;

fun split(thm,ss,anet,ats,cs) =
	case Sequence.pull(tapply(split_tac
                                  (cong_tac i,splits,split_consts) i,thm)) of
		Some(thm',_) => (SIMP_LHS::SPLIT::ss,thm',anet,ats,cs)
	      | None => (ss,thm,anet,ats,cs);

fun step(s::ss, thm, anet, ats, cs) = case s of
	  MK_EQ => (ss, res1(thm,[red2],i), anet, ats, cs)
	| ASMS(a) => add_asms(ss,thm,a,anet,ats,cs)
	| SIMP_LHS => simp_lhs(thm,ss,anet,ats,cs)
	| REW => rew(net_tac net i thm,thm,ss,anet,ats,cs,true)
	| REFL => (ss, res1(thm,refl_thms,i), anet, ats, cs)
	| TRUE => try_true(res1(thm,refl_thms,i),ss,anet,ats,cs)
	| PROVE => (if if_fl then MK_EQ::SIMP_LHS::SPLIT::TRUE::ss
		    else MK_EQ::SIMP_LHS::TRUE::ss, thm, anet, ats, cs)
	| POP_ARTR => (ss,thm,hd ats,tl ats,cs)
	| POP_CS => (ss,thm,anet,ats,tl cs)
	| SPLIT => split(thm,ss,anet,ats,cs);

fun exec(state as (s::ss, thm, _, _, _)) =
	if s=STOP then thm else exec(step(state));

in exec(ss, thm, Net.empty, [], []) end;


(*ss = list of commands (not simpset!); 
  fl = even use case splits to solve conditional rewrite rules;
  addhyps = add hyps to simpset*)
fun EXEC_TAC (ss,fl,addhyps) simpset = METAHYPS 
 (fn hyps => 
     case (if addhyps then simpset addrews hyps else simpset) of
         (SS{auto_tac,cong_net,simp_net,splits,split_consts,...}) =>
	     PRIMITIVE(execute(ss,fl,auto_tac hyps,
			       net_tac cong_net,splits,split_consts,
                               simp_net, 1))
	     THEN TRY(auto_tac hyps 1));

val SIMP_TAC = EXEC_TAC([MK_EQ,SIMP_LHS,SPLIT,REFL,STOP],false,false);

val ASM_SIMP_TAC = 
    EXEC_TAC([ASMS(0),MK_EQ,SIMP_LHS,SPLIT,REFL,STOP],false,true);

val SIMP_SPLIT2_TAC = EXEC_TAC([MK_EQ,SIMP_LHS,SPLIT,REFL,STOP],true,false);

fun REWRITE (ss,fl) (SS{auto_tac,cong_net,simp_net,splits,split_consts,...}) =
let val cong_tac = net_tac cong_net
in fn thm =>
   let val state = thm RSN (2,red1)
   in execute(ss,fl,auto_tac[],cong_tac,splits,split_consts,simp_net,1)state
   end
end;

val SIMP_THM = REWRITE ([ASMS(0),SIMP_LHS,SPLIT,REFL,STOP],false);


(* Compute Congruence rules for individual constants using the substition
   rules *)

val subst_thms = map standard subst_thms;


fun exp_app(0,t) = t
  | exp_app(i,t) = exp_app(i-1,t $ Bound (i-1));

fun exp_abs(Type("fun",[T1,T2]),t,i) =
	Abs("x"^string_of_int i,T1,exp_abs(T2,t,i+1))
  | exp_abs(T,t,i) = exp_app(i,t);

fun eta_Var(ixn,T) = exp_abs(T,Var(ixn,T),0);


fun Pinst(f,fT,(eq,eqT),k,i,T,yik,Ts) =
let fun xn_list(x,n) =
	let val ixs = map (fn i => (x^(radixstring(26,"a",i)),0)) (0 upto n);
	in map eta_Var (ixs ~~ (take(n+1,Ts))) end
    val lhs = list_comb(f,xn_list("X",k-1))
    val rhs = list_comb(f,xn_list("X",i-1) @ [Bound 0] @ yik)
in Abs("", T, Const(eq,[fT,fT]--->eqT) $ lhs $ rhs) end;

fun find_subst tsig T =
let fun find (thm::thms) =
	let val (Const(_,cT), va, vb) =	dest_red(hd(prems_of thm));
	    val [P] = term_vars(concl_of thm) \\ [va,vb]
	    val eqT::_ = binder_types cT
        in if Type.typ_instance(tsig,T,eqT) then Some(thm,va,vb,P)
	   else find thms
	end
      | find [] = None
in find subst_thms end;

fun mk_cong sg (f,aTs,rT) (refl,eq) =
let val tsig = #tsig(Sign.rep_sg sg);
    val k = length aTs;
    fun ri((subst,va as Var(_,Ta),vb as Var(_,Tb),P),i,si,T,yik) =
	let val ca = cterm_of sg va
	    and cx = cterm_of sg (eta_Var(("X"^si,0),T))
	    val cb = cterm_of sg vb
	    and cy = cterm_of sg (eta_Var(("Y"^si,0),T))
	    val cP = cterm_of sg P
	    and cp = cterm_of sg (Pinst(f,rT,eq,k,i,T,yik,aTs))
	in cterm_instantiate [(ca,cx),(cb,cy),(cP,cp)] subst end;
    fun mk(c,T::Ts,i,yik) =
	let val si = radixstring(26,"a",i)
	in case find_subst tsig T of
	     None => mk(c,Ts,i-1,eta_Var(("X"^si,0),T)::yik)
	   | Some s => let val c' = c RSN (2,ri(s,i,si,T,yik))
		       in mk(c',Ts,i-1,eta_Var(("Y"^si,0),T)::yik) end
	end
      | mk(c,[],_,_) = c;
in mk(refl,rev aTs,k-1,[]) end;

fun mk_cong_type sg (f,T) =
let val (aTs,rT) = strip_type T;
    val tsig = #tsig(Sign.rep_sg sg);
    fun find_refl(r::rs) =
	let val (Const(eq,eqT),_,_) = dest_red(concl_of r)
	in if Type.typ_instance(tsig, rT, hd(binder_types eqT))
	   then Some(r,(eq,body_type eqT)) else find_refl rs
	end
      | find_refl([]) = None;
in case find_refl refl_thms of
     None => []  |  Some(refl) => [mk_cong sg (f,aTs,rT) refl]
end;

fun mk_cong_thy thy f =
let val sg = sign_of thy;
    val T = case Sign.const_type sg f of
		None => error(f^" not declared") | Some(T) => T;
    val T' = incr_tvar 9 T;
in mk_cong_type sg (Const(f,T'),T') end;

fun mk_congs thy = filter_out is_fact o flat o map (mk_cong_thy thy);

fun mk_typed_congs thy =
let val sg = sign_of thy;
    val S0 = Type.defaultS(#tsig(Sign.rep_sg sg))
    fun readfT(f,s) =
	let val T = incr_tvar 9 (Sign.read_typ(sg,K(Some(S0))) s);
	    val t = case Sign.const_type sg f of
		      Some(_) => Const(f,T) | None => Free(f,T)
	in (t,T) end
in flat o map (mk_cong_type sg o readfT) end;

(* This code is fishy, esp the "let val T' = ..." 
fun extract_free_congs() =
let val {prop,sign,...} = rep_thm(topthm());
    val frees = add_term_frees(prop,[]);
    fun filter(Free(a,T as Type("fun",_))) =
	  let val T' = incr_tvar 9 (Type.varifyT T)
	  in [(Free(a,T),T)] end
      | filter _ = []
in flat(map (mk_cong_type sign) (flat (map filter frees))) end;
*)

end (* local *)
end (* SIMP *);
