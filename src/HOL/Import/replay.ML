structure Replay =
struct

structure P = ProofKernel

open ProofKernel

exception REPLAY of string * string
fun ERR f mesg = REPLAY (f,mesg)
fun NY f = raise ERR f "NOT YET!"

fun replay_proof int_thms thyname thmname prf thy =
    let
	fun rp (PRefl tm) thy = P.REFL tm thy
	  | rp (PInstT(p,lambda)) thy =
	    let
		val (thy',th) = rp' p thy
	    in
		P.INST_TYPE lambda th thy'
	    end
	  | rp (PSubst(prfs,ctxt,prf)) thy =
	    let
		val (thy',ths) = foldr (fn (p,(thy,ths)) =>
					   let
					       val (thy',th) = rp' p thy
					   in
					       (thy',th::ths)
					   end) (prfs,(thy,[]))
		val (thy'',th) = rp' prf thy'
	    in
		P.SUBST ths ctxt th thy''
	    end
	  | rp (PAbs(prf,v)) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.ABS v th thy'
	    end
	  | rp (PDisch(prf,tm)) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.DISCH tm th thy'
	    end
	  | rp (PMp(prf1,prf2)) thy =
	    let
		val (thy1,th1) = rp' prf1 thy
		val (thy2,th2) = rp' prf2 thy1
	    in
		P.MP th1 th2 thy2
	    end
	  | rp (PHyp tm) thy = P.ASSUME tm thy
	  | rp (PDef(seg,name,rhs)) thy =
	    (case P.get_def seg name rhs thy of
		 (thy',Some res) => (thy',res)
	       | (thy',None) => 
		 if seg = thyname
		 then P.new_definition seg name rhs thy'
		 else raise ERR "replay_proof" "Too late for term definition")
	  | rp (POracle(tg,asl,c)) thy = (*P.mk_oracle_thm tg (map be_contract asl,c)*) NY "ORACLE"
	  | rp (PSpec(prf,tm)) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.SPEC tm th thy'
	    end
	  | rp (PInst(prf,theta)) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.INST theta th thy'
	    end
	  | rp (PGen(prf,v)) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.GEN v th thy'
	    end
	  | rp (PGenAbs(prf,opt,vl)) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.GEN_ABS opt vl th thy'
	    end
	  | rp (PImpAS(prf1,prf2)) thy =
	    let
		val (thy1,th1) = rp' prf1 thy
		val (thy2,th2) = rp' prf2 thy1
	    in
		P.IMP_ANTISYM th1 th2 thy2
	    end
	  | rp (PSym prf) thy =
	    let
		val (thy1,th) = rp' prf thy
	    in
		P.SYM th thy1
	    end
	  | rp (PTrans(prf1,prf2)) thy =
	    let
		val (thy1,th1) = rp' prf1 thy
		val (thy2,th2) = rp' prf2 thy1
	    in
		P.TRANS th1 th2 thy2
	    end
	  | rp (PComb(prf1,prf2)) thy =
	    let
		val (thy1,th1) = rp' prf1 thy
		val (thy2,th2) = rp' prf2 thy1
	    in
		P.COMB th1 th2 thy2
	    end
	  | rp (PEqMp(prf1,prf2)) thy =
	    let
		val (thy1,th1) = rp' prf1 thy
		val (thy2,th2) = rp' prf2 thy1
	    in
		P.EQ_MP th1 th2 thy2
	    end
	  | rp (PEqImp prf) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.EQ_IMP_RULE th thy'
	    end
	  | rp (PExists(prf,ex,wit)) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.EXISTS ex wit th thy'
	    end
	  | rp (PChoose(v,prf1,prf2)) thy =
	    let
		val (thy1,th1) = rp' prf1 thy
		val (thy2,th2) = rp' prf2 thy1
	    in
		P.CHOOSE v th1 th2 thy2
	    end
	  | rp (PConj(prf1,prf2)) thy =
	    let
		val (thy1,th1) = rp' prf1 thy
		val (thy2,th2) = rp' prf2 thy1
	    in
		P.CONJ th1 th2 thy2
	    end
	  | rp (PConjunct1 prf) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.CONJUNCT1 th thy'
	    end
	  | rp (PConjunct2 prf) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.CONJUNCT2 th thy'
	    end
	  | rp (PDisj1(prf,tm)) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.DISJ1 th tm thy'
	    end
	  | rp (PDisj2(prf,tm)) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.DISJ2 tm th thy'
	    end
	  | rp (PDisjCases(prf,prf1,prf2)) thy =
	    let
		val (thy',th)  = rp' prf  thy
		val (thy1,th1) = rp' prf1 thy'
		val (thy2,th2) = rp' prf2 thy1
	    in
		P.DISJ_CASES th th1 th2 thy2
	    end
	  | rp (PNotI prf) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.NOT_INTRO th thy'
	    end
	  | rp (PNotE prf) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.NOT_ELIM th thy'
	    end
	  | rp (PContr(prf,tm)) thy =
	    let
		val (thy',th) = rp' prf thy
	    in
		P.CCONTR tm th thy'
	    end
	  | rp (PTmSpec _) _ = raise ERR "rp" "Shouldn't reach here (PTmSpec)"
	  | rp (PTyDef _) _ = raise ERR "rp" "Shouldn't reach here (PTyDef)"
	  | rp (PTyIntro _) _ = raise ERR "rp" "Shouldn't reach here (PTyIntro)"
	  | rp PDisk _ = raise ERR "rp" "Shouldn't reach here (PDisk)"
	  | rp _ _ = raise ERR "rp" "What the hell is this? Which case did I forget?"
	and rp' p thy =
	    let
		val pc = content_of p
	    in
		case pc of
		    PDisk => (case disk_info_of p of
				  Some(thyname',thmname) =>
				  (case Int.fromString thmname of
				       SOME i =>
				       if thyname' = thyname
				       then
					   (case Array.sub(int_thms,i-1) of
						None =>
						let
						    val (thy',th) = rp' (snd (import_proof thyname' thmname thy) thy) thy
						    val _ = Array.update(int_thms,i-1,Some th)
						in
						    (thy',th)
						end
					      | Some th => (thy,th))
				       else raise ERR "replay_proof" ("Library " ^ thyname' ^ " should be built before " ^ thyname ^ " (" ^ thmname ^ ")")
				     | NONE => 
				       (case P.get_thm thyname' thmname thy of
					    (thy',Some res) => (thy',res)
					  | (thy',None) => 
					    if thyname' = thyname
					    then
						let
						    val _ = writeln ("Found no " ^ thmname ^ " theorem, replaying...")
						    val (f_opt,prf) = import_proof thyname' thmname thy'
						    val prf = prf thy'
						    val (thy',th) = replay_proof int_thms thyname' thmname prf thy'
						in
						    case content_of prf of
							PTmSpec _ => (thy',th)
						      | PTyDef  _ => (thy',th)
						      | PTyIntro _ => (thy',th)
						      | _ => P.store_thm thyname' thmname th thy'
						end
					    else raise ERR "replay_proof" ("Library " ^ thyname' ^ " should be built before " ^ thyname ^ " (" ^ thmname ^ ")")))
				| None => raise ERR "rp'.PDisk" "Not enough information")
		  | PAxm(name,c) =>
		    (case P.get_axiom thyname name thy of
			    (thy',Some res) => (thy',res)
			  | (thy',None) => P.new_axiom name c thy')
		  | PTmSpec(seg,names,prf') =>
		    let
			val (thy',th) = rp' prf' thy
		    in
			P.new_specification seg thmname names th thy'
		    end
		  | PTyDef(seg,name,prf') =>
		    let
			val (thy',th) = rp' prf' thy
		    in
			P.new_type_definition seg thmname name th thy'
		    end
		  | PTyIntro(seg,name,abs_name,rep_name,P,t,prf') =>
		    let
			val (thy',th) = rp' prf' thy
		    in
			P.type_introduction seg thmname name abs_name rep_name (P,t) th thy'
		    end
		  | _ => rp pc thy
	    end
    in
	rp' prf thy handle e => (writeln "Exception in replay_proof"; print_exn e)
    end

fun setup_int_thms thyname thy =
    let
	val is = TextIO.openIn(P.get_proof_dir thyname thy ^"/facts.lst")
	val (num_int_thms,facts) =
	    let
		fun get_facts facts =
		    case TextIO.inputLine is of
			"" => (case facts of
				   i::facts => (valOf (Int.fromString i),rev facts)
				 | _ => raise ERR "replay_thm" "Bad facts.lst file")
		      | fact => get_facts ((String.substring(fact,0,String.size fact -1 ))::facts)
	    in
		get_facts []
	    end
	val _ = TextIO.closeIn is
	val int_thms = Array.array(num_int_thms,None:thm option)
    in
	(int_thms,facts)
    end

fun import_single_thm thyname int_thms thmname thy =
    let
	fun replay_fact (thmname,thy) =
	    let
		val _ = writeln ("Replaying " ^ thmname)
		val prf = mk_proof PDisk
		val _ = set_disk_info_of prf thyname thmname
	    in
		fst (replay_proof int_thms thyname thmname prf thy)
	    end
    in
	replay_fact (thmname,thy)
    end

fun import_thms thyname int_thms thmnames thy =
    let
	fun replay_fact (thy,thmname) =
	    let
		val _ = writeln ("Replaying " ^ thmname)
		val prf = mk_proof PDisk
		val _ = set_disk_info_of prf thyname thmname
	    in
		fst (replay_proof int_thms thyname thmname prf thy)
	    end
	val res_thy = foldl replay_fact (thy,thmnames)
    in
	res_thy
    end

fun import_thm thyname thmname thy =
    let
	val int_thms = fst (setup_int_thms thyname thy)
	fun replay_fact (thmname,thy) =
	    let
		val _ = writeln ("Replaying " ^ thmname)
		val prf = mk_proof PDisk
		val _ = set_disk_info_of prf thyname thmname
	    in
		fst (replay_proof int_thms thyname thmname prf thy)
	    end
    in
	replay_fact (thmname,thy)
    end

end
