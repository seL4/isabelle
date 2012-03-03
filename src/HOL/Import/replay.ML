(*  Title:      HOL/Import/replay.ML
    Author:     Sebastian Skalberg (TU Muenchen)
*)

structure Replay =  (* FIXME proper signature *)
struct

open ProofKernel

exception REPLAY of string * string
fun ERR f mesg = REPLAY (f,mesg)
fun NY f = raise ERR f "NOT YET!"

fun replay_proof int_thms thyname thmname prf thy =
    let
        fun rp (PRefl tm) thy = ProofKernel.REFL tm thy
          | rp (PInstT(p,lambda)) thy =
            let
                val (thy',th) = rp' p thy
            in
                ProofKernel.INST_TYPE lambda th thy'
            end
          | rp (PSubst(prfs,ctxt,prf)) thy =
            let
                val (thy',ths) = fold_rev (fn p => fn (thy, ths) =>
                                           let
                                               val (thy',th) = rp' p thy
                                           in
                                               (thy',th::ths)
                                           end) prfs (thy,[])
                val (thy'',th) = rp' prf thy'
            in
                ProofKernel.SUBST ths ctxt th thy''
            end
          | rp (PAbs(prf,v)) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.ABS v th thy'
            end
          | rp (PDisch(prf,tm)) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.DISCH tm th thy'
            end
          | rp (PMp(prf1,prf2)) thy =
            let
                val (thy1,th1) = rp' prf1 thy
                val (thy2,th2) = rp' prf2 thy1
            in
                ProofKernel.MP th1 th2 thy2
            end
          | rp (PHyp tm) thy = ProofKernel.ASSUME tm thy
          | rp (PDef(seg,name,rhs)) thy =
            (case ProofKernel.get_def seg name rhs thy of
                 (thy',SOME res) => (thy',res)
               | (thy',NONE) => 
                 if seg = thyname
                 then ProofKernel.new_definition seg name rhs thy'
                 else raise ERR "replay_proof" ("Too late for term definition: "^seg^" != "^thyname))
          | rp (POracle _) thy = NY "ORACLE"
          | rp (PSpec(prf,tm)) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.SPEC tm th thy'
            end
          | rp (PInst(prf,theta)) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.INST theta th thy'
            end
          | rp (PGen(prf,v)) thy =
            let
                val (thy',th) = rp' prf thy
                val p = ProofKernel.GEN v th thy'
            in
                p
            end
          | rp (PGenAbs(prf,opt,vl)) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.GEN_ABS opt vl th thy'
            end
          | rp (PImpAS(prf1,prf2)) thy =
            let
                val (thy1,th1) = rp' prf1 thy
                val (thy2,th2) = rp' prf2 thy1
            in
                ProofKernel.IMP_ANTISYM th1 th2 thy2
            end
          | rp (PSym prf) thy =
            let
                val (thy1,th) = rp' prf thy
            in
                ProofKernel.SYM th thy1
            end
          | rp (PTrans(prf1,prf2)) thy =
            let
                val (thy1,th1) = rp' prf1 thy
                val (thy2,th2) = rp' prf2 thy1
            in
                ProofKernel.TRANS th1 th2 thy2
            end
          | rp (PComb(prf1,prf2)) thy =
            let
                val (thy1,th1) = rp' prf1 thy
                val (thy2,th2) = rp' prf2 thy1
            in
                ProofKernel.COMB th1 th2 thy2
            end
          | rp (PEqMp(prf1,prf2)) thy =
            let
                val (thy1,th1) = rp' prf1 thy
                val (thy2,th2) = rp' prf2 thy1
            in
                ProofKernel.EQ_MP th1 th2 thy2
            end
          | rp (PEqImp prf) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.EQ_IMP_RULE th thy'
            end
          | rp (PExists(prf,ex,wit)) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.EXISTS ex wit th thy'
            end
          | rp (PChoose(v,prf1,prf2)) thy =
            let
                val (thy1,th1) = rp' prf1 thy
                val (thy2,th2) = rp' prf2 thy1
            in
                ProofKernel.CHOOSE v th1 th2 thy2
            end
          | rp (PConj(prf1,prf2)) thy =
            let
                val (thy1,th1) = rp' prf1 thy
                val (thy2,th2) = rp' prf2 thy1
            in
                ProofKernel.CONJ th1 th2 thy2
            end
          | rp (PConjunct1 prf) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.CONJUNCT1 th thy'
            end
          | rp (PConjunct2 prf) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.CONJUNCT2 th thy'
            end
          | rp (PDisj1(prf,tm)) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.DISJ1 th tm thy'
            end
          | rp (PDisj2(prf,tm)) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.DISJ2 tm th thy'
            end
          | rp (PDisjCases(prf,prf1,prf2)) thy =
            let
                val (thy',th)  = rp' prf  thy
                val (thy1,th1) = rp' prf1 thy'
                val (thy2,th2) = rp' prf2 thy1
            in
                ProofKernel.DISJ_CASES th th1 th2 thy2
            end
          | rp (PNotI prf) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.NOT_INTRO th thy'
            end
          | rp (PNotE prf) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.NOT_ELIM th thy'
            end
          | rp (PContr(prf,tm)) thy =
            let
                val (thy',th) = rp' prf thy
            in
                ProofKernel.CCONTR tm th thy'
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
                                  SOME(thyname',thmname) =>
                                  (case Int.fromString thmname of
                                       SOME i =>
                                       if thyname' = thyname
                                       then
                                           (case Array.sub(int_thms,i-1) of
                                                NONE =>
                                                let
                                                    val (thy',th) = rp' (snd (import_proof thyname' thmname thy) thy) thy
                                                    val _ = Array.update(int_thms,i-1,SOME th)
                                                in
                                                    (thy',th)
                                                end
                                              | SOME th => (thy,th))
                                       else raise ERR "replay_proof" ("Library " ^ thyname' ^ " should be built before " ^ thyname ^ " (" ^ thmname ^ ")")
                                     | NONE => 
                                       (case ProofKernel.get_thm thyname' thmname thy of
                                            (thy',SOME res) => (thy',res)
                                          | (thy',NONE) => 
                                            if thyname' = thyname
                                            then
                                                let
                                                    val _ = writeln ("Found no " ^ thmname ^ " theorem, replaying...")
                                                    val (_, prf) = import_proof thyname' thmname thy'
                                                    val prf = prf thy'
                                                    val (thy',th) = replay_proof int_thms thyname' thmname prf thy'
                                                    val _ = writeln ("Successfully finished replaying "^thmname^" !")
                                                in
                                                    case content_of prf of
                                                        PTmSpec _ => (thy',th)
                                                      | PTyDef  _ => (thy',th)
                                                      | PTyIntro _ => (thy',th)
                                                      | _ => ProofKernel.store_thm thyname' thmname th thy'
                                                end
                                            else raise ERR "replay_proof" ("Library " ^ thyname' ^ " should be built before " ^ thyname ^ " (" ^ thmname ^ ")")))
                                | NONE => raise ERR "rp'.PDisk" "Not enough information")
                  | PAxm(name,c) =>
                    (case ProofKernel.get_axiom thyname name thy of
                            (thy',SOME res) => (thy',res)
                          | (thy',NONE) => ProofKernel.new_axiom name c thy')
                  | PTmSpec(seg,names,prf') =>
                    let
                        val (thy',th) = rp' prf' thy
                    in
                        ProofKernel.new_specification seg thmname names th thy'
                    end
                  | PTyDef(seg,name,prf') =>
                    let
                        val (thy',th) = rp' prf' thy
                    in
                        ProofKernel.new_type_definition seg thmname name th thy'
                    end
                  | PTyIntro(seg,name,abs_name,rep_name,P,t,prf') =>
                    let
                        val (thy',th) = rp' prf' thy
                    in
                        ProofKernel.type_introduction seg thmname name abs_name rep_name (P,t) th thy'
                    end
                  | _ => rp pc thy
            end
    in
        rp' prf thy
    end

fun setup_int_thms thyname thy =
    let
        val fname =
            case ProofKernel.get_proof_dir thyname thy of
                SOME p => OS.Path.joinDirFile {dir=p,file=OS.Path.joinBaseExt{base = "facts",ext=SOME "lst"}}
              | NONE => error "Cannot find proof files"
        val is = TextIO.openIn fname
        val (num_int_thms,facts) =
            let
                fun get_facts facts =
                    case TextIO.inputLine is of
                        NONE => (case facts of
                                   i::facts => (the (Int.fromString i),map ProofKernel.protect_factname (rev facts))
                                 | _ => raise ERR "replay_thm" "Bad facts.lst file")
                      | SOME fact => get_facts ((String.substring(fact,0,String.size fact -1 ))::facts)
            in
                get_facts []
            end
        val _ = TextIO.closeIn is
        val int_thms = Array.array(num_int_thms,NONE:thm option)
    in
        (int_thms,facts)
    end

fun import_single_thm thyname int_thms thmname thy =
    let
        fun replay_fact (thmname,thy) =
            let
                val prf = mk_proof PDisk
                val _ = set_disk_info_of prf thyname thmname
                val _ = writeln ("Replaying "^thmname^" ...")
                val p = fst (replay_proof int_thms thyname thmname prf thy)
            in
                p
            end
    in
        replay_fact (thmname,thy)
    end

fun import_thms thyname int_thms thmnames thy =
    let
        fun replay_fact thmname thy = 
            let
                val prf = mk_proof PDisk        
                val _ = set_disk_info_of prf thyname thmname
                val _ = writeln ("Replaying "^thmname^" ...")
                val p = fst (replay_proof int_thms thyname thmname prf thy)
            in
                p
            end
        val res_thy = fold replay_fact thmnames thy
    in
        res_thy
    end

fun import_thm thyname thmname thy =
    let
        val int_thms = fst (setup_int_thms thyname thy)
        fun replay_fact (thmname,thy) =
            let
                val prf = mk_proof PDisk        
                val _ = set_disk_info_of prf thyname thmname        
                val _ = writeln ("Replaying "^thmname^" ...")
                val p = fst (replay_proof int_thms thyname thmname prf thy)
            in 
                p
            end
    in
        replay_fact (thmname,thy)
    end

end
