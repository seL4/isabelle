structure Tfl
 :sig
   structure Prim : TFL_sig

   val tgoalw : theory -> thm list -> thm -> thm list
   val tgoal: theory -> thm -> thm list

   val WF_TAC : thm list -> tactic

   val simplifier : thm -> thm
   val std_postprocessor : theory 
                           -> {induction:thm, rules:thm, TCs:term list list} 
                           -> {induction:thm, rules:thm, nested_tcs:thm list}

   val rfunction  : theory
                     -> (thm list -> thm -> thm)
                        -> term -> term  
                          -> {induction:thm, rules:thm, 
                              tcs:term list, theory:theory}

   val Rfunction : theory -> term -> term  
                   -> {induction:thm, rules:thm, 
                       theory:theory, tcs:term list}

   val function : theory -> term -> {theory:theory, eq_ind : thm}
   val lazyR_def : theory -> term -> {theory:theory, eqns : thm}

   val tflcongs : theory -> thm list

  end = 
struct
 structure Prim = Prim

 fun tgoalw thy defs thm = 
    let val L = Prim.termination_goals thm
        open USyntax
        val g = cterm_of (sign_of thy) (mk_prop(list_mk_conj L))
    in goalw_cterm defs g
    end;

 val tgoal = Utils.C tgoalw [];

 fun WF_TAC thms = REPEAT(FIRST1(map rtac thms))
 val WFtac = WF_TAC[wf_measure, wf_inv_image, wf_lex_prod, 
                    wf_pred_nat, wf_pred_list, wf_trancl];

 val terminator = simp_tac(HOL_ss addsimps[pred_nat_def,pred_list_def,
                                           fst_conv,snd_conv,
                                           mem_Collect_eq,lessI]) 1
                  THEN TRY(fast_tac set_cs 1);

 val simpls = [less_eq RS eq_reflection,
               lex_prod_def, measure_def, inv_image_def, 
               fst_conv RS eq_reflection, snd_conv RS eq_reflection,
               mem_Collect_eq RS eq_reflection(*, length_Cons RS eq_reflection*)];

 val std_postprocessor = Prim.postprocess{WFtac = WFtac,
                                    terminator = terminator, 
                                    simplifier = Prim.Rules.simpl_conv simpls};

 val simplifier = rewrite_rule (simpls @ #simps(rep_ss HOL_ss) @ 
                                [pred_nat_def,pred_list_def]);
 fun tflcongs thy = Prim.Context.read() @ (#case_congs(Thry.extract_info thy));


local structure S = Prim.USyntax
in
fun func_of_cond_eqn tm =
  #1(S.strip_comb(#lhs(S.dest_eq(#2(S.strip_forall(#2(S.strip_imp tm)))))))
end;


val concl = #2 o Prim.Rules.dest_thm;

(*---------------------------------------------------------------------------
 * Defining a function with an associated termination relation. Lots of
 * postprocessing takes place.
 *---------------------------------------------------------------------------*)
local 
structure S = Prim.USyntax
structure R = Prim.Rules
structure U = Utils

val solved = not o U.can S.dest_eq o #2 o S.strip_forall o concl

fun id_thm th = 
   let val {lhs,rhs} = S.dest_eq(#2(S.strip_forall(#2 (R.dest_thm th))))
   in S.aconv lhs rhs
   end handle _ => false

fun prover s = prove_goal HOL.thy s (fn _ => [fast_tac HOL_cs 1]);
val P_imp_P_iff_True = prover "P --> (P= True)" RS mp;
val P_imp_P_eq_True = P_imp_P_iff_True RS eq_reflection;
fun mk_meta_eq r = case concl_of r of
     Const("==",_)$_$_ => r
  |   _$(Const("op =",_)$_$_) => r RS eq_reflection
  |   _ => r RS P_imp_P_eq_True
fun rewrite L = rewrite_rule (map mk_meta_eq (Utils.filter(not o id_thm) L))

fun join_assums th = 
  let val {sign,...} = rep_thm th
      val tych = cterm_of sign
      val {lhs,rhs} = S.dest_eq(#2 (S.strip_forall (concl th)))
      val cntxtl = (#1 o S.strip_imp) lhs  (* cntxtl should = cntxtr *)
      val cntxtr = (#1 o S.strip_imp) rhs  (* but union is solider *)
      val cntxt = U.union S.aconv cntxtl cntxtr
  in 
  R.GEN_ALL 
  (R.DISCH_ALL 
    (rewrite (map (R.ASSUME o tych) cntxt) (R.SPEC_ALL th)))
  end
  val gen_all = S.gen_all
in
fun rfunction theory reducer R eqs = 
 let val _ = prs "Making definition..  "
     val {rules,theory, full_pats_TCs,
          TCs,...} = Prim.gen_wfrec_definition theory {R=R,eqs=eqs} 
     val f = func_of_cond_eqn(concl(R.CONJUNCT1 rules handle _ => rules))
     val _ = prs "Definition made.\n"
     val _ = prs "Proving induction theorem..  "
     val ind = Prim.mk_induction theory f R full_pats_TCs
     val _ = prs "Proved induction theorem.\n"
     val pp = std_postprocessor theory
     val _ = prs "Postprocessing..  "
     val {rules,induction,nested_tcs} = pp{rules=rules,induction=ind,TCs=TCs}
     val normal_tcs = Prim.termination_goals rules
 in
 case nested_tcs
 of [] => (prs "Postprocessing done.\n";
           {theory=theory, induction=induction, rules=rules,tcs=normal_tcs})
  | L  => let val _ = prs "Simplifying nested TCs..  "
              val (solved,simplified,stubborn) =
               U.itlist (fn th => fn (So,Si,St) =>
                     if (id_thm th) then (So, Si, th::St) else
                     if (solved th) then (th::So, Si, St) 
                     else (So, th::Si, St)) nested_tcs ([],[],[])
              val simplified' = map join_assums simplified
              val induction' = reducer (solved@simplified') induction
              val rules' = reducer (solved@simplified') rules
              val _ = prs "Postprocessing done.\n"
          in
          {induction = induction',
               rules = rules',
                 tcs = normal_tcs @
                      map (gen_all o S.rhs o #2 o S.strip_forall o concl)
                           (simplified@stubborn),
              theory = theory}
          end
 end
 handle (e as Utils.ERR _) => Utils.Raise e
     |     e               => print_exn e


fun Rfunction thry = 
     rfunction thry 
       (fn thl => rewrite (map standard thl @ #simps(rep_ss HOL_ss)));


end;


local structure R = Prim.Rules
in
fun function theory eqs = 
 let val _ = prs "Making definition..  "
     val {rules,R,theory,full_pats_TCs,...} = Prim.lazyR_def theory eqs
     val f = func_of_cond_eqn (concl(R.CONJUNCT1 rules handle _ => rules))
     val _ = prs "Definition made.\n"
     val _ = prs "Proving induction theorem..  "
     val induction = Prim.mk_induction theory f R full_pats_TCs
     val _ = prs "Induction theorem proved.\n"
 in {theory = theory, 
     eq_ind = standard (induction RS (rules RS conjI))}
 end
 handle (e as Utils.ERR _) => Utils.Raise e
      |     e              => print_exn e
end;


fun lazyR_def theory eqs = 
   let val {rules,theory, ...} = Prim.lazyR_def theory eqs
   in {eqns=rules, theory=theory}
   end
   handle (e as Utils.ERR _) => Utils.Raise e
        |     e              => print_exn e;


 val () = Prim.Context.write[Thms.LET_CONG, Thms.COND_CONG];

end;
