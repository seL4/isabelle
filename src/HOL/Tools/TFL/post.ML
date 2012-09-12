(*  Title:      HOL/Tools/TFL/post.ML
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Second part of main module (postprocessing of TFL definitions).
*)

signature TFL =
sig
  val define_i: bool -> Proof.context -> thm list -> thm list -> xstring -> term -> term list ->
    theory -> {lhs: term, rules: (thm * int) list, induct: thm, tcs: term list} * theory
  val define: bool -> Proof.context -> thm list -> thm list -> xstring -> string -> string list ->
    theory -> {lhs: term, rules: (thm * int) list, induct: thm, tcs: term list} * theory
  val defer_i: thm list -> xstring -> term list -> theory -> thm * theory
  val defer: thm list -> xstring -> string list -> theory -> thm * theory
end;

structure Tfl: TFL =
struct

(* misc *)

(*---------------------------------------------------------------------------
 * Extract termination goals so that they can be put it into a goalstack, or
 * have a tactic directly applied to them.
 *--------------------------------------------------------------------------*)
fun termination_goals rules =
    map (Type.legacy_freeze o HOLogic.dest_Trueprop)
      (fold_rev (union (op aconv) o prems_of) rules []);

(*---------------------------------------------------------------------------
 * Three postprocessors are applied to the definition.  It
 * attempts to prove wellfoundedness of the given relation, simplifies the
 * non-proved termination conditions, and finally attempts to prove the
 * simplified termination conditions.
 *--------------------------------------------------------------------------*)
fun std_postprocessor strict ctxt wfs =
  Prim.postprocess strict
   {wf_tac = REPEAT (ares_tac wfs 1),
    terminator =
      asm_simp_tac (simpset_of ctxt) 1
      THEN TRY (Arith_Data.arith_tac ctxt 1 ORELSE
        fast_force_tac (ctxt addSDs [@{thm not0_implies_Suc}]) 1),
    simplifier = Rules.simpl_conv (simpset_of ctxt) []};



val concl = #2 o Rules.dest_thm;

(*---------------------------------------------------------------------------
 * Postprocess a definition made by "define". This is a separate stage of
 * processing from the definition stage.
 *---------------------------------------------------------------------------*)
local

(* The rest of these local definitions are for the tricky nested case *)
val solved = not o can USyntax.dest_eq o #2 o USyntax.strip_forall o concl

fun id_thm th =
   let val {lhs,rhs} = USyntax.dest_eq (#2 (USyntax.strip_forall (#2 (Rules.dest_thm th))));
   in lhs aconv rhs end
   handle Utils.ERR _ => false;
   
val P_imp_P_eq_True = @{thm eqTrueI} RS eq_reflection;
fun mk_meta_eq r = case concl_of r of
     Const("==",_)$_$_ => r
  |   _ $(Const(@{const_name HOL.eq},_)$_$_) => r RS eq_reflection
  |   _ => r RS P_imp_P_eq_True

(*Is this the best way to invoke the simplifier??*)
fun rewrite L = rewrite_rule (map mk_meta_eq (filter_out id_thm L))

fun join_assums th =
  let val thy = Thm.theory_of_thm th
      val tych = cterm_of thy
      val {lhs,rhs} = USyntax.dest_eq(#2 (USyntax.strip_forall (concl th)))
      val cntxtl = (#1 o USyntax.strip_imp) lhs  (* cntxtl should = cntxtr *)
      val cntxtr = (#1 o USyntax.strip_imp) rhs  (* but union is solider *)
      val cntxt = union (op aconv) cntxtl cntxtr
  in
    Rules.GEN_ALL
      (Rules.DISCH_ALL
         (rewrite (map (Rules.ASSUME o tych) cntxt) (Rules.SPEC_ALL th)))
  end
  val gen_all = USyntax.gen_all
in
fun proof_stage strict ctxt wfs theory {f, R, rules, full_pats_TCs, TCs} =
  let
    val _ = writeln "Proving induction theorem ..."
    val ind = Prim.mk_induction theory {fconst=f, R=R, SV=[], pat_TCs_list=full_pats_TCs}
    val _ = writeln "Postprocessing ...";
    val {rules, induction, nested_tcs} =
      std_postprocessor strict ctxt wfs theory {rules=rules, induction=ind, TCs=TCs}
  in
  case nested_tcs
  of [] => {induction=induction, rules=rules,tcs=[]}
  | L  => let val dummy = writeln "Simplifying nested TCs ..."
              val (solved,simplified,stubborn) =
               fold_rev (fn th => fn (So,Si,St) =>
                     if (id_thm th) then (So, Si, th::St) else
                     if (solved th) then (th::So, Si, St)
                     else (So, th::Si, St)) nested_tcs ([],[],[])
              val simplified' = map join_assums simplified
              val dummy = (Prim.trace_thms "solved =" solved;
                           Prim.trace_thms "simplified' =" simplified')
              val rewr = full_simplify (simpset_of ctxt addsimps (solved @ simplified'));
              val dummy = Prim.trace_thms "Simplifying the induction rule..."
                                          [induction]
              val induction' = rewr induction
              val dummy = Prim.trace_thms "Simplifying the recursion rules..."
                                          [rules]
              val rules'     = rewr rules
              val _ = writeln "... Postprocessing finished";
          in
          {induction = induction',
               rules = rules',
                 tcs = map (gen_all o USyntax.rhs o #2 o USyntax.strip_forall o concl)
                           (simplified@stubborn)}
          end
  end;


(*lcp: curry the predicate of the induction rule*)
fun curry_rule rl =
  Split_Rule.split_rule_var (Term.head_of (HOLogic.dest_Trueprop (concl_of rl))) rl;

(*lcp: put a theorem into Isabelle form, using meta-level connectives*)
fun meta_outer ctxt =
  curry_rule o Drule.export_without_context o
  rule_by_tactic ctxt (REPEAT (FIRSTGOAL (resolve_tac [allI, impI, conjI] ORELSE' etac conjE)));

(*Strip off the outer !P*)
val spec'= read_instantiate @{context} [(("x", 0), "P::?'b=>bool")] spec;

fun tracing true _ = ()
  | tracing false msg = writeln msg;

fun simplify_defn strict thy ctxt congs wfs id pats def0 =
   let
       val def = Thm.unvarify_global def0 RS meta_eq_to_obj_eq
       val {rules,rows,TCs,full_pats_TCs} =
           Prim.post_definition congs (thy, (def, pats))
       val {lhs=f,rhs} = USyntax.dest_eq (concl def)
       val (_,[R,_]) = USyntax.strip_comb rhs
       val dummy = Prim.trace_thms "congs =" congs
       (*the next step has caused simplifier looping in some cases*)
       val {induction, rules, tcs} =
             proof_stage strict ctxt wfs thy
               {f = f, R = R, rules = rules,
                full_pats_TCs = full_pats_TCs,
                TCs = TCs}
       val rules' = map (Drule.export_without_context o Object_Logic.rulify_no_asm)
                        (Rules.CONJUNCTS rules)
         in  {induct = meta_outer ctxt (Object_Logic.rulify_no_asm (induction RS spec')),
        rules = ListPair.zip(rules', rows),
        tcs = (termination_goals rules') @ tcs}
   end
  handle Utils.ERR {mesg,func,module} =>
               error (mesg ^
                      "\n    (In TFL function " ^ module ^ "." ^ func ^ ")");


(* Derive the initial equations from the case-split rules to meet the
users specification of the recursive function. *)
local
  fun get_related_thms i = 
      map_filter ((fn (r,x) => if x = i then SOME r else NONE));

  fun solve_eq _ (th, [], i) =  error "derive_init_eqs: missing rules"
    | solve_eq _ (th, [a], i) = [(a, i)]
    | solve_eq ctxt (th, splitths, i) =
      (writeln "Proving unsplit equation...";
      [((Drule.export_without_context o Object_Logic.rulify_no_asm)
          (CaseSplit.splitto ctxt splitths th), i)])
      handle ERROR s => 
             (warning ("recdef (solve_eq): " ^ s); map (fn x => (x,i)) splitths);
in
fun derive_init_eqs ctxt rules eqs =
  map (Thm.trivial o Thm.cterm_of (Proof_Context.theory_of ctxt) o HOLogic.mk_Trueprop) eqs
  |> map_index (fn (i, e) => solve_eq ctxt (e, (get_related_thms i rules), i))
  |> flat;
end;


(*---------------------------------------------------------------------------
 * Defining a function with an associated termination relation.
 *---------------------------------------------------------------------------*)
fun define_i strict ctxt congs wfs fid R eqs thy =
  let val {functional,pats} = Prim.mk_functional thy eqs
      val (thy, def) = Prim.wfrec_definition0 thy fid R functional
      val ctxt' = Proof_Context.transfer thy ctxt
      val (lhs, _) = Logic.dest_equals (prop_of def)
      val {induct, rules, tcs} = simplify_defn strict thy ctxt' congs wfs fid pats def
      val rules' = 
          if strict then derive_init_eqs ctxt rules eqs
          else rules
  in ({lhs = lhs, rules = rules', induct = induct, tcs = tcs}, thy) end;

fun define strict ctxt congs wfs fid R seqs thy =
  define_i strict ctxt congs wfs fid
      (Syntax.read_term ctxt R) (map (Syntax.read_term ctxt) seqs) thy
    handle Utils.ERR {mesg,...} => error mesg;


(*---------------------------------------------------------------------------
 *
 *     Definitions with synthesized termination relation
 *
 *---------------------------------------------------------------------------*)

fun func_of_cond_eqn tm =
  #1 (USyntax.strip_comb (#lhs (USyntax.dest_eq (#2 (USyntax.strip_forall (#2 (USyntax.strip_imp tm)))))));

fun defer_i congs fid eqs thy =
 let val {rules,R,theory,full_pats_TCs,SV,...} = Prim.lazyR_def thy fid congs eqs
     val f = func_of_cond_eqn (concl (Rules.CONJUNCT1 rules handle Utils.ERR _ => rules));
     val dummy = writeln "Proving induction theorem ...";
     val induction = Prim.mk_induction theory
                        {fconst=f, R=R, SV=SV, pat_TCs_list=full_pats_TCs}
 in
   (*return the conjoined induction rule and recursion equations,
     with assumptions remaining to discharge*)
   (Drule.export_without_context (induction RS (rules RS conjI)), theory)
 end

fun defer congs fid seqs thy =
  defer_i congs fid (map (Syntax.read_term_global thy) seqs) thy
    handle Utils.ERR {mesg,...} => error mesg;
end;

end;
