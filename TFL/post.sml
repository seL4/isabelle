(*-------------------------------------------------------------------------
there are 3 postprocessors that get applied to the definition:

    - a wellfoundedness prover (WF_TAC)
    - a simplifier (tries to eliminate the language of termination expressions)
    - a termination prover
*-------------------------------------------------------------------------*)

signature TFL = 
  sig
   structure Prim : TFL_sig

   val tgoalw : theory -> thm list -> thm list -> thm list
   val tgoal: theory -> thm list -> thm list

   val WF_TAC : thm list -> tactic

   val simplifier : thm -> thm
   val std_postprocessor : theory 
                           -> {induction:thm, rules:thm, TCs:term list list} 
                           -> {induction:thm, rules:thm, nested_tcs:thm list}

   val define_i : theory -> term -> term -> theory * (thm * Prim.pattern list)
   val define   : theory -> string -> string list -> theory * Prim.pattern list

   val simplify_defn : theory * (string * Prim.pattern list)
                        -> {rules:thm list, induct:thm, tcs:term list}

  (*-------------------------------------------------------------------------
       val function : theory -> term -> {theory:theory, eq_ind : thm}
       val lazyR_def: theory -> term -> {theory:theory, eqns : thm}
   *-------------------------------------------------------------------------*)

   val tflcongs : theory -> thm list

  end;


structure Tfl: TFL =
struct
 structure Prim = Prim
 structure S = Prim.USyntax

(*---------------------------------------------------------------------------
 * Extract termination goals so that they can be put it into a goalstack, or 
 * have a tactic directly applied to them.
 *--------------------------------------------------------------------------*)
fun termination_goals rules = 
    map (Logic.freeze_vars o HOLogic.dest_Trueprop)
      (foldr (fn (th,A) => union_term (prems_of th, A)) (rules, []));

 (*---------------------------------------------------------------------------
  * Finds the termination conditions in (highly massaged) definition and 
  * puts them into a goalstack.
  *--------------------------------------------------------------------------*)
 fun tgoalw thy defs rules = 
    let val L = termination_goals rules
        open USyntax
        val g = cterm_of (sign_of thy) (HOLogic.mk_Trueprop(list_mk_conj L))
    in goalw_cterm defs g
    end;

 fun tgoal thy = tgoalw thy [];

 (*---------------------------------------------------------------------------
  * Simple wellfoundedness prover.
  *--------------------------------------------------------------------------*)
 fun WF_TAC thms = REPEAT(FIRST1(map rtac thms))
 val WFtac = WF_TAC[wf_measure, wf_inv_image, wf_lex_prod, wf_less_than, 
                    wf_pred_list, wf_trancl];

 val terminator = simp_tac(!simpset addsimps [less_Suc_eq, pred_list_def]) 1
                  THEN TRY(best_tac
                           (!claset addSDs [not0_implies_Suc]
                                    addss (!simpset)) 1);

 val simpls = [less_eq RS eq_reflection,
               lex_prod_def, rprod_def, measure_def, inv_image_def];

 (*---------------------------------------------------------------------------
  * Does some standard things with the termination conditions of a definition:
  * attempts to prove wellfoundedness of the given relation; simplifies the
  * non-proven termination conditions; and finally attempts to prove the 
  * simplified termination conditions.
  *--------------------------------------------------------------------------*)
 val std_postprocessor = Prim.postprocess{WFtac = WFtac,
                                    terminator = terminator, 
                                    simplifier = Prim.Rules.simpl_conv simpls};

 val simplifier = rewrite_rule (simpls @ #simps(rep_ss (!simpset)) @ 
                                [pred_list_def]);

 fun tflcongs thy = Prim.Context.read() @ (#case_congs(Thry.extract_info thy));


val concl = #2 o Prim.Rules.dest_thm;

(*---------------------------------------------------------------------------
 * Defining a function with an associated termination relation. 
 *---------------------------------------------------------------------------*)
fun define_i thy R eqs = 
  let val dummy = require_thy thy "WF_Rel" "recursive function definitions";
      
      val {functional,pats} = Prim.mk_functional thy eqs
      val (thm,thry) = Prim.wfrec_definition0 thy  R functional
  in (thry,(thm,pats))
  end;

(*lcp's version: takes strings; doesn't return "thm" 
        (whose signature is a draft and therefore useless) *)
fun define thy R eqs = 
  let fun read thy = readtm (sign_of thy) (TVar(("DUMMY",0),[])) 
      val (thy',(_,pats)) =
             define_i thy (read thy R) 
                      (fold_bal (app Ind_Syntax.conj) (map (read thy) eqs))
  in  (thy',pats)  end
  handle Utils.ERR {mesg,...} => error mesg;

(*---------------------------------------------------------------------------
 * Postprocess a definition made by "define". This is a separate stage of 
 * processing from the definition stage.
 *---------------------------------------------------------------------------*)
local 
structure R = Prim.Rules
structure U = Utils

(* The rest of these local definitions are for the tricky nested case *)
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
fun rewrite L = rewrite_rule (map mk_meta_eq (filter(not o id_thm) L))
fun reducer thl = rewrite (map standard thl @ #simps(rep_ss HOL_ss))

fun join_assums th = 
  let val {sign,...} = rep_thm th
      val tych = cterm_of sign
      val {lhs,rhs} = S.dest_eq(#2 (S.strip_forall (concl th)))
      val cntxtl = (#1 o S.strip_imp) lhs  (* cntxtl should = cntxtr *)
      val cntxtr = (#1 o S.strip_imp) rhs  (* but union is solider *)
      val cntxt = gen_union (op aconv) (cntxtl, cntxtr)
  in 
    R.GEN_ALL 
      (R.DISCH_ALL 
         (rewrite (map (R.ASSUME o tych) cntxt) (R.SPEC_ALL th)))
  end
  val gen_all = S.gen_all
in
(*---------------------------------------------------------------------------
 * The "reducer" argument is 
 *  (fn thl => rewrite (map standard thl @ #simps(rep_ss HOL_ss))); 
 *---------------------------------------------------------------------------*)
fun proof_stage theory reducer {f, R, rules, full_pats_TCs, TCs} =
  let val dummy = output(std_out, "Proving induction theorem..  ")
      val ind = Prim.mk_induction theory f R full_pats_TCs
      val dummy = output(std_out, "Proved induction theorem.\n")
      val pp = std_postprocessor theory
      val dummy = output(std_out, "Postprocessing..  ")
      val {rules,induction,nested_tcs} = pp{rules=rules,induction=ind,TCs=TCs}
  in
  case nested_tcs
  of [] => (output(std_out, "Postprocessing done.\n");
            {induction=induction, rules=rules,tcs=[]})
  | L  => let val dummy = output(std_out, "Simplifying nested TCs..  ")
              val (solved,simplified,stubborn) =
               U.itlist (fn th => fn (So,Si,St) =>
                     if (id_thm th) then (So, Si, th::St) else
                     if (solved th) then (th::So, Si, St) 
                     else (So, th::Si, St)) nested_tcs ([],[],[])
              val simplified' = map join_assums simplified
              val induction' = reducer (solved@simplified') induction
              val rules' = reducer (solved@simplified') rules
              val dummy = output(std_out, "Postprocessing done.\n")
          in
          {induction = induction',
               rules = rules',
                 tcs = map (gen_all o S.rhs o #2 o S.strip_forall o concl)
                           (simplified@stubborn)}
          end
  end handle (e as Utils.ERR _) => Utils.Raise e
          |   e                 => print_exn e;


(*lcp: put a theorem into Isabelle form, using meta-level connectives*)
val meta_outer = 
    standard o rule_by_tactic (REPEAT_FIRST (resolve_tac [allI, impI, conjI]));


(*Strip off the outer !P*)
val spec'= read_instantiate [("x","P::?'b=>bool")] spec;


fun simplify_defn (thy,(id,pats)) =
   let val dummy = deny (id  mem  map ! (stamps_of_thy thy))
                        ("Recursive definition " ^ id ^ 
                         " would clash with the theory of the same name!")
       val def = freezeT(get_def thy id  RS  meta_eq_to_obj_eq)
       val {theory,rules,TCs,full_pats_TCs,patterns} = 
                Prim.post_definition (thy,(def,pats))
       val {lhs=f,rhs} = S.dest_eq(concl def)
       val (_,[R,_]) = S.strip_comb rhs
       val {induction, rules, tcs} = 
             proof_stage theory reducer
               {f = f, R = R, rules = rules,
                full_pats_TCs = full_pats_TCs,
                TCs = TCs}
       val rules' = map (standard o normalize_thm [RSmp]) (R.CONJUNCTS rules)
   in  {induct = meta_outer
                  (normalize_thm [RSspec,RSmp] (induction RS spec')), 
        rules = rules', 
        tcs = (termination_goals rules') @ tcs}
   end
  handle Utils.ERR {mesg,...} => error mesg
end;

(*---------------------------------------------------------------------------
 *
 *     Definitions with synthesized termination relation temporarily
 *     deleted -- it's not clear how to integrate this facility with
 *     the Isabelle theory file scheme, which restricts
 *     inference at theory-construction time.
 *

local structure R = Prim.Rules
in
fun function theory eqs = 
 let val dummy = prs "Making definition..   "
     val {rules,R,theory,full_pats_TCs,...} = Prim.lazyR_def theory eqs
     val f = func_of_cond_eqn (concl(R.CONJUNCT1 rules handle _ => rules))
     val dummy = prs "Definition made.\n"
     val dummy = prs "Proving induction theorem..  "
     val induction = Prim.mk_induction theory f R full_pats_TCs
     val dummy = prs "Induction theorem proved.\n"
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
 *
 *
 *---------------------------------------------------------------------------*)




(*---------------------------------------------------------------------------
 * Install the basic context notions. Others (for nat and list and prod) 
 * have already been added in thry.sml
 *---------------------------------------------------------------------------*)
val () = Prim.Context.write[Thms.LET_CONG, Thms.COND_CONG];

end;
