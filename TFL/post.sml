(*  Title:      TFL/post
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Postprocessing of TFL definitions
*)

signature TFL = 
  sig
   structure Prim : TFL_sig

   val tgoalw : theory -> thm list -> thm list -> thm list
   val tgoal: theory -> thm list -> thm list

   val std_postprocessor : simpset -> theory 
                           -> {induction:thm, rules:thm, TCs:term list list} 
                           -> {induction:thm, rules:thm, nested_tcs:thm list}

   val define_i : theory -> xstring -> term -> term list
                  -> theory * Prim.pattern list

   val define   : theory -> xstring -> string -> string list 
                  -> theory * Prim.pattern list

   val simplify_defn : simpset * thm list 
                        -> theory * (string * Prim.pattern list)
                        -> {rules:thm list, induct:thm, tcs:term list}

  (*-------------------------------------------------------------------------
       val function : theory -> term -> {theory:theory, eq_ind : thm}
       val lazyR_def: theory -> term -> {theory:theory, eqns : thm}
   *-------------------------------------------------------------------------*)

  end;


structure Tfl: TFL =
struct
 structure Prim = Prim
 structure S = USyntax

(*---------------------------------------------------------------------------
 * Extract termination goals so that they can be put it into a goalstack, or 
 * have a tactic directly applied to them.
 *--------------------------------------------------------------------------*)
fun termination_goals rules = 
    map (#1 o Type.freeze_thaw o HOLogic.dest_Trueprop)
      (foldr (fn (th,A) => union_term (prems_of th, A)) (rules, []));

(*---------------------------------------------------------------------------
 * Finds the termination conditions in (highly massaged) definition and 
 * puts them into a goalstack.
 *--------------------------------------------------------------------------*)
fun tgoalw thy defs rules = 
  case termination_goals rules of
      [] => error "tgoalw: no termination conditions to prove"
    | L  => goalw_cterm defs 
              (cterm_of (sign_of thy) 
	                (HOLogic.mk_Trueprop(USyntax.list_mk_conj L)));

fun tgoal thy = tgoalw thy [];

(*---------------------------------------------------------------------------
* Three postprocessors are applied to the definition.  It
* attempts to prove wellfoundedness of the given relation, simplifies the
* non-proved termination conditions, and finally attempts to prove the 
* simplified termination conditions.
*--------------------------------------------------------------------------*)
fun std_postprocessor ss =
  Prim.postprocess
   {WFtac      = REPEAT (ares_tac [wf_measure, wf_inv_image, wf_lex_prod, 
				   wf_less_than, wf_trancl] 1),
    terminator = asm_simp_tac ss 1
		 THEN TRY(best_tac
			  (!claset addSDs [not0_implies_Suc] addss ss) 1),
    simplifier = Rules.simpl_conv ss []};



val concl = #2 o Rules.dest_thm;

(*---------------------------------------------------------------------------
 * Defining a function with an associated termination relation. 
 *---------------------------------------------------------------------------*)
fun define_i thy fid R eqs = 
  let val dummy = require_thy thy "WF_Rel" "recursive function definitions"
      val {functional,pats} = Prim.mk_functional thy eqs
  in (Prim.wfrec_definition0 thy fid R functional, pats)
  end;

(*lcp's version: takes strings; doesn't return "thm" 
        (whose signature is a draft and therefore useless) *)
fun define thy fid R eqs = 
  let fun read thy = readtm (sign_of thy) (TVar(("DUMMY",0),[])) 
  in  define_i thy fid (read thy R) (map (read thy) eqs)  end
  handle Utils.ERR {mesg,...} => error mesg;

(*---------------------------------------------------------------------------
 * Postprocess a definition made by "define". This is a separate stage of 
 * processing from the definition stage.
 *---------------------------------------------------------------------------*)
local 
structure R = Rules
structure U = Utils

(* The rest of these local definitions are for the tricky nested case *)
val solved = not o U.can S.dest_eq o #2 o S.strip_forall o concl

fun id_thm th = 
   let val {lhs,rhs} = S.dest_eq(#2(S.strip_forall(#2 (R.dest_thm th))))
   in lhs aconv rhs
   end handle _ => false

fun prover s = prove_goal HOL.thy s (fn _ => [fast_tac HOL_cs 1]);
val P_imp_P_iff_True = prover "P --> (P= True)" RS mp;
val P_imp_P_eq_True = P_imp_P_iff_True RS eq_reflection;
fun mk_meta_eq r = case concl_of r of
     Const("==",_)$_$_ => r
  |   _$(Const("op =",_)$_$_) => r RS eq_reflection
  |   _ => r RS P_imp_P_eq_True

(*Is this the best way to invoke the simplifier??*)
fun rewrite L = rewrite_rule (map mk_meta_eq (filter(not o id_thm) L))

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
fun proof_stage ss theory {f, R, rules, full_pats_TCs, TCs} =
  let val dummy = prs "Proving induction theorem..  "
      val ind = Prim.mk_induction theory f R full_pats_TCs
      val dummy = prs "Proved induction theorem.\nPostprocessing..  "
      val {rules, induction, nested_tcs} = 
	  std_postprocessor ss theory {rules=rules, induction=ind, TCs=TCs}
  in
  case nested_tcs
  of [] => (writeln "Postprocessing done.";
            {induction=induction, rules=rules,tcs=[]})
  | L  => let val dummy = prs "Simplifying nested TCs..  "
              val (solved,simplified,stubborn) =
               U.itlist (fn th => fn (So,Si,St) =>
                     if (id_thm th) then (So, Si, th::St) else
                     if (solved th) then (th::So, Si, St) 
                     else (So, th::Si, St)) nested_tcs ([],[],[])
              val simplified' = map join_assums simplified
              val rewr = full_simplify (ss addsimps (solved @ simplified'));
              val induction' = rewr induction
              and rules'     = rewr rules
              val dummy = writeln "Postprocessing done."
          in
          {induction = induction',
               rules = rules',
                 tcs = map (gen_all o S.rhs o #2 o S.strip_forall o concl)
                           (simplified@stubborn)}
          end
  end;


(*lcp: curry the predicate of the induction rule*)
fun curry_rule rl = Prod_Syntax.split_rule_var
                        (head_of (HOLogic.dest_Trueprop (concl_of rl)), 
			 rl);

(*lcp: put a theorem into Isabelle form, using meta-level connectives*)
val meta_outer = 
    curry_rule o standard o 
    rule_by_tactic (REPEAT_FIRST (resolve_tac [allI, impI, conjI]
				  ORELSE' etac conjE));

(*Strip off the outer !P*)
val spec'= read_instantiate [("x","P::?'b=>bool")] spec;

val wf_rel_defs = [lex_prod_def, measure_def, inv_image_def];

(*Convert conclusion from = to ==*)
val eq_reflect_list = map (fn th => (th RS eq_reflection) handle _ => th);

(*---------------------------------------------------------------------------
 * Install the basic context notions. Others (for nat and list and prod) 
 * have already been added in thry.sml
 *---------------------------------------------------------------------------*)
val defaultTflCongs = eq_reflect_list [Thms.LET_CONG, if_cong];

fun simplify_defn (ss, tflCongs) (thy,(id,pats)) =
   let val dummy = deny (id mem (Sign.stamp_names_of (sign_of thy)))
                        ("Recursive definition " ^ id ^ 
                         " would clash with the theory of the same name!")
       val def =  freezeT(get_def thy id)   RS   meta_eq_to_obj_eq
       val ss' = ss addsimps ((less_Suc_eq RS iffD2) :: wf_rel_defs)
       val {theory,rules,TCs,full_pats_TCs,patterns} = 
                Prim.post_definition
		   (ss', defaultTflCongs @ eq_reflect_list tflCongs)
		   (thy, (def,pats))
       val {lhs=f,rhs} = S.dest_eq(concl def)
       val (_,[R,_]) = S.strip_comb rhs
       val {induction, rules, tcs} = 
             proof_stage ss' theory 
               {f = f, R = R, rules = rules,
                full_pats_TCs = full_pats_TCs,
                TCs = TCs}
       val rules' = map (standard o normalize_thm [RSmp]) (R.CONJUNCTS rules)
   in  {induct = meta_outer
                  (normalize_thm [RSspec,RSmp] (induction RS spec')), 
        rules = rules', 
        tcs = (termination_goals rules') @ tcs}
   end
  handle Utils.ERR {mesg,func,module} => 
               error (mesg ^ 
		      "\n    (In TFL function " ^ module ^ "." ^ func ^ ")");
end;

(*---------------------------------------------------------------------------
 *
 *     Definitions with synthesized termination relation temporarily
 *     deleted -- it's not clear how to integrate this facility with
 *     the Isabelle theory file scheme, which restricts
 *     inference at theory-construction time.
 *

local structure R = Rules
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
end;


fun lazyR_def theory eqs = 
   let val {rules,theory, ...} = Prim.lazyR_def theory eqs
   in {eqns=rules, theory=theory}
   end
   handle    e              => print_exn e;
 *
 *
 *---------------------------------------------------------------------------*)
end;
