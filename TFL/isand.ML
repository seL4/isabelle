(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/isand.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Date:       6 Aug 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Natural Deduction tools

    For working with Isbaelle theorem in a natural detuction style,
    ie, not having to deal with meta level quantified varaibles,
    instead, we work with newly introduced frees, and hide the
    "all"'s, exporting results from theorems proved with the frees, to
    solve the all cases of the previous goal. 

    Note: A nice idea: allow esxporting to solve any subgoal, thus
    allowing the interleaving of proof, or provide a structure for the
    ordering of proof, thus allowing proof attempts in parrelle, but
    recording the order to apply things in.

debugging tools:
fun asm_mk t = (assume (cterm_of (Theory.sign_of (the_context())) t)); 
fun asm_read s =  
    (assume (read_cterm (Theory.sign_of (Context.the_context())) (s,propT))); 

    THINK: are we really ok with our varify name w.r.t the prop - do
    we alos need to avoid named in the hidden hyps?

*)

structure IsaND =
struct

(* Solve *some* subgoal of "th" directly by "sol" *)
(* Note: this is probably what Markus ment to do upon export of a
"show" but maybe he used RS/rtac instead, which would wrongly lead to
failing if there are premices to the shown goal. *)
fun solve_with sol th = 
    let fun solvei 0 = Seq.empty
          | solvei i = 
            Seq.append (bicompose false (false,sol,0) i th, 
                        solvei (i - 1))
    in
      solvei (Thm.nprems_of th)
    end;


(* Given ctertmify function, (string,type) pairs capturing the free
vars that need to be allified in the assumption, and a theorem with
assumptions possibly containing the free vars, then we give back the
assumptions allified as hidden hyps. *)
(* 
Given: vs 
th: A vs ==> B vs
Results in: "B vs" [!!x. A x]
*)
fun allify_conditions ctermify Ts th = 
    let 
      val premts = Thm.prems_of th
    
      fun allify_prem_var (vt as (n,ty),t)  = 
          (Term.all ty) $ (Abs(n,ty,Term.abstract_over (Free vt, t)))

      fun allify_prem Ts p = foldr allify_prem_var (Ts, p)

      val cTs = map (ctermify o Free) Ts
      val cterm_asms = map (ctermify o allify_prem Ts) premts
      val allifyied_asm_thms = map (Drule.forall_elim_list cTs o Thm.assume) cterm_asms
    in
      (foldl (fn (x,y) => y RS x) (th, allifyied_asm_thms), cterm_asms)
    end;

fun allify_conditions' Ts th = 
    allify_conditions (Thm.cterm_of (Thm.sign_of_thm th)) Ts th;



(* change schematic vars to fresh free vars *)
fun fix_vars_to_frees th = 
    let 
      val ctermify = Thm.cterm_of (Thm.sign_of_thm th)
      val prop = Thm.prop_of th
      val vars = map Term.dest_Var (Term.term_vars prop)

      val names = Term.add_term_names (prop, [])

      val (insts,names2) = 
          foldl (fn ((insts,names),v as ((n,i),ty)) => 
                    let val n2 = Term.variant names n in
                      ((ctermify (Var v), ctermify (Free(n2,ty))) :: insts, 
                       n2 :: names)
                    end)
                (([],names), vars)
    in (insts, Thm.instantiate ([], insts) th) end;

(* *)
(*
val th = Thm.freezeT (topthm());
val (insts, th') = fix_vars_to_frees th;
val Ts = map (Term.dest_Free o Thm.term_of o snd) insts;
allify_conditions' Ts th';
*)


(* datatype to capture an exported result, ie a fix or assume. *)
datatype export = 
         export of {fixes : Thm.cterm list, (* fixed vars *)
                    assumes : Thm.cterm list, (* hidden hyps/assumed prems *)
                    sgid : int,
                    gth :  Thm.thm}; (* subgoal/goalthm *)



(* export the result of the new goal thm, ie if we reduced teh
subgoal, then we get a new reduced subtgoal with the old
all-quantified variables *)
local 
fun allify_term (v, t) = 
    let val vt = #t (Thm.rep_cterm v)
      val (n,ty) = Term.dest_Free vt
    in (Term.all ty) $ (Abs(n,ty,Term.abstract_over (vt, t))) end;

fun allify_for_sg_term ctermify vs t =
    let val t_alls = foldr allify_term (vs,t);
        val ct_alls = ctermify t_alls; 
    in 
      (ct_alls, Drule.forall_elim_list vs (Thm.assume ct_alls))
    end;

fun lookupfree vs vn  = 
    case Library.find_first (fn (n,ty) => n = vn) vs of 
      None => raise ERROR_MESSAGE ("prepare_goal_export:lookupfree: " 
                    ^ vn ^ " does not occur in the term")
    | Some x => x;
in
fun export_back (export {fixes = vs, assumes = hprems, 
                         sgid = i, gth = gth}) newth = 
    let 
      val sgn = Thm.sign_of_thm newth;
      val ctermify = Thm.cterm_of sgn;

      val sgs = prems_of newth;
      val (sgallcts, sgthms) = 
          Library.split_list (map (allify_for_sg_term ctermify vs) sgs);
      val minimal_newth = 
          (foldl (fn ( newth', sgthm) => 
                          Drule.compose_single (sgthm, 1, newth'))
                      (newth, sgthms));
      val allified_newth = 
          minimal_newth 
            |> Drule.implies_intr_list hprems
            |> Drule.forall_intr_list vs 

      val newth' = Drule.implies_intr_list sgallcts allified_newth
    in
      bicompose false (false, newth', (length sgallcts)) i gth
    end;

(* given a thm of the form: 
P1 vs; ...; Pn vs ==> Goal(C vs)

Gives back: 
n,
[| !! vs. P1 vs; !! vs. Pn vs |] 
  ==> !! C vs
*)
(* note: C may contain further premices etc 
Note that cterms is the assumed facts, ie prems of "P1" that are
reintroduced.
*)
fun prepare_goal_export (vs, cterms) th = 
    let 
      val sgn = Thm.sign_of_thm th;
      val ctermify = Thm.cterm_of sgn;

      val allfrees = map Term.dest_Free (Term.term_frees (Thm.prop_of th))
      val cfrees = map (ctermify o Free o lookupfree allfrees) vs

      val sgs = prems_of th;
      val (sgallcts, sgthms) = 
          Library.split_list (map (allify_for_sg_term ctermify cfrees) sgs);

      val minimal_th = 
          (foldl (fn ( th', sgthm) => 
                          Drule.compose_single (sgthm, 1, th'))
                      (th, sgthms)) RS Drule.rev_triv_goal;

      val allified_th = 
          minimal_th 
            |> Drule.implies_intr_list cterms
            |> Drule.forall_intr_list cfrees 

      val th' = Drule.implies_intr_list sgallcts allified_th
    in
      ((length sgallcts), th')
    end;

end;

(* val exports_back = foldr (uncurry export_to_sg); *)

(* test with:

fun asm_mk t = (assume (cterm_of (Theory.sign_of (the_context())) t)); 
fun asm_read s =  
    (assume (read_cterm (Theory.sign_of (Context.the_context())) (s,propT))); 
use_thy "theories/dbg2";
Goal "!! x :: nat. [| A x; B x; C x; D x |] ==> ((P1 x & P2 x) & P3 x)";
by (rtac conjI 1);
by (rtac conjI 1);
val th = topthm();
val i = 1;
val (gthi, exp) = IsaND.fix_alls i th;
val [th'] = Seq.list_of (rtac (thm "p321") 1 gthi);
val oldthewth = Seq.list_of (IsaND.export_back exp th');
 or 
val [th'] = Seq.list_of (RWStepTac.rwstep_tac (thms "aa2") 1 gthi);
val oldthewth = Seq.list_of (IsaND.export_back exp th');


val th = topthm();
val i = 1;
val (goalth, exp1) = IsaND.fix_alls' i th;
val (newth, exp2) = IsaND.hide_other_goals 2 goalth;
val oldthewth = Seq.list_of (IsaND.export_back exp2 newth);
val (export {fixes = vs, assumes = hprems, 
                            sgid = i, gth = gth}) = exp2;


Goal "!! x y. P (x + (Suc y)) ==> Z x y ==> Q ((Suc x) + y)"; 
val th = topthm();
val i = 1;
val (gthi, exp) = IsaND.fix_alls i th;
val newth = Seq.hd (Asm_full_simp_tac 1 gthi);
Seq.list_of (IsaND.export_back exp newth);
*)



(* exporting function that takes a solution to the fixed/assumed goal,
and uses this to solve the subgoal in the main theorem *)
fun export_solution (export {fixes = cfvs, assumes = hcprems,
                             sgid = i, gth = gth}) solth = 
    let 
      val solth' = 
          solth |> Drule.implies_intr_list hcprems
                |> Drule.forall_intr_list cfvs
    in Drule.compose_single (solth', i, gth) end;

val exports_solution = foldr (uncurry export_solution);




(* fix parameters of a subgoal "i", as free variables, and create an
exporting function that will use the result of this proved goal to
show the goal in the original theorem. 

Note, an advantage of this over Isar is that it supports instantiation
of unkowns in the earlier theorem, ie we can do instantiation of meta
vars! *)
(* loosely corresponds to:
Given "[| SG0; ... !! x. As ==> SGi x; ... SGm |] ==> G" : thm
Result: 
  ("(As ==> SGi x') ==> (As ==> SGi x')" : thm, 
   expf : 
     ("As ==> SGi x'" : thm) -> 
     ("[| SG0; ... SGi-1; SGi+1; ... SGm |] ==> G") : thm)
*)
fun fix_alls' i th = 
    let 
      val t = (prop_of th); 
      val names = Term.add_term_names (t,[]);
      val gt = Logic.get_goal t i;
      val body = Term.strip_all_body gt;
      val alls = rev (Term.strip_all_vars gt);
      val fvs = map Free 
                    ((Term.variantlist (map fst alls, names)) 
                       ~~ (map snd alls));
      val sgn = Thm.sign_of_thm th;
      val ctermify = Thm.cterm_of sgn;
      val cfvs = rev (map ctermify fvs);

      val body' = (subst_bounds (fvs,body));
      val gthi0 = Thm.trivial (ctermify body');
      
      (* Given a thm justifying subgoal i, solve subgoal i *)
      (* Note: fails if there are choices! *)
      (* fun exportf thi = 
          Drule.compose_single (Drule.forall_intr_list cfvs thi, 
                                i, th) *)
    in (gthi0, cfvs) end;

(* small example: 
Goal "!! x. [| False; C x |] ==> P x";
val th = topthm();
val i = 1;
val (goalth, fixes) = fix_alls' i (topthm());

Goal "!! x. P (x + (Suc y)) ==> Q ((Suc x) + y)";
Goal "!! x. P x y = Q y x ==> P x y";
val th = topthm();
val i = 1;
val (prems, gthi, expf) = IsaND.fixes_and_assumes i th;
val gth2 = Seq.hd (RWStepTac.rwstep_tac prems 1 gthi);
*)


(* hide other goals *) 
(* note the export goal is rotated by (i - 1) and will have to be
unrotated to get backto the originial position(s) *)
fun hide_other_goals th = 
    let
      (* tl beacuse fst sg is the goal we are interested in *)
      val cprems = tl (Drule.cprems_of th)
      val aprems = map Thm.assume cprems
    in
      (Drule.implies_elim_list (Drule.rotate_prems 1 th) aprems, 
       cprems)
    end;
(* test with: 
Goal "!! x. [| False; C x |] ==> P x";
val th = topthm();
val i = 1;
val (goalth, fixedvars) = IsaND.fix_alls' i th;
val (newth, hiddenprems) = IsaND.hide_other_goals goalth;
*)

(* a nicer version of the above that leaves only a single subgoal (the
other subgoals are hidden hyps, that the exporter suffles about)
namely the subgoal that we were trying to solve. *)
(* loosely corresponds to:
Given "[| SG0; ... !! x. As ==> SGi x; ... SGm |] ==> G" : thm
Result: 
  ("(As ==> SGi x') ==> SGi x'" : thm, 
   expf : 
     ("SGi x'" : thm) -> 
     ("[| SG0; ... SGi-1; SGi+1; ... SGm |] ==> G") : thm)
*)
fun fix_alls i th = 
    let 
      val (fixed_gth, fixedvars) = fix_alls' i th
      val (sml_gth, othergoals) = hide_other_goals fixed_gth
    in
      (sml_gth, export {fixes = fixedvars, 
                        assumes = othergoals, 
                        sgid = i, gth = th})
    end;

(* small example: 
Goal "!! x. [| False; C x |] ==> P x";
val th = topthm();
val i = 1;
val (goalth, exp) = IsaND.fix_alls i th;
val oldthewth = Seq.list_of (IsaND.export_back exp goalth);

val (premths, goalth2, expf2) = IsaND.assume_prems 1 goalth;
val False_th = nth_elem (0,premths);
val anything = False_th RS (thm "FalseE");
val th2 = anything RS goalth2;
val th1 = expf2 th2;
val final_th = flat (map expf th1);
*)


(* assume the premises of subgoal "i", this gives back a list of
assumed theorems that are the premices of subgoal i, it also gives
back a new goal thm and an exporter, the new goalthm is as the old
one, but without the premices, and the exporter will use a proof of
the new goalthm, possibly using the assumed premices, to shoe the
orginial goal. *)

(* Note: Dealing with meta vars, need to meta-level-all them in the
shyps, which we can later instantiate with a specific value.... ? 
think about this... maybe need to introduce some new fixed vars and
then remove them again at the end... like I do with rw_inst. *)
(* loosely corresponds to:
Given "[| SG0; ... [| A0; ... An |] ==> SGi; ... SGm |] ==> G" : thm
Result: 
(["A0" [A0], ... ,"An" [An]] : thm list, -- assumptions
 "SGi ==> SGi" : thm, -- new goal 
 "SGi" ["A0" ... "An"] : thm ->   -- export function
    ("[| SG0 ... SGi-1, SGi+1, SGm |] ==> G" : thm) list)
*)
fun assume_prems i th =
    let 
      val t = (prop_of th); 
      val gt = Logic.get_goal t i;
      val _ = case Term.strip_all_vars gt of [] => () 
              | _ => raise ERROR_MESSAGE "assume_prems: goal has params"
      val body = gt;
      val prems = Logic.strip_imp_prems body;
      val concl = Logic.strip_imp_concl body;

      val sgn = Thm.sign_of_thm th;
      val ctermify = Thm.cterm_of sgn;
      val cprems = map ctermify prems;
      val aprems = map Thm.assume cprems;
      val gthi = Thm.trivial (ctermify concl);

      (* fun explortf thi = 
          Drule.compose (Drule.implies_intr_list cprems thi, 
                         i, th) *)
    in
      (aprems, gthi, cprems)
    end;
(* small example: 
Goal "False ==> b";
val th = topthm();
val i = 1;
val (prems, goalth, cprems) = IsaND.assume_prems i (topthm());
val F = hd prems;
val FalseE = thm "FalseE";
val anything = F RS FalseE;
val thi = anything RS goalth;
val res' = expf thi;
*)


(* first fix the variables, then assume the assumptions *)
(* loosely corresponds to:
Given 
  "[| SG0; ... 
      !! xs. [| A0 xs; ... An xs |] ==> SGi xs; 
      ... SGm |] ==> G" : thm
Result: 
(["A0 xs'" [A0 xs'], ... ,"An xs'" [An xs']] : thm list, -- assumptions
 "SGi xs' ==> SGi xs'" : thm,  -- new goal 
 "SGi xs'" ["A0 xs'" ... "An xs'"] : thm ->   -- export function
    ("[| SG0 ... SGi-1, SGi+1, SGm |] ==> G" : thm) list)
*)

(* Note: the fix_alls actually pulls through all the assumptions which
means that the second export is not needed. *)
fun fixes_and_assumes i th = 
    let 
      val (fixgth, exp1) = fix_alls i th
      val (assumps, goalth, _) = assume_prems 1 fixgth
    in 
      (assumps, goalth, exp1)
    end;
(* test with: 
Goal "!! x. [| False; C x |] ==> P x";
val th = topthm();
val i = 1;
val (fixgth, exp) = IsaND.fix_alls i th;
val (assumps, goalth, _) = assume_prems 1 fixgth;

val oldthewth = Seq.list_of (IsaND.export_back exp fixgth);
val oldthewth = Seq.list_of (IsaND.export_back exp goalth);


val (prems, goalth, expf) = IsaND.fixes_and_assumes i th;
val F = hd prems;
val FalseE = thm "FalseE";
val anything = F RS FalseE;
val thi = anything RS goalth;
val res' = expf thi;
*)

(* Fixme: allow different order of subgoals given to expf *)
(* make each subgoal into a separate thm that needs to be proved *)
(* loosely corresponds to:
Given 
  "[| SG0; ... SGm |] ==> G" : thm
Result: 
(["SG0 ==> SG0", ... ,"SGm ==> SGm"] : thm list, -- goals
 ["SG0", ..., "SGm"] : thm list ->   -- export function
   "G" : thm)
*)
fun subgoal_thms th = 
    let 
      val t = (prop_of th); 

      val prems = Logic.strip_imp_prems t;

      val sgn = Thm.sign_of_thm th;
      val ctermify = Thm.cterm_of sgn;

      val aprems = map (Thm.trivial o ctermify) prems;

      fun explortf premths = 
          Drule.implies_elim_list th premths
    in
      (aprems, explortf)
    end;
(* small example: 
Goal "A & B";
by (rtac conjI 1);
val th = topthm();
val (subgoals, expf) = subgoal_thms (topthm());
*)

(* make all the premices of a theorem hidden, and provide an unhide
function, that will bring them back out at a later point. This is
useful if you want to get back these premices, after having used the
theorem with the premices hidden *)
(* loosely corresponds to:
Given "As ==> G" : thm
Result: ("G [As]" : thm, 
         "G [As]" : thm -> "As ==> G" : thm
*)
fun hide_prems th = 
    let 
      val sgn = Thm.sign_of_thm th;
      val ctermify = Thm.cterm_of sgn;

      val t = (prop_of th);
      val prems = Logic.strip_imp_prems t;
      val cprems = map ctermify prems;
      val aprems = map Thm.trivial cprems;

    (*   val unhidef = Drule.implies_intr_list cprems; *)
    in
      (Drule.implies_elim_list th aprems, cprems)
    end;




(* Fixme: allow different order of subgoals in exportf *)
(* as above, but also fix all parameters in all subgoals, and uses
fix_alls, not fix_alls', ie doesn't leave extra asumptions as apparent
subgoals. *)
(* loosely corresponds to:
Given 
  "[| !! x0s. A0s x0s ==> SG0 x0s; 
      ...; !! xms. Ams xms ==> SGm xms|] ==> G" : thm
Result: 
(["(A0s x0s' ==> SG0 x0s') ==> SG0 x0s'", 
  ... ,"(Ams xms' ==> SGm xms') ==> SGm xms'"] : thm list, -- goals
 ["SG0 x0s'", ..., "SGm xms'"] : thm list ->   -- export function
   "G" : thm)
*)
(* requires being given solutions! *)
fun fixed_subgoal_thms th = 
    let 
      val (subgoals, expf) = subgoal_thms th;
(*       fun export_sg (th, exp) = exp th; *)
      fun export_sgs expfs solthms = 
          expf (map2 (op |>) (solthms, expfs));
(*           expf (map export_sg (ths ~~ expfs)); *)
    in 
      apsnd export_sgs (Library.split_list (map (apsnd export_solution o 
                                                 fix_alls 1) subgoals))
    end;


(* small example: 
Goal "(!! x. ((C x) ==> (A x)))";
val th = topthm();
val i = 1;
val (subgoals, expf) = fixed_subgoal_thms (topthm());
*)

end;
