(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      TFL/isand.ML
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
*)

structure IsaND =
struct

(* Solve *some* subgoal of "th" directly by "sol" *)
(* Note: this is probably what Markus ment to do upon export of a
"show" but maybe he used RS/rtac intead, which would wrongly lead to
failing if there are premices to the shown goal. *)
fun solve_with sol th = 
    let fun solvei 0 = Seq.empty
          | solvei i = 
            Seq.append (bicompose false (false,sol,0) i th, 
                        solvei (i - 1))
    in
      solvei (Thm.nprems_of th)
    end;


(* fix parameters of a subgoal "i", as free variables, and create an
exporting function that will use the result of this proved goal to
show the goal in the original theorem. 

Note, an advantage of this over Isar is that it supports instantiation
of unkowns in the earlier theorem, ie we can do instantiation of meta
vars! *)
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
      fun exportf thi = 
          Drule.compose_single (Drule.forall_intr_list cfvs thi, 
                                i, th)
    in
      (gthi0, exportf)
    end;

(* small example: 
Goal "!! x. [| False; C x |] ==> P x";
val th = topthm();
val i = 1;
val (goalth, expf) = fix_alls i (topthm());
*)


(* a nicer version of the above that leaves only a single subgoal (the
other subgoals are hidden hyps, that the exporter suffles about)
namely the subgoal that we were trying to solve. *)

fun fix_alls i th = 
    let 
      val (gthi, exportf) = fix_alls' i th
      val gthi' = Drule.rotate_prems 1 gthi

      val sgn = Thm.sign_of_thm th;
      val ctermify = Thm.cterm_of sgn;

      val prems = tl (Thm.prems_of gthi)
      val cprems = map ctermify prems;
      val aprems = map Thm.assume cprems;

      val exportf' = 
          exportf o (Drule.implies_intr_list cprems)
    in
      (Drule.implies_elim_list gthi' aprems, exportf')
    end;

(* small example: 
Goal "P x";
val i = 1;
val th = topthm();
val x = fix_alls (topthm()) 1;

Goal "!! x. [| False; C x |] ==> P x";
val th = topthm();
val i = 1;
val (goalth, expf) = fix_alls' th i;

val (premths, goalth2, expf2) = assume_prems 1 goalth;
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

      fun explortf thi = 
          Drule.compose (Drule.implies_intr_list cprems thi, 
                         i, th)
    in
      (aprems, gthi, explortf)
    end;
(* small example: 
Goal "False ==> b";
val th = topthm();
val i = 1;
val (prems, goalth, expf) = assume_prems i (topthm());
val F = hd prems;
val FalseE = thm "FalseE";
val anything = F RS FalseE;
val thi = anything RS goalth;
val res' = expf thi;
*)


(* Fixme: allow different order of subgoals *)
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
fun hide_prems th = 
    let 
      val sgn = Thm.sign_of_thm th;
      val ctermify = Thm.cterm_of sgn;

      val t = (prop_of th);
      val prems = Logic.strip_imp_prems t;
      val cprems = map ctermify prems;
      val aprems = map Thm.trivial cprems;

      val unhidef = Drule.implies_intr_list cprems;
    in
      (Drule.implies_elim_list th aprems, unhidef)
    end;




(* Fixme: allow different order of subgoals *)
fun fixed_subgoal_thms th = 
    let 
      val (subgoals, expf) = subgoal_thms th;

(*       fun export_sg (th, exp) = exp th; *)
      fun export_sgs expfs ths = 
          expf (map2 (op |>) (ths, expfs));

(*           expf (map export_sg (ths ~~ expfs)); *)



    in 
      apsnd export_sgs (Library.split_list (map (fix_alls 1) subgoals))
    end;


(* small example: 
Goal "(!! x. ((C x) ==> (A x)))";
val th = topthm();
val i = 1;
val (subgoals, expf) = fixed_subgoal_thms (topthm());
*)

end;