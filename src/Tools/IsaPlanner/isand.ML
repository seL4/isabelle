(*  Title:      Tools/IsaPlanner/isand.ML
    Author:     Lucas Dixon, University of Edinburgh

Natural Deduction tools.

For working with Isabelle theorems in a natural detuction style.
ie, not having to deal with meta level quantified varaibles,
instead, we work with newly introduced frees, and hide the
"all"'s, exporting results from theorems proved with the frees, to
solve the all cases of the previous goal. This allows resolution
to do proof search normally. 

Note: A nice idea: allow exporting to solve any subgoal, thus
allowing the interleaving of proof, or provide a structure for the
ordering of proof, thus allowing proof attempts in parrell, but
recording the order to apply things in.

THINK: are we really ok with our varify name w.r.t the prop - do
we also need to avoid names in the hidden hyps? What about
unification contraints in flex-flex pairs - might they also have
extra free vars?
*)

signature ISA_ND =
sig

  (* export data *)
  datatype export = export of
           {gth: Thm.thm, (* initial goal theorem *)
            sgid: int, (* subgoal id which has been fixed etc *)
            fixes: Thm.cterm list, (* frees *)
            assumes: Thm.cterm list} (* assumptions *)
  val fixes_of_exp : export -> Thm.cterm list
  val export_back : export -> Thm.thm -> Thm.thm Seq.seq
  val export_solution : export -> Thm.thm -> Thm.thm
  val export_solutions : export list * Thm.thm -> Thm.thm

  (* inserting meta level params for frees in the conditions *)
  val allify_conditions :
      (Term.term -> Thm.cterm) ->
      (string * Term.typ) list -> Thm.thm -> Thm.thm * Thm.cterm list
  val allify_conditions' :
      (string * Term.typ) list -> Thm.thm -> Thm.thm * Thm.cterm list
  val assume_allified :
      theory -> (string * Term.sort) list * (string * Term.typ) list
      -> Term.term -> (Thm.cterm * Thm.thm)

  (* meta level fixed params (i.e. !! vars) *)
  val fix_alls_in_term : Term.term -> Term.term * Term.term list
  val fix_alls_term : int -> Term.term -> Term.term * Term.term list
  val fix_alls_cterm : int -> Thm.thm -> Thm.cterm * Thm.cterm list
  val fix_alls' : int -> Thm.thm -> Thm.thm * Thm.cterm list
  val fix_alls : int -> Thm.thm -> Thm.thm * export

  (* meta variables in types and terms *)
  val fix_tvars_to_tfrees_in_terms 
      : string list (* avoid these names *)
        -> Term.term list -> 
        (((string * int) * Term.sort) * (string * Term.sort)) list (* renamings *)
  val fix_vars_to_frees_in_terms
      : string list (* avoid these names *)
        -> Term.term list ->
        (((string * int) * Term.typ) * (string * Term.typ)) list (* renamings *)
  val fix_tvars_to_tfrees : Thm.thm -> Thm.ctyp list * Thm.thm
  val fix_vars_to_frees : Thm.thm -> Thm.cterm list * Thm.thm
  val fix_vars_and_tvars : 
      Thm.thm -> (Thm.cterm list * Thm.ctyp list) * Thm.thm
  val fix_vars_upto_idx : int -> Thm.thm -> Thm.thm
  val fix_tvars_upto_idx : int -> Thm.thm -> Thm.thm
  val unfix_frees : Thm.cterm list -> Thm.thm -> Thm.thm
  val unfix_tfrees : Thm.ctyp list -> Thm.thm -> Thm.thm
  val unfix_frees_and_tfrees :
      (Thm.cterm list * Thm.ctyp list) -> Thm.thm -> Thm.thm

  (* assumptions/subgoals *)
  val assume_prems :
      int -> Thm.thm -> Thm.thm list * Thm.thm * Thm.cterm list
  val fixed_subgoal_thms : Thm.thm -> Thm.thm list * (Thm.thm list -> Thm.thm)
  val fixes_and_assumes : int -> Thm.thm -> Thm.thm list * Thm.thm * export
  val hide_other_goals : Thm.thm -> Thm.thm * Thm.cterm list
  val hide_prems : Thm.thm -> Thm.thm * Thm.cterm list

  (* abstracts cterms (vars) to locally meta-all bounds *)
  val prepare_goal_export : string list * Thm.cterm list -> Thm.thm 
                            -> int * Thm.thm
  val solve_with : Thm.thm -> Thm.thm -> Thm.thm Seq.seq
  val subgoal_thms : Thm.thm -> Thm.thm list * (Thm.thm list -> Thm.thm)
end


structure IsaND 
: ISA_ND
= struct

(* Solve *some* subgoal of "th" directly by "sol" *)
(* Note: this is probably what Markus ment to do upon export of a
"show" but maybe he used RS/rtac instead, which would wrongly lead to
failing if there are premices to the shown goal. 

given: 
sol : Thm.thm = [| Ai... |] ==> Ci
th : Thm.thm = 
  [| ... [| Ai... |] ==> Ci ... |] ==> G
results in: 
  [| ... [| Ai-1... |] ==> Ci-1
    [| Ai+1... |] ==> Ci+1 ...
  |] ==> G
i.e. solves some subgoal of th that is identical to sol. 
*)
fun solve_with sol th = 
    let fun solvei 0 = Seq.empty
          | solvei i = 
            Seq.append (Thm.bicompose false (false,sol,0) i th) (solvei (i - 1))
    in
      solvei (Thm.nprems_of th)
    end;


(* Given ctertmify function, (string,type) pairs capturing the free
vars that need to be allified in the assumption, and a theorem with
assumptions possibly containing the free vars, then we give back the
assumptions allified as hidden hyps. 

Given: x 
th: A vs ==> B vs 
Results in: "B vs" [!!x. A x]
*)
fun allify_conditions ctermify Ts th = 
    let 
      val premts = Thm.prems_of th;
    
      fun allify_prem_var (vt as (n,ty),t)  = 
          (Logic.all_const ty) $ (Abs(n,ty,Term.abstract_over (Free vt, t)))

      fun allify_prem Ts p = List.foldr allify_prem_var p Ts

      val cTs = map (ctermify o Free) Ts
      val cterm_asms = map (ctermify o allify_prem Ts) premts
      val allifyied_asm_thms = map (Drule.forall_elim_list cTs o Thm.assume) cterm_asms
    in 
      (Library.foldl (fn (x,y) => y COMP x) (th, allifyied_asm_thms), cterm_asms)
    end;

fun allify_conditions' Ts th = 
    allify_conditions (Thm.cterm_of (Thm.theory_of_thm th)) Ts th;

(* allify types *)
fun allify_typ ts ty = 
    let 
      fun trec (x as (TFree (s,srt))) = 
          (case Library.find_first (fn (s2,srt2) => s = s2) ts
            of NONE => x
             | SOME (s2,_) => TVar ((s,0),srt))
            (*  Maybe add in check here for bad sorts? 
             if srt = srt2 then TVar ((s,0),srt) 
               else raise  ("thaw_typ", ts, ty) *)
          | trec (Type (s,typs)) = Type (s, map trec typs)
          | trec (v as TVar _) = v;
    in trec ty end;

(* implicit types and term *)
fun allify_term_typs ty = Term.map_types (allify_typ ty);

(* allified version of term, given frees to allify over. Note that we
only allify over the types on the given allified cterm, we can't do
this for the theorem as we are not allowed type-vars in the hyp. *)
(* FIXME: make the allified term keep the same conclusion as it
started with, rather than a strictly more general version (ie use
instantiate with initial params we abstracted from, rather than
forall_elim_vars. *)
fun assume_allified sgn (tyvs,vs) t = 
    let
      fun allify_var (vt as (n,ty),t)  = 
          (Logic.all_const ty) $ (Abs(n,ty,Term.abstract_over (Free vt, t)))
      fun allify Ts p = List.foldr allify_var p Ts

      val ctermify = Thm.cterm_of sgn;
      val cvars = map (fn (n,ty) => ctermify (Var ((n,0),ty))) vs
      val allified_term = t |> allify vs;
      val ct = ctermify allified_term;
      val typ_allified_ct = ctermify (allify_term_typs tyvs allified_term);
    in (typ_allified_ct, 
        Thm.forall_elim_vars 0 (Thm.assume ct)) end;


(* change type-vars to fresh type frees *)
fun fix_tvars_to_tfrees_in_terms names ts = 
    let 
      val tfree_names = map fst (List.foldr Misc_Legacy.add_term_tfrees [] ts);
      val tvars = List.foldr Misc_Legacy.add_term_tvars [] ts;
      val (names',renamings) = 
          List.foldr (fn (tv as ((n,i),s),(Ns,Rs)) => 
                         let val n2 = singleton (Name.variant_list Ns) n in 
                           (n2::Ns, (tv, (n2,s))::Rs)
                         end) (tfree_names @ names,[]) tvars;
    in renamings end;
fun fix_tvars_to_tfrees th = 
    let 
      val sign = Thm.theory_of_thm th;
      val ctypify = Thm.ctyp_of sign;
      val tpairs = Thm.terms_of_tpairs (Thm.tpairs_of th);
      val renamings = fix_tvars_to_tfrees_in_terms 
                        [] ((Thm.prop_of th) :: tpairs);
      val crenamings = 
          map (fn (v,f) => (ctypify (TVar v), ctypify (TFree f)))
              renamings;
      val fixedfrees = map snd crenamings;
    in (fixedfrees, Thm.instantiate (crenamings, []) th) end;


(* change type-free's to type-vars in th, skipping the ones in "ns" *)
fun unfix_tfrees ns th = 
    let 
      val varfiytfrees = map (Term.dest_TFree o Thm.typ_of) ns
      val skiptfrees = subtract (op =) varfiytfrees (Misc_Legacy.add_term_tfrees (Thm.prop_of th,[]));
    in #2 (Thm.varifyT_global' skiptfrees th) end;

(* change schematic/meta vars to fresh free vars, avoiding name clashes 
   with "names" *)
fun fix_vars_to_frees_in_terms names ts = 
    let 
      val vars = map Term.dest_Var (List.foldr Misc_Legacy.add_term_vars [] ts);
      val Ns = List.foldr Misc_Legacy.add_term_names names ts;
      val (_,renamings) = 
          Library.foldl (fn ((Ns,Rs),v as ((n,i),ty)) => 
                    let val n2 = singleton (Name.variant_list Ns) n in
                      (n2 :: Ns, (v, (n2,ty)) :: Rs)
                    end) ((Ns,[]), vars);
    in renamings end;
fun fix_vars_to_frees th = 
    let 
      val ctermify = Thm.cterm_of (Thm.theory_of_thm th)
      val tpairs = Thm.terms_of_tpairs (Thm.tpairs_of th);
      val renamings = fix_vars_to_frees_in_terms 
                        [] ([Thm.prop_of th] @ tpairs);
      val crenamings = 
          map (fn (v,f) => (ctermify (Var v), ctermify (Free f)))
              renamings;
      val fixedfrees = map snd crenamings;
    in (fixedfrees, Thm.instantiate ([], crenamings) th) end;

fun fix_tvars_upto_idx ix th = 
    let 
      val sgn = Thm.theory_of_thm th;
      val ctypify = Thm.ctyp_of sgn
      val tpairs = Thm.terms_of_tpairs (Thm.tpairs_of th);
      val prop = (Thm.prop_of th);
      val tvars = List.foldr Misc_Legacy.add_term_tvars [] (prop :: tpairs);
      val ctyfixes = 
          map_filter 
            (fn (v as ((s,i),ty)) => 
                if i <= ix then SOME (ctypify (TVar v), ctypify (TFree (s,ty)))
                else NONE) tvars;
    in Thm.instantiate (ctyfixes, []) th end;
fun fix_vars_upto_idx ix th = 
    let 
      val sgn = Thm.theory_of_thm th;
      val ctermify = Thm.cterm_of sgn
      val tpairs = Thm.terms_of_tpairs (Thm.tpairs_of th);
      val prop = (Thm.prop_of th);
      val vars = map Term.dest_Var (List.foldr Misc_Legacy.add_term_vars 
                                               [] (prop :: tpairs));
      val cfixes = 
          map_filter 
            (fn (v as ((s,i),ty)) => 
                if i <= ix then SOME (ctermify (Var v), ctermify (Free (s,ty)))
                else NONE) vars;
    in Thm.instantiate ([], cfixes) th end;


(* make free vars into schematic vars with index zero *)
 fun unfix_frees frees = 
     apply (map (K (Thm.forall_elim_var 0)) frees) 
     o Drule.forall_intr_list frees;

(* fix term and type variables *)
fun fix_vars_and_tvars th = 
    let val (tvars, th') = fix_tvars_to_tfrees th
      val (vars, th'') = fix_vars_to_frees th' 
    in ((vars, tvars), th'') end;

(* implicit Thm.thm argument *)
(* assumes: vars may contain fixed versions of the frees *)
(* THINK: what if vs already has types varified? *)
fun unfix_frees_and_tfrees (vs,tvs) = 
    (unfix_tfrees tvs o unfix_frees vs);

(* datatype to capture an exported result, ie a fix or assume. *)
datatype export = 
         export of {fixes : Thm.cterm list, (* fixed vars *)
                    assumes : Thm.cterm list, (* hidden hyps/assumed prems *)
                    sgid : int,
                    gth :  Thm.thm}; (* subgoal/goalthm *)

fun fixes_of_exp (export rep) = #fixes rep;

(* export the result of the new goal thm, ie if we reduced teh
subgoal, then we get a new reduced subtgoal with the old
all-quantified variables *)
local 

(* allify puts in a meta level univ quantifier for a free variavble *)
fun allify_term (v, t) = 
    let val vt = #t (Thm.rep_cterm v)
      val (n,ty) = Term.dest_Free vt
    in (Logic.all_const ty) $ (Abs(n,ty,Term.abstract_over (vt, t))) end;

fun allify_for_sg_term ctermify vs t =
    let val t_alls = List.foldr allify_term t vs;
        val ct_alls = ctermify t_alls; 
    in 
      (ct_alls, Drule.forall_elim_list vs (Thm.assume ct_alls))
    end;
(* lookup type of a free var name from a list *)
fun lookupfree vs vn  = 
    case Library.find_first (fn (n,ty) => n = vn) vs of 
      NONE => error ("prepare_goal_export:lookupfree: " ^ vn ^ " does not occur in the term")
    | SOME x => x;
in
fun export_back (export {fixes = vs, assumes = hprems, 
                         sgid = i, gth = gth}) newth = 
    let 
      val sgn = Thm.theory_of_thm newth;
      val ctermify = Thm.cterm_of sgn;

      val sgs = prems_of newth;
      val (sgallcts, sgthms) = 
          Library.split_list (map (allify_for_sg_term ctermify vs) sgs);
      val minimal_newth = 
          (Library.foldl (fn ( newth', sgthm) => 
                          Drule.compose_single (sgthm, 1, newth'))
                      (newth, sgthms));
      val allified_newth = 
          minimal_newth 
            |> Drule.implies_intr_list hprems
            |> Drule.forall_intr_list vs 

      val newth' = Drule.implies_intr_list sgallcts allified_newth
    in
      Thm.bicompose false (false, newth', (length sgallcts)) i gth
    end;

(* 
Given "vs" : names of free variables to abstract over,
Given cterms : premices to abstract over (P1... Pn) in terms of vs,
Given a thm of the form: 
P1 vs; ...; Pn vs ==> Goal(C vs)

Gives back: 
(n, length of given cterms which have been allified
 [| !! vs. P1 vs; !! vs. Pn vs |] ==> !! C vs) the allified thm
*)
(* note: C may contain further premices etc 
Note that cterms is the assumed facts, ie prems of "P1" that are
reintroduced in allified form.
*)
fun prepare_goal_export (vs, cterms) th = 
    let 
      val sgn = Thm.theory_of_thm th;
      val ctermify = Thm.cterm_of sgn;

      val allfrees = map Term.dest_Free (Misc_Legacy.term_frees (Thm.prop_of th))
      val cfrees = map (ctermify o Free o lookupfree allfrees) vs

      val sgs = prems_of th;
      val (sgallcts, sgthms) = 
          Library.split_list (map (allify_for_sg_term ctermify cfrees) sgs);

      val minimal_th = 
          Goal.conclude (Library.foldl (fn ( th', sgthm) => 
                          Drule.compose_single (sgthm, 1, th'))
                      (th, sgthms));

      val allified_th = 
          minimal_th 
            |> Drule.implies_intr_list cterms
            |> Drule.forall_intr_list cfrees 

      val th' = Drule.implies_intr_list sgallcts allified_th
    in
      ((length sgallcts), th')
    end;

end;


(* exporting function that takes a solution to the fixed/assumed goal,
and uses this to solve the subgoal in the main theorem *)
fun export_solution (export {fixes = cfvs, assumes = hcprems,
                             sgid = i, gth = gth}) solth = 
    let 
      val solth' = 
          solth |> Drule.implies_intr_list hcprems
                |> Drule.forall_intr_list cfvs
    in Drule.compose_single (solth', i, gth) end;

fun export_solutions (xs,th) = List.foldr (uncurry export_solution) th xs;


(* fix parameters of a subgoal "i", as free variables, and create an
exporting function that will use the result of this proved goal to
show the goal in the original theorem. 

Note, an advantage of this over Isar is that it supports instantiation
of unkowns in the earlier theorem, ie we can do instantiation of meta
vars! 

avoids constant, free and vars names. 

loosely corresponds to:
Given "[| SG0; ... !! x. As ==> SGi x; ... SGm |] ==> G" : thm
Result: 
  ("(As ==> SGi x') ==> (As ==> SGi x')" : thm, 
   expf : 
     ("As ==> SGi x'" : thm) -> 
     ("[| SG0; ... SGi-1; SGi+1; ... SGm |] ==> G") : thm)
*)
fun fix_alls_in_term alledt = 
    let
      val t = Term.strip_all_body alledt;
      val alls = rev (Term.strip_all_vars alledt);
      val varnames = map (fst o fst o Term.dest_Var) (Misc_Legacy.term_vars t)
      val names = Misc_Legacy.add_term_names (t,varnames);
      val fvs = map Free 
                    (Name.variant_list names (map fst alls)
                       ~~ (map snd alls));
    in ((subst_bounds (fvs,t)), fvs) end;

fun fix_alls_term i t = 
    let 
      val varnames = map (fst o fst o Term.dest_Var) (Misc_Legacy.term_vars t)
      val names = Misc_Legacy.add_term_names (t,varnames);
      val gt = Logic.get_goal t i;
      val body = Term.strip_all_body gt;
      val alls = rev (Term.strip_all_vars gt);
      val fvs = map Free 
                    (Name.variant_list names (map fst alls)
                       ~~ (map snd alls));
    in ((subst_bounds (fvs,body)), fvs) end;

fun fix_alls_cterm i th = 
    let
      val ctermify = Thm.cterm_of (Thm.theory_of_thm th);
      val (fixedbody, fvs) = fix_alls_term i (Thm.prop_of th);
      val cfvs = rev (map ctermify fvs);
      val ct_body = ctermify fixedbody
    in
      (ct_body, cfvs)
    end;

fun fix_alls' i = 
     (apfst Thm.trivial) o (fix_alls_cterm i);


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


(* assume the premises of subgoal "i", this gives back a list of
assumed theorems that are the premices of subgoal i, it also gives
back a new goal thm and an exporter, the new goalthm is as the old
one, but without the premices, and the exporter will use a proof of
the new goalthm, possibly using the assumed premices, to shoe the
orginial goal.

Note: Dealing with meta vars, need to meta-level-all them in the
shyps, which we can later instantiate with a specific value.... ? 
think about this... maybe need to introduce some new fixed vars and
then remove them again at the end... like I do with rw_inst. 

loosely corresponds to:
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
              | _ => error "assume_prems: goal has params"
      val body = gt;
      val prems = Logic.strip_imp_prems body;
      val concl = Logic.strip_imp_concl body;

      val sgn = Thm.theory_of_thm th;
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

      val sgn = Thm.theory_of_thm th;
      val ctermify = Thm.cterm_of sgn;

      val aprems = map (Thm.trivial o ctermify) prems;

      fun explortf premths = 
          Drule.implies_elim_list th premths
    in
      (aprems, explortf)
    end;


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
      val cprems = Drule.cprems_of th;
      val aprems = map Thm.assume cprems;
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
          expf (map2 (curry (op |>)) solthms expfs);
(*           expf (map export_sg (ths ~~ expfs)); *)
    in 
      apsnd export_sgs (Library.split_list (map (apsnd export_solution o 
                                                 fix_alls 1) subgoals))
    end;

end;
