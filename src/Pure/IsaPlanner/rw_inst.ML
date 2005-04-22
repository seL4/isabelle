(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/rw_inst.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    25 Aug 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    rewriting using a conditional meta-equality theorem which supports 
    schematic variable instantiation.

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature RW_INST =
sig

  (* Rewrite: give it instantiation infromation, a rule, and the
  target thm, and it will return the rewritten target thm *)
  val rw :
      ((Term.indexname * Term.typ) list *  (* type var instantiations *)
       (Term.indexname * Term.term) list)  (* schematic var instantiations *)
      * (string * Term.typ) list           (* Fake named bounds + types *)
      * (string * Term.typ) list           (* names of bound + types *)
      * Term.term ->                       (* outer term for instantiation *)
      Thm.thm ->                           (* rule with indexies lifted *)
      Thm.thm ->                           (* target thm *)
      Thm.thm                              (* rewritten theorem possibly 
                                              with additional premises for 
                                              rule conditions *)

  (* used tools *)
  val mk_abstractedrule :
      (string * Term.typ) list (* faked outer bound *)
      -> (string * Term.typ) list (* hopeful name of outer bounds *)
      -> Thm.thm -> Thm.cterm list * Thm.thm
  val mk_fixtvar_tyinsts :
      Term.indexname list ->
      Term.term list -> ((string * int) * Term.typ) list * (string * sort) list
  val mk_renamings :
      Term.term -> Thm.thm -> (((string * int) * Term.typ) * Term.term) list
  val new_tfree :
      ((string * int) * Term.sort) *
      (((string * int) * Term.typ) list * string list) ->
      ((string * int) * Term.typ) list * string list
  val cross_inst : (Term.indexname * Term.term) list 
                   -> (Term.indexname * Term.term) list

  val beta_contract_tac : Thm.thm -> Thm.thm
  val beta_eta_contract_tac : Thm.thm -> Thm.thm

end;

structure RWInst : RW_INST= 
struct


(* beta contract the theorem *)
fun beta_contract_tac thm = 
    equal_elim (Thm.beta_conversion true (Thm.cprop_of thm)) thm;

(* beta-eta contract the theorem *)
fun beta_eta_contract_tac thm = 
    let
      val thm2 = equal_elim (Thm.beta_conversion true (Thm.cprop_of thm)) thm
      val thm3 = equal_elim (Thm.eta_conversion (Thm.cprop_of thm2)) thm2
    in thm3 end;

(* Given a list of variables that were bound, and a that has been
instantiated with free variable placeholders for the bound vars, it
creates an abstracted version of the theorem, with local bound vars as
lambda-params:

Ts: 
("x", ty)

rule::
C :x ==> P :x = Q :x

results in:
("!! x. C x", (%x. p x = %y. p y) [!! x. C x])

note: assumes rule is instantiated
*)
(* Note, we take abstraction in the order of last abstraction first *)
fun mk_abstractedrule TsFake Ts rule = 
    let 
      val ctermify = Thm.cterm_of (Thm.sign_of_thm rule);

      (* now we change the names of temporary free vars that represent 
         bound vars with binders outside the redex *)
      val prop = Thm.prop_of rule;
      val names = TermLib.usednames_of_thm rule;
      val (fromnames,tonames,names2,Ts') = 
          Library.foldl (fn ((rnf,rnt,names, Ts''),((faken,_),(n,ty))) => 
                    let val n2 = Term.variant names n in
                      (ctermify (Free(faken,ty)) :: rnf,
                       ctermify (Free(n2,ty)) :: rnt, 
                       n2 :: names,
                       (n2,ty) :: Ts'')
                    end)
                (([],[],names, []), TsFake~~Ts);

      (* rename conflicting free's in the rule to avoid cconflicts
      with introduced vars from bounds outside in redex *)
      val rule' = rule |> Drule.forall_intr_list fromnames
                       |> Drule.forall_elim_list tonames;
      
      (* make unconditional rule and prems *)
      val (uncond_rule, cprems) = IsaND.allify_conditions ctermify (rev Ts') 
                                                          rule';

      (* using these names create lambda-abstracted version of the rule *)
      val abstractions = rev (Ts' ~~ tonames);
      val abstract_rule = Library.foldl (fn (th,((n,ty),ct)) => 
                                    Thm.abstract_rule n ct th)
                                (uncond_rule, abstractions);
    in (cprems, abstract_rule) end;


(* given names to avoid, and vars that need to be fixed, it gives
unique new names to the vars so that they can be fixed as free
variables *)
(* make fixed unique free variable instantiations for non-ground vars *)
(* Create a table of vars to be renamed after instantiation - ie
      other uninstantiated vars in the hyps of the rule 
      ie ?z in C ?z ?x ==> A ?x ?y = B ?x ?y *)
fun mk_renamings tgt rule_inst = 
    let
      val rule_conds = Thm.prems_of rule_inst
      val names = foldr Term.add_term_names [] (tgt :: rule_conds);
      val (conds_tyvs,cond_vs) = 
          Library.foldl (fn ((tyvs, vs), t) => 
                    (Library.union
                       (Term.term_tvars t, tyvs),
                     Library.union 
                       (map Term.dest_Var (Term.term_vars t), vs))) 
                (([],[]), rule_conds);
      val termvars = map Term.dest_Var (Term.term_vars tgt); 
      val vars_to_fix = Library.union (termvars, cond_vs);
      val (renamings, names2) = 
          foldr (fn (((n,i),ty), (vs, names')) => 
                    let val n' = Term.variant names' n in
                      ((((n,i),ty), Free (n', ty)) :: vs, n'::names')
                    end)
                ([], names) vars_to_fix;
    in renamings end;

(* make a new fresh typefree instantiation for the given tvar *)
fun new_tfree (tv as (ix,sort), (pairs,used)) =
      let val v = variant used (string_of_indexname ix)
      in  ((ix,TFree(v,sort))::pairs, v::used)  end;


(* make instantiations to fix type variables that are not 
   already instantiated (in ignore_ixs) from the list of terms. *)
fun mk_fixtvar_tyinsts ignore_ixs ts = 
    let val (tvars, tfrees) = 
            foldr (fn (t, (varixs, tfrees)) => 
                      (Term.add_term_tvars (t,varixs),
                       Term.add_term_tfrees (t,tfrees)))
                  ([],[]) ts;
        val unfixed_tvars = List.filter (fn (ix,s) => not (ix mem ignore_ixs)) tvars;
        val (fixtyinsts, _) = foldr new_tfree ([], map fst tfrees) unfixed_tvars
    in (fixtyinsts, tfrees) end;


(* cross-instantiate the instantiations - ie for each instantiation
replace all occurances in other instantiations - no loops are possible
and thus only one-parsing of the instantiations is necessary. *)
fun cross_inst insts = 
    let 
      fun instL (ix, t) = 
          map (fn (ix2,t2) => (ix2, Term.subst_vars ([], [(ix, t)]) t2));

      fun cross_instL ([], l) = rev l
        | cross_instL ((ix, t) :: insts, l) = 
          cross_instL (instL (ix, t) insts, (ix, t) :: (instL (ix, t) l));

    in cross_instL (insts, []) end;
(* as above but for types -- I don't know if this is needed, will we ever incur mixed up types? *)
fun cross_inst_typs insts = 
    let 
      fun instL (ix, ty) = 
          map (fn (ix2,ty2) => (ix2, Term.typ_subst_TVars [(ix, ty)] ty2));

      fun cross_instL ([], l) = rev l
        | cross_instL ((ix, t) :: insts, l) = 
          cross_instL (instL (ix, t) insts, (ix, t) :: (instL (ix, t) l));

    in cross_instL (insts, []) end;


(* assume that rule and target_thm have distinct var names *)
(* THINK: efficient version with tables for vars for: target vars,
introduced vars, and rule vars, for quicker instantiation? *)
(* The outerterm defines which part of the target_thm was modified *)
(* Note: we take Ts in the upterm order, ie last abstraction first.,
and with an outeterm where the abstracted subterm has the arguments in
the revered order, ie first abstraction first. *)
fun rw ((nonfixed_typinsts, unprepinsts), FakeTs, Ts, outerterm) rule target_thm = 
    let 
      (* general signature info *)
      val target_sign = (Thm.sign_of_thm target_thm);
      val ctermify = Thm.cterm_of target_sign;
      val ctypeify = Thm.ctyp_of target_sign;

      (* fix all non-instantiated tvars *)
      val (fixtyinsts, othertfrees) = 
          mk_fixtvar_tyinsts (map fst nonfixed_typinsts) 
                             [Thm.prop_of rule, Thm.prop_of target_thm];

      val typinsts = cross_inst_typs (nonfixed_typinsts @ fixtyinsts);

      (* certified instantiations for types *)
      val ctyp_insts = map (apsnd ctypeify) typinsts;

      (* type instantiated versions *)
      fun tyinst insts rule =
        let val (_, rsorts) = types_sorts rule
        in Thm.instantiate (List.mapPartial (fn (ixn, cT) => Option.map
          (fn S => (ctypeify (TVar (ixn, S)), cT)) (rsorts ixn)) insts, []) rule
        end;
      val tgt_th_tyinst = tyinst ctyp_insts target_thm;
      val rule_tyinst = tyinst ctyp_insts rule;

      (* type instanitated outer term *)
      val outerterm_tyinst = 
          Term.subst_vars (typinsts,[]) outerterm;

      (* type-instantiate the var instantiations *)
      val insts_tyinst = foldr (fn ((ix,t),insts_tyinst) => 
                            (ix, Term.subst_vars (typinsts,[]) t)
                            :: insts_tyinst)
                        [] unprepinsts;

      (* cross-instantiate *)
      val insts_tyinst_inst = cross_inst insts_tyinst;

      (* create certms of instantiations *)
      val cinsts_tyinst = 
          map (fn (ix,t) => (ctermify (Var (ix, Term.type_of t)), 
                             ctermify t)) insts_tyinst_inst;

      (* The instantiated rule *)
      val rule_inst = rule_tyinst |> Thm.instantiate ([], cinsts_tyinst);

      (* Create a table of vars to be renamed after instantiation - ie
      other uninstantiated vars in the hyps the *instantiated* rule 
      ie ?z in C ?z ?x ==> A ?x ?y = B ?x ?y *)
      val renamings = mk_renamings (Thm.prop_of tgt_th_tyinst) 
                                   rule_inst;
      val cterm_renamings = 
          map (fn (x,y) => (ctermify (Var x), ctermify y)) renamings;

      (* Create the specific version of the rule for this target application *)
      val outerterm_inst = 
          outerterm_tyinst 
            |> Term.subst_vars ([], insts_tyinst_inst)
            |> Term.subst_vars ([], map (fn ((ix,ty),t) => (ix,t)) 
                                        renamings);
      val couter_inst = Thm.reflexive (ctermify outerterm_inst);
      val (cprems, abstract_rule_inst) = 
          rule_inst |> Thm.instantiate ([], cterm_renamings)
                    |> mk_abstractedrule FakeTs Ts;
      val specific_tgt_rule = 
          beta_eta_contract_tac
            (Thm.combination couter_inst abstract_rule_inst);

      (* create an instantiated version of the target thm *)
      val tgt_th_inst = 
          tgt_th_tyinst |> Thm.instantiate ([], cinsts_tyinst)
                        |> Thm.instantiate ([], cterm_renamings);

      val (vars,frees_of_fixed_vars) = Library.split_list cterm_renamings;

    in
      (beta_eta_contract_tac tgt_th_inst)
        |> Thm.equal_elim specific_tgt_rule
        |> Drule.implies_intr_list cprems
        |> Drule.forall_intr_list frees_of_fixed_vars
        |> Drule.forall_elim_list vars
        |> fst o Thm.varifyT' othertfrees
        |> Drule.zero_var_indexes
    end;


end; (* struct *)
