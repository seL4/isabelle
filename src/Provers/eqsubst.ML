(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      Provers/eqsubst.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Modified:   18 Feb 2005 - Lucas - 
    Created:    29 Jan 2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    A Tactic to perform a substiution using an equation.

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* Logic specific data stub *)
signature EQRULE_DATA =
sig

  (* to make a meta equality theorem in the current logic *)
  val prep_meta_eq : thm -> thm list

end;


(* the signature of an instance of the SQSUBST tactic *)
signature EQSUBST_TAC = 
sig

  val prep_subst_in_asm :
      (Sign.sg (* sign for matching *)
       -> int (* maxidx *)
       -> 'a (* input object kind *)
       -> BasicIsaFTerm.FcTerm (* focusterm to search under *)
       -> 'b) (* result type *)
      -> int (* subgoal to subst in *)
      -> Thm.thm (* target theorem with subgoals *)
      -> int (* premise to subst in *)
      -> (Thm.cterm list (* certified free var placeholders for vars *) 
          * int (* premice no. to subst *)
          * int (* number of assumptions of premice *)
          * Thm.thm) (* premice as a new theorem for forward reasoning *)
         * ('a -> 'b) (* matchf *)

  val prep_subst_in_asms :
      (Sign.sg -> int -> 'a -> BasicIsaFTerm.FcTerm -> 'b) 
      -> int (* subgoal to subst in *)
      -> Thm.thm (* target theorem with subgoals *)
      -> ((Thm.cterm list (* certified free var placeholders for vars *) 
          * int (* premice no. to subst *)
          * int (* number of assumptions of premice *)
          * Thm.thm) (* premice as a new theorem for forward reasoning *)
         * ('a -> 'b)) (* matchf *)
                       Seq.seq

  val apply_subst_in_asm :
      int (* subgoal *)
      -> Thm.thm (* overall theorem *)
      -> (Thm.cterm list (* certified free var placeholders for vars *) 
          * int (* assump no being subst *)
          * int (* num of premises of asm *) 
          * Thm.thm) (* premthm *)
      -> Thm.thm (* rule *)
      -> (((Term.indexname * Term.typ) list (* type instantiations *)
          * (Term.indexname * Term.term) list) (* term instantiations *)
         * (string * Term.typ) list (* type abs env *)
         * Term.term) (* outer term *)
      -> Thm.thm Seq.seq

  val prep_concl_subst :
      (Sign.sg -> int -> 'a -> BasicIsaFTerm.FcTerm -> 'b) (* searchf *) 
      -> int (* subgoal *)
      -> Thm.thm (* overall goal theorem *)
      -> (Thm.cterm list * Thm.thm) * ('a -> 'b) (* (cvfs, conclthm), matchf *)

  val apply_subst_in_concl :
        int (* subgoal *)
        -> Thm.thm (* thm with all goals *)
        -> Thm.cterm list (* certified free var placeholders for vars *)
           * Thm.thm  (* trivial thm of goal concl *)
            (* possible matches/unifiers *)
        -> Thm.thm (* rule *)
        -> (((Term.indexname * Term.typ) list (* type instantiations *)
              * (Term.indexname * Term.term) list ) (* term instantiations *)
             * (string * Term.typ) list (* Type abs env *)
             * Term.term) (* outer term *)
        -> Thm.thm Seq.seq (* substituted goal *)

  val eqsubst_asm_meth : Thm.thm list -> Proof.method
  val eqsubst_asm_tac : Thm.thm list -> int -> Thm.thm -> Thm.thm Seq.seq
  val eqsubst_asm_tac' : Thm.thm -> int -> Thm.thm -> Thm.thm Seq.seq

  val eqsubst_meth : Thm.thm list -> Proof.method
  val eqsubst_tac : Thm.thm list -> int -> Thm.thm -> Thm.thm Seq.seq
  val eqsubst_tac' : Thm.thm -> int -> Thm.thm -> Thm.thm Seq.seq

  val meth : bool * Thm.thm list -> Proof.context -> Proof.method
  val setup : (Theory.theory -> Theory.theory) list
end;

functor EQSubstTacFUN (structure EqRuleData : EQRULE_DATA) 
  : EQSUBST_TAC
= struct

(* FOR DEBUGGING...
type trace_subst_errT = int (* subgoal *)
        * Thm.thm (* thm with all goals *)
        * (Thm.cterm list (* certified free var placeholders for vars *)
           * Thm.thm)  (* trivial thm of goal concl *)
            (* possible matches/unifiers *)
        * Thm.thm (* rule *)
        * (((Term.indexname * Term.typ) list (* type instantiations *)
              * (Term.indexname * Term.term) list ) (* term instantiations *)
             * (string * Term.typ) list (* Type abs env *)
             * Term.term) (* outer term *);

val trace_subst_err = (ref NONE : trace_subst_errT option ref);
val trace_subst_search = ref false;
exception trace_subst_exp of trace_subst_errT;
 *)

(* also defined in /HOL/Tools/inductive_codegen.ML, 
   maybe move this to seq.ML ? *)
infix 5 :->;
fun s :-> f = Seq.flat (Seq.map f s);

(* search from the top to bottom, left to right *)
fun search_lr_f f ft = 
    let
      fun maux ft = 
          let val t' = (IsaFTerm.focus_of_fcterm ft) 
            (* val _ = 
                if !trace_subst_search then 
                  (writeln ("Examining: " ^ (TermLib.string_of_term t'));
                   TermLib.writeterm t'; ())
                else (); *)
          in 
          (case t' of 
            (_ $ _) => Seq.append(maux (IsaFTerm.focus_left ft), 
                       Seq.append(f ft, 
                                  maux (IsaFTerm.focus_right ft)))
          | (Abs _) => Seq.append (f ft, maux (IsaFTerm.focus_abs ft))
          | leaf => f ft) end
    in maux ft end;

fun search_for_match sgn maxidx lhs  = 
    IsaFTerm.find_fcterm_matches 
      search_lr_f 
      (IsaFTerm.clean_unify_ft sgn maxidx lhs);

(* apply a substitution in the conclusion of the theorem th *)
(* cfvs are certified free var placeholders for goal params *)
(* conclthm is a theorem of for just the conclusion *)
(* m is instantiation/match information *)
(* rule is the equation for substitution *)
fun apply_subst_in_concl i th (cfvs, conclthm) rule m = 
    (RWInst.rw m rule conclthm)
      |> IsaND.schemify_frees_to_vars cfvs
      |> RWInst.beta_eta_contract_tac
      |> (fn r => Tactic.rtac r i th);

(*
? is the following equivalent to rtac ? 

 |> Thm.lift_rule (th, i)
 |> (fn r => Thm.bicompose false (false, r, Thm.nprems_of r) i th)

*)

(* substitute within the conclusion of goal i of gth, using a meta
equation rule. Note that we assume rule has var indicies zero'd *)
fun prep_concl_subst searchf i gth = 
    let 
      val th = Thm.incr_indexes 1 gth;
      val tgt_term = Thm.prop_of th;

      val sgn = Thm.sign_of_thm th;
      val ctermify = Thm.cterm_of sgn;
      val trivify = Thm.trivial o ctermify;

      val (fixedbody, fvs) = IsaND.fix_alls_term i tgt_term;
      val cfvs = rev (map ctermify fvs);

      val conclterm = Logic.strip_imp_concl fixedbody;
      val conclthm = trivify conclterm;
      val maxidx = Term.maxidx_of_term conclterm;
    in
      ((cfvs, conclthm), 
       (fn lhs => searchf sgn maxidx lhs 
                          ((IsaFTerm.focus_right  
                            o IsaFTerm.focus_left
                            o IsaFTerm.fcterm_of_term 
                            o Thm.prop_of) conclthm)))
    end;


(* substitute using an object or meta level equality *)
fun eqsubst_tac' instepthm i th = 
    let 
      val (cvfsconclthm, findmatchf) = 
          prep_concl_subst search_for_match i th;

      val stepthms = 
          Seq.map Drule.zero_var_indexes 
                  (Seq.of_list (EqRuleData.prep_meta_eq instepthm));

      fun rewrite_with_thm r =
          let val (lhs,_) = Logic.dest_equals (Thm.concl_of r);
          in (findmatchf lhs)
             :-> (apply_subst_in_concl i th cvfsconclthm r) end;

    in (stepthms :-> rewrite_with_thm) end;


(* substitute using one of the given theorems *)
fun eqsubst_tac instepthms i th = 
    if Thm.nprems_of th < i then Seq.empty else
    (Seq.of_list instepthms) :-> (fn r => eqsubst_tac' r i th);

(* inthms are the given arguments in Isar, and treated as eqstep with
   the first one, then the second etc *)
fun eqsubst_meth inthms =
    Method.METHOD 
      (fn facts =>
          HEADGOAL ( Method.insert_tac facts THEN' eqsubst_tac inthms ));


fun apply_subst_in_asm i th (cfvs, j, nprems, pth) rule m = 
    (RWInst.rw m rule pth)
      |> Thm.permute_prems 0 ~1
      |> IsaND.schemify_frees_to_vars cfvs
      |> RWInst.beta_eta_contract_tac
      |> (fn r => Tactic.dtac r i th);

(*
? should I be using bicompose what if we match more than one
assumption, even after instantiation ? (back will work, but it would
be nice to avoid the redudent search)

something like... 
 |> Thm.lift_rule (th, i)
 |> (fn r => Thm.bicompose false (false, r, Thm.nprems_of r - nprems) i th)

*)


(* prepare to substitute within the j'th premise of subgoal i of gth,
using a meta-level equation. Note that we assume rule has var indicies
zero'd. Note that we also assume that premt is the j'th premice of
subgoal i of gth. Note the repetition of work done for each
assumption, i.e. this can be made more efficient for search over
multiple assumptions.  *)
fun prep_subst_in_asm searchf i gth j = 
    let 
      val th = Thm.incr_indexes 1 gth;
      val tgt_term = Thm.prop_of th;

      val sgn = Thm.sign_of_thm th;
      val ctermify = Thm.cterm_of sgn;
      val trivify = Thm.trivial o ctermify;

      val (fixedbody, fvs) = IsaND.fix_alls_term i tgt_term;
      val cfvs = rev (map ctermify fvs);

      val asmt = Library.nth_elem(j - 1,(Logic.strip_imp_prems fixedbody));
      val asm_nprems = length (Logic.strip_imp_prems asmt);

      val pth = trivify asmt;
      val maxidx = Term.maxidx_of_term asmt;

    in
      ((cfvs, j, asm_nprems, pth), 
       (fn lhs => (searchf sgn maxidx lhs
                           ((IsaFTerm.focus_right 
                             o IsaFTerm.fcterm_of_term 
                             o Thm.prop_of) pth))))
    end;

(* prepare subst in every possible assumption *)
fun prep_subst_in_asms searchf i gth = 
    Seq.map 
      (prep_subst_in_asm searchf i gth)
      (Seq.of_list (IsaPLib.mk_num_list
                      (length (Logic.prems_of_goal (Thm.prop_of gth) i))));


(* substitute in an assumption using an object or meta level equality *)
fun eqsubst_asm_tac' instepthm i th = 
    let 
      val asmpreps = prep_subst_in_asms search_for_match i th;
      val stepthms = 
          Seq.map Drule.zero_var_indexes 
                  (Seq.of_list (EqRuleData.prep_meta_eq instepthm))

      fun rewrite_with_thm (asminfo, findmatchf) r =
          let val (lhs,_) = Logic.dest_equals (Thm.concl_of r);
          in (findmatchf lhs)
             :-> (apply_subst_in_asm i th asminfo r) end;
    in
      (asmpreps :-> (fn a => stepthms :-> rewrite_with_thm a))
    end;

(* substitute using one of the given theorems *)
fun eqsubst_asm_tac instepthms i th = 
    if Thm.nprems_of th < i then Seq.empty else
    (Seq.of_list instepthms) :-> (fn r => eqsubst_asm_tac' r i th);

(* inthms are the given arguments in Isar, and treated as eqstep with
   the first one, then the second etc *)
fun eqsubst_asm_meth inthms =
    Method.METHOD 
      (fn facts =>
          HEADGOAL (Method.insert_tac facts THEN' eqsubst_asm_tac inthms ));

(* combination method that takes a flag (true indicates that subst
should be done to an assumption, false = apply to the conclusion of
the goal) as well as the theorems to use *)
fun meth (asmflag, inthms) ctxt = 
    if asmflag then eqsubst_asm_meth inthms else eqsubst_meth inthms;

(* syntax for options, given "(asm)" will give back true, without
   gives back false *)
val options_syntax =
    (Args.parens (Args.$$$ "asm") >> (K true)) ||
     (Scan.succeed false);

(* method syntax, first take options, then theorems *)
fun meth_syntax meth src ctxt =
    meth (snd (Method.syntax ((Scan.lift options_syntax) 
                                -- Attrib.local_thms) src ctxt)) 
         ctxt;

(* setup function for adding method to theory. *)
val setup = 
    [Method.add_method ("subst", meth_syntax meth, "Substiution with an equation. Use \"(asm)\" option to substitute in an assumption.")];

end;