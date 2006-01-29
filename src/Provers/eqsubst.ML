(*  Title:      Provers/eqsubst.ML
    ID:         $Id$
    Author:     Lucas Dixon, University of Edinburgh, lucas.dixon@ed.ac.uk

A proof method to perform a substiution using an equation.
*)

signature EQSUBST =
sig
  val setup : theory -> theory
end;

structure EqSubst: EQSUBST =
struct

fun prep_meta_eq ctxt =
  let val (_, {mk_rews = {mk, ...}, ...}) = Simplifier.rep_ss (Simplifier.local_simpset_of ctxt)
  in mk #> map Drule.zero_var_indexes end;


  (* a type abriviation for match information *)
  type match =
       ((indexname * (sort * typ)) list (* type instantiations *)
        * (indexname * (typ * term)) list) (* term instantiations *)
       * (string * typ) list (* fake named type abs env *)
       * (string * typ) list (* type abs env *)
       * term (* outer term *)

  type searchinfo =
       theory
       * int (* maxidx *)
       * BasicIsaFTerm.FcTerm (* focusterm to search under *)

(* FOR DEBUGGING...
type trace_subst_errT = int (* subgoal *)
        * thm (* thm with all goals *)
        * (Thm.cterm list (* certified free var placeholders for vars *)
           * thm)  (* trivial thm of goal concl *)
            (* possible matches/unifiers *)
        * thm (* rule *)
        * (((indexname * typ) list (* type instantiations *)
              * (indexname * term) list ) (* term instantiations *)
             * (string * typ) list (* Type abs env *)
             * term) (* outer term *);

val trace_subst_err = (ref NONE : trace_subst_errT option ref);
val trace_subst_search = ref false;
exception trace_subst_exp of trace_subst_errT;
 *)

(* search from top, left to right, then down *)
fun search_tlr_all_f f ft =
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
                       Seq.cons(f ft,
                                  maux (IsaFTerm.focus_right ft)))
          | (Abs _) => Seq.cons(f ft, maux (IsaFTerm.focus_abs ft))
          | leaf => Seq.single (f ft)) end
    in maux ft end;

(* search from top, left to right, then down *)
fun search_tlr_valid_f f ft =
    let
      fun maux ft =
          let
            val hereseq = if IsaFTerm.valid_match_start ft then f ft else Seq.empty
          in
          (case (IsaFTerm.focus_of_fcterm ft) of
            (_ $ _) => Seq.append(maux (IsaFTerm.focus_left ft),
                       Seq.cons(hereseq,
                                  maux (IsaFTerm.focus_right ft)))
          | (Abs _) => Seq.cons(hereseq, maux (IsaFTerm.focus_abs ft))
          | leaf => Seq.single (hereseq))
          end
    in maux ft end;

(* search all unifications *)
fun searchf_tlr_unify_all (sgn, maxidx, ft) lhs =
    IsaFTerm.find_fcterm_matches
      search_tlr_all_f
      (IsaFTerm.clean_unify_ft sgn maxidx lhs)
      ft;

(* search only for 'valid' unifiers (non abs subterms and non vars) *)
fun searchf_tlr_unify_valid (sgn, maxidx, ft) lhs  =
    IsaFTerm.find_fcterm_matches
      search_tlr_valid_f
      (IsaFTerm.clean_unify_ft sgn maxidx lhs)
      ft;


(* apply a substitution in the conclusion of the theorem th *)
(* cfvs are certified free var placeholders for goal params *)
(* conclthm is a theorem of for just the conclusion *)
(* m is instantiation/match information *)
(* rule is the equation for substitution *)
fun apply_subst_in_concl i th (cfvs, conclthm) rule m =
    (RWInst.rw m rule conclthm)
      |> IsaND.unfix_frees cfvs
      |> RWInst.beta_eta_contract
      |> (fn r => Tactic.rtac r i th);

(* substitute within the conclusion of goal i of gth, using a meta
equation rule. Note that we assume rule has var indicies zero'd *)
fun prep_concl_subst i gth =
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
      val ft = ((IsaFTerm.focus_right
                 o IsaFTerm.focus_left
                 o IsaFTerm.fcterm_of_term
                 o Thm.prop_of) conclthm)
    in
      ((cfvs, conclthm), (sgn, maxidx, ft))
    end;

(* substitute using an object or meta level equality *)
fun eqsubst_tac' ctxt searchf instepthm i th =
    let
      val (cvfsconclthm, searchinfo) = prep_concl_subst i th;
      val stepthms = Seq.of_list (prep_meta_eq ctxt instepthm);
      fun rewrite_with_thm r =
          let val (lhs,_) = Logic.dest_equals (Thm.concl_of r);
          in searchf searchinfo lhs
             |> Seq.maps (apply_subst_in_concl i th cvfsconclthm r) end;
    in stepthms |> Seq.maps rewrite_with_thm end;


(* Tactic.distinct_subgoals_tac -- fails to free type variables *)

(* custom version of distinct subgoals that works with term and
   type variables. Asssumes th is in beta-eta normal form.
   Also, does nothing if flexflex contraints are present. *)
fun distinct_subgoals th =
    if List.null (Thm.tpairs_of th) then
      let val (fixes,fixedthm) = IsaND.fix_vars_and_tvars th
        val (fixedthconcl,cprems) = IsaND.hide_prems fixedthm
      in
        IsaND.unfix_frees_and_tfrees
          fixes
          (Drule.implies_intr_list
             (Library.gen_distinct
                (fn (x, y) => Thm.term_of x = Thm.term_of y)
                cprems) fixedthconcl)
      end
    else th;

(* General substiuttion of multiple occurances using one of
   the given theorems*)
exception eqsubst_occL_exp of
          string * (int list) * (thm list) * int * thm;
fun skip_first_occs_search occ srchf sinfo lhs =
    case (IsaPLib.skipto_seqseq occ (srchf sinfo lhs)) of
      IsaPLib.skipmore _ => Seq.empty
    | IsaPLib.skipseq ss => Seq.flat ss;

fun eqsubst_tac ctxt occL thms i th =
    let val nprems = Thm.nprems_of th in
      if nprems < i then Seq.empty else
      let val thmseq = (Seq.of_list thms)
        fun apply_occ occ th =
            thmseq |> Seq.maps
                    (fn r => eqsubst_tac' ctxt (skip_first_occs_search
                                    occ searchf_tlr_unify_valid) r
                                 (i + ((Thm.nprems_of th) - nprems))
                                 th);
        val sortedoccL =
            Library.sort (Library.rev_order o Library.int_ord) occL;
      in
        Seq.map distinct_subgoals (Seq.EVERY (map apply_occ sortedoccL) th)
      end
    end
    handle THM _ => raise eqsubst_occL_exp ("THM",occL,thms,i,th);


(* inthms are the given arguments in Isar, and treated as eqstep with
   the first one, then the second etc *)
fun eqsubst_meth ctxt occL inthms =
    Method.METHOD
      (fn facts =>
          HEADGOAL (Method.insert_tac facts THEN' eqsubst_tac ctxt occL inthms));

(* apply a substitution inside assumption j, keeps asm in the same place *)
fun apply_subst_in_asm i th rule ((cfvs, j, ngoalprems, pth),m) =
    let
      val th2 = Thm.rotate_rule (j - 1) i th; (* put premice first *)
      val preelimrule =
          (RWInst.rw m rule pth)
            |> (Seq.hd o Tactic.prune_params_tac)
            |> Thm.permute_prems 0 ~1 (* put old asm first *)
            |> IsaND.unfix_frees cfvs (* unfix any global params *)
            |> RWInst.beta_eta_contract; (* normal form *)
  (*    val elimrule =
          preelimrule
            |> Tactic.make_elim (* make into elim rule *)
            |> Thm.lift_rule (th2, i); (* lift into context *)
   *)
    in
      (* ~j because new asm starts at back, thus we subtract 1 *)
      Seq.map (Thm.rotate_rule (~j) ((Thm.nprems_of rule) + i))
      (Tactic.dtac preelimrule i th2)

      (* (Thm.bicompose
                 false (* use unification *)
                 (true, (* elim resolution *)
                  elimrule, (2 + (Thm.nprems_of rule)) - ngoalprems)
                 i th2) *)
    end;


(* prepare to substitute within the j'th premise of subgoal i of gth,
using a meta-level equation. Note that we assume rule has var indicies
zero'd. Note that we also assume that premt is the j'th premice of
subgoal i of gth. Note the repetition of work done for each
assumption, i.e. this can be made more efficient for search over
multiple assumptions.  *)
fun prep_subst_in_asm i gth j =
    let
      val th = Thm.incr_indexes 1 gth;
      val tgt_term = Thm.prop_of th;

      val sgn = Thm.sign_of_thm th;
      val ctermify = Thm.cterm_of sgn;
      val trivify = Thm.trivial o ctermify;

      val (fixedbody, fvs) = IsaND.fix_alls_term i tgt_term;
      val cfvs = rev (map ctermify fvs);

      val asmt = nth (Logic.strip_imp_prems fixedbody) (j - 1);
      val asm_nprems = length (Logic.strip_imp_prems asmt);

      val pth = trivify asmt;
      val maxidx = Term.maxidx_of_term asmt;

      val ft = ((IsaFTerm.focus_right
                 o IsaFTerm.fcterm_of_term
                 o Thm.prop_of) pth)
    in ((cfvs, j, asm_nprems, pth), (sgn, maxidx, ft)) end;

(* prepare subst in every possible assumption *)
fun prep_subst_in_asms i gth =
    map (prep_subst_in_asm i gth)
        ((rev o IsaPLib.mk_num_list o length)
           (Logic.prems_of_goal (Thm.prop_of gth) i));


(* substitute in an assumption using an object or meta level equality *)
fun eqsubst_asm_tac' ctxt searchf skipocc instepthm i th =
    let
      val asmpreps = prep_subst_in_asms i th;
      val stepthms = Seq.of_list (prep_meta_eq ctxt instepthm);
      fun rewrite_with_thm r =
          let val (lhs,_) = Logic.dest_equals (Thm.concl_of r)
            fun occ_search occ [] = Seq.empty
              | occ_search occ ((asminfo, searchinfo)::moreasms) =
                (case searchf searchinfo occ lhs of
                   IsaPLib.skipmore i => occ_search i moreasms
                 | IsaPLib.skipseq ss =>
                   Seq.append (Seq.map (Library.pair asminfo)
                                       (Seq.flat ss),
                               occ_search 1 moreasms))
                              (* find later substs also *)
          in
            occ_search skipocc asmpreps |> Seq.maps (apply_subst_in_asm i th r)
          end;
    in stepthms |> Seq.maps rewrite_with_thm end;


fun skip_first_asm_occs_search searchf sinfo occ lhs =
    IsaPLib.skipto_seqseq occ (searchf sinfo lhs);

fun eqsubst_asm_tac ctxt occL thms i th =
    let val nprems = Thm.nprems_of th
    in
      if nprems < i then Seq.empty else
      let val thmseq = (Seq.of_list thms)
        fun apply_occ occK th =
            thmseq |> Seq.maps
                    (fn r =>
                        eqsubst_asm_tac' ctxt (skip_first_asm_occs_search
                                            searchf_tlr_unify_valid) occK r
                                         (i + ((Thm.nprems_of th) - nprems))
                                         th);
        val sortedoccs =
            Library.sort (Library.rev_order o Library.int_ord) occL
      in
        Seq.map distinct_subgoals
                (Seq.EVERY (map apply_occ sortedoccs) th)
      end
    end
    handle THM _ => raise eqsubst_occL_exp ("THM",occL,thms,i,th);

(* inthms are the given arguments in Isar, and treated as eqstep with
   the first one, then the second etc *)
fun eqsubst_asm_meth ctxt occL inthms =
    Method.METHOD
      (fn facts =>
          HEADGOAL (Method.insert_tac facts THEN' eqsubst_asm_tac ctxt occL inthms ));

(* syntax for options, given "(asm)" will give back true, without
   gives back false *)
val options_syntax =
    (Args.parens (Args.$$$ "asm") >> (K true)) ||
     (Scan.succeed false);

val ith_syntax =
    (Args.parens (Scan.repeat Args.nat))
      || (Scan.succeed [0]);

(* combination method that takes a flag (true indicates that subst
should be done to an assumption, false = apply to the conclusion of
the goal) as well as the theorems to use *)
fun subst_meth src =
  Method.syntax ((Scan.lift options_syntax) -- (Scan.lift ith_syntax) -- Attrib.local_thms) src
  #> (fn (ctxt, ((asmflag, occL), inthms)) =>
    (if asmflag then eqsubst_asm_meth else eqsubst_meth) ctxt occL inthms);


val setup =
  Method.add_method ("subst", subst_meth, "single-step substitution");

end;
