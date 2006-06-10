(*  Title:      Provers/eqsubst.ML
    ID:         $Id$
    Author:     Lucas Dixon, University of Edinburgh, lucas.dixon@ed.ac.uk

A proof method to perform a substiution using an equation.
*)

signature EQSUBST =
sig
  val setup : theory -> theory
end;

structure EqSubst
(* : EQSUBST *)
= struct

structure Z = Zipper;

(* changes object "=" to meta "==" which prepares a given rewrite rule *)
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
       * Zipper.T (* focusterm to search under *)


(* skipping non-empty sub-sequences but when we reach the end
   of the seq, remembering how much we have left to skip. *)
datatype 'a skipseq = SkipMore of int
  | SkipSeq of 'a Seq.seq Seq.seq;
(* given a seqseq, skip the first m non-empty seq's, note deficit *)
fun skipto_skipseq m s = 
    let 
      fun skip_occs n sq = 
          case Seq.pull sq of 
            NONE => SkipMore n
          | SOME (h,t) => 
            (case Seq.pull h of NONE => skip_occs n t
             | SOME _ => if n <= 1 then SkipSeq (Seq.cons h t)
                         else skip_occs (n - 1) t)
    in (skip_occs m s) end;

(* note: outerterm is the taget with the match replaced by a bound 
         variable : ie: "P lhs" beocmes "%x. P x" 
         insts is the types of instantiations of vars in lhs
         and typinsts is the type instantiations of types in the lhs
         Note: Final rule is the rule lifted into the ontext of the 
         taget thm. *)
fun mk_foo_match mkuptermfunc Ts t = 
    let 
      val ty = Term.type_of t
      val bigtype = (rev (map snd Ts)) ---> ty
      fun mk_foo 0 t = t
        | mk_foo i t = mk_foo (i - 1) (t $ (Bound (i - 1)))
      val num_of_bnds = (length Ts)
      (* foo_term = "fooabs y0 ... yn" where y's are local bounds *)
      val foo_term = mk_foo num_of_bnds (Bound num_of_bnds)
    in Abs("fooabs", bigtype, mkuptermfunc foo_term) end;

(* T is outer bound vars, n is number of locally bound vars *)
(* THINK: is order of Ts correct...? or reversed? *)
fun fakefree_badbounds Ts t = 
    let val (FakeTs,Ts,newnames) = 
            List.foldr (fn ((n,ty),(FakeTs,Ts,usednames)) => 
                           let val newname = Term.variant usednames n
                           in ((RWTools.mk_fake_bound_name newname,ty)::FakeTs,
                               (newname,ty)::Ts, 
                               newname::usednames) end)
                       ([],[],[])
                       Ts
    in (FakeTs, Ts, Term.subst_bounds (map Free FakeTs, t)) end;

(* before matching we need to fake the bound vars that are missing an
abstraction. In this function we additionally construct the
abstraction environment, and an outer context term (with the focus
abstracted out) for use in rewriting with RWInst.rw *)
fun prep_zipper_match z = 
    let 
      val t = Z.trm z  
      val c = Z.ctxt z
      val Ts = Z.C.nty_ctxt c
      val (FakeTs', Ts', t') = fakefree_badbounds Ts t
      val absterm = mk_foo_match (Z.C.apply c) Ts' t'
    in
      (t', (FakeTs', Ts', absterm))
    end;

(* Matching and Unification with exception handled *)
fun clean_match thy (a as (pat, t)) =
  let val (tyenv, tenv) = Pattern.match thy a (Vartab.empty, Vartab.empty)
  in SOME (Vartab.dest tyenv, Vartab.dest tenv)
  end handle Pattern.MATCH => NONE;
(* given theory, max var index, pat, tgt; returns Seq of instantiations *)
fun clean_unify sgn ix (a as (pat, tgt)) =
    let
      (* type info will be re-derived, maybe this can be cached
         for efficiency? *)
      val pat_ty = Term.type_of pat;
      val tgt_ty = Term.type_of tgt;
      (* is it OK to ignore the type instantiation info?
         or should I be using it? *)
      val typs_unify =
          SOME (Sign.typ_unify sgn (pat_ty, tgt_ty) (Term.Vartab.empty, ix))
            handle Type.TUNIFY => NONE;
    in
      case typs_unify of
        SOME (typinsttab, ix2) =>
        let
      (* is it right to throw away the flexes?
         or should I be using them somehow? *)
          fun mk_insts env =
            (Vartab.dest (Envir.type_env env),
             Envir.alist_of env);
          val initenv = Envir.Envir {asol = Vartab.empty,
                                     iTs = typinsttab, maxidx = ix2};
          val useq = (Unify.smash_unifiers (sgn,initenv,[a]))
	            handle UnequalLengths => Seq.empty
		               | Term.TERM _ => Seq.empty;
          fun clean_unify' useq () =
              (case (Seq.pull useq) of
                 NONE => NONE
               | SOME (h,t) => SOME (mk_insts h, Seq.make (clean_unify' t)))
	      handle UnequalLengths => NONE
                   | Term.TERM _ => NONE;
        in
          (Seq.make (clean_unify' useq))
        end
      | NONE => Seq.empty
    end;

(* Matching and Unification for zippers *)
(* Note: Ts is a modified version of the original names of the outer
bound variables. New names have been introduced to make sure they are
unique w.r.t all names in the term and each other. usednames' is
oldnames + new names. *)
fun clean_match_z thy pat z = 
    let val (t, (FakeTs,Ts,absterm)) = prep_zipper_match z in
      case clean_match thy (pat, t) of 
        NONE => NONE 
      | SOME insts => SOME (insts, FakeTs, Ts, absterm) end;
(* ix = max var index *)
fun clean_unify_z sgn ix pat z = 
    let val (t, (FakeTs, Ts,absterm)) = prep_zipper_match z in
    Seq.map (fn insts => (insts, FakeTs, Ts, absterm)) 
            (clean_unify sgn ix (t, pat)) end;


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


fun bot_left_leaf_of (l $ r) = bot_left_leaf_of l
  | bot_left_leaf_of (Abs(s,ty,t)) = bot_left_leaf_of t
  | bot_left_leaf_of x = x;

fun valid_match_start z =
    (case bot_left_leaf_of (Z.trm z) of 
       Const _ => true
     | Free _ => true
     | Abs _ => true (* allowed to look inside abs... search decides if we actually consider the abstraction itself *)
     | _ => false); (* avoid vars - always suceeds uninterestingly. *)
                      
(* search from top, left to right, then down *)
val search_tlr_all = ZipperSearch.all_td_lr;

(* search from top, left to right, then down *)
fun search_tlr_valid validf =
    let 
      fun sf_valid_td_lr z = 
          let val here = if validf z then [Z.Here z] else [] in
            case Z.trm z 
             of _ $ _ => here @ [Z.LookIn (Z.move_down_left z),
                                 Z.LookIn (Z.move_down_right z)]
              | Abs _ => here @ [Z.LookIn (Z.move_down_abs z)]
              | _ => here
          end;
    in Z.lzy_search sf_valid_td_lr end;

(* search all unifications *)
fun searchf_tlr_unify_all (sgn, maxidx, z) lhs =
    Seq.map (clean_unify_z sgn maxidx lhs) 
            (Z.limit_apply search_tlr_all z);

(* search only for 'valid' unifiers (non abs subterms and non vars) *)
fun searchf_tlr_unify_valid (sgn, maxidx, z) lhs  =
    Seq.map (clean_unify_z sgn maxidx lhs) 
            (Z.limit_apply (search_tlr_valid valid_match_start) z);


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
      val ft = ((Z.move_down_right (* ==> *)
                 o Z.move_down_left (* Trueprop *)
                 o Z.mktop
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


(* distinct subgoals *)
fun distinct_subgoals th =
  the_default th (SINGLE distinct_subgoals_tac th);

(* General substitution of multiple occurances using one of
   the given theorems*)


exception eqsubst_occL_exp of
          string * (int list) * (thm list) * int * thm;
fun skip_first_occs_search occ srchf sinfo lhs =
    case (skipto_skipseq occ (srchf sinfo lhs)) of
      SkipMore _ => Seq.empty
    | SkipSeq ss => Seq.flat ss;

fun eqsubst_tac ctxt occL thms i th =
    let val nprems = Thm.nprems_of th in
      if nprems < i then Seq.empty else
      let val thmseq = (Seq.of_list thms)
        fun apply_occ occ th =
            thmseq |> Seq.maps
                    (fn r => eqsubst_tac' 
                               ctxt 
                               (skip_first_occs_search
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

      val ft = ((Z.move_down_right (* trueprop *)
                 o Z.mktop
                 o Thm.prop_of) pth)
    in ((cfvs, j, asm_nprems, pth), (sgn, maxidx, ft)) end;

(* prepare subst in every possible assumption *)
fun prep_subst_in_asms i gth =
    map (prep_subst_in_asm i gth)
        ((fn l => Library.upto (1, length l))
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
                   SkipMore i => occ_search i moreasms
                 | SkipSeq ss =>
                   Seq.append (Seq.map (Library.pair asminfo)
                                       (Seq.flat ss),
                               occ_search 1 moreasms))
                              (* find later substs also *)
          in
            occ_search skipocc asmpreps |> Seq.maps (apply_subst_in_asm i th r)
          end;
    in stepthms |> Seq.maps rewrite_with_thm end;


fun skip_first_asm_occs_search searchf sinfo occ lhs =
    skipto_skipseq occ (searchf sinfo lhs);

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
  Method.syntax ((Scan.lift options_syntax) -- (Scan.lift ith_syntax) -- Attrib.thms) src
  #> (fn (ctxt, ((asmflag, occL), inthms)) =>
    (if asmflag then eqsubst_asm_meth else eqsubst_meth) ctxt occL inthms);


val setup =
  Method.add_method ("subst", subst_meth, "single-step substitution");

end;
