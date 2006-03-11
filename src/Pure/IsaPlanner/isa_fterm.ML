(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      Pure/IsaPlanner/isa_fterm.ML
    ID:		$Id$
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
    Date:       16 April 2003
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Generic Foucs terms (like Zippers) instantiation for Isabelle terms. 

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature ISA_ENCODE_TERM =  (* cf. F_ENCODE_TERM_SIG *)
sig
  type term
  type typ
  type LeafT
  datatype TermT = $ of TermT * TermT
    | Abs of string * typ * TermT
    | lf of LeafT
  val fakebounds : string * typ -> term -> term
  val encode : term -> TermT
  val decode : TermT -> term
end;

(* signature BASIC_ISA_FTERM = 
FOCUS_TERM_SIG where type Term = ISA_ENCODE_TERM.Term *)

signature ISA_FTERM =
  sig
    type Term (*= EncodeIsaFTerm.TermT*)
    type Type (*= Term.typ*)
    type UpTerm
    datatype FcTerm = focus of Term * UpTerm
    structure MinTermS : F_ENCODE_TERM_SIG
    val add_upterm :
       UpTerm -> FcTerm -> FcTerm
    val clean_match_ft :
       theory ->
       Term.term ->
       FcTerm ->
       (
       ((Term.indexname * (Term.sort * Term.typ)) list 
        * (Term.indexname * (Term.typ * Term.term)) list)
       * (string * Term.typ) list 
       * (string * Term.typ) list 
       * Term.term)
       option
    val clean_unify_ft :
       theory ->
       int ->
       Term.term ->
       FcTerm ->
       (
       ((Term.indexname * (Term.sort * Term.typ)) list 
        * (Term.indexname * (Term.typ * Term.term)) list)
       * (string * Term.typ) list * (string * Term.typ) list * Term.term)
       Seq.seq
    val enc_appl :
       EncodeIsaFTerm.term * UpTerm -> UpTerm
    val enc_appr :
       EncodeIsaFTerm.term * UpTerm -> UpTerm

    val fcterm_of_term : EncodeIsaFTerm.term -> FcTerm
    val find_fcterm_matches :
       ((FcTerm -> 'a) -> FcTerm -> 'b) ->
       (FcTerm -> 'a) -> FcTerm -> 'b
    val find_sg_concl_matches :
       ((FcTerm -> 'a) -> FcTerm -> 'b) ->
       (FcTerm -> 'a) -> int -> EncodeIsaFTerm.term -> 'b
    val find_sg_concl_thm_matches :
       ((FcTerm -> 'a) -> FcTerm -> 'b) ->
       (FcTerm -> 'a) -> int -> Thm.thm -> 'b
    val find_sg_matches :
       ((FcTerm -> 'a) -> FcTerm -> 'b) ->
       (FcTerm -> 'a) -> int -> EncodeIsaFTerm.term -> 'b
    val find_sg_thm_matches :
       ((FcTerm -> 'a) -> FcTerm -> 'b) ->
       (FcTerm -> 'a) -> int -> Thm.thm -> 'b
    val focus_abs : FcTerm -> FcTerm
    val focus_bot_left_leaf : FcTerm -> FcTerm
    val focus_bot_left_nonabs_leaf :
       FcTerm -> FcTerm
    val focus_fake_abs : FcTerm -> FcTerm
    val focus_left : FcTerm -> FcTerm
    val focus_of_fcterm : FcTerm -> EncodeIsaFTerm.term
    val focus_right : FcTerm -> FcTerm
    val focus_strict_left : FcTerm -> FcTerm
    exception focus_term_exp of string
    val focus_to_concl : FcTerm -> FcTerm
    val focus_to_concl_of_term : EncodeIsaFTerm.term -> FcTerm
    val focus_to_dest_impl :
       FcTerm -> FcTerm * FcTerm
    val focus_to_subgoal :
       int -> FcTerm -> FcTerm
    val focus_to_subgoal_of_term :
       int -> EncodeIsaFTerm.term -> FcTerm
    val focus_to_term_goal_prem :
       int * int -> EncodeIsaFTerm.term -> FcTerm
    val focus_to_top : FcTerm -> FcTerm
    val focus_up : FcTerm -> FcTerm
    val focus_up_abs : FcTerm -> FcTerm option
    val focus_up_abs_or_appr :
       FcTerm -> FcTerm option
    val focus_up_appl : FcTerm -> FcTerm option
    val focus_up_appr : FcTerm -> FcTerm option
    val focus_up_right : FcTerm -> FcTerm
    val focus_up_right1 : FcTerm -> FcTerm
    val focuseq_to_subgoals :
       FcTerm -> FcTerm Seq.seq
    exception isa_focus_term_exp of string
    val leaf_seq_of_fcterm :
       FcTerm -> FcTerm Seq.seq
    val mk_term_of_upterm :
       EncodeIsaFTerm.term * UpTerm -> EncodeIsaFTerm.term
    val mk_termf_of_upterm :
       UpTerm ->
       (string * Type) list *
       (EncodeIsaFTerm.term -> EncodeIsaFTerm.term)
    val next_leaf_fcterm : FcTerm -> FcTerm
    val next_leaf_of_fcterm_seq :
       FcTerm -> FcTerm Seq.seq
    exception out_of_term_exception of string

    val pure_mk_termf_of_upterm :
       (EncodeIsaFTerm.term, Type) UpTermLib.T ->
       (string * Type) list *
       (EncodeIsaFTerm.term -> EncodeIsaFTerm.term)
    val search_all_bl_ru_f :
       (FcTerm -> 'a Seq.seq) ->
       FcTerm -> 'a Seq.seq
    val search_all_bl_ur_f :
       (FcTerm -> 'a Seq.seq) ->
       FcTerm -> 'a Seq.seq
    val search_tlr_all_f :
       (FcTerm -> 'a Seq.seq) ->
       FcTerm -> 'a Seq.seq
    val search_tlr_valid_f :
       (FcTerm -> 'a Seq.seq) ->
       FcTerm -> 'a Seq.seq
    val search_valid_bl_ru_f :
       (FcTerm -> 'a Seq.seq) ->
       FcTerm -> 'a Seq.seq
    val search_valid_bl_ur_f :
       (FcTerm -> 'a Seq.seq) ->
       FcTerm -> 'a Seq.seq
    val set_focus_of_fcterm :
       FcTerm -> EncodeIsaFTerm.term -> FcTerm
    val term_of_fcterm : FcTerm -> EncodeIsaFTerm.term
    val tyenv_of_focus :
       FcTerm -> (string * Type) list
    val tyenv_of_focus' : FcTerm -> Type list
    val upsize_of_fcterm : FcTerm -> int
    val upterm_of : FcTerm -> UpTerm
    val valid_match_start : FcTerm -> bool

     (* pre-matching/pre-unification *)
     val fakefree_badbounds : 
       (string * Term.typ) list -> Term.term ->
       (string * Term.typ) list * (string * Term.typ) list * Term.term
     val mk_foo_match :
       (Term.term -> Term.term) ->
       ('a * Term.typ) list -> Term.term -> Term.term
     val prepmatch :
       FcTerm ->
       Term.term *
       ((string * Term.typ) list * (string * Term.typ) list * Term.term)


    val pretty : Theory.theory -> FcTerm -> Pretty.T

  end;



structure BasicIsaFTerm = 
FocusTermFUN( structure EncodeTerm = EncodeIsaFTerm);

(* HOL Dependent *)
structure IsaFTerm : ISA_FTERM=
struct 

(* include BasicIsaFTerm *)
(* open FocusTermFUN( structure EncodeTerm = EncodeIsaFTerm ); *)

open BasicIsaFTerm;


(* Some general search within a focus term... *)

(* Note: only upterms with a free or constant are going to yeald a
match, thus if we get anything else (bound or var) skip it! This is
important if we switch to a unification net! in particular to avoid
vars. *)

fun valid_match_start ft =
    (case TermLib.bot_left_leaf_of (focus_of_fcterm ft) of 
       Const _ => true
     | Free _ => true
     | Abs _ => true (* allowed to look inside abs... search decides if we actually consider the abstraction itself *)
     | _ => false); (* avoid vars - always suceeds uninterestingly. *)

(* match starting at the bottom left, moving up to top of the term,
   then moving right to the next leaf and up again etc *)
(* FIXME: make properly lazy! *)
fun search_valid_bl_ur_f f ft = 
    let 
      val fts = 
          Seq.filter valid_match_start
                     (leaf_seq_of_fcterm ft)

      fun mk_match_up_seq ft =
          (* avoid abstractions? - possibly infinite unifiers? *)
          let val hereseq = case (focus_of_fcterm ft) of 
                              Abs _ => Seq.empty
                            | _ => f ft
          in
            case focus_up_abs_or_appr ft of 
              SOME ft' => Seq.append(hereseq, mk_match_up_seq ft')
            | NONE => hereseq
          end
    in
      Seq.flat (Seq.map mk_match_up_seq fts)
    end;

fun search_all_bl_ur_f f ft = 
    let 
      val fts = (leaf_seq_of_fcterm ft)

      fun mk_match_up_seq ft =            
          case focus_up_abs_or_appr ft of 
            SOME ft' => Seq.append(f ft, mk_match_up_seq ft')
          | NONE => f ft
    in
      Seq.flat (Seq.map mk_match_up_seq fts)
    end;


(* FIXME: make properly lazy! *)
(* FIXME: make faking of bound vars local - for speeeeed *)
fun search_valid_bl_ru_f f ft = 
    let
      fun mauxtop ft = 
          if (valid_match_start ft)
            then maux ft else Seq.empty
      and maux ft = 
          let val t' = (focus_of_fcterm ft) 
          (* val _ = writeln ("Examining: " ^ (TermLib.string_of_term t')) *)
          in 
          (case t' of 
            (_ $ _) => Seq.append (maux (focus_left ft), 
                         Seq.append(mauxtop (focus_right ft), 
                                    f ft))
          | (Abs _) => maux (focus_abs ft)
          | leaf => f ft) end
    in
      mauxtop ft
    end;


fun search_all_bl_ru_f f ft = 
    let
      fun maux ft = 
          let val t' = (focus_of_fcterm ft) 
          (*   val _ = writeln ("Examining: " ^ (TermLib.string_of_term t')) *)
          in 
          (case t' of 
            (_ $ _) => Seq.append (maux (focus_left ft), 
                         Seq.append(maux (focus_right ft), 
                                    f ft))
          | (Abs _) => Seq.append (maux (focus_abs ft), 
                                   f ft)
          | leaf => f ft) end
    in maux ft end;

(* search from top, left to right, then down *)
fun search_tlr_all_f f ft = 
    let
      fun maux ft = 
          let val t' = (focus_of_fcterm ft) 
            (* val _ = 
                if !trace_subst_search then 
                  (writeln ("Examining: " ^ (TermLib.string_of_term t'));
                   TermLib.writeterm t'; ())
                else (); *)
          in 
          (case t' of 
            (_ $ _) => Seq.append(maux (focus_left ft), 
                       Seq.append(f ft, 
                                  maux (focus_right ft)))
          | (Abs _) => Seq.append(f ft, maux (focus_abs ft))
          | leaf => f ft) end
    in maux ft end;

fun search_tlr_valid_f f ft = 
    let
      fun maux ft = 
          let 
            val hereseq = if valid_match_start ft then f ft else Seq.empty
          in 
          (case (focus_of_fcterm ft) of 
            (_ $ _) => Seq.append(maux (focus_left ft), 
                       Seq.append(hereseq, 
                                  maux (focus_right ft)))
          | (Abs _) => Seq.append(hereseq, maux (focus_abs ft))
          | leaf => hereseq)
          end
    in maux ft end;



exception isa_focus_term_exp of string;


fun focus_to_dest_impl ft = 
    let val (lhs, rhs) = 
            Logic.dest_implies (focus_of_fcterm ft) 
    in (focus_left ft, focus_right ft) end
    handle Term.TERM _ => 
           raise isa_focus_term_exp 
                   "focus_to_dest_impl: applied to non implication";


(* move focus to the conlusion *)
fun focus_to_concl ft = 
    let val (lhs, rhs) = 
            Logic.dest_implies (focus_of_fcterm ft) 
    in focus_to_concl (focus_right ft) end
    handle Term.TERM _ =>  ft;

val focus_to_concl_of_term = focus_to_concl o fcterm_of_term;



(* give back sequence of focuses at different subgoals *)
(* FIXME: make truly lazy *)
fun focuseq_to_subgoals ft = 
    if (Logic.is_implies (focus_of_fcterm ft)) then 
      Seq.cons (focus_right (focus_left ft), focuseq_to_subgoals (focus_right ft))
    else
      Seq.empty;

(* move focus to a specific subgoal, 0 is first  *)
fun focus_to_subgoal j ft = 
    let fun focus_to_subgoal' (ft, 0) = 
            let val (lhs, rhs) = Logic.dest_implies (focus_of_fcterm ft) 
            in ft |> focus_left |> focus_right end
          | focus_to_subgoal' (ft, i) = 
            let val (lhs, rhs) = Logic.dest_implies (focus_of_fcterm ft) 
            in focus_to_subgoal' (focus_right ft, i - 1) end
    in focus_to_subgoal' (ft, j - 1) end
    handle Term.TERM _ => 
           raise isa_focus_term_exp 
                   ("focus_to_subgoal: No such subgoal: " ^ 
                    (string_of_int j));

fun focus_to_subgoal_of_term i t = 
    focus_to_subgoal i (fcterm_of_term t)

(* move focus to a specific premise *)
(* fun focus_past_params i ft = 
    (focus_to_subgoal (focus_right ft, i))
    handle isa_focus_term_exp _ => 
           raise isa_focus_term_exp 
             ("focus_to_prmise: No such premise: " ^ (string_of_int i)); *)

fun focus_to_term_goal_prem (premid,gaolid) t = 
    focus_to_subgoal premid (focus_to_subgoal_of_term gaolid t);



(* FIXME: make a sturcture for holding free variable names and making
them distinct --- ? maybe part of the new prooftree datatype ?
Alos: use this to fix below... *)

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

(* fun fakefree_badbounds usednames T n (a $ b) =  *)
(*     let val (usednames', T', a') = fakefree_badbounds usednames T n a *)
(*       val (usednames'', T'', b') = fakefree_badbounds usednames' T n b in  *)
(*       (usednames'', T'', a' $ b') end *)
(*   | fakefree_badbounds usednames T n (Abs(s,ty,t)) =  *)
(*     let val (usednames', T', t') = fakefree_badbounds usednames T (n + 1) t in *)
(*     (usednames', T', Abs(s,ty, t')) *)
(*   | fakefree_badbounds usednames T n (b as Bound i) =  *)
(*     let fun mkfake_bound j [] =  *)
(*             raise ERROR_MESSAGE "fakefree_badbounds: bound is outside of the known types!" *)
(*           | mkfake_bound 0 ((s,ty)::Ts) =  *)
(*             let val newname = Term.variant s usednames in *)
(*             usednames, (newname,ty) :: T,  Free (newname,ty) *)
(*           | mkfake_bound j (d::Ts) = mkfake_bound (j - 1) Ts *)
(*     in if n <= i then mkfake_bound (i - n) T else b end *)
(*   | fakefree_badbounds usednames T t = t; *)


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

(* before matching we need to fake the bound vars that are missing an
abstraction. In this function we additionally construct the
abstraction environment, and an outer context term (with the focus
abstracted out) for use in rewriting with RWInst.rw *)
fun prepmatch ft = 
    let 
      val t = focus_of_fcterm ft  
      val Ts = tyenv_of_focus ft
      val (FakeTs', Ts', t') = fakefree_badbounds Ts t
      fun mktermf t = 
          term_of_fcterm (set_focus_of_fcterm ft t)
      val absterm = mk_foo_match mktermf Ts' t'
    in
      (t', (FakeTs', Ts', absterm))
    end;


fun pretty thy ft = 
    let val (t', (_,_,absterm)) = prepmatch ft in 
      Pretty.chunks
        [ Pretty.block [Pretty.str "(Abs:",
                        Pretty.quote (Display.pretty_cterm (Thm.cterm_of thy absterm)),
                        Pretty.str ","],
          Pretty.block [Pretty.str " Foc:",
                        Pretty.quote (Display.pretty_cterm (Thm.cterm_of thy t')),
                        Pretty.str ")" ] ]
    end;

(* 
    Pretty.str "no yet implemented";
      Display.pretty_cterm (Thm.cterm_of t)
      Term.Free ("FOCUS", Term.type_of t)
*)


(* matching and unification for a focus term's focus *)

(* Note: Ts is a modified version of the original names of the outer
bound variables. New names have been introduced to make sure they are
unique w.r.t all names in the term and each other. usednames' is
oldnames + new names. *)
fun clean_match_ft thy pat ft = 
    let val (t, (FakeTs,Ts,absterm)) = prepmatch ft in
      case TermLib.clean_match thy (pat, t) of 
        NONE => NONE 
      | SOME insts => SOME (insts, FakeTs, Ts, absterm) end;
(* ix = max var index *)
fun clean_unify_ft sgn ix pat ft = 
    let val (t, (FakeTs, Ts,absterm)) = prepmatch ft in
    Seq.map (fn insts => (insts, FakeTs, Ts, absterm)) 
            (TermLib.clean_unify sgn ix (t, pat)) end;


(* THINK: ? do we not need to incremement bound indices? *)
(* THINK: it should be the search which localisaes the search to the
current focus, not this hack in the matcher... ? *)
(* find matches below this particular focus term *) 
(* The search function is to find a match within a term... *)
(* the matcher is something that is applied to each node chosen by the
searchf and the results are flattened to form a lazy list. *)
fun find_fcterm_matches searchf matcher ft = 
    let 
      val ftupterm = upterm_of ft
      val focusft = focus_of_fcterm ft
      val add_uptermf = add_upterm ftupterm 
    in
    searchf
      (fn ft' => matcher (add_uptermf ft'))
      (fcterm_of_term focusft)
    end;

(* FIXME: move argument orders for efficiency... 
i.e. wenzel style val foofunc = x o y;
*)

(* find the matches inside subgoal i of th *)
fun find_sg_matches searchf matcher i t = 
    let 
      val subgoal_fcterm = focus_to_subgoal_of_term i t
    in find_fcterm_matches searchf matcher subgoal_fcterm end;

(* find the matches inside subgoal i of th *)
fun find_sg_thm_matches searchf matcher i th = 
    find_sg_matches searchf matcher i (Thm.prop_of th);


(* find the matches inside subgoal i's conclusion of th *)
fun find_sg_concl_matches searchf matcher i t = 
    let 
      val subgoal_fcterm = 
          focus_to_concl (focus_to_subgoal_of_term i t)
    in
      find_fcterm_matches searchf matcher subgoal_fcterm
    end;

(* find the matches inside subgoal i's conclusion of th *)
fun find_sg_concl_thm_matches searchf matcher i th = 
    find_sg_concl_matches searchf matcher i (Thm.prop_of th);

end;

(* 
test... 

f_encode_isatermS.encode (read "P a");
isafocustermS.fcterm_of_term (read "f a");
isafocustermS.term_of_fcterm it;

Goal "P b ==> P (suc b)";

TermLib.string_of_term ((focus_of_fcterm o focus_to_subgoal_of_term 1 o prop_of) (topthm()));

TermLib.string_of_term ((focus_of_fcterm o focus_to_concl o focus_to_subgoal_of_term 1 o prop_of) (topthm()));

TermLib.string_of_term ((focus_of_fcterm o focus_to_term_goal_prem (1,1) o prop_of) (topthm()));

*)
