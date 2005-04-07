(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      libs/isa_fterm.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
    Date:       16 April 2003
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Generic Foucs terms (like Zippers) instantiation for Isabelle terms. 

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature ISA_ENCODE_TERM = 
  F_ENCODE_TERM_SIG
    where type term = Term.term type TypeT = Term.typ;


(* signature BASIC_ISA_FTERM = 
FOCUS_TERM_SIG where type Term = ISA_ENCODE_TERM.Term *)

(* 
signature ISA_FTERM =
sig
  include F_ENCODE_TERM_SIG

    val clean_match_ft :
       Type.tsig ->
       FcTerm ->
       Term.term ->
       (
       ((Term.indexname * Term.typ) list * (Term.indexname * Term.term) list)
       * (string * Type) list * Term.term) option
    val clean_unify_ft :
       Sign.sg ->
       int ->
       FcTerm ->
       Term.term ->
       (
       ((Term.indexname * Term.typ) list * (Term.indexname * Term.term) list)
       * (string * Type) list * Term.term) Seq.seq
    val fakefree_badbounds :
       (string * Term.typ) list -> int -> Term.term -> Term.term
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
    val focus_to_concl : FcTerm -> FcTerm
    val focus_to_concl_of_term : EncodeIsaFTerm.term -> FcTerm
    val focus_to_subgoal :
       int -> FcTerm -> FcTerm
    val focus_to_subgoal_of_term :
       int -> EncodeIsaFTerm.term -> FcTerm
    val focus_to_term_goal_prem :
       int * int -> EncodeIsaFTerm.term -> FcTerm
    val focuseq_to_subgoals :
       FcTerm -> FcTerm Seq.seq
    exception isa_focus_term_exp of string
    val mk_foo_match :
       (Term.term -> Term.term) ->
       ('a * Term.typ) list -> Term.term -> Term.term
    val prepmatch :
       FcTerm ->
       Term.term * ((string * Type) list * Term.term)
    val search_bl_ru_f :
       (FcTerm -> 'a Seq.seq) ->
       FcTerm -> 'a Seq.seq
    val search_bl_ur_f :
       (FcTerm -> 'a Seq.seq) ->
       FcTerm -> 'a Seq.seq
    val valid_match_start : FcTerm -> bool

end *)

structure BasicIsaFTerm = 
FocusTermFUN( structure EncodeTerm = EncodeIsaFTerm);

(* HOL Dependent *)
structure IsaFTerm =
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
     | Free _ =>  true
     | Abs _ =>  true
     | _ => false);

(* match starting at the bottom left, moving up to top of the term,
   then moving right to the next leaf and up again etc *)
(* FIXME: make properly lazy! *)
fun search_nonvar_bl_ur_f f ft = 
    let 
      val fts = 
          Seq.filter valid_match_start
                     (leaf_seq_of_fcterm ft)

      fun mk_match_up_seq ft =
          case focus_up_abs_or_appr ft of 
            SOME ft' => Seq.append(f ft, mk_match_up_seq ft')
          | NONE => f ft
    in
      Seq.flat (Seq.map mk_match_up_seq fts)
    end;

fun search_bl_ur_f f ft = 
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
fun search_nonvar_bl_ru_f f ft = 
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
          | (Abs _) => Seq.append (maux (focus_abs ft), 
                                   f ft)
          | leaf => f ft) end
    in
      mauxtop ft
    end;


fun search_bl_ru_f f ft = 
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




(* T is outer bound vars, n is number of locally bound vars *)
fun fakefree_badbounds T n (a $ b) = 
    (fakefree_badbounds T n a) $ (fakefree_badbounds T n b)
  | fakefree_badbounds T n (Abs(s,ty,t)) =  
    Abs(s,ty, fakefree_badbounds T (n + 1) t)
  | fakefree_badbounds T n (b as Bound i) = 
    let fun mkfake_bound j [] = 
            raise ERROR_MESSAGE "fakefree_badbounds: bound is outside of the known types!"
          | mkfake_bound 0 ((s,ty)::Ts) = 
            Free (RWTools.mk_fake_bound_name s,ty)
          | mkfake_bound j (d::Ts) = mkfake_bound (j - 1) Ts
    in if n <= i then mkfake_bound (i - n) T else b end
  | fakefree_badbounds T n t = t;


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

(* before matching we need to fake the bound vars that missing an
abstraction. In this function we additionally construct the
abstraction environment, and an outer context term (with the focus
abstracted out) for use in rewriting with RWInst.rw *)
fun prepmatch ft = 
    let 
      val t = focus_of_fcterm ft  
      val Ts = tyenv_of_focus ft
      val t' = fakefree_badbounds Ts 0 t
      fun mktermf t = 
          term_of_fcterm (set_focus_of_fcterm ft t)
      val absterm = mk_foo_match mktermf Ts t'
    in
      (t', (Ts, absterm))
    end;

(* matching and unification for a focus term's focus *)
fun clean_match_ft tsig pat ft = 
    let val (t, (Ts,absterm)) = prepmatch ft in
      case TermLib.clean_match tsig (pat, t) of 
        NONE => NONE 
      | SOME insts => SOME (insts, Ts, absterm) end;
(* ix = max var index *)
fun clean_unify_ft sgn ix pat ft = 
    let val (t, (Ts,absterm)) = prepmatch ft in
    Seq.map (fn insts => (insts, Ts, absterm)) 
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
    let val subgoal_fcterm = focus_to_subgoal_of_term i t
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
