(*  Title:      HOL/Modelcheck/MuckeSyn.thy
    Author:     Tobias Hamberger
    Copyright   1999  TU Muenchen
*)

theory MuckeSyn
imports MuCalculus
uses "mucke_oracle.ML"
begin

(* extended with some operators and case treatment (which requires postprocessing with
transform_case (from MuCalculus) (TH) *)

nonterminals
  mutype
  decl decls
  cases_syn case_syn

syntax (Mucke output)
  True          :: bool                                 ("true")
  False         :: bool                                 ("false")
  Not           :: "bool => bool"                       ("! _" [40] 40)
  If            :: "[bool, 'a, 'a] => 'a"       ("('(if'((_)')/ '((_)')/ else/ '((_)'))')" 10)

  "op &"        :: "[bool, bool] => bool"               (infixr "&" 35)
  "op |"        :: "[bool, bool] => bool"               (infixr "|" 30)
  "op -->"      :: "[bool, bool] => bool"               (infixr "->" 25)
  "op ="        :: "['a, 'a] => bool"                   ("(_ =/ _)" [51, 51] 50)
  "_not_equal"  :: "['a, 'a] => bool"                   ("(_ !=/ _)" [51, 51] 50)

  All_binder    :: "[idts, bool] => bool"               ("'((3forall _./ _)')" [0, 10] 10)
  Ex_binder     :: "[idts, bool] => bool"               ("'((3exists _./ _)')" [0, 10] 10)

  "_lambda"     :: "[idts, 'a] => 'b"                   ("(3L _./ _)" 10)
  "_applC"      :: "[('b => 'a), cargs] => aprop"       ("(1_/ '(_'))" [1000,1000] 999)
  "_cargs"      :: "['a, cargs] => cargs"               ("_,/ _" [1000,1000] 1000)

  "_idts"       :: "[idt, idts] => idts"                ("_,/ _" [1, 0] 0)

  "_tuple"      :: "'a => tuple_args => 'a * 'b"        ("(1_,/ _)")
(* "@pttrn"     :: "[pttrn, pttrns] => pttrn"           ("_,/ _" [1, 0] 0)
  "_pattern"    :: "[pttrn, patterns] => pttrn"         ("_,/ _" [1, 0] 0) *)

  "_decl"       :: "[mutype,pttrn] => decl"             ("_ _")
  "_decls"      :: "[decl,decls] => decls"              ("_,/ _")
  ""            :: "decl => decls"                      ("_")
  "_mu"         :: "[decl,decls,'a pred] => 'a pred"    ("mu _ '(_') _ ;")
  "_mudec"      :: "[decl,decls] => 'a pred"            ("mu _ '(_') ;")
  "_nu"         :: "[decl,decls,'a pred] => 'a pred"    ("nu _ '(_') _ ;")
  "_nudec"      :: "[decl,decls] => 'a pred"            ("nu _ '(_') ;")
  "_fun"        :: "[decl,decls,'a pred] => 'a pred"    ("_ '(_') _ ;")
  "_dec"        :: "[decl,decls] => 'a pred"            ("_ '(_') ;")

  "_Ex"         :: "[decl,idts,'a pred] => 'a pred"     ("'((3exists _ _./ _)')")
  "_All"        :: "[decl,idts,'a pred] => 'a pred"     ("'((3forall _ _./ _)')")

  "Mu "         :: "[idts, 'a pred] => 'a pred"         ("(3mu _./ _)" 1000)
  "Nu "         :: "[idts, 'a pred] => 'a pred"         ("(3nu _./ _)" 1000)

  "_case_syntax":: "['a, cases_syn] => 'b"              ("(case*_* / _ / esac*)" 10)
  "_case1"      :: "['a, 'b] => case_syn"               ("(2*= _ :/ _;)" 10)
  ""            :: "case_syn => cases_syn"              ("_")
  "_case2"      :: "[case_syn, cases_syn] => cases_syn" ("_/ _")

(*Terms containing a case statement must be post-processed with the
  ML function transform_case. There, all asterikses before the "="
  will be replaced by the expression between the two asterisks
  following "case" and the asterisk after esac will be deleted *)

oracle mc_mucke_oracle = mk_mc_mucke_oracle

ML {*
(* search_mu t searches for Mu terms in term t. In the case of nested Mu's,
   it yields innermost one. If no Mu term is present, search_mu yields NONE
*)

(* extended for treatment of nu (TH) *)
fun search_mu ((Const("MuCalculus.mu",tp)) $ t2) = 
        (case (search_mu t2) of
              SOME t => SOME t 
            | NONE => SOME ((Const("MuCalculus.mu",tp)) $ t2))
  | search_mu ((Const("MuCalculus.nu",tp)) $ t2) =
        (case (search_mu t2) of
              SOME t => SOME t
            | NONE => SOME ((Const("MuCalculus.nu",tp)) $ t2))
  | search_mu (t1 $ t2) = 
        (case (search_mu t1) of
              SOME t => SOME t 
            | NONE     => search_mu t2)
  | search_mu (Abs(_,_,t)) = search_mu t
  | search_mu _ = NONE;




(* seraching a variable in a term. Used in move_mus to extract the
   term-rep of var b in hthm *)

fun search_var s t =
case t of
     t1 $ t2 => (case (search_var s t1) of
                             SOME tt => SOME tt |
                             NONE => search_var s t2) |
     Abs(_,_,t) => search_var s t |
     Var((s1,_),_) => if s = s1 then SOME t else NONE |
     _ => NONE;
        

(* function move_mus:
   Mucke can't deal with nested Mu terms. move_mus i searches for 
   Mu terms in the subgoal i and replaces Mu terms in the conclusion
   by constants and definitions in the premises recursively.

   move_thm is the theorem the performs the replacement. To create NEW
   names for the Mu terms, the indizes of move_thm are incremented by
   max_idx of the subgoal.
*)

local

  val move_thm = OldGoals.prove_goal @{theory} "[| a = b ==> P a; a = b |] ==> P b"
        (fn prems => [cut_facts_tac prems 1, dtac sym 1, hyp_subst_tac 1,
                     REPEAT (resolve_tac prems 1)]);

  val sig_move_thm = Thm.theory_of_thm move_thm;
  val bCterm = cterm_of sig_move_thm (the (search_var "b" (concl_of move_thm)));
  val aCterm = cterm_of sig_move_thm (the (search_var "a" (hd(prems_of move_thm)))); 

in

fun move_mus i state =
let val sign = Thm.theory_of_thm state;
    val (subgoal::_) = Library.drop(i-1,prems_of state);
    val concl = Logic.strip_imp_concl subgoal; (* recursive mu's in prems? *)
    val redex = search_mu concl;
    val idx = let val t = #maxidx (rep_thm state) in 
              if t < 0 then 1 else t+1 end;
in
case redex of
     NONE => all_tac state |
     SOME redexterm => 
        let val Credex = cterm_of sign redexterm;
            val aiCterm = 
                cterm_of sig_move_thm (Logic.incr_indexes ([],idx) (term_of aCterm));
            val inst_move_thm = cterm_instantiate 
                                [(bCterm,Credex),(aCterm,aiCterm)] move_thm;
        in
            ((rtac inst_move_thm i) THEN (dtac eq_reflection i) 
                THEN (move_mus i)) state
        end
end;
end;


val call_mucke_tac = CSUBGOAL (fn (cgoal, i) =>
let val OraAss = mc_mucke_oracle cgoal
in cut_facts_tac [OraAss] i end);


(* transforming fun-defs into lambda-defs *)

val [eq] = OldGoals.goal Pure.thy "(!! x. f x == g x) ==> f == g";
 OldGoals.by (rtac (extensional eq) 1);
OldGoals.qed "ext_rl";

infix cc;

fun NONE cc xl = xl
  | (SOME x) cc xl = x::xl;

fun getargs ((x $ y) $ (Var ((z,_),_))) = getargs (x $ y) ^ " " ^z
  | getargs (x $ (Var ((y,_),_))) = y;

fun getfun ((x $ y) $ z) = getfun (x $ y)
  | getfun (x $ _) = x;

local

fun delete_bold [] = []
| delete_bold (x::xs) = if (is_prefix (op =) ("\^["::"["::"0"::"m"::[]) (x::xs))
        then (let val (_::_::_::s) = xs in delete_bold s end)
        else (if (is_prefix (op =) ("\^["::"["::"1"::"m"::[]) (x::xs))
                then  (let val (_::_::_::s) = xs in delete_bold s end)
                else (x::delete_bold xs));

fun delete_bold_string s = implode(delete_bold (explode s));

in

(* extension with removing bold font (TH) *)
fun mk_lam_def (_::_) _ _ = NONE  
  | mk_lam_def [] ((Const("==",_) $ (Const _)) $ RHS) t = SOME t
  | mk_lam_def [] ((Const("==",_) $ LHS) $ RHS) t = 
    let val thy = theory_of_thm t;
        val fnam = Syntax.string_of_term_global thy (getfun LHS);
        val rhs = Syntax.string_of_term_global thy (freeze_thaw RHS)
        val gl = delete_bold_string (fnam ^" == % " ^ (getargs LHS) ^" . " ^ rhs);
    in
        SOME (OldGoals.prove_goal thy gl (fn prems =>
                [(REPEAT (rtac ext_rl 1)), (rtac t 1) ]))
    end
| mk_lam_def [] _ t= NONE; 

fun mk_lam_defs ([]:thm list) = ([]: thm list) 
  | mk_lam_defs (t::l) = 
      (mk_lam_def (prems_of t) (concl_of t) t) cc (mk_lam_defs l);

end;


(* first simplification, then model checking *)

val pair_eta_expand = Thm.symmetric (mk_meta_eq (thm "split_eta"));

val pair_eta_expand_proc =
  Simplifier.simproc @{theory} "pair_eta_expand" ["f::'a*'b=>'c"]
  (fn _ => fn _ => fn t => case t of Abs _ => SOME pair_eta_expand | _ => NONE);

val Mucke_ss = @{simpset} addsimprocs [pair_eta_expand_proc] addsimps [Let_def];


(* the interface *)

fun mc_mucke_tac defs i state =
  (case Library.drop (i - 1, Thm.prems_of state) of
    [] => no_tac state
  | subgoal :: _ =>
      EVERY [
        REPEAT (etac thin_rl i),
        cut_facts_tac (mk_lam_defs defs) i,
        full_simp_tac (Mucke_ss delsimps [not_iff,split_part]) i,
        move_mus i, call_mucke_tac i,atac i,
        REPEAT (rtac refl i)] state);
*}

end
