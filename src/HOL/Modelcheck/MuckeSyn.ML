(* search_mu t searches for Mu terms in term t. In the case of nested Mu's,
   it yields innermost one. If no Mu term is present, search_mu yields None
*)

(* extended for treatment of nu (TH) *)
fun search_mu ((Const("MuCalculus.mu",tp)) $ t2) = 
	(case (search_mu t2) of
	      Some t => Some t 
	    | None => Some ((Const("MuCalculus.mu",tp)) $ t2))
  | search_mu ((Const("MuCalculus.nu",tp)) $ t2) =
        (case (search_mu t2) of
              Some t => Some t
            | None => Some ((Const("MuCalculus.nu",tp)) $ t2))
  | search_mu (t1 $ t2) = 
	(case (search_mu t1) of
	      Some t => Some t 
	    | None     => search_mu t2)
  | search_mu (Abs(_,_,t)) = search_mu t
  | search_mu _ = None;




(* seraching a variable in a term. Used in move_mus to extract the
   term-rep of var b in hthm *)

fun search_var s t =
case t of
     t1 $ t2 => (case (search_var s t1) of
		             Some tt => Some tt |
			     None => search_var s t2) |
     Abs(_,_,t) => search_var s t |
     Var((s1,_),_) => if s = s1 then Some t else None |
     _ => None;
	

(* function move_mus:
   Mucke can't deal with nested Mu terms. move_mus i searches for 
   Mu terms in the subgoal i and replaces Mu terms in the conclusion
   by constants and definitions in the premises recursively.

   move_thm is the theorem the performs the replacement. To create NEW
   names for the Mu terms, the indizes of move_thm are incremented by
   max_idx of the subgoal.
*)

local

  val move_thm = prove_goal MuckeSyn.thy "[| a = b ==> P a; a = b |] ==> P b"
	(fn prems => [cut_facts_tac prems 1, dtac sym 1, hyp_subst_tac 1,
		     REPEAT (resolve_tac prems 1)]);

  val sig_move_thm = #sign (rep_thm move_thm);
  val bCterm = cterm_of sig_move_thm (the (search_var "b" (concl_of move_thm)));
  val aCterm = cterm_of sig_move_thm (the (search_var "a" (hd(prems_of move_thm)))); 

in

fun move_mus i state =
let val sign = #sign (rep_thm state);
    val (subgoal::_) = drop(i-1,prems_of state);
    val concl = Logic.strip_imp_concl subgoal; (* recursive mu's in prems? *)
    val redex = search_mu concl;
    val idx = let val t = #maxidx (rep_thm state) in 
	      if t < 0 then 1 else t+1 end;
in
case redex of
     None => all_tac state |
     Some redexterm => 
	let val Credex = cterm_of sign redexterm;
	    val aiCterm = 
		cterm_of sig_move_thm (Logic.incr_indexes ([],idx) (term_of aCterm));
	    val inst_move_thm = cterm_instantiate 
				[(bCterm,Credex),(aCterm,aiCterm)] move_thm;
	in
            ((rtac inst_move_thm i) THEN (dtac eq_reflection i) 
		THEN (move_mus i)) state
	end
end; (* outer let *)
end; (* local *)


(* Type of call_mucke_tac has changed: an argument t of type thy was inserted (TH); *)
(* Normally t can be user-instantiated by the value thy of the Isabelle context     *)
fun call_mucke_tac i state =
let val sign = #sign (rep_thm state);
    val (subgoal::_) = drop(i-1,prems_of state);
    val OraAss = invoke_oracle MuckeSyn.thy "Mucke" (sign,MuckeOracleExn (subgoal));
in 
(cut_facts_tac [OraAss] i) state
end;


(* transforming fun-defs into lambda-defs *)

val [eq] = goal CPure.thy "(!! x. f x == g x) ==> f == g";
 by (rtac (extensional eq) 1);
qed "ext_rl";

infix cc;

fun None cc xl = xl
  | (Some x) cc xl = x::xl;

fun getargs ((x $ y) $ (Var ((z,_),_))) = getargs (x $ y) ^ " " ^z
  | getargs (x $ (Var ((y,_),_))) = y;

fun getfun ((x $ y) $ z) = getfun (x $ y)
  | getfun (x $ _) = x;

local

fun is_prefix [] s = true
| is_prefix (p::ps) [] = false
| is_prefix (p::ps) (x::xs) = (p=x) andalso (is_prefix ps xs);

fun delete_bold [] = []
| delete_bold (x::xs) = if (is_prefix ("\^["::"["::"0"::"m"::[]) (x::xs))
        then (let val (_::_::_::s) = xs in delete_bold s end)
        else (if (is_prefix ("\^["::"["::"1"::"m"::[]) (x::xs))
                then  (let val (_::_::_::s) = xs in delete_bold s end)
                else (x::delete_bold xs));

fun delete_bold_string s = implode(delete_bold (explode s));

in

(* extension with removing bold font (TH) *)
fun mk_lam_def (_::_) _ _ = None  
  | mk_lam_def [] ((Const("==",_) $ (Const _)) $ RHS) t = Some t
  | mk_lam_def [] ((Const("==",_) $ LHS) $ RHS) t = 
    let val tsig = #sign (rep_thm t);
	val fnam = Sign.string_of_term tsig (getfun LHS);
	val rhs = Sign.string_of_term tsig (freeze_thaw RHS)
	val gl = delete_bold_string (fnam ^" == % " ^ (getargs LHS) ^" . " ^ rhs);
    in
	Some (prove_goal (theory_of_sign tsig) gl (fn prems =>
  		[(REPEAT (rtac ext_rl 1)), (rtac t 1) ]))
    end
| mk_lam_def [] _ t= None; 

fun mk_lam_defs ([]:thm list) = ([]: thm list) 
  | mk_lam_defs (t::l) = 
      (mk_lam_def (prems_of t) (concl_of t) t) cc (mk_lam_defs l);

end;

(* first simplification, then model checking *)

goalw Prod.thy [split_def] "(f::'a*'b=>'c) = (%(x, y). f (x, y))";
  by (rtac ext 1);
  by (stac (surjective_pairing RS sym) 1);
  by (rtac refl 1);
qed "pair_eta_expand";

local
  val lhss = [read_cterm (sign_of thy) ("f::'a*'b=>'c", TVar (("'a", 0), []))];
  val rew = mk_meta_eq pair_eta_expand;

  fun proc _ _ (Abs _) = Some rew
    | proc _ _ _ = None;
in
  val pair_eta_expand_proc = Simplifier.mk_simproc "pair_eta_expand" lhss proc;
end;


val Mucke_ss = simpset() addsimprocs [pair_eta_expand_proc] addsimps [Let_def];


(* the interface *)

fun mc_mucke_tac defs i state =
  (case drop (i - 1, Thm.prems_of state) of
    [] => PureGeneral.Seq.empty
  | subgoal :: _ =>
      EVERY [
        REPEAT (etac thin_rl i),
        cut_facts_tac (mk_lam_defs defs) i,
        full_simp_tac (Mucke_ss delsimps [not_iff,split_part]) i,
        move_mus i, call_mucke_tac i,atac i,
        REPEAT (rtac refl i)] state);

(*check if user has mucke installed*)
fun mucke_enabled () = getenv "MUCKE_HOME" <> "";
fun if_mucke_enabled f x = if mucke_enabled () then f x else ();
