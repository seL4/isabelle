(*  Title: 	ZF/ind-syntax.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Abstract Syntax functions for Inductive Definitions
*)


(*SHOULD BE ABLE TO DELETE THESE!*)
fun flatten_typ sign T = 
    let val {syn,...} = Sign.rep_sg sign 
    in  Pretty.str_of (Syntax.pretty_typ syn T)
    end;
fun flatten_term sign t = Pretty.str_of (Sign.pretty_term sign t);

(*Add constants to a theory*)
infix addconsts;
fun thy addconsts const_decs = 
    extend_theory thy (space_implode "_" (flat (map #1 const_decs)) 
		       ^ "_Theory")
		  ([], [], [], [], const_decs, None) [];


(*Make a definition, lhs==rhs, checking that vars on lhs contain *)
fun mk_defpair sign (lhs,rhs) = 
  let val Const(name,_) = head_of lhs
      val dummy = assert (term_vars rhs subset term_vars lhs
		       andalso
		       term_frees rhs subset term_frees lhs
		       andalso
		       term_tvars rhs subset term_tvars lhs
		       andalso
		       term_tfrees rhs subset term_tfrees lhs)
	          ("Extra variables on RHS in definition of " ^ name)
  in  (name ^ "_def",
       flatten_term sign (Logic.mk_equals (lhs,rhs)))
  end;

fun lookup_const sign a = Symtab.lookup(#const_tab (Sign.rep_sg sign), a);

(*export to Pure/library?  *)
fun assert_all pred l msg_fn = 
  let fun asl [] = ()
	| asl (x::xs) = if pred x then asl xs
	                else error (msg_fn x)
  in  asl l  end;


(** Abstract syntax definitions for FOL and ZF **)

val iT = Type("i",[])
and oT = Type("o",[]);

fun ap t u = t$u;
fun app t (u1,u2) = t $ u1 $ u2;

(*Given u expecting arguments of types [T1,...,Tn], create term of 
  type T1*...*Tn => i using split*)
fun ap_split split u [ ]   = Abs("null", iT, u)
  | ap_split split u [_]   = u
  | ap_split split u [_,_] = split $ u
  | ap_split split u (T::Ts) = 
      split $ (Abs("v", T, ap_split split (u $ Bound(length Ts - 2)) Ts));

val conj = Const("op &", [oT,oT]--->oT)
and disj = Const("op |", [oT,oT]--->oT)
and imp = Const("op -->", [oT,oT]--->oT);

val eq_const = Const("op =", [iT,iT]--->oT);

val mem_const = Const("op :", [iT,iT]--->oT);

val exists_const = Const("Ex", [iT-->oT]--->oT);
fun mk_exists (Free(x,T),P) = exists_const $ (absfree (x,T,P));

val all_const = Const("All", [iT-->oT]--->oT);
fun mk_all (Free(x,T),P) = all_const $ (absfree (x,T,P));

(*Creates All(%v.v:A --> P(v)) rather than Ball(A,P) *)
fun mk_all_imp (A,P) = 
    all_const $ Abs("v", iT, imp $ (mem_const $ Bound 0 $ A) $ (P $ Bound 0));


val Part_const = Const("Part", [iT,iT-->iT]--->iT);

val Collect_const = Const("Collect", [iT,iT-->oT]--->iT);
fun mk_Collect (a,D,t) = Collect_const $ D $ absfree(a, iT, t);

val Trueprop = Const("Trueprop",oT-->propT);
fun mk_tprop P = Trueprop $ P;
fun dest_tprop (Const("Trueprop",_) $ P) = P;

(*** Tactic for folding constructor definitions ***)

(*The depth of injections in a constructor function*)
fun inject_depth (Const _ $ t) = 1 + inject_depth t
  | inject_depth t             = 0;

val rhs_of_thm = #2 o Logic.dest_equals o #prop o rep_thm;

(*There are critical pairs!  E.g. K == Inl(0),  S == Inr(Inl(0))
  Folds longest definitions first to avoid folding subexpressions of an rhs.*)
fun fold_con_tac defs =
  let val keylist = make_keylist (inject_depth o rhs_of_thm) defs;
      val keys = distinct (sort op> (map #2 keylist));
      val deflists = map (keyfilter keylist) keys
  in  EVERY (map fold_tac deflists)  end;

(*Prove a goal stated as a term, with exception handling*)
fun prove_term sign defs (P,tacsf) = 
    let val ct = Sign.cterm_of sign P
    in  prove_goalw_cterm defs ct tacsf
	handle e => (writeln ("Exception in proof of\n" ^
			       Sign.string_of_cterm ct); 
		     raise e)
    end;

(*Read an assumption in the given theory*)
fun assume_read thy a = assume (Sign.read_cterm (sign_of thy) (a,propT));

(*Make distinct individual variables a1, a2, a3, ..., an. *)
fun mk_frees a [] = []
  | mk_frees a (T::Ts) = Free(a,T) :: mk_frees (bump_string a) Ts;

(*Used by intr-elim.ML and in individual datatype definitions*)
val basic_monos = [subset_refl, imp_refl, disj_mono, conj_mono, 
		   ex_mono, Collect_mono, Part_mono, in_mono];

(*Return the conclusion of a rule, of the form t:X*)
fun rule_concl rl = 
    case dest_tprop (Logic.strip_imp_concl rl) of
        Const("op :",_) $ t $ X => (t,X) 
      | _ => error "Conclusion of rule should be a set membership";

(*For deriving cases rules.  CollectD2 discards the domain, which is redundant;
  read_instantiate replaces a propositional variable by a formula variable*)
val equals_CollectD = 
    read_instantiate [("W","?Q")]
        (make_elim (equalityD1 RS subsetD RS CollectD2));


(*From HOL/ex/meson.ML: raises exception if no rules apply -- unlike RL*)
fun tryres (th, rl::rls) = (th RS rl handle THM _ => tryres(th,rls))
  | tryres (th, []) = raise THM("tryres", 0, [th]);

fun gen_make_elim elim_rls rl = 
      standard (tryres (rl, elim_rls @ [revcut_rl]));

(** For constructor.ML **)

(*Avoids duplicate definitions by removing constants already declared mixfix*)
fun remove_mixfixes None decs = decs
  | remove_mixfixes (Some sext) decs =
      let val mixtab = Symtab.st_of_declist(Syntax.constants sext, Symtab.null)
	  fun is_mix c = case Symtab.lookup(mixtab,c) of
			     None=>false | Some _ => true
      in  map (fn (cs,styp)=> (filter_out is_mix cs, styp)) decs
      end;

fun ext_constants None        = []
  | ext_constants (Some sext) = Syntax.constants sext;


(*Could go to FOL, but it's hardly general*)
val [def] = goal IFOL.thy "a==b ==> a=c <-> c=b";
by (rewtac def);
by (rtac iffI 1);
by (REPEAT (etac sym 1));
val def_swap_iff = result();

val def_trans = prove_goal IFOL.thy "[| f==g;  g(a)=b |] ==> f(a)=b"
  (fn [rew,prem] => [ rewtac rew, rtac prem 1 ]);


