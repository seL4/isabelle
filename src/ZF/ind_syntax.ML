(*  Title: 	ZF/ind-syntax.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Abstract Syntax functions for Inductive Definitions
*)

(*The structure protects these items from redeclaration (somewhat!).  The 
  datatype definitions in theory files refer to these items by name!
*)
structure Ind_Syntax =
struct
(*Make a definition lhs==rhs, checking that vars on lhs contain those of rhs*)
fun mk_defpair (lhs, rhs) = 
  let val Const(name, _) = head_of lhs
  in (name ^ "_def", Logic.mk_equals (lhs, rhs)) end;

fun get_def thy s = get_axiom thy (s^"_def");

fun lookup_const sign a = Symtab.lookup(#const_tab (Sign.rep_sg sign), a);

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

(*Read an assumption in the given theory*)
fun assume_read thy a = assume (read_cterm (sign_of thy) (a,propT));

fun readtm sign T a = 
    read_cterm sign (a,T) |> term_of
    handle ERROR => error ("The error above occurred for " ^ a);

(*Skipping initial blanks, find the first identifier*)
fun scan_to_id s = 
    s |> explode |> take_prefix is_blank |> #2 |> Lexicon.scan_id |> #1
    handle LEXICAL_ERROR => error ("Expected to find an identifier in " ^ s);

fun is_backslash c = c = "\\";

(*Apply string escapes to a quoted string; see Def of Standard ML, page 3
  Does not handle the \ddd form;  no error checking*)
fun escape [] = []
  | escape cs = (case take_prefix (not o is_backslash) cs of
	 (front, []) => front
       | (front, _::"n"::rest) => front @ ("\n" :: escape rest)
       | (front, _::"t"::rest) => front @ ("\t" :: escape rest)
       | (front, _::"^"::c::rest) => front @ (chr(ord(c)-64) :: escape rest)
       | (front, _::"\""::rest) => front @ ("\"" :: escape rest)
       | (front, _::"\\"::rest) => front @ ("\\" :: escape rest)
       | (front, b::c::rest) => 
	   if is_blank c   (*remove any further blanks and the following \ *)
	   then front @ escape (tl (snd (take_prefix is_blank rest)))
	   else error ("Unrecognized string escape: " ^ implode(b::c::rest)));

(*Remove the first and last charaters -- presumed to be quotes*)
val trim = implode o escape o rev o tl o rev o tl o explode;

(*simple error-checking in the premises of an inductive definition*)
fun chk_prem rec_hd (Const("op &",_) $ _ $ _) =
	error"Premises may not be conjuctive"
  | chk_prem rec_hd (Const("op :",_) $ t $ X) = 
	deny (Logic.occs(rec_hd,t)) "Recursion term on left of member symbol"
  | chk_prem rec_hd t = 
	deny (Logic.occs(rec_hd,t)) "Recursion term in side formula";

(*Make distinct individual variables a1, a2, a3, ..., an. *)
fun mk_frees a [] = []
  | mk_frees a (T::Ts) = Free(a,T) :: mk_frees (bump_string a) Ts;

(*Return the conclusion of a rule, of the form t:X*)
fun rule_concl rl = 
    let val Const("Trueprop",_) $ (Const("op :",_) $ t $ X) = 
		Logic.strip_imp_concl rl
    in  (t,X)  end;

(*As above, but return error message if bad*)
fun rule_concl_msg sign rl = rule_concl rl
    handle Bind => error ("Ill-formed conclusion of introduction rule: " ^ 
			  Sign.string_of_term sign rl);

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

(** For datatype definitions **)

fun dest_mem (Const("op :",_) $ x $ A) = (x,A)
  | dest_mem _ = error "Constructor specifications must have the form x:A";

(*read a constructor specification*)
fun read_construct sign (id, sprems, syn) =
    let val prems = map (readtm sign oT) sprems
	val args = map (#1 o dest_mem) prems
	val T = (map (#2 o dest_Free) args) ---> iT
		handle TERM _ => error 
		    "Bad variable in constructor specification"
        val name = const_name id syn  (*handle infix constructors*)
    in ((id,T,syn), name, args, prems) end;

val read_constructs = map o map o read_construct;

(*convert constructor specifications into introduction rules*)
fun mk_intr_tms (rec_tm, constructs) =
  let fun mk_intr ((id,T,syn), name, args, prems) =
	  Logic.list_implies
	      (map mk_tprop prems,
	       mk_tprop (mem_const $ list_comb(Const(name,T), args) $ rec_tm)) 
  in  map mk_intr constructs  end;

val mk_all_intr_tms = flat o map mk_intr_tms o op ~~;

val Un		= Const("op Un", [iT,iT]--->iT)
and empty	= Const("0", iT)
and univ	= Const("univ", iT-->iT)
and quniv	= Const("quniv", iT-->iT);

(*Make a datatype's domain: form the union of its set parameters*)
fun union_params rec_tm =
  let val (_,args) = strip_comb rec_tm
  in  case (filter (fn arg => type_of arg = iT) args) of
         []    => empty
       | iargs => fold_bal (app Un) iargs
  end;

fun data_domain rec_tms =
  replicate (length rec_tms) (univ $ union_params (hd rec_tms));

fun Codata_domain rec_tms =
  replicate (length rec_tms) (quniv $ union_params (hd rec_tms));

(*Could go to FOL, but it's hardly general*)
val def_swap_iff = prove_goal IFOL.thy "a==b ==> a=c <-> c=b"
 (fn [def] => [(rewtac def), (rtac iffI 1), (REPEAT (etac sym 1))]);

val def_trans = prove_goal IFOL.thy "[| f==g;  g(a)=b |] ==> f(a)=b"
  (fn [rew,prem] => [ rewtac rew, rtac prem 1 ]);

(*Delete needless equality assumptions*)
val refl_thin = prove_goal IFOL.thy "!!P. [| a=a;  P |] ==> P"
     (fn _ => [assume_tac 1]);

end;

