(*  Title: 	Pure/logic.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   Cambridge University 1992

Supporting code for defining the abstract type "thm"
*)

infix occs;

signature LOGIC = 
  sig
  val assum_pairs	: term -> (term*term)list
  val auto_rename	: bool ref   
  val close_form	: term -> term   
  val count_prems	: term * int -> int
  val dest_equals	: term -> term * term
  val dest_flexpair	: term -> term * term
  val dest_implies	: term -> term * term
  val dest_inclass	: term -> typ * class
  val dest_type		: term -> typ
  val flatten_params	: int -> term -> term
  val incr_indexes	: typ list * int -> term -> term
  val is_equals         : term -> bool
  val lift_fns		: term * int -> (term -> term) * (term -> term)
  val list_flexpairs	: (term*term)list * term -> term
  val list_implies	: term list * term -> term
  val list_rename_params: string list * term -> term
  val loops		: Sign.sg -> term list -> term -> term
                          -> string option * bool
  val mk_equals		: term * term -> term
  val mk_flexpair	: term * term -> term
  val mk_implies	: term * term -> term
  val mk_inclass	: typ * class -> term
  val mk_type		: typ -> term
  val occs		: term * term -> bool
  val rule_of		: (term*term)list * term list * term -> term
  val set_rename_prefix	: string -> unit   
  val skip_flexpairs	: term -> term
  val strip_assums_concl: term -> term
  val strip_assums_hyp	: term -> term list
  val strip_flexpairs	: term -> (term*term)list * term
  val strip_horn	: term -> (term*term)list * term list * term
  val strip_imp_concl	: term -> term
  val strip_imp_prems	: term -> term list
  val strip_params	: term -> (string * typ) list
  val strip_prems	: int * term list * term -> term list * term
  val unvarify		: term -> term
  val varify		: term -> term
  val termord		: term * term -> order
  val lextermord	: term list * term list -> order
  val termless		: term * term -> bool
  end;

structure Logic : LOGIC =
struct

(*** Abstract syntax operations on the meta-connectives ***)

(** equality **)

(*Make an equality.  DOES NOT CHECK TYPE OF u*)
fun mk_equals(t,u) = equals(fastype_of t) $ t $ u;

fun dest_equals (Const("==",_) $ t $ u)  =  (t,u)
  | dest_equals t = raise TERM("dest_equals", [t]);

fun is_equals (Const ("==", _) $ _ $ _) = true
  | is_equals _ = false;


(** implies **)

fun mk_implies(A,B) = implies $ A $ B;

fun dest_implies (Const("==>",_) $ A $ B)  =  (A,B)
  | dest_implies A = raise TERM("dest_implies", [A]);

(** nested implications **)

(* [A1,...,An], B  goes to  A1==>...An==>B  *)
fun list_implies ([], B) = B : term
  | list_implies (A::AS, B) = implies $ A $ list_implies(AS,B);

(* A1==>...An==>B  goes to  [A1,...,An], where B is not an implication *)
fun strip_imp_prems (Const("==>", _) $ A $ B) = A :: strip_imp_prems B
  | strip_imp_prems _ = [];

(* A1==>...An==>B  goes to B, where B is not an implication *)
fun strip_imp_concl (Const("==>", _) $ A $ B) = strip_imp_concl B
  | strip_imp_concl A = A : term;

(*Strip and return premises: (i, [], A1==>...Ai==>B)
    goes to   ([Ai, A(i-1),...,A1] , B) 	(REVERSED) 
  if  i<0 or else i too big then raises  TERM*)
fun strip_prems (0, As, B) = (As, B) 
  | strip_prems (i, As, Const("==>", _) $ A $ B) = 
	strip_prems (i-1, A::As, B)
  | strip_prems (_, As, A) = raise TERM("strip_prems", A::As);

(*Count premises -- quicker than (length ostrip_prems) *)
fun count_prems (Const("==>", _) $ A $ B, n) = count_prems (B,n+1)
  | count_prems (_,n) = n;

(** flex-flex constraints **)

(*Make a constraint.*)
fun mk_flexpair(t,u) = flexpair(fastype_of t) $ t $ u;

fun dest_flexpair (Const("=?=",_) $ t $ u)  =  (t,u)
  | dest_flexpair t = raise TERM("dest_flexpair", [t]);

(*make flexflex antecedents: ( [(a1,b1),...,(an,bn)] , C )
    goes to (a1=?=b1) ==>...(an=?=bn)==>C *)
fun list_flexpairs ([], A) = A
  | list_flexpairs ((t,u)::pairs, A) =
	implies $ (mk_flexpair(t,u)) $ list_flexpairs(pairs,A);

(*Make the object-rule tpairs==>As==>B   *)
fun rule_of (tpairs, As, B) = list_flexpairs(tpairs, list_implies(As, B));

(*Remove and return flexflex pairs: 
    (a1=?=b1)==>...(an=?=bn)==>C  to  ( [(a1,b1),...,(an,bn)] , C )	
  [Tail recursive in order to return a pair of results] *)
fun strip_flex_aux (pairs, Const("==>", _) $ (Const("=?=",_)$t$u) $ C) =
        strip_flex_aux ((t,u)::pairs, C)
  | strip_flex_aux (pairs,C) = (rev pairs, C);

fun strip_flexpairs A = strip_flex_aux([], A);

(*Discard flexflex pairs*)
fun skip_flexpairs (Const("==>", _) $ (Const("=?=",_)$_$_) $ C) =
	skip_flexpairs C
  | skip_flexpairs C = C;

(*strip a proof state (Horn clause): 
   (a1==b1)==>...(am==bm)==>B1==>...Bn==>C
    goes to   ( [(a1,b1),...,(am,bm)] , [B1,...,Bn] , C)    *)
fun strip_horn A =
  let val (tpairs,horn) = strip_flexpairs A 
  in  (tpairs, strip_imp_prems horn, strip_imp_concl horn)   end;

(** types as terms **)

fun mk_type ty = Const ("TYPE", itselfT ty);

fun dest_type (Const ("TYPE", Type ("itself", [ty]))) = ty
  | dest_type t = raise TERM ("dest_type", [t]);

(** class constraints **)

fun mk_inclass (ty, c) =
  Const (Sign.const_of_class c, itselfT ty --> propT) $ mk_type ty;

fun dest_inclass (t as Const (c_class, _) $ ty) =
      ((dest_type ty, Sign.class_of_const c_class)
        handle TERM _ => raise TERM ("dest_inclass", [t]))
  | dest_inclass t = raise TERM ("dest_inclass", [t]);


(*** Low-level term operations ***)

(*Does t occur in u?  Or is alpha-convertible to u?
  The term t must contain no loose bound variables*)
fun t occs u = (t aconv u) orelse 
      (case u of
          Abs(_,_,body) => t occs body
	| f$t' => t occs f  orelse  t occs t'
	| _ => false);

(*Close up a formula over all free variables by quantification*)
fun close_form A =
    list_all_free (map dest_Free (sort atless (term_frees A)),   
		   A);


(*** Specialized operations for resolution... ***)

(*For all variables in the term, increment indexnames and lift over the Us
    result is ?Gidx(B.(lev+n-1),...,B.lev) where lev is abstraction level *)
fun incr_indexes (Us: typ list, inc:int) t = 
  let fun incr (Var ((a,i), T), lev) = 
		Unify.combound (Var((a, i+inc), Us---> incr_tvar inc T),
				lev, length Us)
	| incr (Abs (a,T,body), lev) =
		Abs (a, incr_tvar inc T, incr(body,lev+1))
	| incr (Const(a,T),_) = Const(a, incr_tvar inc T)
	| incr (Free(a,T),_) = Free(a, incr_tvar inc T)
	| incr (f$t, lev) = incr(f,lev) $ incr(t,lev)
	| incr (t,lev) = t
  in  incr(t,0)  end;

(*Make lifting functions from subgoal and increment.
    lift_abs operates on tpairs (unification constraints)
    lift_all operates on propositions     *)
fun lift_fns (B,inc) =
  let fun lift_abs (Us, Const("==>", _) $ _ $ B) u = lift_abs (Us,B) u
	| lift_abs (Us, Const("all",_)$Abs(a,T,t)) u =
	      Abs(a, T, lift_abs (T::Us, t) u)
	| lift_abs (Us, _) u = incr_indexes(rev Us, inc) u
      fun lift_all (Us, Const("==>", _) $ A $ B) u =
	      implies $ A $ lift_all (Us,B) u
	| lift_all (Us, Const("all",_)$Abs(a,T,t)) u = 
	      all T $ Abs(a, T, lift_all (T::Us,t) u)
	| lift_all (Us, _) u = incr_indexes(rev Us, inc) u;
  in  (lift_abs([],B), lift_all([],B))  end;

(*Strips assumptions in goal, yielding list of hypotheses.   *)
fun strip_assums_hyp (Const("==>", _) $ H $ B) = H :: strip_assums_hyp B
  | strip_assums_hyp (Const("all",_)$Abs(a,T,t)) = strip_assums_hyp t
  | strip_assums_hyp B = [];

(*Strips assumptions in goal, yielding conclusion.   *)
fun strip_assums_concl (Const("==>", _) $ H $ B) = strip_assums_concl B
  | strip_assums_concl (Const("all",_)$Abs(a,T,t)) = strip_assums_concl t
  | strip_assums_concl B = B;

(*Make a list of all the parameters in a subgoal, even if nested*)
fun strip_params (Const("==>", _) $ H $ B) = strip_params B
  | strip_params (Const("all",_)$Abs(a,T,t)) = (a,T) :: strip_params t
  | strip_params B = [];

(*Removes the parameters from a subgoal and renumber bvars in hypotheses,
    where j is the total number of parameters (precomputed) 
  If n>0 then deletes assumption n. *)
fun remove_params j n A = 
    if j=0 andalso n<=0 then A  (*nothing left to do...*)
    else case A of
        Const("==>", _) $ H $ B => 
	  if n=1 then                           (remove_params j (n-1) B)
	  else implies $ (incr_boundvars j H) $ (remove_params j (n-1) B)
      | Const("all",_)$Abs(a,T,t) => remove_params (j-1) n t
      | _ => if n>0 then raise TERM("remove_params", [A])
             else A;

(** Auto-renaming of parameters in subgoals **)

val auto_rename = ref false
and rename_prefix = ref "ka";

(*rename_prefix is not exported; it is set by this function.*)
fun set_rename_prefix a =
    if a<>"" andalso forall is_letter (explode a)
    then  (rename_prefix := a;  auto_rename := true)
    else  error"rename prefix must be nonempty and consist of letters";

(*Makes parameters in a goal have distinctive names (not guaranteed unique!)
  A name clash could cause the printer to rename bound vars;
    then res_inst_tac would not work properly.*)
fun rename_vars (a, []) = []
  | rename_vars (a, (_,T)::vars) =
        (a,T) :: rename_vars (bump_string a, vars);

(*Move all parameters to the front of the subgoal, renaming them apart;
  if n>0 then deletes assumption n. *)
fun flatten_params n A =
    let val params = strip_params A;
	val vars = if !auto_rename 
		   then rename_vars (!rename_prefix, params)
		   else ListPair.zip (variantlist(map #1 params,[]),
				      map #2 params)
    in  list_all (vars, remove_params (length vars) n A)
    end;

(*Makes parameters in a goal have the names supplied by the list cs.*)
fun list_rename_params (cs, Const("==>", _) $ A $ B) =
      implies $ A $ list_rename_params (cs, B)
  | list_rename_params (c::cs, Const("all",_)$Abs(_,T,t)) = 
      all T $ Abs(c, T, list_rename_params (cs, t))
  | list_rename_params (cs, B) = B;

(*Strips assumptions in goal yielding  ( [Hn,...,H1], [xm,...,x1], B )
  where H1,...,Hn are the hypotheses and x1...xm are the parameters.   *)
fun strip_assums_aux (Hs, params, Const("==>", _) $ H $ B) = 
	strip_assums_aux (H::Hs, params, B)
  | strip_assums_aux (Hs, params, Const("all",_)$Abs(a,T,t)) =
	strip_assums_aux (Hs, (a,T)::params, t)
  | strip_assums_aux (Hs, params, B) = (Hs, params, B);

fun strip_assums A = strip_assums_aux ([],[],A);


(*Produces disagreement pairs, one for each assumption proof, in order.
  A is the first premise of the lifted rule, and thus has the form
    H1 ==> ... Hk ==> B   and the pairs are (H1,B),...,(Hk,B) *)
fun assum_pairs A =
  let val (Hs, params, B) = strip_assums A
      val D = Unify.rlist_abs(params, B)
      fun pairrev ([],pairs) = pairs  
        | pairrev (H::Hs,pairs) = 
	    pairrev(Hs, (Unify.rlist_abs(params,H), D) :: pairs)
  in  pairrev (Hs,[])   (*WAS:  map pair (rev Hs)  *)
  end;


(*Converts Frees to Vars and TFrees to TVars so that axioms can be written
  without (?) everywhere*)
fun varify (Const(a,T)) = Const(a, Type.varifyT T)
  | varify (Free(a,T)) = Var((a,0), Type.varifyT T)
  | varify (Var(ixn,T)) = Var(ixn, Type.varifyT T)
  | varify (Abs (a,T,body)) = Abs (a, Type.varifyT T, varify body)
  | varify (f$t) = varify f $ varify t
  | varify t = t;

(*Inverse of varify.  Converts axioms back to their original form.*)
fun unvarify (Const(a,T))    = Const(a, Type.unvarifyT T)
  | unvarify (Var((a,0), T)) = Free(a, Type.unvarifyT T)
  | unvarify (Var(ixn,T))    = Var(ixn, Type.unvarifyT T)  (*non-0 index!*)
  | unvarify (Abs (a,T,body)) = Abs (a, Type.unvarifyT T, unvarify body)
  | unvarify (f$t) = unvarify f $ unvarify t
  | unvarify t = t;


(*** term order ***)

(* NB: non-linearity of the ordering is not a soundness problem *)

(* FIXME: "***ABSTRACTION***" is a hack and makes the ordering non-linear *)
fun string_of_hd(Const(a,_)) = a
  | string_of_hd(Free(a,_))  = a
  | string_of_hd(Var(v,_))   = Syntax.string_of_vname v
  | string_of_hd(Bound i)    = string_of_int i
  | string_of_hd(Abs _)      = "***ABSTRACTION***";

(* a strict (not reflexive) linear well-founded AC-compatible ordering
 * for terms:
 * s < t <=> 1. size(s) < size(t) or
             2. size(s) = size(t) and s=f(...) and t = g(...) and f<g or
             3. size(s) = size(t) and s=f(s1..sn) and t=f(t1..tn) and
                (s1..sn) < (t1..tn) (lexicographically)
 *)

(* FIXME: should really take types into account as well.
 * Otherwise non-linear *)
fun termord(Abs(_,_,t),Abs(_,_,u)) = termord(t,u)
  | termord(t,u) =
      (case intord(size_of_term t,size_of_term u) of
         EQUAL => let val (f,ts) = strip_comb t and (g,us) = strip_comb u
                  in case stringord(string_of_hd f, string_of_hd g) of
                       EQUAL => lextermord(ts,us)
                     | ord   => ord
                  end
       | ord => ord)
and lextermord(t::ts,u::us) =
      (case termord(t,u) of
         EQUAL => lextermord(ts,us)
       | ord   => ord)
  | lextermord([],[]) = EQUAL
  | lextermord _ = error("lextermord");

fun termless tu = (termord tu = LESS);

(** Check for looping rewrite rules **)

fun vperm (Var _, Var _) = true
  | vperm (Abs (_, _, s), Abs (_, _, t)) = vperm (s, t)
  | vperm (t1 $ t2, u1 $ u2) = vperm (t1, u1) andalso vperm (t2, u2)
  | vperm (t, u) = (t = u);

fun var_perm (t, u) =
  vperm (t, u) andalso eq_set_term (term_vars t, term_vars u);

(*simple test for looping rewrite*)
fun looptest sign prems lhs rhs =
   is_Var (head_of lhs)
  orelse
   (exists (apl (lhs, op occs)) (rhs :: prems))
  orelse
   (null prems andalso
    Pattern.matches (#tsig (Sign.rep_sg sign)) (lhs, rhs));
(*the condition "null prems" in the last case is necessary because
  conditional rewrites with extra variables in the conditions may terminate
  although the rhs is an instance of the lhs. Example:
  ?m < ?n ==> f(?n) == f(?m)*)

fun loops sign prems lhs rhs =
  let
    val elhs = Pattern.eta_contract lhs;
    val erhs = Pattern.eta_contract rhs;
    val perm = var_perm (elhs, erhs) andalso not (elhs aconv erhs)
               andalso not (is_Var elhs)
  in (if not ((term_vars erhs) subset
              (union_term (term_vars elhs, List.concat(map term_vars prems))))
      then Some("extra Var(s) on rhs") else
      if not perm andalso looptest sign prems elhs erhs
      then Some("loops")
      else None
      ,perm)
  end;

end;
