(*  Title:      Pure/logic.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   Cambridge University 1992

Abstract syntax operations of the Pure meta-logic.
*)

infix occs;

signature LOGIC =
sig
  val is_all            : term -> bool
  val mk_equals         : term * term -> term
  val dest_equals       : term -> term * term
  val is_equals         : term -> bool
  val mk_implies        : term * term -> term
  val dest_implies      : term -> term * term
  val is_implies        : term -> bool
  val list_implies      : term list * term -> term
  val strip_imp_prems   : term -> term list
  val strip_imp_concl   : term -> term
  val strip_prems       : int * term list * term -> term list * term
  val count_prems       : term * int -> int
  val mk_conjunction    : term * term -> term
  val mk_conjunction_list: term list -> term
  val strip_horn        : term -> term list * term
  val mk_cond_defpair   : term list -> term * term -> string * term
  val mk_defpair        : term * term -> string * term
  val mk_type           : typ -> term
  val dest_type         : term -> typ
  val mk_inclass        : typ * class -> term
  val dest_inclass      : term -> typ * class
  val goal_const        : term
  val mk_goal           : term -> term
  val dest_goal         : term -> term
  val occs              : term * term -> bool
  val close_form        : term -> term
  val incr_indexes      : typ list * int -> term -> term
  val lift_fns          : term * int -> (term -> term) * (term -> term)
  val strip_assums_hyp  : term -> term list
  val strip_assums_concl: term -> term
  val strip_params      : term -> (string * typ) list
  val has_meta_prems    : term -> int -> bool
  val flatten_params    : int -> term -> term
  val auto_rename       : bool ref
  val set_rename_prefix : string -> unit
  val list_rename_params: string list * term -> term
  val assum_pairs       : term -> (term*term)list
  val varify            : term -> term
  val unvarify          : term -> term
  val get_goal          : term -> int -> term
  val prems_of_goal     : term -> int -> term list
  val concl_of_goal     : term -> int -> term
end;

structure Logic : LOGIC =
struct


(*** Abstract syntax operations on the meta-connectives ***)

(** all **)

fun is_all (Const ("all", _) $ _) = true
  | is_all _ = false;


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

fun is_implies (Const ("==>", _) $ _ $ _) = true
  | is_implies _ = false;


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
    goes to   ([Ai, A(i-1),...,A1] , B)         (REVERSED)
  if  i<0 or else i too big then raises  TERM*)
fun strip_prems (0, As, B) = (As, B)
  | strip_prems (i, As, Const("==>", _) $ A $ B) =
        strip_prems (i-1, A::As, B)
  | strip_prems (_, As, A) = raise TERM("strip_prems", A::As);

(*Count premises -- quicker than (length ostrip_prems) *)
fun count_prems (Const("==>", _) $ A $ B, n) = count_prems (B,n+1)
  | count_prems (_,n) = n;

(*strip a proof state (Horn clause):
  B1 ==> ... Bn ==> C   goes to   ([B1, ..., Bn], C)    *)
fun strip_horn A = (strip_imp_prems A, strip_imp_concl A);


(** conjunction **)

fun mk_conjunction (t, u) =
  Term.list_all ([("C", propT)], mk_implies (list_implies ([t, u], Bound 0), Bound 0));

fun mk_conjunction_list [] = Term.all propT $ Abs ("dummy", propT, mk_implies (Bound 0, Bound 0))
  | mk_conjunction_list ts = foldr1 mk_conjunction ts;


(** definitions **)

fun mk_cond_defpair As (lhs, rhs) =
  (case Term.head_of lhs of
    Const (name, _) =>
      (Sign.base_name name ^ "_def", list_implies (As, mk_equals (lhs, rhs)))
  | _ => raise TERM ("Malformed definition: head of lhs not a constant", [lhs, rhs]));

fun mk_defpair lhs_rhs = mk_cond_defpair [] lhs_rhs;


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


(** atomic goals **)

val goal_const = Const ("Goal", propT --> propT);
fun mk_goal t = goal_const $ t;

fun dest_goal (Const ("Goal", _) $ t) = t
  | dest_goal t = raise TERM ("dest_goal", [t]);


(*** Low-level term operations ***)

(*Does t occur in u?  Or is alpha-convertible to u?
  The term t must contain no loose bound variables*)
fun t occs u = exists_subterm (fn s => t aconv s) u;

(*Close up a formula over all free variables by quantification*)
fun close_form A =
  list_all_free (sort_wrt fst (map dest_Free (term_frees A)), A);


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

(*test for meta connectives in prems of a 'subgoal'*)
fun has_meta_prems prop i =
  let
    fun is_meta (Const ("==>", _) $ _ $ _) = true
      | is_meta (Const ("==", _) $ _ $ _) = true
      | is_meta (Const ("all", _) $ _) = true
      | is_meta _ = false;
  in
    (case strip_prems (i, [], prop) of
      (B :: _, _) => exists is_meta (strip_assums_hyp B)
    | _ => false) handle TERM _ => false
  end;

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
    if a<>"" andalso forall Symbol.is_letter (Symbol.explode a)
    then  (rename_prefix := a;  auto_rename := true)
    else  error"rename prefix must be nonempty and consist of letters";

(*Makes parameters in a goal have distinctive names (not guaranteed unique!)
  A name clash could cause the printer to rename bound vars;
    then res_inst_tac would not work properly.*)
fun rename_vars (a, []) = []
  | rename_vars (a, (_,T)::vars) =
        (a,T) :: rename_vars (Symbol.bump_string a, vars);

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

(*Strips assumptions in goal yielding  ( [HPn,...,HP1], [xm,...,x1], B ).
  Where HPi has the form (Hi,nparams_i) and x1...xm are the parameters.
  We need nparams_i only when the parameters aren't flattened; then we
    must call incr_boundvars to make up the difference.  See assum_pairs.
  Without this refinement we can get the wrong answer, e.g. by
        Goal "!!f. EX B. Q(f,B) ==> (!!y. P(f,y))";
        by (etac exE 1);
 *)
fun strip_assums_aux (HPs, params, Const("==>", _) $ H $ B) =
        strip_assums_aux ((H,length params)::HPs, params, B)
  | strip_assums_aux (HPs, params, Const("all",_)$Abs(a,T,t)) =
        strip_assums_aux (HPs, (a,T)::params, t)
  | strip_assums_aux (HPs, params, B) = (HPs, params, B);

fun strip_assums A = strip_assums_aux ([],[],A);


(*Produces disagreement pairs, one for each assumption proof, in order.
  A is the first premise of the lifted rule, and thus has the form
    H1 ==> ... Hk ==> B   and the pairs are (H1,B),...,(Hk,B) *)
fun assum_pairs A =
  let val (HPs, params, B) = strip_assums A
      val nparams = length params
      val D = Unify.rlist_abs(params, B)
      fun incr_hyp(H,np) =
          Unify.rlist_abs(params, incr_boundvars (nparams-np) H)
      fun pairrev ([],pairs) = pairs
        | pairrev ((H,np)::HPs, pairs) =
            pairrev(HPs,  (incr_hyp(H,np),D) :: pairs)
  in  pairrev (HPs,[])
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


(*Get subgoal i*)
fun get_goal st i = List.nth (strip_imp_prems st, i-1)
  handle Subscript => error "get_goal: Goal number out of range";

(*reverses parameters for substitution*)
fun goal_params st i =
  let val gi = get_goal st i
      val rfrees = rev (map Free (rename_wrt_term gi (strip_params gi)))
  in (gi, rfrees) end;

fun concl_of_goal st i =
  let val (gi, rfrees) = goal_params st i
      val B = strip_assums_concl gi
  in subst_bounds (rfrees, B) end;

fun prems_of_goal st i =
  let val (gi, rfrees) = goal_params st i
      val As = strip_assums_hyp gi
  in map (fn A => subst_bounds (rfrees, A)) As end;

end;
