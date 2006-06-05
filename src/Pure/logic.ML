(*  Title:      Pure/logic.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   Cambridge University 1992

Abstract syntax operations of the Pure meta-logic.
*)

signature LOGIC =
sig
  val is_all: term -> bool
  val dest_all: term -> typ * term
  val mk_equals: term * term -> term
  val dest_equals: term -> term * term
  val is_equals: term -> bool
  val mk_implies: term * term -> term
  val dest_implies: term -> term * term
  val is_implies: term -> bool
  val list_implies: term list * term -> term
  val strip_imp_prems: term -> term list
  val strip_imp_concl: term -> term
  val strip_prems: int * term list * term -> term list * term
  val count_prems: term * int -> int
  val nth_prem: int * term -> term
  val conjunction: term
  val mk_conjunction: term * term -> term
  val mk_conjunction_list: term list -> term
  val mk_conjunction_list2: term list list -> term
  val dest_conjunction: term -> term * term
  val dest_conjunction_list: term -> term list
  val dest_conjunctions: term -> term list
  val strip_horn: term -> term list * term
  val dest_type: term -> typ
  val const_of_class: class -> string
  val class_of_const: string -> class
  val mk_inclass: typ * class -> term
  val dest_inclass: term -> typ * class
  val mk_classrel: class * class -> term
  val dest_classrel: term -> class * class
  val mk_arities: string * sort list * sort -> term list
  val dest_arity: term -> string * sort list * class
  val dest_def: Pretty.pp -> (term -> bool) -> (string -> bool) -> (string -> bool) ->
    term -> (term * term) * term
  val abs_def: term -> term * term
  val mk_cond_defpair: term list -> term * term -> string * term
  val mk_defpair: term * term -> string * term
  val mk_type: typ -> term
  val protectC: term
  val protect: term -> term
  val unprotect: term -> term
  val mk_term: term -> term
  val dest_term: term -> term
  val occs: term * term -> bool
  val close_form: term -> term
  val combound: term * int * int -> term
  val rlist_abs: (string * typ) list * term -> term
  val incr_indexes: typ list * int -> term -> term
  val incr_tvar: int -> typ -> typ
  val lift_abs: int -> term -> term -> term
  val lift_all: int -> term -> term -> term
  val strip_assums_hyp: term -> term list
  val strip_assums_concl: term -> term
  val strip_params: term -> (string * typ) list
  val has_meta_prems: term -> int -> bool
  val flatten_params: int -> term -> term
  val auto_rename: bool ref
  val set_rename_prefix: string -> unit
  val list_rename_params: string list * term -> term
  val assum_pairs: int * term -> (term*term)list
  val varify: term -> term
  val unvarify: term -> term
  val get_goal: term -> int -> term
  val goal_params: term -> int -> term * term list
  val prems_of_goal: term -> int -> term list
  val concl_of_goal: term -> int -> term
end;

structure Logic : LOGIC =
struct


(*** Abstract syntax operations on the meta-connectives ***)

(** all **)

fun is_all (Const ("all", _) $ _) = true
  | is_all _ = false;

fun dest_all (Const ("all", Type ("fun", [Type ("fun", [T, _]), _])) $ A) = (T, A)
  | dest_all t = raise TERM ("dest_all", [t]);



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
fun list_implies ([], B) = B
  | list_implies (A::As, B) = implies $ A $ list_implies(As,B);

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

(*Count premises -- quicker than (length o strip_prems) *)
fun count_prems (Const("==>", _) $ A $ B, n) = count_prems (B,n+1)
  | count_prems (_,n) = n;

(*Select Ai from A1 ==>...Ai==>B*)
fun nth_prem (1, Const ("==>", _) $ A $ _) = A
  | nth_prem (i, Const ("==>", _) $ _ $ B) = nth_prem (i - 1, B)
  | nth_prem (_, A) = raise TERM ("nth_prem", [A]);

(*strip a proof state (Horn clause):
  B1 ==> ... Bn ==> C   goes to   ([B1, ..., Bn], C)    *)
fun strip_horn A = (strip_imp_prems A, strip_imp_concl A);


(** conjunction **)

val conjunction = Const ("ProtoPure.conjunction", propT --> propT --> propT);

(*A && B*)
fun mk_conjunction (A, B) = conjunction $ A $ B;

(*A && B && C -- improper*)
fun mk_conjunction_list [] = Term.all propT $ Abs ("dummy", propT, mk_implies (Bound 0, Bound 0))
  | mk_conjunction_list ts = foldr1 mk_conjunction ts;

(*(A1 && B1 && C1) && (A2 && B2 && C2 && D2) && A3 && B3 -- improper*)
fun mk_conjunction_list2 tss =
  mk_conjunction_list (map mk_conjunction_list (filter_out null tss));

(*A && B*)
fun dest_conjunction (Const ("ProtoPure.conjunction", _) $ A $ B) = (A, B)
  | dest_conjunction t = raise TERM ("dest_conjunction", [t]);

(*A && B && C -- improper*)
fun dest_conjunction_list t =
  (case try dest_conjunction t of
    NONE => [t]
  | SOME (A, B) => A :: dest_conjunction_list B);

(*((A && B) && C) && D && E -- flat*)
fun dest_conjunctions t =
  (case try dest_conjunction t of
    NONE => [t]
  | SOME (A, B) => dest_conjunctions A @ dest_conjunctions B);



(** types as terms **)

fun mk_type ty = Const ("TYPE", Term.itselfT ty);

fun dest_type (Const ("TYPE", Type ("itself", [ty]))) = ty
  | dest_type t = raise TERM ("dest_type", [t]);



(** type classes **)

(* const names *)

val classN = "_class";

val const_of_class = suffix classN;

fun class_of_const c = unsuffix classN c
  handle Fail _ => raise TERM ("class_of_const: bad name " ^ quote c, []);


(* class constraints *)

fun mk_inclass (ty, c) =
  Const (const_of_class c, Term.itselfT ty --> propT) $ mk_type ty;

fun dest_inclass (t as Const (c_class, _) $ ty) = (dest_type ty, class_of_const c_class)
  | dest_inclass t = raise TERM ("dest_inclass", [t]);


(* class relations *)

fun mk_classrel (c1, c2) = mk_inclass (Term.aT [c1], c2);

fun dest_classrel tm =
  (case dest_inclass tm of
    (TVar (_, [c1]), c2) => (c1, c2)
  | _ => raise TERM ("dest_classrel", [tm]));


(* type arities *)

fun mk_arities (t, Ss, S) =
  let val T = Type (t, ListPair.map TFree (Term.invent_names [] "'a" (length Ss), Ss))
  in map (fn c => mk_inclass (T, c)) S end;

fun dest_arity tm =
  let
    fun err () = raise TERM ("dest_arity", [tm]);

    val (ty, c) = dest_inclass tm;
    val (t, tvars) =
      (case ty of
        Type (t, tys) => (t, map dest_TVar tys handle TYPE _ => err ())
      | _ => err ());
    val Ss =
      if has_duplicates (eq_fst (op =)) tvars then err ()
      else map snd tvars;
  in (t, Ss, c) end;



(** definitions **)

fun term_kind (Const _) = "existing constant "
  | term_kind (Free _) = "free variable "
  | term_kind (Bound _) = "bound variable "
  | term_kind _ = "";

(*c x == t[x] to !!x. c x == t[x]*)
fun dest_def pp check_head is_fixed is_fixedT eq =
  let
    fun err msg = raise TERM (msg, [eq]);
    val eq_vars = Term.strip_all_vars eq;
    val eq_body = Term.strip_all_body eq;

    val display_terms = commas_quote o map (Pretty.string_of_term pp o Syntax.bound_vars eq_vars);
    val display_types = commas_quote o map (Pretty.string_of_typ pp);

    val (raw_lhs, rhs) = dest_equals eq_body handle TERM _ => err "Not a meta-equality (==)";
    val lhs = Envir.beta_eta_contract raw_lhs;
    val (head, args) = Term.strip_comb lhs;
    val head_tfrees = Term.add_tfrees head [];

    fun check_arg (Bound _) = true
      | check_arg (Free (x, _)) = not (is_fixed x)
      | check_arg (Const ("TYPE", Type ("itself", [TFree _]))) = true
      | check_arg _ = false;
    fun close_arg (Bound _) t = t
      | close_arg x t = Term.all (Term.fastype_of x) $ lambda x t;

    val lhs_bads = filter_out check_arg args;
    val lhs_dups = duplicates (op aconv) args;
    val rhs_extras = Term.fold_aterms (fn v as Free (x, _) =>
      if is_fixed x orelse member (op aconv) args v then I
      else insert (op aconv) v | _ => I) rhs [];
    val rhs_extrasT = Term.fold_aterms (Term.fold_types (fn v as TFree (a, S) =>
      if is_fixedT a orelse member (op =) head_tfrees (a, S) then I
      else insert (op =) v | _ => I)) rhs [];
  in
    if not (check_head head) then
      err ("Bad head of lhs: " ^ term_kind head ^ display_terms [head])
    else if not (null lhs_bads) then
      err ("Bad arguments on lhs: " ^ display_terms lhs_bads)
    else if not (null lhs_dups) then
      err ("Duplicate arguments on lhs: " ^ display_terms lhs_dups)
    else if not (null rhs_extras) then
      err ("Extra variables on rhs: " ^ display_terms rhs_extras)
    else if not (null rhs_extrasT) then
      err ("Extra type variables on rhs: " ^ display_types rhs_extrasT)
    else if exists_subterm (fn t => t aconv head) rhs then
      err "Entity to be defined occurs on rhs"
    else ((lhs, rhs), fold_rev close_arg args (Term.list_all (eq_vars, (mk_equals (lhs, rhs)))))
  end;

(*!!x. c x == t[x] to c == %x. t[x]*)
fun abs_def eq =
  let
    val body = Term.strip_all_body eq;
    val vars = map Free (Term.rename_wrt_term body (Term.strip_all_vars eq));
    val (lhs, rhs) = dest_equals (Term.subst_bounds (vars, body));
    val (lhs', args) = Term.strip_comb lhs;
    val rhs' = Term.list_abs_free (map Term.dest_Free args, rhs);
  in (lhs', rhs') end;

fun mk_cond_defpair As (lhs, rhs) =
  (case Term.head_of lhs of
    Const (name, _) =>
      (NameSpace.base name ^ "_def", list_implies (As, mk_equals (lhs, rhs)))
  | _ => raise TERM ("Malformed definition: head of lhs not a constant", [lhs, rhs]));

fun mk_defpair lhs_rhs = mk_cond_defpair [] lhs_rhs;



(** protected propositions and embedded terms **)

val protectC = Const ("prop", propT --> propT);
fun protect t = protectC $ t;

fun unprotect (Const ("prop", _) $ t) = t
  | unprotect t = raise TERM ("unprotect", [t]);


fun mk_term t = Const ("ProtoPure.term", Term.fastype_of t --> propT) $ t;

fun dest_term (Const ("ProtoPure.term", _) $ t) = t
  | dest_term t = raise TERM ("dest_term", [t]);



(*** Low-level term operations ***)

(*Does t occur in u?  Or is alpha-convertible to u?
  The term t must contain no loose bound variables*)
fun occs (t, u) = exists_subterm (fn s => t aconv s) u;

(*Close up a formula over all free variables by quantification*)
fun close_form A =
  Term.list_all_free (rev (Term.add_frees A []), A);



(*** Specialized operations for resolution... ***)

(*computes t(Bound(n+k-1),...,Bound(n))  *)
fun combound (t, n, k) =
    if  k>0  then  combound (t,n+1,k-1) $ (Bound n)  else  t;

(* ([xn,...,x1], t)   ======>   (x1,...,xn)t *)
fun rlist_abs ([], body) = body
  | rlist_abs ((a,T)::pairs, body) = rlist_abs(pairs, Abs(a, T, body));


local exception SAME in

fun incrT k =
  let
    fun incr (TVar ((a, i), S)) = TVar ((a, i + k), S)
      | incr (Type (a, Ts)) = Type (a, incrs Ts)
      | incr _ = raise SAME
    and incrs (T :: Ts) =
        (incr T :: (incrs Ts handle SAME => Ts)
          handle SAME => T :: incrs Ts)
      | incrs [] = raise SAME;
  in incr end;

(*For all variables in the term, increment indexnames and lift over the Us
    result is ?Gidx(B.(lev+n-1),...,B.lev) where lev is abstraction level *)
fun incr_indexes ([], 0) t = t
  | incr_indexes (Ts, k) t =
  let
    val n = length Ts;
    val incrT = if k = 0 then I else incrT k;

    fun incr lev (Var ((x, i), T)) =
          combound (Var ((x, i + k), Ts ---> (incrT T handle SAME => T)), lev, n)
      | incr lev (Abs (x, T, body)) =
          (Abs (x, incrT T, incr (lev + 1) body handle SAME => body)
            handle SAME => Abs (x, T, incr (lev + 1) body))
      | incr lev (t $ u) =
          (incr lev t $ (incr lev u handle SAME => u)
            handle SAME => t $ incr lev u)
      | incr _ (Const (c, T)) = Const (c, incrT T)
      | incr _ (Free (x, T)) = Free (x, incrT T)
      | incr _ (t as Bound _) = t;
  in incr 0 t handle SAME => t end;

fun incr_tvar 0 T = T
  | incr_tvar k T = incrT k T handle SAME => T;

end;


(* Lifting functions from subgoal and increment:
    lift_abs operates on terms
    lift_all operates on propositions *)

fun lift_abs inc =
  let
    fun lift Ts (Const ("==>", _) $ _ $ B) t = lift Ts B t
      | lift Ts (Const ("all", _) $ Abs (a, T, B)) t = Abs (a, T, lift (T :: Ts) B t)
      | lift Ts _ t = incr_indexes (rev Ts, inc) t;
  in lift [] end;

fun lift_all inc =
  let
    fun lift Ts ((c as Const ("==>", _)) $ A $ B) t = c $ A $ lift Ts B t
      | lift Ts ((c as Const ("all", _)) $ Abs (a, T, B)) t = c $ Abs (a, T, lift (T :: Ts) B t)
      | lift Ts _ t = incr_indexes (rev Ts, inc) t;
  in lift [] end;

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

(*** Treatmsent of "assume", "erule", etc. ***)

(*Strips assumptions in goal yielding
   HS = [Hn,...,H1],   params = [xm,...,x1], and B,
  where x1...xm are the parameters. This version (21.1.2005) REQUIRES
  the the parameters to be flattened, but it allows erule to work on
  assumptions of the form !!x. phi. Any !! after the outermost string
  will be regarded as belonging to the conclusion, and left untouched.
  Used ONLY by assum_pairs.
      Unless nasms<0, it can terminate the recursion early; that allows
  erule to work on assumptions of the form P==>Q.*)
fun strip_assums_imp (0, Hs, B) = (Hs, B)  (*recursion terminated by nasms*)
  | strip_assums_imp (nasms, Hs, Const("==>", _) $ H $ B) =
      strip_assums_imp (nasms-1, H::Hs, B)
  | strip_assums_imp (_, Hs, B) = (Hs, B); (*recursion terminated by B*)


(*Strips OUTER parameters only, unlike similar legacy versions.*)
fun strip_assums_all (params, Const("all",_)$Abs(a,T,t)) =
      strip_assums_all ((a,T)::params, t)
  | strip_assums_all (params, B) = (params, B);

(*Produces disagreement pairs, one for each assumption proof, in order.
  A is the first premise of the lifted rule, and thus has the form
    H1 ==> ... Hk ==> B   and the pairs are (H1,B),...,(Hk,B).
  nasms is the number of assumptions in the original subgoal, needed when B
    has the form B1 ==> B2: it stops B1 from being taken as an assumption. *)
fun assum_pairs(nasms,A) =
  let val (params, A') = strip_assums_all ([],A)
      val (Hs,B) = strip_assums_imp (nasms,[],A')
      fun abspar t = rlist_abs(params, t)
      val D = abspar B
      fun pairrev ([], pairs) = pairs
        | pairrev (H::Hs, pairs) = pairrev(Hs,  (abspar H, D) :: pairs)
  in  pairrev (Hs,[])
  end;

(*Converts Frees to Vars and TFrees to TVars*)
fun varify (Const(a, T)) = Const (a, Type.varifyT T)
  | varify (Free (a, T)) = Var ((a, 0), Type.varifyT T)
  | varify (Var (ixn, T)) = Var (ixn, Type.varifyT T)
  | varify (t as Bound _) = t
  | varify (Abs (a, T, body)) = Abs (a, Type.varifyT T, varify body)
  | varify (f $ t) = varify f $ varify t;

(*Inverse of varify.*)
fun unvarify (Const (a, T)) = Const (a, Type.unvarifyT T)
  | unvarify (Free (a, T)) = Free (a, Type.unvarifyT T)
  | unvarify (Var ((a, 0), T)) = Free (a, Type.unvarifyT T)
  | unvarify (Var (ixn, T)) = Var (ixn, Type.unvarifyT T)  (*non-0 index!*)
  | unvarify (t as Bound _) = t
  | unvarify (Abs (a, T, body)) = Abs (a, Type.unvarifyT T, unvarify body)
  | unvarify (f $ t) = unvarify f $ unvarify t;


(* goal states *)

fun get_goal st i = nth_prem (i, st)
  handle TERM _ => error "Goal number out of range";

(*reverses parameters for substitution*)
fun goal_params st i =
  let val gi = get_goal st i
      val rfrees = map Free (rename_wrt_term gi (strip_params gi))
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
