(*  Title:      HOL/Library/old_recdef.ML
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Author:     Lucas Dixon, University of Edinburgh

Old TFL/recdef package.
*)

signature CASE_SPLIT =
sig
  (* try to recursively split conjectured thm to given list of thms *)
  val splitto : Proof.context -> thm list -> thm -> thm
end;

signature UTILS =
sig
  exception ERR of {module: string, func: string, mesg: string}
  val end_itlist: ('a -> 'a -> 'a) -> 'a list -> 'a
  val itlist2: ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val pluck: ('a -> bool) -> 'a list -> 'a * 'a list
  val zip3: 'a list -> 'b list -> 'c list -> ('a*'b*'c) list
  val take: ('a -> 'b) -> int * 'a list -> 'b list
end;

signature USYNTAX =
sig
  datatype lambda = VAR   of {Name : string, Ty : typ}
                  | CONST of {Name : string, Ty : typ}
                  | COMB  of {Rator: term, Rand : term}
                  | LAMB  of {Bvar : term, Body : term}

  val alpha : typ

  (* Types *)
  val type_vars  : typ -> typ list
  val type_varsl : typ list -> typ list
  val mk_vartype : string -> typ
  val is_vartype : typ -> bool
  val strip_prod_type : typ -> typ list

  (* Terms *)
  val free_vars_lr : term -> term list
  val type_vars_in_term : term -> typ list
  val dest_term  : term -> lambda

  (* Prelogic *)
  val inst      : (typ*typ) list -> term -> term

  (* Construction routines *)
  val mk_abs    :{Bvar  : term, Body : term} -> term

  val mk_imp    :{ant : term, conseq :  term} -> term
  val mk_select :{Bvar : term, Body : term} -> term
  val mk_forall :{Bvar : term, Body : term} -> term
  val mk_exists :{Bvar : term, Body : term} -> term
  val mk_conj   :{conj1 : term, conj2 : term} -> term
  val mk_disj   :{disj1 : term, disj2 : term} -> term
  val mk_pabs   :{varstruct : term, body : term} -> term

  (* Destruction routines *)
  val dest_const: term -> {Name : string, Ty : typ}
  val dest_comb : term -> {Rator : term, Rand : term}
  val dest_abs  : string list -> term -> {Bvar : term, Body : term} * string list
  val dest_eq     : term -> {lhs : term, rhs : term}
  val dest_imp    : term -> {ant : term, conseq : term}
  val dest_forall : term -> {Bvar : term, Body : term}
  val dest_exists : term -> {Bvar : term, Body : term}
  val dest_neg    : term -> term
  val dest_conj   : term -> {conj1 : term, conj2 : term}
  val dest_disj   : term -> {disj1 : term, disj2 : term}
  val dest_pair   : term -> {fst : term, snd : term}
  val dest_pabs   : string list -> term -> {varstruct : term, body : term, used : string list}

  val lhs   : term -> term
  val rhs   : term -> term
  val rand  : term -> term

  (* Query routines *)
  val is_imp    : term -> bool
  val is_forall : term -> bool
  val is_exists : term -> bool
  val is_neg    : term -> bool
  val is_conj   : term -> bool
  val is_disj   : term -> bool
  val is_pair   : term -> bool
  val is_pabs   : term -> bool

  (* Construction of a term from a list of Preterms *)
  val list_mk_abs    : (term list * term) -> term
  val list_mk_imp    : (term list * term) -> term
  val list_mk_forall : (term list * term) -> term
  val list_mk_conj   : term list -> term

  (* Destructing a term to a list of Preterms *)
  val strip_comb     : term -> (term * term list)
  val strip_abs      : term -> (term list * term)
  val strip_imp      : term -> (term list * term)
  val strip_forall   : term -> (term list * term)
  val strip_exists   : term -> (term list * term)
  val strip_disj     : term -> term list

  (* Miscellaneous *)
  val mk_vstruct : typ -> term list -> term
  val gen_all    : term -> term
  val find_term  : (term -> bool) -> term -> term option
  val dest_relation : term -> term * term * term
  val is_WFR : term -> bool
  val ARB : typ -> term
end;

signature DCTERM =
sig
  val dest_comb: cterm -> cterm * cterm
  val dest_abs: cterm -> cterm * cterm
  val capply: cterm -> cterm -> cterm
  val cabs: cterm -> cterm -> cterm
  val mk_conj: cterm * cterm -> cterm
  val mk_disj: cterm * cterm -> cterm
  val mk_exists: cterm * cterm -> cterm
  val dest_conj: cterm -> cterm * cterm
  val dest_const: cterm -> {Name: string, Ty: typ}
  val dest_disj: cterm -> cterm * cterm
  val dest_eq: cterm -> cterm * cterm
  val dest_exists: cterm -> cterm * cterm
  val dest_forall: cterm -> cterm * cterm
  val dest_imp: cterm -> cterm * cterm
  val dest_neg: cterm -> cterm
  val dest_pair: cterm -> cterm * cterm
  val dest_var: cterm -> {Name:string, Ty:typ}
  val is_conj: cterm -> bool
  val is_disj: cterm -> bool
  val is_eq: cterm -> bool
  val is_exists: cterm -> bool
  val is_forall: cterm -> bool
  val is_imp: cterm -> bool
  val is_neg: cterm -> bool
  val is_pair: cterm -> bool
  val list_mk_disj: cterm list -> cterm
  val strip_abs: cterm -> cterm list * cterm
  val strip_comb: cterm -> cterm * cterm list
  val strip_disj: cterm -> cterm list
  val strip_exists: cterm -> cterm list * cterm
  val strip_forall: cterm -> cterm list * cterm
  val strip_imp: cterm -> cterm list * cterm
  val drop_prop: cterm -> cterm
  val mk_prop: cterm -> cterm
end;

signature RULES =
sig
  val dest_thm: thm -> term list * term

  (* Inference rules *)
  val REFL: cterm -> thm
  val ASSUME: cterm -> thm
  val MP: thm -> thm -> thm
  val MATCH_MP: thm -> thm -> thm
  val CONJUNCT1: thm -> thm
  val CONJUNCT2: thm -> thm
  val CONJUNCTS: thm -> thm list
  val DISCH: cterm -> thm -> thm
  val UNDISCH: thm  -> thm
  val SPEC: cterm -> thm -> thm
  val ISPEC: cterm -> thm -> thm
  val ISPECL: cterm list -> thm -> thm
  val GEN: Proof.context -> cterm -> thm -> thm
  val GENL: Proof.context -> cterm list -> thm -> thm
  val LIST_CONJ: thm list -> thm

  val SYM: thm -> thm
  val DISCH_ALL: thm -> thm
  val FILTER_DISCH_ALL: (term -> bool) -> thm -> thm
  val SPEC_ALL: thm -> thm
  val GEN_ALL: Proof.context -> thm -> thm
  val IMP_TRANS: thm -> thm -> thm
  val PROVE_HYP: thm -> thm -> thm

  val CHOOSE: Proof.context -> cterm * thm -> thm -> thm
  val EXISTS: Proof.context -> cterm * cterm -> thm -> thm
  val IT_EXISTS: Proof.context -> (cterm * cterm) list -> thm -> thm

  val EVEN_ORS: thm list -> thm list
  val DISJ_CASESL: thm -> thm list -> thm

  val list_beta_conv: cterm -> cterm list -> thm
  val SUBS: Proof.context -> thm list -> thm -> thm
  val simpl_conv: Proof.context -> thm list -> cterm -> thm

  val rbeta: thm -> thm
  val tracing: bool Unsynchronized.ref
  val CONTEXT_REWRITE_RULE: Proof.context ->
    term * term list * thm * thm list -> thm -> thm * term list
  val RIGHT_ASSOC: Proof.context -> thm -> thm

  val prove: Proof.context -> bool -> term * tactic -> thm
end;

signature THRY =
sig
  val match_term: theory -> term -> term -> (term * term) list * (typ * typ) list
  val match_type: theory -> typ -> typ -> (typ * typ) list
  val typecheck: theory -> term -> cterm
  (*datatype facts of various flavours*)
  val match_info: theory -> string -> {constructors: term list, case_const: term} option
  val induct_info: theory -> string -> {constructors: term list, nchotomy: thm} option
  val extract_info: theory -> {case_congs: thm list, case_rewrites: thm list}
end;

signature PRIM =
sig
  val trace: bool Unsynchronized.ref
  val trace_thms: Proof.context -> string -> thm list -> unit
  val trace_cterm: Proof.context -> string -> cterm -> unit
  type pattern
  val mk_functional: theory -> term list -> {functional: term, pats: pattern list}
  val wfrec_definition0: string -> term -> term -> theory -> thm * theory
  val post_definition: Proof.context -> thm list -> thm * pattern list ->
   {rules: thm,
    rows: int list,
    TCs: term list list,
    full_pats_TCs: (term * term list) list}
  val mk_induction: Proof.context ->
    {fconst: term, R: term, SV: term list, pat_TCs_list: (term * term list) list} -> thm
  val postprocess: Proof.context -> bool ->
    {wf_tac: tactic, terminator: tactic, simplifier: cterm -> thm} ->
    {rules: thm, induction: thm, TCs: term list list} ->
    {rules: thm, induction: thm, nested_tcs: thm list}
end;

signature TFL =
sig
  val define_i: bool -> thm list -> thm list -> xstring -> term -> term list -> Proof.context ->
    {lhs: term, rules: (thm * int) list, induct: thm, tcs: term list} * Proof.context
  val define: bool -> thm list -> thm list -> xstring -> string -> string list -> Proof.context ->
    {lhs: term, rules: (thm * int) list, induct: thm, tcs: term list} * Proof.context
end;

signature OLD_RECDEF =
sig
  val get_recdef: theory -> string
    -> {lhs: term, simps: thm list, rules: thm list list, induct: thm, tcs: term list} option
  val get_hints: Proof.context -> {simps: thm list, congs: (string * thm) list, wfs: thm list}
  val simp_add: attribute
  val simp_del: attribute
  val cong_add: attribute
  val cong_del: attribute
  val wf_add: attribute
  val wf_del: attribute
  val add_recdef: bool -> xstring -> string -> ((binding * string) * Token.src list) list ->
    Token.src option -> theory -> theory
      * {lhs: term, simps: thm list, rules: thm list list, induct: thm, tcs: term list}
  val add_recdef_i: bool -> xstring -> term -> ((binding * term) * attribute list) list ->
    theory -> theory * {lhs: term, simps: thm list, rules: thm list list, induct: thm, tcs: term list}
end;

structure Old_Recdef: OLD_RECDEF =
struct

(*** extra case splitting for TFL ***)

structure CaseSplit: CASE_SPLIT =
struct

(* make a casethm from an induction thm *)
fun cases_thm_of_induct_thm ctxt =
  Seq.hd o (ALLGOALS (fn i => REPEAT (eresolve_tac ctxt [Drule.thin_rl] i)));

(* get the case_thm (my version) from a type *)
fun case_thm_of_ty ctxt ty  =
    let
      val thy = Proof_Context.theory_of ctxt
      val ty_str = case ty of
                     Type(ty_str, _) => ty_str
                   | TFree(s,_)  => error ("Free type: " ^ s)
                   | TVar((s,_),_) => error ("Free variable: " ^ s)
      val {induct, ...} = BNF_LFP_Compat.the_info thy [BNF_LFP_Compat.Keep_Nesting] ty_str
    in
      cases_thm_of_induct_thm ctxt induct
    end;


(* for use when there are no prems to the subgoal *)
(* does a case split on the given variable *)
fun mk_casesplit_goal_thm ctxt (vstr,ty) gt =
    let
      val thy = Proof_Context.theory_of ctxt;

      val x = Free(vstr,ty);
      val abst = Abs(vstr, ty, Term.abstract_over (x, gt));

      val case_thm = case_thm_of_ty ctxt ty;

      val abs_ct = Thm.cterm_of ctxt abst;
      val free_ct = Thm.cterm_of ctxt x;

      val (Pv, Dv, type_insts) =
          case (Thm.concl_of case_thm) of
            (_ $ (Pv $ (Dv as Var(_, Dty)))) =>
            (Pv, Dv,
             Sign.typ_match thy (Dty, ty) Vartab.empty)
          | _ => error "not a valid case thm";
      val type_cinsts = map (fn (ixn, (S, T)) => ((ixn, S), Thm.ctyp_of ctxt T))
        (Vartab.dest type_insts);
      val Pv = dest_Var (Envir.subst_term_types type_insts Pv);
      val Dv = dest_Var (Envir.subst_term_types type_insts Dv);
    in
      Conv.fconv_rule Drule.beta_eta_conversion
         (case_thm
            |> Thm.instantiate (TVars.make type_cinsts, Vars.empty)
            |> Thm.instantiate (TVars.empty, Vars.make [(Pv, abs_ct), (Dv, free_ct)]))
    end;


(* the find_XXX_split functions are simply doing a lightwieght (I
think) term matching equivalent to find where to do the next split *)

(* assuming two twems are identical except for a free in one at a
subterm, or constant in another, ie assume that one term is a plit of
another, then gives back the free variable that has been split. *)
exception find_split_exp of string
fun find_term_split (Free v, _ $ _) = SOME v
  | find_term_split (Free v, Const _) = SOME v
  | find_term_split (Free v, Abs _) = SOME v (* do we really want this case? *)
  | find_term_split (Free _, Var _) = NONE (* keep searching *)
  | find_term_split (a $ b, a2 $ b2) =
    (case find_term_split (a, a2) of
       NONE => find_term_split (b,b2)
     | vopt => vopt)
  | find_term_split (Abs(_,_,t1), Abs(_,_,t2)) =
    find_term_split (t1, t2)
  | find_term_split (Const (x,_), Const(x2,_)) =
    if x = x2 then NONE else (* keep searching *)
    raise find_split_exp (* stop now *)
            "Terms are not identical upto a free varaible! (Consts)"
  | find_term_split (Bound i, Bound j) =
    if i = j then NONE else (* keep searching *)
    raise find_split_exp (* stop now *)
            "Terms are not identical upto a free varaible! (Bound)"
  | find_term_split _ =
    raise find_split_exp (* stop now *)
            "Terms are not identical upto a free varaible! (Other)";

(* assume that "splitth" is a case split form of subgoal i of "genth",
then look for a free variable to split, breaking the subgoal closer to
splitth. *)
fun find_thm_split splitth i genth =
    find_term_split (Logic.get_goal (Thm.prop_of genth) i,
                     Thm.concl_of splitth) handle find_split_exp _ => NONE;

(* as above but searches "splitths" for a theorem that suggest a case split *)
fun find_thms_split splitths i genth =
    Library.get_first (fn sth => find_thm_split sth i genth) splitths;


(* split the subgoal i of "genth" until we get to a member of
splitths. Assumes that genth will be a general form of splitths, that
can be case-split, as needed. Otherwise fails. Note: We assume that
all of "splitths" are split to the same level, and thus it doesn't
matter which one we choose to look for the next split. Simply add
search on splitthms and split variable, to change this.  *)
(* Note: possible efficiency measure: when a case theorem is no longer
useful, drop it? *)
(* Note: This should not be a separate tactic but integrated into the
case split done during recdef's case analysis, this would avoid us
having to (re)search for variables to split. *)
fun splitto ctxt splitths genth =
    let
      val _ = not (null splitths) orelse error "splitto: no given splitths";

      (* check if we are a member of splitths - FIXME: quicker and
      more flexible with discrim net. *)
      fun solve_by_splitth th split =
        Thm.biresolution (SOME ctxt) false [(false,split)] 1 th;

      fun split th =
        (case find_thms_split splitths 1 th of
          NONE =>
           (writeln (cat_lines
            (["th:", Thm.string_of_thm ctxt th, "split ths:"] @
              map (Thm.string_of_thm ctxt) splitths @ ["\n--"]));
            error "splitto: cannot find variable to split on")
        | SOME v =>
            let
              val gt = HOLogic.dest_Trueprop (#1 (Logic.dest_implies (Thm.prop_of th)));
              val split_thm = mk_casesplit_goal_thm ctxt v gt;
              val (subthms, expf) = IsaND.fixed_subgoal_thms ctxt split_thm;
            in
              expf (map recsplitf subthms)
            end)

      and recsplitf th =
        (* note: multiple unifiers! we only take the first element,
           probably fine -- there is probably only one anyway. *)
        (case get_first (Seq.pull o solve_by_splitth th) splitths of
          NONE => split th
        | SOME (solved_th, _) => solved_th);
    in
      recsplitf genth
    end;

end;



(*** basic utilities ***)

structure Utils: UTILS =
struct

(*standard exception for TFL*)
exception ERR of {module: string, func: string, mesg: string};

fun UTILS_ERR func mesg = ERR {module = "Utils", func = func, mesg = mesg};


fun end_itlist _ [] = raise (UTILS_ERR "end_itlist" "list too short")
  | end_itlist _ [x] = x
  | end_itlist f (x :: xs) = f x (end_itlist f xs);

fun itlist2 f L1 L2 base_value =
 let fun it ([],[]) = base_value
       | it ((a::rst1),(b::rst2)) = f a b (it (rst1,rst2))
       | it _ = raise UTILS_ERR "itlist2" "different length lists"
 in  it (L1,L2)
 end;

fun pluck p  =
  let fun remv ([],_) = raise UTILS_ERR "pluck" "item not found"
        | remv (h::t, A) = if p h then (h, rev A @ t) else remv (t,h::A)
  in fn L => remv(L,[])
  end;

fun take f =
  let fun grab(0, _) = []
        | grab(n, x::rst) = f x::grab(n-1,rst)
  in grab
  end;

fun zip3 [][][] = []
  | zip3 (x::l1) (y::l2) (z::l3) = (x,y,z)::zip3 l1 l2 l3
  | zip3 _ _ _ = raise UTILS_ERR "zip3" "different lengths";


end;



(*** emulation of HOL's abstract syntax functions ***)

structure USyntax: USYNTAX =
struct

infix 4 ##;

fun USYN_ERR func mesg = Utils.ERR {module = "USyntax", func = func, mesg = mesg};


(*---------------------------------------------------------------------------
 *
 *                            Types
 *
 *---------------------------------------------------------------------------*)
val mk_prim_vartype = TVar;
fun mk_vartype s = mk_prim_vartype ((s, 0), \<^sort>\<open>type\<close>);

(* But internally, it's useful *)
fun dest_vtype (TVar x) = x
  | dest_vtype _ = raise USYN_ERR "dest_vtype" "not a flexible type variable";

val is_vartype = can dest_vtype;

val type_vars  = map mk_prim_vartype o Misc_Legacy.typ_tvars
fun type_varsl L = distinct (op =) (fold (curry op @ o type_vars) L []);

val alpha  = mk_vartype "'a"

val strip_prod_type = HOLogic.flatten_tupleT;



(*---------------------------------------------------------------------------
 *
 *                              Terms
 *
 *---------------------------------------------------------------------------*)

(* Free variables, in order of occurrence, from left to right in the
 * syntax tree. *)
fun free_vars_lr tm =
  let fun memb x = let fun m[] = false | m(y::rst) = (x=y)orelse m rst in m end
      fun add (t, frees) = case t of
            Free   _ => if (memb t frees) then frees else t::frees
          | Abs (_,_,body) => add(body,frees)
          | f$t =>  add(t, add(f, frees))
          | _ => frees
  in rev(add(tm,[]))
  end;



val type_vars_in_term = map mk_prim_vartype o Misc_Legacy.term_tvars;



(* Prelogic *)
fun dest_tybinding (v,ty) = (#1(dest_vtype v),ty)
fun inst theta = subst_vars (map dest_tybinding theta,[])


(* Construction routines *)

fun mk_abs{Bvar as Var((s,_),ty),Body}  = Abs(s,ty,abstract_over(Bvar,Body))
  | mk_abs{Bvar as Free(s,ty),Body}  = Abs(s,ty,abstract_over(Bvar,Body))
  | mk_abs _ = raise USYN_ERR "mk_abs" "Bvar is not a variable";


fun mk_imp{ant,conseq} =
   let val c = Const(\<^const_name>\<open>HOL.implies\<close>,HOLogic.boolT --> HOLogic.boolT --> HOLogic.boolT)
   in list_comb(c,[ant,conseq])
   end;

fun mk_select (r as {Bvar,Body}) =
  let val ty = type_of Bvar
      val c = Const(\<^const_name>\<open>Eps\<close>,(ty --> HOLogic.boolT) --> ty)
  in list_comb(c,[mk_abs r])
  end;

fun mk_forall (r as {Bvar,Body}) =
  let val ty = type_of Bvar
      val c = Const(\<^const_name>\<open>All\<close>,(ty --> HOLogic.boolT) --> HOLogic.boolT)
  in list_comb(c,[mk_abs r])
  end;

fun mk_exists (r as {Bvar,Body}) =
  let val ty = type_of Bvar
      val c = Const(\<^const_name>\<open>Ex\<close>,(ty --> HOLogic.boolT) --> HOLogic.boolT)
  in list_comb(c,[mk_abs r])
  end;


fun mk_conj{conj1,conj2} =
   let val c = Const(\<^const_name>\<open>HOL.conj\<close>,HOLogic.boolT --> HOLogic.boolT --> HOLogic.boolT)
   in list_comb(c,[conj1,conj2])
   end;

fun mk_disj{disj1,disj2} =
   let val c = Const(\<^const_name>\<open>HOL.disj\<close>,HOLogic.boolT --> HOLogic.boolT --> HOLogic.boolT)
   in list_comb(c,[disj1,disj2])
   end;

fun prod_ty ty1 ty2 = HOLogic.mk_prodT (ty1,ty2);

local
fun mk_uncurry (xt, yt, zt) =
    Const(\<^const_name>\<open>case_prod\<close>, (xt --> yt --> zt) --> prod_ty xt yt --> zt)
fun dest_pair(Const(\<^const_name>\<open>Pair\<close>,_) $ M $ N) = {fst=M, snd=N}
  | dest_pair _ = raise USYN_ERR "dest_pair" "not a pair"
fun is_var (Var _) = true | is_var (Free _) = true | is_var _ = false
in
fun mk_pabs{varstruct,body} =
 let fun mpa (varstruct, body) =
       if is_var varstruct
       then mk_abs {Bvar = varstruct, Body = body}
       else let val {fst, snd} = dest_pair varstruct
            in mk_uncurry (type_of fst, type_of snd, type_of body) $
               mpa (fst, mpa (snd, body))
            end
 in mpa (varstruct, body) end
 handle TYPE _ => raise USYN_ERR "mk_pabs" "";
end;

(* Destruction routines *)

datatype lambda = VAR   of {Name : string, Ty : typ}
                | CONST of {Name : string, Ty : typ}
                | COMB  of {Rator: term, Rand : term}
                | LAMB  of {Bvar : term, Body : term};


fun dest_term(Var((s,_),ty)) = VAR{Name = s, Ty = ty}
  | dest_term(Free(s,ty))    = VAR{Name = s, Ty = ty}
  | dest_term(Const(s,ty))   = CONST{Name = s, Ty = ty}
  | dest_term(M$N)           = COMB{Rator=M,Rand=N}
  | dest_term(Abs(s,ty,M))   = let  val v = Free(s,ty)
                               in LAMB{Bvar = v, Body = Term.betapply (M,v)}
                               end
  | dest_term(Bound _)       = raise USYN_ERR "dest_term" "Bound";

fun dest_const(Const(s,ty)) = {Name = s, Ty = ty}
  | dest_const _ = raise USYN_ERR "dest_const" "not a constant";

fun dest_comb(t1 $ t2) = {Rator = t1, Rand = t2}
  | dest_comb _ =  raise USYN_ERR "dest_comb" "not a comb";

fun dest_abs used (a as Abs(s, ty, _)) =
     let
       val s' = singleton (Name.variant_list used) s;
       val v = Free(s', ty);
     in ({Bvar = v, Body = Term.betapply (a,v)}, s'::used)
     end
  | dest_abs _ _ =  raise USYN_ERR "dest_abs" "not an abstraction";

fun dest_eq(Const(\<^const_name>\<open>HOL.eq\<close>,_) $ M $ N) = {lhs=M, rhs=N}
  | dest_eq _ = raise USYN_ERR "dest_eq" "not an equality";

fun dest_imp(Const(\<^const_name>\<open>HOL.implies\<close>,_) $ M $ N) = {ant=M, conseq=N}
  | dest_imp _ = raise USYN_ERR "dest_imp" "not an implication";

fun dest_forall(Const(\<^const_name>\<open>All\<close>,_) $ (a as Abs _)) = fst (dest_abs [] a)
  | dest_forall _ = raise USYN_ERR "dest_forall" "not a forall";

fun dest_exists(Const(\<^const_name>\<open>Ex\<close>,_) $ (a as Abs _)) = fst (dest_abs [] a)
  | dest_exists _ = raise USYN_ERR "dest_exists" "not an existential";

fun dest_neg(Const(\<^const_name>\<open>Not\<close>,_) $ M) = M
  | dest_neg _ = raise USYN_ERR "dest_neg" "not a negation";

fun dest_conj(Const(\<^const_name>\<open>HOL.conj\<close>,_) $ M $ N) = {conj1=M, conj2=N}
  | dest_conj _ = raise USYN_ERR "dest_conj" "not a conjunction";

fun dest_disj(Const(\<^const_name>\<open>HOL.disj\<close>,_) $ M $ N) = {disj1=M, disj2=N}
  | dest_disj _ = raise USYN_ERR "dest_disj" "not a disjunction";

fun mk_pair{fst,snd} =
   let val ty1 = type_of fst
       val ty2 = type_of snd
       val c = Const(\<^const_name>\<open>Pair\<close>,ty1 --> ty2 --> prod_ty ty1 ty2)
   in list_comb(c,[fst,snd])
   end;

fun dest_pair(Const(\<^const_name>\<open>Pair\<close>,_) $ M $ N) = {fst=M, snd=N}
  | dest_pair _ = raise USYN_ERR "dest_pair" "not a pair";


local  fun ucheck t = (if #Name (dest_const t) = \<^const_name>\<open>case_prod\<close> then t
                       else raise Match)
in
fun dest_pabs used tm =
   let val ({Bvar,Body}, used') = dest_abs used tm
   in {varstruct = Bvar, body = Body, used = used'}
   end handle Utils.ERR _ =>
          let val {Rator,Rand} = dest_comb tm
              val _ = ucheck Rator
              val {varstruct = lv, body, used = used'} = dest_pabs used Rand
              val {varstruct = rv, body, used = used''} = dest_pabs used' body
          in {varstruct = mk_pair {fst = lv, snd = rv}, body = body, used = used''}
          end
end;


val lhs   = #lhs o dest_eq
val rhs   = #rhs o dest_eq
val rand  = #Rand o dest_comb


(* Query routines *)
val is_imp    = can dest_imp
val is_forall = can dest_forall
val is_exists = can dest_exists
val is_neg    = can dest_neg
val is_conj   = can dest_conj
val is_disj   = can dest_disj
val is_pair   = can dest_pair
val is_pabs   = can (dest_pabs [])


(* Construction of a cterm from a list of Terms *)

fun list_mk_abs(L,tm) = fold_rev (fn v => fn M => mk_abs{Bvar=v, Body=M}) L tm;

(* These others are almost never used *)
fun list_mk_imp(A,c) = fold_rev (fn a => fn tm => mk_imp{ant=a,conseq=tm}) A c;
fun list_mk_forall(V,t) = fold_rev (fn v => fn b => mk_forall{Bvar=v, Body=b})V t;
val list_mk_conj = Utils.end_itlist(fn c1 => fn tm => mk_conj{conj1=c1, conj2=tm})


(* Need to reverse? *)
fun gen_all tm = list_mk_forall(Misc_Legacy.term_frees tm, tm);

(* Destructing a cterm to a list of Terms *)
fun strip_comb tm =
   let fun dest(M$N, A) = dest(M, N::A)
         | dest x = x
   in dest(tm,[])
   end;

fun strip_abs(tm as Abs _) =
       let val ({Bvar,Body}, _) = dest_abs [] tm
           val (bvs, core) = strip_abs Body
       in (Bvar::bvs, core)
       end
  | strip_abs M = ([],M);


fun strip_imp fm =
   if (is_imp fm)
   then let val {ant,conseq} = dest_imp fm
            val (was,wb) = strip_imp conseq
        in ((ant::was), wb)
        end
   else ([],fm);

fun strip_forall fm =
   if (is_forall fm)
   then let val {Bvar,Body} = dest_forall fm
            val (bvs,core) = strip_forall Body
        in ((Bvar::bvs), core)
        end
   else ([],fm);


fun strip_exists fm =
   if (is_exists fm)
   then let val {Bvar, Body} = dest_exists fm
            val (bvs,core) = strip_exists Body
        in (Bvar::bvs, core)
        end
   else ([],fm);

fun strip_disj w =
   if (is_disj w)
   then let val {disj1,disj2} = dest_disj w
        in (strip_disj disj1@strip_disj disj2)
        end
   else [w];


(* Miscellaneous *)

fun mk_vstruct ty V =
  let fun follow_prod_type (Type(\<^type_name>\<open>Product_Type.prod\<close>,[ty1,ty2])) vs =
              let val (ltm,vs1) = follow_prod_type ty1 vs
                  val (rtm,vs2) = follow_prod_type ty2 vs1
              in (mk_pair{fst=ltm, snd=rtm}, vs2) end
        | follow_prod_type _ (v::vs) = (v,vs)
  in #1 (follow_prod_type ty V)  end;


(* Search a term for a sub-term satisfying the predicate p. *)
fun find_term p =
   let fun find tm =
      if (p tm) then SOME tm
      else case tm of
          Abs(_,_,body) => find body
        | (t$u)         => (case find t of NONE => find u | some => some)
        | _             => NONE
   in find
   end;

fun dest_relation tm =
   if (type_of tm = HOLogic.boolT)
   then let val (Const(\<^const_name>\<open>Set.member\<close>,_) $ (Const(\<^const_name>\<open>Pair\<close>,_)$y$x) $ R) = tm
        in (R,y,x)
        end handle Bind => raise USYN_ERR "dest_relation" "unexpected term structure"
   else raise USYN_ERR "dest_relation" "not a boolean term";

fun is_WFR (Const(\<^const_name>\<open>Wellfounded.wf\<close>,_)$_) = true
  | is_WFR _                 = false;

fun ARB ty = mk_select{Bvar=Free("v",ty),
                       Body=Const(\<^const_name>\<open>True\<close>,HOLogic.boolT)};

end;



(*** derived cterm destructors ***)

structure Dcterm: DCTERM =
struct

fun ERR func mesg = Utils.ERR {module = "Dcterm", func = func, mesg = mesg};


fun dest_comb t = Thm.dest_comb t
  handle CTERM (msg, _) => raise ERR "dest_comb" msg;

fun dest_abs t = Thm.dest_abs t
  handle CTERM (msg, _) => raise ERR "dest_abs" msg;

fun capply t u = Thm.apply t u
  handle CTERM (msg, _) => raise ERR "capply" msg;

fun cabs a t = Thm.lambda a t
  handle CTERM (msg, _) => raise ERR "cabs" msg;


(*---------------------------------------------------------------------------
 * Some simple constructor functions.
 *---------------------------------------------------------------------------*)

val mk_hol_const = Thm.cterm_of \<^theory_context>\<open>HOL\<close> o Const;

fun mk_exists (r as (Bvar, Body)) =
  let val ty = Thm.typ_of_cterm Bvar
      val c = mk_hol_const(\<^const_name>\<open>Ex\<close>, (ty --> HOLogic.boolT) --> HOLogic.boolT)
  in capply c (uncurry cabs r) end;


local val c = mk_hol_const(\<^const_name>\<open>HOL.conj\<close>, HOLogic.boolT --> HOLogic.boolT --> HOLogic.boolT)
in fun mk_conj(conj1,conj2) = capply (capply c conj1) conj2
end;

local val c = mk_hol_const(\<^const_name>\<open>HOL.disj\<close>, HOLogic.boolT --> HOLogic.boolT --> HOLogic.boolT)
in fun mk_disj(disj1,disj2) = capply (capply c disj1) disj2
end;


(*---------------------------------------------------------------------------
 * The primitives.
 *---------------------------------------------------------------------------*)
fun dest_const ctm =
   (case Thm.term_of ctm
      of Const(s,ty) => {Name = s, Ty = ty}
       | _ => raise ERR "dest_const" "not a constant");

fun dest_var ctm =
   (case Thm.term_of ctm
      of Var((s,_),ty) => {Name=s, Ty=ty}
       | Free(s,ty)    => {Name=s, Ty=ty}
       |             _ => raise ERR "dest_var" "not a variable");


(*---------------------------------------------------------------------------
 * Derived destructor operations.
 *---------------------------------------------------------------------------*)

fun dest_monop expected tm =
 let
   fun err () = raise ERR "dest_monop" ("Not a(n) " ^ quote expected);
   val (c, N) = dest_comb tm handle Utils.ERR _ => err ();
   val name = #Name (dest_const c handle Utils.ERR _ => err ());
 in if name = expected then N else err () end;

fun dest_binop expected tm =
 let
   fun err () = raise ERR "dest_binop" ("Not a(n) " ^ quote expected);
   val (M, N) = dest_comb tm handle Utils.ERR _ => err ()
 in (dest_monop expected M, N) handle Utils.ERR _ => err () end;

fun dest_binder expected tm =
  dest_abs (dest_monop expected tm)
  handle Utils.ERR _ => raise ERR "dest_binder" ("Not a(n) " ^ quote expected);


val dest_neg    = dest_monop \<^const_name>\<open>Not\<close>
val dest_pair   = dest_binop \<^const_name>\<open>Pair\<close>
val dest_eq     = dest_binop \<^const_name>\<open>HOL.eq\<close>
val dest_imp    = dest_binop \<^const_name>\<open>HOL.implies\<close>
val dest_conj   = dest_binop \<^const_name>\<open>HOL.conj\<close>
val dest_disj   = dest_binop \<^const_name>\<open>HOL.disj\<close>
val dest_exists = dest_binder \<^const_name>\<open>Ex\<close>
val dest_forall = dest_binder \<^const_name>\<open>All\<close>

(* Query routines *)

val is_eq     = can dest_eq
val is_imp    = can dest_imp
val is_forall = can dest_forall
val is_exists = can dest_exists
val is_neg    = can dest_neg
val is_conj   = can dest_conj
val is_disj   = can dest_disj
val is_pair   = can dest_pair


(*---------------------------------------------------------------------------
 * Iterated creation.
 *---------------------------------------------------------------------------*)
val list_mk_disj = Utils.end_itlist (fn d1 => fn tm => mk_disj (d1, tm));

(*---------------------------------------------------------------------------
 * Iterated destruction. (To the "right" in a term.)
 *---------------------------------------------------------------------------*)
fun strip break tm =
  let fun dest (p as (ctm,accum)) =
        let val (M,N) = break ctm
        in dest (N, M::accum)
        end handle Utils.ERR _ => p
  in dest (tm,[])
  end;

fun rev2swap (x,l) = (rev l, x);

val strip_comb   = strip (Library.swap o dest_comb)  (* Goes to the "left" *)
val strip_imp    = rev2swap o strip dest_imp
val strip_abs    = rev2swap o strip dest_abs
val strip_forall = rev2swap o strip dest_forall
val strip_exists = rev2swap o strip dest_exists

val strip_disj   = rev o (op::) o strip dest_disj


(*---------------------------------------------------------------------------
 * Going into and out of prop
 *---------------------------------------------------------------------------*)

fun is_Trueprop ct =
  (case Thm.term_of ct of
    Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => true
  | _ => false);

fun mk_prop ct = if is_Trueprop ct then ct else Thm.apply \<^cterm>\<open>Trueprop\<close> ct;
fun drop_prop ct = if is_Trueprop ct then Thm.dest_arg ct else ct;

end;



(*** emulation of HOL inference rules for TFL ***)

structure Rules: RULES =
struct

fun RULES_ERR func mesg = Utils.ERR {module = "Rules", func = func, mesg = mesg};


fun cconcl thm = Dcterm.drop_prop (Thm.cprop_of thm);
fun chyps thm = map Dcterm.drop_prop (Thm.chyps_of thm);

fun dest_thm thm =
  (map HOLogic.dest_Trueprop (Thm.hyps_of thm), HOLogic.dest_Trueprop (Thm.prop_of thm))
    handle TERM _ => raise RULES_ERR "dest_thm" "missing Trueprop";


(* Inference rules *)

(*---------------------------------------------------------------------------
 *        Equality (one step)
 *---------------------------------------------------------------------------*)

fun REFL tm = HOLogic.mk_obj_eq (Thm.reflexive tm)
  handle THM (msg, _, _) => raise RULES_ERR "REFL" msg;

fun SYM thm = thm RS sym
  handle THM (msg, _, _) => raise RULES_ERR "SYM" msg;

fun ALPHA thm ctm1 =
  let
    val ctm2 = Thm.cprop_of thm;
    val ctm2_eq = Thm.reflexive ctm2;
    val ctm1_eq = Thm.reflexive ctm1;
  in Thm.equal_elim (Thm.transitive ctm2_eq ctm1_eq) thm end
  handle THM (msg, _, _) => raise RULES_ERR "ALPHA" msg;

fun rbeta th =
  (case Dcterm.strip_comb (cconcl th) of
    (_, [_, r]) => Thm.transitive th (Thm.beta_conversion false r)
  | _ => raise RULES_ERR "rbeta" "");


(*----------------------------------------------------------------------------
 *        Implication and the assumption list
 *
 * Assumptions get stuck on the meta-language assumption list. Implications
 * are in the object language, so discharging an assumption "A" from theorem
 * "B" results in something that looks like "A --> B".
 *---------------------------------------------------------------------------*)

fun ASSUME ctm = Thm.assume (Dcterm.mk_prop ctm);


(*---------------------------------------------------------------------------
 * Implication in TFL is -->. Meta-language implication (==>) is only used
 * in the implementation of some of the inference rules below.
 *---------------------------------------------------------------------------*)
fun MP th1 th2 = th2 RS (th1 RS mp)
  handle THM (msg, _, _) => raise RULES_ERR "MP" msg;

(*forces the first argument to be a proposition if necessary*)
fun DISCH tm thm = Thm.implies_intr (Dcterm.mk_prop tm) thm COMP impI
  handle THM (msg, _, _) => raise RULES_ERR "DISCH" msg;

fun DISCH_ALL thm = fold_rev DISCH (Thm.chyps_of thm) thm;


fun FILTER_DISCH_ALL P thm =
 let fun check tm = P (Thm.term_of tm)
 in  fold_rev (fn tm => fn th => if check tm then DISCH tm th else th) (chyps thm) thm
 end;

fun UNDISCH thm =
   let val tm = Dcterm.mk_prop (#1 (Dcterm.dest_imp (cconcl thm)))
   in Thm.implies_elim (thm RS mp) (ASSUME tm) end
   handle Utils.ERR _ => raise RULES_ERR "UNDISCH" ""
     | THM _ => raise RULES_ERR "UNDISCH" "";

fun PROVE_HYP ath bth = MP (DISCH (cconcl ath) bth) ath;

fun IMP_TRANS th1 th2 = th2 RS (th1 RS @{thm tfl_imp_trans})
  handle THM (msg, _, _) => raise RULES_ERR "IMP_TRANS" msg;


(*----------------------------------------------------------------------------
 *        Conjunction
 *---------------------------------------------------------------------------*)

fun CONJUNCT1 thm = thm RS conjunct1
  handle THM (msg, _, _) => raise RULES_ERR "CONJUNCT1" msg;

fun CONJUNCT2 thm = thm RS conjunct2
  handle THM (msg, _, _) => raise RULES_ERR "CONJUNCT2" msg;

fun CONJUNCTS th = CONJUNCTS (CONJUNCT1 th) @ CONJUNCTS (CONJUNCT2 th) handle Utils.ERR _ => [th];

fun LIST_CONJ [] = raise RULES_ERR "LIST_CONJ" "empty list"
  | LIST_CONJ [th] = th
  | LIST_CONJ (th :: rst) = MP (MP (conjI COMP (impI RS impI)) th) (LIST_CONJ rst)
      handle THM (msg, _, _) => raise RULES_ERR "LIST_CONJ" msg;


(*----------------------------------------------------------------------------
 *        Disjunction
 *---------------------------------------------------------------------------*)
local
  val prop = Thm.prop_of disjI1
  val [_,Q] = Misc_Legacy.term_vars prop
  val disj1 = Thm.forall_intr (Thm.cterm_of \<^context> Q) disjI1
in
fun DISJ1 thm tm = thm RS (Thm.forall_elim (Dcterm.drop_prop tm) disj1)
  handle THM (msg, _, _) => raise RULES_ERR "DISJ1" msg;
end;

local
  val prop = Thm.prop_of disjI2
  val [P,_] = Misc_Legacy.term_vars prop
  val disj2 = Thm.forall_intr (Thm.cterm_of \<^context> P) disjI2
in
fun DISJ2 tm thm = thm RS (Thm.forall_elim (Dcterm.drop_prop tm) disj2)
  handle THM (msg, _, _) => raise RULES_ERR "DISJ2" msg;
end;


(*----------------------------------------------------------------------------
 *
 *                   A1 |- M1, ..., An |- Mn
 *     ---------------------------------------------------
 *     [A1 |- M1 \/ ... \/ Mn, ..., An |- M1 \/ ... \/ Mn]
 *
 *---------------------------------------------------------------------------*)


fun EVEN_ORS thms =
  let fun blue ldisjs [] _ = []
        | blue ldisjs (th::rst) rdisjs =
            let val tail = tl rdisjs
                val rdisj_tl = Dcterm.list_mk_disj tail
            in fold_rev DISJ2 ldisjs (DISJ1 th rdisj_tl)
               :: blue (ldisjs @ [cconcl th]) rst tail
            end handle Utils.ERR _ => [fold_rev DISJ2 ldisjs th]
   in blue [] thms (map cconcl thms) end;


(*----------------------------------------------------------------------------
 *
 *         A |- P \/ Q   B,P |- R    C,Q |- R
 *     ---------------------------------------------------
 *                     A U B U C |- R
 *
 *---------------------------------------------------------------------------*)

fun DISJ_CASES th1 th2 th3 =
  let
    val c = Dcterm.drop_prop (cconcl th1);
    val (disj1, disj2) = Dcterm.dest_disj c;
    val th2' = DISCH disj1 th2;
    val th3' = DISCH disj2 th3;
  in
    th3' RS (th2' RS (th1 RS @{thm tfl_disjE}))
      handle THM (msg, _, _) => raise RULES_ERR "DISJ_CASES" msg
  end;


(*-----------------------------------------------------------------------------
 *
 *       |- A1 \/ ... \/ An     [A1 |- M, ..., An |- M]
 *     ---------------------------------------------------
 *                           |- M
 *
 * Note. The list of theorems may be all jumbled up, so we have to
 * first organize it to align with the first argument (the disjunctive
 * theorem).
 *---------------------------------------------------------------------------*)

fun organize eq =    (* a bit slow - analogous to insertion sort *)
 let fun extract a alist =
     let fun ex (_,[]) = raise RULES_ERR "organize" "not a permutation.1"
           | ex(left,h::t) = if (eq h a) then (h,rev left@t) else ex(h::left,t)
     in ex ([],alist)
     end
     fun place [] [] = []
       | place (a::rst) alist =
           let val (item,next) = extract a alist
           in item::place rst next
           end
       | place _ _ = raise RULES_ERR "organize" "not a permutation.2"
 in place
 end;

fun DISJ_CASESL disjth thl =
   let val c = cconcl disjth
       fun eq th atm =
        exists (fn t => HOLogic.dest_Trueprop t aconv Thm.term_of atm) (Thm.hyps_of th)
       val tml = Dcterm.strip_disj c
       fun DL _ [] = raise RULES_ERR "DISJ_CASESL" "no cases"
         | DL th [th1] = PROVE_HYP th th1
         | DL th [th1,th2] = DISJ_CASES th th1 th2
         | DL th (th1::rst) =
            let val tm = #2 (Dcterm.dest_disj (Dcterm.drop_prop(cconcl th)))
             in DISJ_CASES th th1 (DL (ASSUME tm) rst) end
   in DL disjth (organize eq tml thl)
   end;


(*----------------------------------------------------------------------------
 *        Universals
 *---------------------------------------------------------------------------*)
local (* this is fragile *)
  val prop = Thm.prop_of spec
  val x = hd (tl (Misc_Legacy.term_vars prop))
  val TV = dest_TVar (type_of x)
  val gspec = Thm.forall_intr (Thm.cterm_of \<^context> x) spec
in
fun SPEC tm thm =
   let val gspec' =
    Drule.instantiate_normalize (TVars.make [(TV, Thm.ctyp_of_cterm tm)], Vars.empty) gspec
   in thm RS (Thm.forall_elim tm gspec') end
end;

fun SPEC_ALL thm = fold SPEC (#1 (Dcterm.strip_forall(cconcl thm))) thm;

val ISPEC = SPEC
val ISPECL = fold ISPEC;

(* Not optimized! Too complicated. *)
local
  val prop = Thm.prop_of allI
  val [P] = Misc_Legacy.add_term_vars (prop, [])
  fun cty_theta ctxt = map (fn (i, (S, ty)) => ((i, S), Thm.ctyp_of ctxt ty))
  fun ctm_theta ctxt =
    map (fn (i, (_, tm2)) =>
      let val ctm2 = Thm.cterm_of ctxt tm2
      in ((i, Thm.typ_of_cterm ctm2), ctm2) end)
  fun certify ctxt (ty_theta,tm_theta) =
    (TVars.make (cty_theta ctxt (Vartab.dest ty_theta)),
     Vars.make (ctm_theta ctxt (Vartab.dest tm_theta)))
in
fun GEN ctxt v th =
   let val gth = Thm.forall_intr v th
       val thy = Proof_Context.theory_of ctxt
       val Const(\<^const_name>\<open>Pure.all\<close>,_)$Abs(x,ty,rst) = Thm.prop_of gth
       val P' = Abs(x,ty, HOLogic.dest_Trueprop rst)  (* get rid of trueprop *)
       val theta = Pattern.match thy (P,P') (Vartab.empty, Vartab.empty);
       val allI2 = Drule.instantiate_normalize (certify ctxt theta) allI
       val thm = Thm.implies_elim allI2 gth
       val tp $ (A $ Abs(_,_,M)) = Thm.prop_of thm
       val prop' = tp $ (A $ Abs(x,ty,M))
   in ALPHA thm (Thm.cterm_of ctxt prop') end
end;

fun GENL ctxt = fold_rev (GEN ctxt);

fun GEN_ALL ctxt thm =
  let
    val prop = Thm.prop_of thm
    val vlist = map (Thm.cterm_of ctxt) (Misc_Legacy.add_term_vars (prop, []))
  in GENL ctxt vlist thm end;


fun MATCH_MP th1 th2 =
   if (Dcterm.is_forall (Dcterm.drop_prop(cconcl th1)))
   then MATCH_MP (th1 RS spec) th2
   else MP th1 th2;


(*----------------------------------------------------------------------------
 *        Existentials
 *---------------------------------------------------------------------------*)



(*---------------------------------------------------------------------------
 * Existential elimination
 *
 *      A1 |- ?x.t[x]   ,   A2, "t[v]" |- t'
 *      ------------------------------------     (variable v occurs nowhere)
 *                A1 u A2 |- t'
 *
 *---------------------------------------------------------------------------*)

fun CHOOSE ctxt (fvar, exth) fact =
  let
    val lam = #2 (Dcterm.dest_comb (Dcterm.drop_prop (cconcl exth)))
    val redex = Dcterm.capply lam fvar
    val t$u = Thm.term_of redex
    val residue = Thm.cterm_of ctxt (Term.betapply (t, u))
  in
    GEN ctxt fvar (DISCH residue fact) RS (exth RS @{thm tfl_exE})
      handle THM (msg, _, _) => raise RULES_ERR "CHOOSE" msg
  end;

fun EXISTS ctxt (template,witness) thm =
  let val abstr = #2 (Dcterm.dest_comb template) in
    thm RS (infer_instantiate ctxt [(("P", 0), abstr), (("x", 0), witness)] exI)
      handle THM (msg, _, _) => raise RULES_ERR "EXISTS" msg
  end;

(*----------------------------------------------------------------------------
 *
 *       A |- M[x_1,...,x_n]
 *   ----------------------------   [(x |-> y)_1,...,(x |-> y)_n]
 *       A |- ?y_1...y_n. M
 *
 *---------------------------------------------------------------------------*)
(* Could be improved, but needs "subst_free" for certified terms *)

fun IT_EXISTS ctxt blist th =
  let
    val blist' = map (apply2 Thm.term_of) blist
    fun ex v M = Thm.cterm_of ctxt (USyntax.mk_exists{Bvar=v,Body = M})
  in
    fold_rev (fn (b as (r1,r2)) => fn thm =>
        EXISTS ctxt (ex r2 (subst_free [b]
                   (HOLogic.dest_Trueprop(Thm.prop_of thm))), Thm.cterm_of ctxt r1)
              thm)
       blist' th
  end;

(*----------------------------------------------------------------------------
 *        Rewriting
 *---------------------------------------------------------------------------*)

fun SUBS ctxt thl =
  rewrite_rule ctxt (map (fn th => th RS eq_reflection handle THM _ => th) thl);

val rew_conv = Raw_Simplifier.rewrite_cterm (true, false, false) (K (K NONE));

fun simpl_conv ctxt thl ctm =
  HOLogic.mk_obj_eq (rew_conv (ctxt addsimps thl) ctm);


fun RIGHT_ASSOC ctxt = rewrite_rule ctxt @{thms tfl_disj_assoc};



(*---------------------------------------------------------------------------
 *                  TERMINATION CONDITION EXTRACTION
 *---------------------------------------------------------------------------*)


(* Object language quantifier, i.e., "!" *)
fun Forall v M = USyntax.mk_forall{Bvar=v, Body=M};


(* Fragile: it's a cong if it is not "R y x ==> cut f R x y = f y" *)
fun is_cong thm =
  case (Thm.prop_of thm) of
    (Const(\<^const_name>\<open>Pure.imp\<close>,_)$(Const(\<^const_name>\<open>Trueprop\<close>,_)$ _) $
      (Const(\<^const_name>\<open>Pure.eq\<close>,_) $ (Const (\<^const_name>\<open>Wfrec.cut\<close>,_) $ _ $ _ $ _ $ _) $ _)) =>
        false
  | _ => true;


fun dest_equal(Const (\<^const_name>\<open>Pure.eq\<close>,_) $
               (Const (\<^const_name>\<open>Trueprop\<close>,_) $ lhs)
               $ (Const (\<^const_name>\<open>Trueprop\<close>,_) $ rhs)) = {lhs=lhs, rhs=rhs}
  | dest_equal(Const (\<^const_name>\<open>Pure.eq\<close>,_) $ lhs $ rhs) = {lhs=lhs, rhs=rhs}
  | dest_equal tm = USyntax.dest_eq tm;

fun get_lhs tm = #lhs(dest_equal (HOLogic.dest_Trueprop tm));

fun dest_all used (Const(\<^const_name>\<open>Pure.all\<close>,_) $ (a as Abs _)) = USyntax.dest_abs used a
  | dest_all _ _ = raise RULES_ERR "dest_all" "not a !!";

val is_all = can (dest_all []);

fun strip_all used fm =
   if (is_all fm)
   then let val ({Bvar, Body}, used') = dest_all used fm
            val (bvs, core, used'') = strip_all used' Body
        in ((Bvar::bvs), core, used'')
        end
   else ([], fm, used);

fun list_break_all(Const(\<^const_name>\<open>Pure.all\<close>,_) $ Abs (s,ty,body)) =
     let val (L,core) = list_break_all body
     in ((s,ty)::L, core)
     end
  | list_break_all tm = ([],tm);

(*---------------------------------------------------------------------------
 * Rename a term of the form
 *
 *      !!x1 ...xn. x1=M1 ==> ... ==> xn=Mn
 *                  ==> ((%v1...vn. Q) x1 ... xn = g x1 ... xn.
 * to one of
 *
 *      !!v1 ... vn. v1=M1 ==> ... ==> vn=Mn
 *      ==> ((%v1...vn. Q) v1 ... vn = g v1 ... vn.
 *
 * This prevents name problems in extraction, and helps the result to read
 * better. There is a problem with varstructs, since they can introduce more
 * than n variables, and some extra reasoning needs to be done.
 *---------------------------------------------------------------------------*)

fun get ([],_,L) = rev L
  | get (ant::rst,n,L) =
      case (list_break_all ant)
        of ([],_) => get (rst, n+1,L)
         | (_,body) =>
            let val eq = Logic.strip_imp_concl body
                val (f,_) = USyntax.strip_comb (get_lhs eq)
                val (vstrl,_) = USyntax.strip_abs f
                val names  =
                  Name.variant_list (Misc_Legacy.add_term_names(body, [])) (map (#1 o dest_Free) vstrl)
            in get (rst, n+1, (names,n)::L) end
            handle TERM _ => get (rst, n+1, L)
              | Utils.ERR _ => get (rst, n+1, L);

(* Note: Thm.rename_params_rule counts from 1, not 0 *)
fun rename thm =
  let
    val ants = Logic.strip_imp_prems (Thm.prop_of thm)
    val news = get (ants,1,[])
  in fold Thm.rename_params_rule news thm end;


(*---------------------------------------------------------------------------
 * Beta-conversion to the rhs of an equation (taken from hol90/drule.sml)
 *---------------------------------------------------------------------------*)

fun list_beta_conv tm =
  let fun rbeta th = Thm.transitive th (Thm.beta_conversion false (#2(Dcterm.dest_eq(cconcl th))))
      fun iter [] = Thm.reflexive tm
        | iter (v::rst) = rbeta (Thm.combination(iter rst) (Thm.reflexive v))
  in iter  end;


(*---------------------------------------------------------------------------
 * Trace information for the rewriter
 *---------------------------------------------------------------------------*)
val tracing = Unsynchronized.ref false;

fun say s = if !tracing then writeln s else ();

fun print_thms ctxt s L =
  say (cat_lines (s :: map (Thm.string_of_thm ctxt) L));

fun print_term ctxt s t =
  say (cat_lines [s, Syntax.string_of_term ctxt t]);


(*---------------------------------------------------------------------------
 * General abstraction handlers, should probably go in USyntax.
 *---------------------------------------------------------------------------*)
fun mk_aabs (vstr, body) =
  USyntax.mk_abs {Bvar = vstr, Body = body}
  handle Utils.ERR _ => USyntax.mk_pabs {varstruct = vstr, body = body};

fun list_mk_aabs (vstrl,tm) =
    fold_rev (fn vstr => fn tm => mk_aabs(vstr,tm)) vstrl tm;

fun dest_aabs used tm =
   let val ({Bvar,Body}, used') = USyntax.dest_abs used tm
   in (Bvar, Body, used') end
   handle Utils.ERR _ =>
     let val {varstruct, body, used} = USyntax.dest_pabs used tm
     in (varstruct, body, used) end;

fun strip_aabs used tm =
   let val (vstr, body, used') = dest_aabs used tm
       val (bvs, core, used'') = strip_aabs used' body
   in (vstr::bvs, core, used'') end
   handle Utils.ERR _ => ([], tm, used);

fun dest_combn tm 0 = (tm,[])
  | dest_combn tm n =
     let val {Rator,Rand} = USyntax.dest_comb tm
         val (f,rands) = dest_combn Rator (n-1)
     in (f,Rand::rands)
     end;




local fun dest_pair M = let val {fst,snd} = USyntax.dest_pair M in (fst,snd) end
      fun mk_fst tm =
          let val ty as Type(\<^type_name>\<open>Product_Type.prod\<close>, [fty,sty]) = type_of tm
          in  Const (\<^const_name>\<open>Product_Type.fst\<close>, ty --> fty) $ tm  end
      fun mk_snd tm =
          let val ty as Type(\<^type_name>\<open>Product_Type.prod\<close>, [fty,sty]) = type_of tm
          in  Const (\<^const_name>\<open>Product_Type.snd\<close>, ty --> sty) $ tm  end
in
fun XFILL tych x vstruct =
  let fun traverse p xocc L =
        if (is_Free p)
        then tych xocc::L
        else let val (p1,p2) = dest_pair p
             in traverse p1 (mk_fst xocc) (traverse p2  (mk_snd xocc) L)
             end
  in
  traverse vstruct x []
end end;

(*---------------------------------------------------------------------------
 * Replace a free tuple (vstr) by a universally quantified variable (a).
 * Note that the notion of "freeness" for a tuple is different than for a
 * variable: if variables in the tuple also occur in any other place than
 * an occurrences of the tuple, they aren't "free" (which is thus probably
 *  the wrong word to use).
 *---------------------------------------------------------------------------*)

fun VSTRUCT_ELIM ctxt tych a vstr th =
  let val L = USyntax.free_vars_lr vstr
      val bind1 = tych (HOLogic.mk_Trueprop (HOLogic.mk_eq(a,vstr)))
      val thm1 = Thm.implies_intr bind1 (SUBS ctxt [SYM(Thm.assume bind1)] th)
      val thm2 = forall_intr_list (map tych L) thm1
      val thm3 = forall_elim_list (XFILL tych a vstr) thm2
  in refl RS
     rewrite_rule ctxt [Thm.symmetric (@{thm surjective_pairing} RS eq_reflection)] thm3
  end;

fun PGEN ctxt tych a vstr th =
  let val a1 = tych a
  in Thm.forall_intr a1 (VSTRUCT_ELIM ctxt tych a vstr th) end;


(*---------------------------------------------------------------------------
 * Takes apart a paired beta-redex, looking like "(\(x,y).N) vstr", into
 *
 *     (([x,y],N),vstr)
 *---------------------------------------------------------------------------*)
fun dest_pbeta_redex used M n =
  let val (f,args) = dest_combn M n
      val _ = dest_aabs used f
  in (strip_aabs used f,args)
  end;

fun pbeta_redex M n = can (fn t => dest_pbeta_redex [] t n) M;

fun dest_impl tm =
  let val ants = Logic.strip_imp_prems tm
      val eq = Logic.strip_imp_concl tm
  in (ants,get_lhs eq)
  end;

fun restricted t = is_some (USyntax.find_term
                            (fn (Const(\<^const_name>\<open>Wfrec.cut\<close>,_)) =>true | _ => false)
                            t)

fun CONTEXT_REWRITE_RULE main_ctxt (func, G, cut_lemma, congs) th =
 let val globals = func::G
     val ctxt0 = empty_simpset main_ctxt
     val pbeta_reduce = simpl_conv ctxt0 [@{thm split_conv} RS eq_reflection];
     val tc_list = Unsynchronized.ref []: term list Unsynchronized.ref
     val cut_lemma' = cut_lemma RS eq_reflection
     fun prover used ctxt thm =
     let fun cong_prover ctxt thm =
         let val _ = say "cong_prover:"
             val cntxt = Simplifier.prems_of ctxt
             val _ = print_thms ctxt "cntxt:" cntxt
             val _ = say "cong rule:"
             val _ = say (Thm.string_of_thm ctxt thm)
             (* Unquantified eliminate *)
             fun uq_eliminate (thm,imp) =
                 let val tych = Thm.cterm_of ctxt
                     val _ = print_term ctxt "To eliminate:" imp
                     val ants = map tych (Logic.strip_imp_prems imp)
                     val eq = Logic.strip_imp_concl imp
                     val lhs = tych(get_lhs eq)
                     val ctxt' = Simplifier.add_prems (map ASSUME ants) ctxt
                     val lhs_eq_lhs1 = Raw_Simplifier.rewrite_cterm (false,true,false) (prover used) ctxt' lhs
                       handle Utils.ERR _ => Thm.reflexive lhs
                     val _ = print_thms ctxt' "proven:" [lhs_eq_lhs1]
                     val lhs_eq_lhs2 = implies_intr_list ants lhs_eq_lhs1
                     val lhs_eeq_lhs2 = HOLogic.mk_obj_eq lhs_eq_lhs2
                  in
                  lhs_eeq_lhs2 COMP thm
                  end
             fun pq_eliminate (thm, vlist, imp_body, lhs_eq) =
              let val ((vstrl, _, used'), args) = dest_pbeta_redex used lhs_eq (length vlist)
                  val _ = forall (op aconv) (ListPair.zip (vlist, args))
                    orelse error "assertion failed in CONTEXT_REWRITE_RULE"
                  val imp_body1 = subst_free (ListPair.zip (args, vstrl))
                                             imp_body
                  val tych = Thm.cterm_of ctxt
                  val ants1 = map tych (Logic.strip_imp_prems imp_body1)
                  val eq1 = Logic.strip_imp_concl imp_body1
                  val Q = get_lhs eq1
                  val QeqQ1 = pbeta_reduce (tych Q)
                  val Q1 = #2(Dcterm.dest_eq(cconcl QeqQ1))
                  val ctxt' = Simplifier.add_prems (map ASSUME ants1) ctxt
                  val Q1eeqQ2 = Raw_Simplifier.rewrite_cterm (false,true,false) (prover used') ctxt' Q1
                                handle Utils.ERR _ => Thm.reflexive Q1
                  val Q2 = #2 (Logic.dest_equals (Thm.prop_of Q1eeqQ2))
                  val Q3 = tych(list_comb(list_mk_aabs(vstrl,Q2),vstrl))
                  val Q2eeqQ3 = Thm.symmetric(pbeta_reduce Q3 RS eq_reflection)
                  val thA = Thm.transitive(QeqQ1 RS eq_reflection) Q1eeqQ2
                  val QeeqQ3 = Thm.transitive thA Q2eeqQ3 handle THM _ =>
                               (HOLogic.mk_obj_eq Q2eeqQ3
                                RS (HOLogic.mk_obj_eq thA RS trans))
                                RS eq_reflection
                  val impth = implies_intr_list ants1 QeeqQ3
                  val impth1 = HOLogic.mk_obj_eq impth
                  (* Need to abstract *)
                  val ant_th = Utils.itlist2 (PGEN ctxt' tych) args vstrl impth1
              in ant_th COMP thm
              end
             fun q_eliminate (thm, imp) =
              let val (vlist, imp_body, used') = strip_all used imp
                  val (ants,Q) = dest_impl imp_body
              in if (pbeta_redex Q) (length vlist)
                 then pq_eliminate (thm, vlist, imp_body, Q)
                 else
                 let val tych = Thm.cterm_of ctxt
                     val ants1 = map tych ants
                     val ctxt' = Simplifier.add_prems (map ASSUME ants1) ctxt
                     val Q_eeq_Q1 = Raw_Simplifier.rewrite_cterm
                        (false,true,false) (prover used') ctxt' (tych Q)
                      handle Utils.ERR _ => Thm.reflexive (tych Q)
                     val lhs_eeq_lhs2 = implies_intr_list ants1 Q_eeq_Q1
                     val lhs_eq_lhs2 = HOLogic.mk_obj_eq lhs_eeq_lhs2
                     val ant_th = forall_intr_list(map tych vlist)lhs_eq_lhs2
                 in
                 ant_th COMP thm
              end end

             fun eliminate thm =
               case Thm.prop_of thm of
                 Const(\<^const_name>\<open>Pure.imp\<close>,_) $ imp $ _ =>
                   eliminate
                    (if not(is_all imp)
                     then uq_eliminate (thm, imp)
                     else q_eliminate (thm, imp))
                            (* Assume that the leading constant is ==,   *)
                | _ => thm  (* if it is not a ==>                        *)
         in SOME(eliminate (rename thm)) end
         handle Utils.ERR _ => NONE    (* FIXME handle THM as well?? *)

        fun restrict_prover ctxt thm =
          let val _ = say "restrict_prover:"
              val cntxt = rev (Simplifier.prems_of ctxt)
              val _ = print_thms ctxt "cntxt:" cntxt
              val Const(\<^const_name>\<open>Pure.imp\<close>,_) $ (Const(\<^const_name>\<open>Trueprop\<close>,_) $ A) $ _ =
                Thm.prop_of thm
              fun genl tm = let val vlist = subtract (op aconv) globals
                                           (Misc_Legacy.add_term_frees(tm,[]))
                            in fold_rev Forall vlist tm
                            end
              (*--------------------------------------------------------------
               * This actually isn't quite right, since it will think that
               * not-fully applied occs. of "f" in the context mean that the
               * current call is nested. The real solution is to pass in a
               * term "f v1..vn" which is a pattern that any full application
               * of "f" will match.
               *-------------------------------------------------------------*)
              val func_name = #1(dest_Const func)
              fun is_func (Const (name,_)) = (name = func_name)
                | is_func _                = false
              val rcontext = rev cntxt
              val cncl = HOLogic.dest_Trueprop o Thm.prop_of
              val antl = case rcontext of [] => []
                         | _   => [USyntax.list_mk_conj(map cncl rcontext)]
              val TC = genl(USyntax.list_mk_imp(antl, A))
              val _ = print_term ctxt "func:" func
              val _ = print_term ctxt "TC:" (HOLogic.mk_Trueprop TC)
              val _ = tc_list := (TC :: !tc_list)
              val nestedp = is_some (USyntax.find_term is_func TC)
              val _ = if nestedp then say "nested" else say "not_nested"
              val th' = if nestedp then raise RULES_ERR "solver" "nested function"
                        else let val cTC = Thm.cterm_of ctxt (HOLogic.mk_Trueprop TC)
                             in case rcontext of
                                [] => SPEC_ALL(ASSUME cTC)
                               | _ => MP (SPEC_ALL (ASSUME cTC))
                                         (LIST_CONJ rcontext)
                             end
              val th'' = th' RS thm
          in SOME (th'')
          end handle Utils.ERR _ => NONE    (* FIXME handle THM as well?? *)
    in
    (if (is_cong thm) then cong_prover else restrict_prover) ctxt thm
    end
    val ctm = Thm.cprop_of th
    val names = Misc_Legacy.add_term_names (Thm.term_of ctm, [])
    val th1 =
      Raw_Simplifier.rewrite_cterm (false, true, false)
        (prover names) (ctxt0 addsimps [cut_lemma'] |> fold Simplifier.add_eqcong congs) ctm
    val th2 = Thm.equal_elim th1 th
 in
 (th2, filter_out restricted (!tc_list))
 end;


fun prove ctxt strict (t, tac) =
  let
    val ctxt' = Proof_Context.augment t ctxt;
  in
    if strict
    then Goal.prove ctxt' [] [] t (K tac)
    else Goal.prove ctxt' [] [] t (K tac)
      handle ERROR msg => (warning msg; raise RULES_ERR "prove" msg)
  end;

end;



(*** theory operations ***)

structure Thry: THRY =
struct


fun THRY_ERR func mesg = Utils.ERR {module = "Thry", func = func, mesg = mesg};


(*---------------------------------------------------------------------------
 *    Matching
 *---------------------------------------------------------------------------*)

local

fun tybind (ixn, (S, T)) = (TVar (ixn, S), T);

in

fun match_term thry pat ob =
  let
    val (ty_theta, tm_theta) = Pattern.match thry (pat,ob) (Vartab.empty, Vartab.empty);
    fun tmbind (ixn, (T, t)) = (Var (ixn, Envir.subst_type ty_theta T), t)
  in (map tmbind (Vartab.dest tm_theta), map tybind (Vartab.dest ty_theta))
  end;

fun match_type thry pat ob =
  map tybind (Vartab.dest (Sign.typ_match thry (pat, ob) Vartab.empty));

end;


(*---------------------------------------------------------------------------
 * Typing
 *---------------------------------------------------------------------------*)

fun typecheck thy t =
  Thm.global_cterm_of thy t
    handle TYPE (msg, _, _) => raise THRY_ERR "typecheck" msg
      | TERM (msg, _) => raise THRY_ERR "typecheck" msg;


(*---------------------------------------------------------------------------
 * Get information about datatypes
 *---------------------------------------------------------------------------*)

fun match_info thy dtco =
  case (BNF_LFP_Compat.get_info thy [BNF_LFP_Compat.Keep_Nesting] dtco,
         BNF_LFP_Compat.get_constrs thy dtco) of
      (SOME {case_name, ... }, SOME constructors) =>
        SOME {case_const = Const (case_name, Sign.the_const_type thy case_name), constructors = map Const constructors}
    | _ => NONE;

fun induct_info thy dtco = case BNF_LFP_Compat.get_info thy [BNF_LFP_Compat.Keep_Nesting] dtco of
        NONE => NONE
      | SOME {nchotomy, ...} =>
          SOME {nchotomy = nchotomy,
                constructors = (map Const o the o BNF_LFP_Compat.get_constrs thy) dtco};

fun extract_info thy =
 let val infos = map snd (Symtab.dest (BNF_LFP_Compat.get_all thy [BNF_LFP_Compat.Keep_Nesting]))
 in {case_congs = map (mk_meta_eq o #case_cong) infos,
     case_rewrites = maps (map mk_meta_eq o #case_rewrites) infos}
 end;


end;



(*** first part of main module ***)

structure Prim: PRIM =
struct

val trace = Unsynchronized.ref false;


fun TFL_ERR func mesg = Utils.ERR {module = "Tfl", func = func, mesg = mesg};

val concl = #2 o Rules.dest_thm;

val list_mk_type = Utils.end_itlist (curry (op -->));

fun front_last [] = raise TFL_ERR "front_last" "empty list"
  | front_last [x] = ([],x)
  | front_last (h::t) =
     let val (pref,x) = front_last t
     in
        (h::pref,x)
     end;


(*---------------------------------------------------------------------------
 * The next function is common to pattern-match translation and
 * proof of completeness of cases for the induction theorem.
 *
 * The curried function "gvvariant" returns a function to generate distinct
 * variables that are guaranteed not to be in names.  The names of
 * the variables go u, v, ..., z, aa, ..., az, ...  The returned
 * function contains embedded refs!
 *---------------------------------------------------------------------------*)
fun gvvariant names =
  let val slist = Unsynchronized.ref names
      val vname = Unsynchronized.ref "u"
      fun new() =
         if member (op =) (!slist) (!vname)
         then (vname := Symbol.bump_string (!vname);  new())
         else (slist := !vname :: !slist;  !vname)
  in
  fn ty => Free(new(), ty)
  end;


(*---------------------------------------------------------------------------
 * Used in induction theorem production. This is the simple case of
 * partitioning up pattern rows by the leading constructor.
 *---------------------------------------------------------------------------*)
fun ipartition gv (constructors,rows) =
  let fun pfail s = raise TFL_ERR "partition.part" s
      fun part {constrs = [],   rows = [],   A} = rev A
        | part {constrs = [],   rows = _::_, A} = pfail"extra cases in defn"
        | part {constrs = _::_, rows = [],   A} = pfail"cases missing in defn"
        | part {constrs = c::crst, rows,     A} =
          let val (c, T) = dest_Const c
              val L = binder_types T
              val (in_group, not_in_group) =
               fold_rev (fn (row as (p::rst, rhs)) =>
                         fn (in_group,not_in_group) =>
                  let val (pc,args) = USyntax.strip_comb p
                  in if (#1(dest_Const pc) = c)
                     then ((args@rst, rhs)::in_group, not_in_group)
                     else (in_group, row::not_in_group)
                  end)      rows ([],[])
              val col_types = Utils.take type_of (length L, #1(hd in_group))
          in
          part{constrs = crst, rows = not_in_group,
               A = {constructor = c,
                    new_formals = map gv col_types,
                    group = in_group}::A}
          end
  in part{constrs = constructors, rows = rows, A = []}
  end;



(*---------------------------------------------------------------------------
 * Each pattern carries with it a tag (i,b) where
 * i is the clause it came from and
 * b=true indicates that clause was given by the user
 * (or is an instantiation of a user supplied pattern)
 * b=false --> i = ~1
 *---------------------------------------------------------------------------*)

type pattern = term * (int * bool)

fun pattern_map f (tm,x) = (f tm, x);

fun pattern_subst theta = pattern_map (subst_free theta);

val pat_of = fst;
fun row_of_pat x = fst (snd x);
fun given x = snd (snd x);

(*---------------------------------------------------------------------------
 * Produce an instance of a constructor, plus genvars for its arguments.
 *---------------------------------------------------------------------------*)
fun fresh_constr ty_match colty gv c =
  let val (_,Ty) = dest_Const c
      val L = binder_types Ty
      and ty = body_type Ty
      val ty_theta = ty_match ty colty
      val c' = USyntax.inst ty_theta c
      val gvars = map (USyntax.inst ty_theta o gv) L
  in (c', gvars)
  end;


(*---------------------------------------------------------------------------
 * Goes through a list of rows and picks out the ones beginning with a
 * pattern with constructor = name.
 *---------------------------------------------------------------------------*)
fun mk_group name rows =
  fold_rev (fn (row as ((prfx, p::rst), rhs)) =>
            fn (in_group,not_in_group) =>
               let val (pc,args) = USyntax.strip_comb p
               in if ((#1 (Term.dest_Const pc) = name) handle TERM _ => false)
                  then (((prfx,args@rst), rhs)::in_group, not_in_group)
                  else (in_group, row::not_in_group) end)
      rows ([],[]);

(*---------------------------------------------------------------------------
 * Partition the rows. Not efficient: we should use hashing.
 *---------------------------------------------------------------------------*)
fun partition _ _ (_,_,_,[]) = raise TFL_ERR "partition" "no rows"
  | partition gv ty_match
              (constructors, colty, res_ty, rows as (((prfx,_),_)::_)) =
let val fresh = fresh_constr ty_match colty gv
     fun part {constrs = [],      rows, A} = rev A
       | part {constrs = c::crst, rows, A} =
         let val (c',gvars) = fresh c
             val (in_group, not_in_group) = mk_group (#1 (dest_Const c')) rows
             val in_group' =
                 if (null in_group)  (* Constructor not given *)
                 then [((prfx, #2(fresh c)), (USyntax.ARB res_ty, (~1,false)))]
                 else in_group
         in
         part{constrs = crst,
              rows = not_in_group,
              A = {constructor = c',
                   new_formals = gvars,
                   group = in_group'}::A}
         end
in part{constrs=constructors, rows=rows, A=[]}
end;

(*---------------------------------------------------------------------------
 * Misc. routines used in mk_case
 *---------------------------------------------------------------------------*)

fun mk_pat (c,l) =
  let val L = length (binder_types (type_of c))
      fun build (prfx,tag,plist) =
          let val (args, plist') = chop L plist
          in (prfx,tag,list_comb(c,args)::plist') end
  in map build l end;

fun v_to_prfx (prfx, v::pats) = (v::prfx,pats)
  | v_to_prfx _ = raise TFL_ERR "mk_case" "v_to_prfx";

fun v_to_pats (v::prfx,tag, pats) = (prfx, tag, v::pats)
  | v_to_pats _ = raise TFL_ERR "mk_case" "v_to_pats";


(*----------------------------------------------------------------------------
 * Translation of pattern terms into nested case expressions.
 *
 * This performs the translation and also builds the full set of patterns.
 * Thus it supports the construction of induction theorems even when an
 * incomplete set of patterns is given.
 *---------------------------------------------------------------------------*)

fun mk_case ty_info ty_match usednames range_ty =
 let
 fun mk_case_fail s = raise TFL_ERR "mk_case" s
 val fresh_var = gvvariant usednames
 val divide = partition fresh_var ty_match
 fun expand _ ty ((_,[]), _) = mk_case_fail"expand_var_row"
   | expand constructors ty (row as ((prfx, p::rst), rhs)) =
       if (is_Free p)
       then let val fresh = fresh_constr ty_match ty fresh_var
                fun expnd (c,gvs) =
                  let val capp = list_comb(c,gvs)
                  in ((prfx, capp::rst), pattern_subst[(p,capp)] rhs)
                  end
            in map expnd (map fresh constructors)  end
       else [row]
 fun mk{rows=[],...} = mk_case_fail"no rows"
   | mk{path=[], rows = ((prfx, []), (tm,tag))::_} =  (* Done *)
        ([(prfx,tag,[])], tm)
   | mk{path=[], rows = _::_} = mk_case_fail"blunder"
   | mk{path as u::rstp, rows as ((prfx, []), rhs)::rst} =
        mk{path = path,
           rows = ((prfx, [fresh_var(type_of u)]), rhs)::rst}
   | mk{path = u::rstp, rows as ((_, p::_), _)::_} =
     let val (pat_rectangle,rights) = ListPair.unzip rows
         val col0 = map(hd o #2) pat_rectangle
     in
     if (forall is_Free col0)
     then let val rights' = map (fn(v,e) => pattern_subst[(v,u)] e)
                                (ListPair.zip (col0, rights))
              val pat_rectangle' = map v_to_prfx pat_rectangle
              val (pref_patl,tm) = mk{path = rstp,
                                      rows = ListPair.zip (pat_rectangle',
                                                           rights')}
          in (map v_to_pats pref_patl, tm)
          end
     else
     let val pty as Type (ty_name,_) = type_of p
     in
     case (ty_info ty_name)
     of NONE => mk_case_fail("Not a known datatype: "^ty_name)
      | SOME{case_const,constructors} =>
        let
            val case_const_name = #1(dest_Const case_const)
            val nrows = maps (expand constructors pty) rows
            val subproblems = divide(constructors, pty, range_ty, nrows)
            val groups      = map #group subproblems
            and new_formals = map #new_formals subproblems
            and constructors' = map #constructor subproblems
            val news = map (fn (nf,rows) => {path = nf@rstp, rows=rows})
                           (ListPair.zip (new_formals, groups))
            val rec_calls = map mk news
            val (pat_rect,dtrees) = ListPair.unzip rec_calls
            val case_functions = map USyntax.list_mk_abs
                                  (ListPair.zip (new_formals, dtrees))
            val types = map type_of (case_functions@[u]) @ [range_ty]
            val case_const' = Const(case_const_name, list_mk_type types)
            val tree = list_comb(case_const', case_functions@[u])
            val pat_rect1 = flat (ListPair.map mk_pat (constructors', pat_rect))
        in (pat_rect1,tree)
        end
     end end
 in mk
 end;


(* Repeated variable occurrences in a pattern are not allowed. *)
fun FV_multiset tm =
   case (USyntax.dest_term tm)
     of USyntax.VAR{Name = c, Ty = T} => [Free(c, T)]
      | USyntax.CONST _ => []
      | USyntax.COMB{Rator, Rand} => FV_multiset Rator @ FV_multiset Rand
      | USyntax.LAMB _ => raise TFL_ERR "FV_multiset" "lambda";

fun no_repeat_vars thy pat =
 let fun check [] = true
       | check (v::rst) =
         if member (op aconv) rst v then
            raise TFL_ERR "no_repeat_vars"
                          (quote (#1 (dest_Free v)) ^
                          " occurs repeatedly in the pattern " ^
                          quote (Syntax.string_of_term_global thy pat))
         else check rst
 in check (FV_multiset pat)
 end;

fun dest_atom (Free p) = p
  | dest_atom (Const p) = p
  | dest_atom  _ = raise TFL_ERR "dest_atom" "function name not an identifier";

fun same_name (p,q) = #1(dest_atom p) = #1(dest_atom q);

local fun mk_functional_err s = raise TFL_ERR "mk_functional" s
      fun single [_$_] =
              mk_functional_err "recdef does not allow currying"
        | single [f] = f
        | single fs  =
              (*multiple function names?*)
              if length (distinct same_name fs) < length fs
              then mk_functional_err
                   "The function being declared appears with multiple types"
              else mk_functional_err
                   (string_of_int (length fs) ^
                    " distinct function names being declared")
in
fun mk_functional thy clauses =
 let val (L,R) = ListPair.unzip (map HOLogic.dest_eq clauses
                   handle TERM _ => raise TFL_ERR "mk_functional"
                        "recursion equations must use the = relation")
     val (funcs,pats) = ListPair.unzip (map (fn (t$u) =>(t,u)) L)
     val atom = single (distinct (op aconv) funcs)
     val (fname,ftype) = dest_atom atom
     val _ = map (no_repeat_vars thy) pats
     val rows = ListPair.zip (map (fn x => ([]:term list,[x])) pats,
                              map_index (fn (i, t) => (t,(i,true))) R)
     val names = List.foldr Misc_Legacy.add_term_names [] R
     val atype = type_of(hd pats)
     and aname = singleton (Name.variant_list names) "a"
     val a = Free(aname,atype)
     val ty_info = Thry.match_info thy
     val ty_match = Thry.match_type thy
     val range_ty = type_of (hd R)
     val (patts, case_tm) = mk_case ty_info ty_match (aname::names) range_ty
                                    {path=[a], rows=rows}
     val patts1 = map (fn (_,tag,[pat]) => (pat,tag)) patts
          handle Match => mk_functional_err "error in pattern-match translation"
     val patts2 = Library.sort (Library.int_ord o apply2 row_of_pat) patts1
     val finals = map row_of_pat patts2
     val originals = map (row_of_pat o #2) rows
     val _ = case (subtract (op =) finals originals)
             of [] => ()
          | L => mk_functional_err
 ("The following clauses are redundant (covered by preceding clauses): " ^
                   commas (map (fn i => string_of_int (i + 1)) L))
 in {functional = Abs(Long_Name.base_name fname, ftype,
                      abstract_over (atom, absfree (aname,atype) case_tm)),
     pats = patts2}
end end;


(*----------------------------------------------------------------------------
 *
 *                    PRINCIPLES OF DEFINITION
 *
 *---------------------------------------------------------------------------*)


(*For Isabelle, the lhs of a definition must be a constant.*)
fun const_def sign (c, Ty, rhs) =
  singleton (Syntax.check_terms (Proof_Context.init_global sign))
    (Const(\<^const_name>\<open>Pure.eq\<close>,dummyT) $ Const(c,Ty) $ rhs);

(*Make all TVars available for instantiation by adding a ? to the front*)
fun poly_tvars (Type(a,Ts)) = Type(a, map (poly_tvars) Ts)
  | poly_tvars (TFree (a,sort)) = TVar (("?" ^ a, 0), sort)
  | poly_tvars (TVar ((a,i),sort)) = TVar (("?" ^ a, i+1), sort);

local
  val f_eq_wfrec_R_M =
    #ant(USyntax.dest_imp(#2(USyntax.strip_forall (concl @{thm tfl_wfrec}))))
  val {lhs=f, rhs} = USyntax.dest_eq f_eq_wfrec_R_M
  val _ = dest_Free f
  val (wfrec,_) = USyntax.strip_comb rhs
in

fun wfrec_definition0 fid R (functional as Abs(x, Ty, _)) thy =
  let
    val def_name = Thm.def_name (Long_Name.base_name fid)
    val wfrec_R_M = map_types poly_tvars (wfrec $ map_types poly_tvars R) $ functional
    val def_term = const_def thy (fid, Ty, wfrec_R_M)
    val ([def], thy') =
      Global_Theory.add_defs false [Thm.no_attributes (Binding.name def_name, def_term)] thy
  in (def, thy') end;

end;



(*---------------------------------------------------------------------------
 * This structure keeps track of congruence rules that aren't derived
 * from a datatype definition.
 *---------------------------------------------------------------------------*)
fun extraction_thms thy =
 let val {case_rewrites,case_congs} = Thry.extract_info thy
 in (case_rewrites, case_congs)
 end;


(*---------------------------------------------------------------------------
 * Pair patterns with termination conditions. The full list of patterns for
 * a definition is merged with the TCs arising from the user-given clauses.
 * There can be fewer clauses than the full list, if the user omitted some
 * cases. This routine is used to prepare input for mk_induction.
 *---------------------------------------------------------------------------*)
fun merge full_pats TCs =
let fun insert (p,TCs) =
      let fun insrt ((x as (h,[]))::rst) =
                 if (p aconv h) then (p,TCs)::rst else x::insrt rst
            | insrt (x::rst) = x::insrt rst
            | insrt[] = raise TFL_ERR "merge.insert" "pattern not found"
      in insrt end
    fun pass ([],ptcl_final) = ptcl_final
      | pass (ptcs::tcl, ptcl) = pass(tcl, insert ptcs ptcl)
in
  pass (TCs, map (fn p => (p,[])) full_pats)
end;


fun givens pats = map pat_of (filter given pats);

fun post_definition ctxt meta_tflCongs (def, pats) =
 let val thy = Proof_Context.theory_of ctxt
     val tych = Thry.typecheck thy
     val f = #lhs(USyntax.dest_eq(concl def))
     val corollary = Rules.MATCH_MP @{thm tfl_wfrec} def
     val pats' = filter given pats
     val given_pats = map pat_of pats'
     val rows = map row_of_pat pats'
     val WFR = #ant(USyntax.dest_imp(concl corollary))
     val R = #Rand(USyntax.dest_comb WFR)
     val corollary' = Rules.UNDISCH corollary  (* put WF R on assums *)
     val corollaries = map (fn pat => Rules.SPEC (tych pat) corollary') given_pats
     val (case_rewrites,context_congs) = extraction_thms thy
     (*case_ss causes minimal simplification: bodies of case expressions are
       not simplified. Otherwise large examples (Red-Black trees) are too
       slow.*)
     val case_simpset =
       put_simpset HOL_basic_ss ctxt
          addsimps case_rewrites
          |> fold (Simplifier.add_cong o #case_cong_weak o snd)
              (Symtab.dest (BNF_LFP_Compat.get_all thy [BNF_LFP_Compat.Keep_Nesting]))
     val corollaries' = map (Simplifier.simplify case_simpset) corollaries
     val extract =
      Rules.CONTEXT_REWRITE_RULE ctxt (f, [R], @{thm cut_apply}, meta_tflCongs @ context_congs)
     val (rules, TCs) = ListPair.unzip (map extract corollaries')
     val rules0 = map (rewrite_rule ctxt @{thms tfl_cut_def}) rules
     val mk_cond_rule = Rules.FILTER_DISCH_ALL(not o curry (op aconv) WFR)
     val rules1 = Rules.LIST_CONJ(map mk_cond_rule rules0)
 in
 {rules = rules1,
  rows = rows,
  full_pats_TCs = merge (map pat_of pats) (ListPair.zip (given_pats, TCs)),
  TCs = TCs}
 end;


(*----------------------------------------------------------------------------
 *
 *                           INDUCTION THEOREM
 *
 *---------------------------------------------------------------------------*)


(*------------------------  Miscellaneous function  --------------------------
 *
 *           [x_1,...,x_n]     ?v_1...v_n. M[v_1,...,v_n]
 *     -----------------------------------------------------------
 *     ( M[x_1,...,x_n], [(x_i,?v_1...v_n. M[v_1,...,v_n]),
 *                        ...
 *                        (x_j,?v_n. M[x_1,...,x_(n-1),v_n])] )
 *
 * This function is totally ad hoc. Used in the production of the induction
 * theorem. The nchotomy theorem can have clauses that look like
 *
 *     ?v1..vn. z = C vn..v1
 *
 * in which the order of quantification is not the order of occurrence of the
 * quantified variables as arguments to C. Since we have no control over this
 * aspect of the nchotomy theorem, we make the correspondence explicit by
 * pairing the incoming new variable with the term it gets beta-reduced into.
 *---------------------------------------------------------------------------*)

fun alpha_ex_unroll (xlist, tm) =
  let val (qvars,body) = USyntax.strip_exists tm
      val vlist = #2 (USyntax.strip_comb (USyntax.rhs body))
      val plist = ListPair.zip (vlist, xlist)
      val args = map (the o AList.lookup (op aconv) plist) qvars
                   handle Option.Option => raise Fail "TFL.alpha_ex_unroll: no correspondence"
      fun build ex      []   = []
        | build (_$rex) (v::rst) =
           let val ex1 = Term.betapply(rex, v)
           in  ex1 :: build ex1 rst
           end
     val (nex::exl) = rev (tm::build tm args)
  in
  (nex, ListPair.zip (args, rev exl))
  end;



(*----------------------------------------------------------------------------
 *
 *             PROVING COMPLETENESS OF PATTERNS
 *
 *---------------------------------------------------------------------------*)

fun mk_case ctxt ty_info usednames =
 let
 val thy = Proof_Context.theory_of ctxt
 val divide = ipartition (gvvariant usednames)
 val tych = Thry.typecheck thy
 fun tych_binding(x,y) = (tych x, tych y)
 fun fail s = raise TFL_ERR "mk_case" s
 fun mk{rows=[],...} = fail"no rows"
   | mk{path=[], rows = [([], (thm, bindings))]} =
                         Rules.IT_EXISTS ctxt (map tych_binding bindings) thm
   | mk{path = u::rstp, rows as (p::_, _)::_} =
     let val (pat_rectangle,rights) = ListPair.unzip rows
         val col0 = map hd pat_rectangle
         val pat_rectangle' = map tl pat_rectangle
     in
     if (forall is_Free col0) (* column 0 is all variables *)
     then let val rights' = map (fn ((thm,theta),v) => (thm,theta@[(u,v)]))
                                (ListPair.zip (rights, col0))
          in mk{path = rstp, rows = ListPair.zip (pat_rectangle', rights')}
          end
     else                     (* column 0 is all constructors *)
     let val Type (ty_name,_) = type_of p
     in
     case (ty_info ty_name)
     of NONE => fail("Not a known datatype: "^ty_name)
      | SOME{constructors,nchotomy} =>
        let val thm' = Rules.ISPEC (tych u) nchotomy
            val disjuncts = USyntax.strip_disj (concl thm')
            val subproblems = divide(constructors, rows)
            val groups      = map #group subproblems
            and new_formals = map #new_formals subproblems
            val existentials = ListPair.map alpha_ex_unroll
                                   (new_formals, disjuncts)
            val constraints = map #1 existentials
            val vexl = map #2 existentials
            fun expnd tm (pats,(th,b)) = (pats, (Rules.SUBS ctxt [Rules.ASSUME (tych tm)] th, b))
            val news = map (fn (nf,rows,c) => {path = nf@rstp,
                                               rows = map (expnd c) rows})
                           (Utils.zip3 new_formals groups constraints)
            val recursive_thms = map mk news
            val build_exists = Library.foldr
                                (fn((x,t), th) =>
                                 Rules.CHOOSE ctxt (tych x, Rules.ASSUME (tych t)) th)
            val thms' = ListPair.map build_exists (vexl, recursive_thms)
            val same_concls = Rules.EVEN_ORS thms'
        in Rules.DISJ_CASESL thm' same_concls
        end
     end end
 in mk
 end;


fun complete_cases ctxt =
 let val thy = Proof_Context.theory_of ctxt
     val tych = Thry.typecheck thy
     val ty_info = Thry.induct_info thy
 in fn pats =>
 let val names = List.foldr Misc_Legacy.add_term_names [] pats
     val T = type_of (hd pats)
     val aname = singleton (Name.variant_list names) "a"
     val vname = singleton (Name.variant_list (aname::names)) "v"
     val a = Free (aname, T)
     val v = Free (vname, T)
     val a_eq_v = HOLogic.mk_eq(a,v)
     val ex_th0 = Rules.EXISTS ctxt (tych (USyntax.mk_exists{Bvar=v,Body=a_eq_v}), tych a)
                           (Rules.REFL (tych a))
     val th0 = Rules.ASSUME (tych a_eq_v)
     val rows = map (fn x => ([x], (th0,[]))) pats
 in
 Rules.GEN ctxt (tych a)
       (Rules.RIGHT_ASSOC ctxt
          (Rules.CHOOSE ctxt (tych v, ex_th0)
                (mk_case ctxt ty_info (vname::aname::names)
                 {path=[v], rows=rows})))
 end end;


(*---------------------------------------------------------------------------
 * Constructing induction hypotheses: one for each recursive call.
 *
 * Note. R will never occur as a variable in the ind_clause, because
 * to do so, it would have to be from a nested definition, and we don't
 * allow nested defns to have R variable.
 *
 * Note. When the context is empty, there can be no local variables.
 *---------------------------------------------------------------------------*)

local infix 5 ==>
      fun (tm1 ==> tm2) = USyntax.mk_imp{ant = tm1, conseq = tm2}
in
fun build_ih f (P,SV) (pat,TCs) =
 let val pat_vars = USyntax.free_vars_lr pat
     val globals = pat_vars@SV
     fun nested tm = is_some (USyntax.find_term (curry (op aconv) f) tm)
     fun dest_TC tm =
         let val (cntxt,R_y_pat) = USyntax.strip_imp(#2(USyntax.strip_forall tm))
             val (R,y,_) = USyntax.dest_relation R_y_pat
             val P_y = if (nested tm) then R_y_pat ==> P$y else P$y
         in case cntxt
              of [] => (P_y, (tm,[]))
               | _  => let
                    val imp = USyntax.list_mk_conj cntxt ==> P_y
                    val lvs = subtract (op aconv) globals (USyntax.free_vars_lr imp)
                    val locals = #2(Utils.pluck (curry (op aconv) P) lvs) handle Utils.ERR _ => lvs
                    in (USyntax.list_mk_forall(locals,imp), (tm,locals)) end
         end
 in case TCs
    of [] => (USyntax.list_mk_forall(pat_vars, P$pat), [])
     |  _ => let val (ihs, TCs_locals) = ListPair.unzip(map dest_TC TCs)
                 val ind_clause = USyntax.list_mk_conj ihs ==> P$pat
             in (USyntax.list_mk_forall(pat_vars,ind_clause), TCs_locals)
             end
 end
end;

(*---------------------------------------------------------------------------
 * This function makes good on the promise made in "build_ih".
 *
 * Input  is tm = "(!y. R y pat ==> P y) ==> P pat",
 *           TCs = TC_1[pat] ... TC_n[pat]
 *           thm = ih1 /\ ... /\ ih_n |- ih[pat]
 *---------------------------------------------------------------------------*)
fun prove_case ctxt f (tm,TCs_locals,thm) =
 let val tych = Thry.typecheck (Proof_Context.theory_of ctxt)
     val antc = tych(#ant(USyntax.dest_imp tm))
     val thm' = Rules.SPEC_ALL thm
     fun nested tm = is_some (USyntax.find_term (curry (op aconv) f) tm)
     fun get_cntxt TC = tych(#ant(USyntax.dest_imp(#2(USyntax.strip_forall(concl TC)))))
     fun mk_ih ((TC,locals),th2,nested) =
         Rules.GENL ctxt (map tych locals)
            (if nested then Rules.DISCH (get_cntxt TC) th2 handle Utils.ERR _ => th2
             else if USyntax.is_imp (concl TC) then Rules.IMP_TRANS TC th2
             else Rules.MP th2 TC)
 in
 Rules.DISCH antc
 (if USyntax.is_imp(concl thm') (* recursive calls in this clause *)
  then let val th1 = Rules.ASSUME antc
           val TCs = map #1 TCs_locals
           val ylist = map (#2 o USyntax.dest_relation o #2 o USyntax.strip_imp o
                            #2 o USyntax.strip_forall) TCs
           val TClist = map (fn(TC,lvs) => (Rules.SPEC_ALL(Rules.ASSUME(tych TC)),lvs))
                            TCs_locals
           val th2list = map (fn t => Rules.SPEC (tych t) th1) ylist
           val nlist = map nested TCs
           val triples = Utils.zip3 TClist th2list nlist
           val Pylist = map mk_ih triples
       in Rules.MP thm' (Rules.LIST_CONJ Pylist) end
  else thm')
 end;


(*---------------------------------------------------------------------------
 *
 *         x = (v1,...,vn)  |- M[x]
 *    ---------------------------------------------
 *      ?v1 ... vn. x = (v1,...,vn) |- M[x]
 *
 *---------------------------------------------------------------------------*)
fun LEFT_ABS_VSTRUCT ctxt tych thm =
  let fun CHOOSER v (tm,thm) =
        let val ex_tm = USyntax.mk_exists{Bvar=v,Body=tm}
        in (ex_tm, Rules.CHOOSE ctxt (tych v, Rules.ASSUME (tych ex_tm)) thm)
        end
      val [veq] = filter (can USyntax.dest_eq) (#1 (Rules.dest_thm thm))
      val {lhs,rhs} = USyntax.dest_eq veq
      val L = USyntax.free_vars_lr rhs
  in  #2 (fold_rev CHOOSER L (veq,thm))  end;


(*----------------------------------------------------------------------------
 * Input : f, R,  and  [(pat1,TCs1),..., (patn,TCsn)]
 *
 * Instantiates tfl_wf_induct, getting Sinduct and then tries to prove
 * recursion induction (Rinduct) by proving the antecedent of Sinduct from
 * the antecedent of Rinduct.
 *---------------------------------------------------------------------------*)
fun mk_induction ctxt {fconst, R, SV, pat_TCs_list} =
let
    val thy = Proof_Context.theory_of ctxt
    val tych = Thry.typecheck thy
    val Sinduction = Rules.UNDISCH (Rules.ISPEC (tych R) @{thm tfl_wf_induct})
    val (pats,TCsl) = ListPair.unzip pat_TCs_list
    val case_thm = complete_cases ctxt pats
    val domain = (type_of o hd) pats
    val Pname = singleton (Name.variant_list (List.foldr (Library.foldr Misc_Legacy.add_term_names)
                              [] (pats::TCsl))) "P"
    val P = Free(Pname, domain --> HOLogic.boolT)
    val Sinduct = Rules.SPEC (tych P) Sinduction
    val Sinduct_assumf = USyntax.rand ((#ant o USyntax.dest_imp o concl) Sinduct)
    val Rassums_TCl' = map (build_ih fconst (P,SV)) pat_TCs_list
    val (Rassums,TCl') = ListPair.unzip Rassums_TCl'
    val Rinduct_assum = Rules.ASSUME (tych (USyntax.list_mk_conj Rassums))
    val cases = map (fn pat => Term.betapply (Sinduct_assumf, pat)) pats
    val tasks = Utils.zip3 cases TCl' (Rules.CONJUNCTS Rinduct_assum)
    val proved_cases = map (prove_case ctxt fconst) tasks
    val v =
      Free (singleton
        (Name.variant_list (List.foldr Misc_Legacy.add_term_names [] (map concl proved_cases))) "v",
          domain)
    val vtyped = tych v
    val substs = map (Rules.SYM o Rules.ASSUME o tych o (curry HOLogic.mk_eq v)) pats
    val proved_cases1 = ListPair.map (fn (th,th') => Rules.SUBS ctxt [th]th')
                          (substs, proved_cases)
    val abs_cases = map (LEFT_ABS_VSTRUCT ctxt tych) proved_cases1
    val dant = Rules.GEN ctxt vtyped (Rules.DISJ_CASESL (Rules.ISPEC vtyped case_thm) abs_cases)
    val dc = Rules.MP Sinduct dant
    val Parg_ty = type_of(#Bvar(USyntax.dest_forall(concl dc)))
    val vars = map (gvvariant[Pname]) (USyntax.strip_prod_type Parg_ty)
    val dc' = fold_rev (Rules.GEN ctxt o tych) vars
                       (Rules.SPEC (tych(USyntax.mk_vstruct Parg_ty vars)) dc)
in
   Rules.GEN ctxt (tych P) (Rules.DISCH (tych(concl Rinduct_assum)) dc')
end
handle Utils.ERR _ => raise TFL_ERR "mk_induction" "failed derivation";



(*---------------------------------------------------------------------------
 *
 *                        POST PROCESSING
 *
 *---------------------------------------------------------------------------*)


fun simplify_induction thy hth ind =
  let val tych = Thry.typecheck thy
      val (asl,_) = Rules.dest_thm ind
      val (_,tc_eq_tc') = Rules.dest_thm hth
      val tc = USyntax.lhs tc_eq_tc'
      fun loop [] = ind
        | loop (asm::rst) =
          if (can (Thry.match_term thy asm) tc)
          then Rules.UNDISCH
                 (Rules.MATCH_MP
                     (Rules.MATCH_MP @{thm tfl_simp_thm} (Rules.DISCH (tych asm) ind))
                     hth)
         else loop rst
  in loop asl
end;


(*---------------------------------------------------------------------------
 * The termination condition is an antecedent to the rule, and an
 * assumption to the theorem.
 *---------------------------------------------------------------------------*)
fun elim_tc tcthm (rule,induction) =
   (Rules.MP rule tcthm, Rules.PROVE_HYP tcthm induction)


fun trace_thms ctxt s L =
  if !trace then writeln (cat_lines (s :: map (Thm.string_of_thm ctxt) L))
  else ();

fun trace_cterm ctxt s ct =
  if !trace then
    writeln (cat_lines [s, Syntax.string_of_term ctxt (Thm.term_of ct)])
  else ();


fun postprocess ctxt strict {wf_tac, terminator, simplifier} {rules,induction,TCs} =
  let
    val thy = Proof_Context.theory_of ctxt;
    val tych = Thry.typecheck thy;

   (*---------------------------------------------------------------------
    * Attempt to eliminate WF condition. It's the only assumption of rules
    *---------------------------------------------------------------------*)
    val (rules1,induction1)  =
       let val thm =
        Rules.prove ctxt strict (HOLogic.mk_Trueprop (hd(#1(Rules.dest_thm rules))), wf_tac)
       in (Rules.PROVE_HYP thm rules, Rules.PROVE_HYP thm induction)
       end handle Utils.ERR _ => (rules,induction);

   (*----------------------------------------------------------------------
    * The termination condition (tc) is simplified to |- tc = tc' (there
    * might not be a change!) and then 3 attempts are made:
    *
    *   1. if |- tc = T, then eliminate it with tfl_eq_True; otherwise,
    *   2. apply the terminator to tc'. If |- tc' = T then eliminate; else
    *   3. replace tc by tc' in both the rules and the induction theorem.
    *---------------------------------------------------------------------*)

   fun simplify_tc tc (r,ind) =
       let val tc1 = tych tc
           val _ = trace_cterm ctxt "TC before simplification: " tc1
           val tc_eq = simplifier tc1
           val _ = trace_thms ctxt "result: " [tc_eq]
       in
       elim_tc (Rules.MATCH_MP @{thm tfl_eq_True} tc_eq) (r,ind)
       handle Utils.ERR _ =>
        (elim_tc (Rules.MATCH_MP(Rules.MATCH_MP @{thm tfl_rev_eq_mp} tc_eq)
                  (Rules.prove ctxt strict (HOLogic.mk_Trueprop(USyntax.rhs(concl tc_eq)),
                           terminator)))
                 (r,ind)
         handle Utils.ERR _ =>
          (Rules.UNDISCH(Rules.MATCH_MP (Rules.MATCH_MP @{thm tfl_simp_thm} r) tc_eq),
           simplify_induction thy tc_eq ind))
       end

   (*----------------------------------------------------------------------
    * Nested termination conditions are harder to get at, since they are
    * left embedded in the body of the function (and in induction
    * theorem hypotheses). Our "solution" is to simplify them, and try to
    * prove termination, but leave the application of the resulting theorem
    * to a higher level. So things go much as in "simplify_tc": the
    * termination condition (tc) is simplified to |- tc = tc' (there might
    * not be a change) and then 2 attempts are made:
    *
    *   1. if |- tc = T, then return |- tc; otherwise,
    *   2. apply the terminator to tc'. If |- tc' = T then return |- tc; else
    *   3. return |- tc = tc'
    *---------------------------------------------------------------------*)
   fun simplify_nested_tc tc =
      let val tc_eq = simplifier (tych (#2 (USyntax.strip_forall tc)))
      in
      Rules.GEN_ALL ctxt
       (Rules.MATCH_MP @{thm tfl_eq_True} tc_eq
        handle Utils.ERR _ =>
          (Rules.MATCH_MP(Rules.MATCH_MP @{thm tfl_rev_eq_mp} tc_eq)
                      (Rules.prove ctxt strict (HOLogic.mk_Trueprop (USyntax.rhs(concl tc_eq)),
                               terminator))
            handle Utils.ERR _ => tc_eq))
      end

   (*-------------------------------------------------------------------
    * Attempt to simplify the termination conditions in each rule and
    * in the induction theorem.
    *-------------------------------------------------------------------*)
   fun strip_imp tm = if USyntax.is_neg tm then ([],tm) else USyntax.strip_imp tm
   fun loop ([],extras,R,ind) = (rev R, ind, extras)
     | loop ((r,ftcs)::rst, nthms, R, ind) =
        let val tcs = #1(strip_imp (concl r))
            val extra_tcs = subtract (op aconv) tcs ftcs
            val extra_tc_thms = map simplify_nested_tc extra_tcs
            val (r1,ind1) = fold simplify_tc tcs (r,ind)
            val r2 = Rules.FILTER_DISCH_ALL(not o USyntax.is_WFR) r1
        in loop(rst, nthms@extra_tc_thms, r2::R, ind1)
        end
   val rules_tcs = ListPair.zip (Rules.CONJUNCTS rules1, TCs)
   val (rules2,ind2,extras) = loop(rules_tcs,[],[],induction1)
in
  {induction = ind2, rules = Rules.LIST_CONJ rules2, nested_tcs = extras}
end;

end;



(*** second part of main module (postprocessing of TFL definitions) ***)

structure Tfl: TFL =
struct

(* misc *)

(*---------------------------------------------------------------------------
 * Extract termination goals so that they can be put it into a goalstack, or
 * have a tactic directly applied to them.
 *--------------------------------------------------------------------------*)
fun termination_goals rules =
    map (Type.legacy_freeze o HOLogic.dest_Trueprop)
      (fold_rev (union (op aconv) o Thm.prems_of) rules []);

(*---------------------------------------------------------------------------
 * Three postprocessors are applied to the definition.  It
 * attempts to prove wellfoundedness of the given relation, simplifies the
 * non-proved termination conditions, and finally attempts to prove the
 * simplified termination conditions.
 *--------------------------------------------------------------------------*)
fun std_postprocessor ctxt strict wfs =
  Prim.postprocess ctxt strict
   {wf_tac = REPEAT (ares_tac ctxt wfs 1),
    terminator =
      asm_simp_tac ctxt 1
      THEN TRY (Arith_Data.arith_tac ctxt 1 ORELSE
        fast_force_tac (ctxt addSDs @{thms not0_implies_Suc}) 1),
    simplifier = Rules.simpl_conv ctxt []};



val concl = #2 o Rules.dest_thm;

(*---------------------------------------------------------------------------
 * Postprocess a definition made by "define". This is a separate stage of
 * processing from the definition stage.
 *---------------------------------------------------------------------------*)
local

(* The rest of these local definitions are for the tricky nested case *)
val solved = not o can USyntax.dest_eq o #2 o USyntax.strip_forall o concl

fun id_thm th =
   let val {lhs,rhs} = USyntax.dest_eq (#2 (USyntax.strip_forall (#2 (Rules.dest_thm th))));
   in lhs aconv rhs end
   handle Utils.ERR _ => false;

val P_imp_P_eq_True = @{thm eqTrueI} RS eq_reflection;
fun mk_meta_eq r =
  (case Thm.concl_of r of
     Const(\<^const_name>\<open>Pure.eq\<close>,_)$_$_ => r
  |   _ $(Const(\<^const_name>\<open>HOL.eq\<close>,_)$_$_) => r RS eq_reflection
  |   _ => r RS P_imp_P_eq_True)

(*Is this the best way to invoke the simplifier??*)
fun rewrite ctxt L = rewrite_rule ctxt (map mk_meta_eq (filter_out id_thm L))

fun join_assums ctxt th =
  let val tych = Thm.cterm_of ctxt
      val {lhs,rhs} = USyntax.dest_eq(#2 (USyntax.strip_forall (concl th)))
      val cntxtl = (#1 o USyntax.strip_imp) lhs  (* cntxtl should = cntxtr *)
      val cntxtr = (#1 o USyntax.strip_imp) rhs  (* but union is solider *)
      val cntxt = union (op aconv) cntxtl cntxtr
  in
    Rules.GEN_ALL ctxt
      (Rules.DISCH_ALL
         (rewrite ctxt (map (Rules.ASSUME o tych) cntxt) (Rules.SPEC_ALL th)))
  end
  val gen_all = USyntax.gen_all
in
fun proof_stage ctxt strict wfs {f, R, rules, full_pats_TCs, TCs} =
  let
    val _ = writeln "Proving induction theorem ..."
    val ind =
      Prim.mk_induction ctxt
        {fconst=f, R=R, SV=[], pat_TCs_list=full_pats_TCs}
    val _ = writeln "Postprocessing ...";
    val {rules, induction, nested_tcs} =
      std_postprocessor ctxt strict wfs {rules=rules, induction=ind, TCs=TCs}
  in
  case nested_tcs
  of [] => {induction=induction, rules=rules,tcs=[]}
  | L  => let val _ = writeln "Simplifying nested TCs ..."
              val (solved,simplified,stubborn) =
               fold_rev (fn th => fn (So,Si,St) =>
                     if (id_thm th) then (So, Si, th::St) else
                     if (solved th) then (th::So, Si, St)
                     else (So, th::Si, St)) nested_tcs ([],[],[])
              val simplified' = map (join_assums ctxt) simplified
              val dummy = (Prim.trace_thms ctxt "solved =" solved;
                           Prim.trace_thms ctxt "simplified' =" simplified')
              val rewr = full_simplify (ctxt addsimps (solved @ simplified'));
              val dummy = Prim.trace_thms ctxt "Simplifying the induction rule..." [induction]
              val induction' = rewr induction
              val dummy = Prim.trace_thms ctxt "Simplifying the recursion rules..." [rules]
              val rules'     = rewr rules
              val _ = writeln "... Postprocessing finished";
          in
          {induction = induction',
               rules = rules',
                 tcs = map (gen_all o USyntax.rhs o #2 o USyntax.strip_forall o concl)
                           (simplified@stubborn)}
          end
  end;


(*lcp: curry the predicate of the induction rule*)
fun curry_rule ctxt rl =
  Split_Rule.split_rule_var ctxt (Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of rl))) rl;

(*lcp: put a theorem into Isabelle form, using meta-level connectives*)
fun meta_outer ctxt =
  curry_rule ctxt o Drule.export_without_context o
  rule_by_tactic ctxt
    (REPEAT (FIRSTGOAL (resolve_tac ctxt [allI, impI, conjI] ORELSE' eresolve_tac ctxt [conjE])));

(*Strip off the outer !P*)
val spec'=
  Rule_Insts.read_instantiate \<^context> [((("x", 0), Position.none), "P::'b=>bool")] [] spec;

fun simplify_defn ctxt strict congs wfs pats def0 =
  let
    val thy = Proof_Context.theory_of ctxt;
    val def = HOLogic.mk_obj_eq (Thm.unvarify_global thy def0)
    val {rules, rows, TCs, full_pats_TCs} = Prim.post_definition ctxt congs (def, pats)
    val {lhs=f,rhs} = USyntax.dest_eq (concl def)
    val (_,[R,_]) = USyntax.strip_comb rhs
    val _ = Prim.trace_thms ctxt "congs =" congs
    (*the next step has caused simplifier looping in some cases*)
    val {induction, rules, tcs} =
      proof_stage ctxt strict wfs
       {f = f, R = R, rules = rules,
        full_pats_TCs = full_pats_TCs,
        TCs = TCs}
    val rules' = map (Drule.export_without_context o Object_Logic.rulify_no_asm ctxt)
                      (Rules.CONJUNCTS rules)
  in
    {induct = meta_outer ctxt (Object_Logic.rulify_no_asm ctxt (induction RS spec')),
     rules = ListPair.zip(rules', rows),
     tcs = (termination_goals rules') @ tcs}
  end
  handle Utils.ERR {mesg,func,module} =>
    error (mesg ^ "\n    (In TFL function " ^ module ^ "." ^ func ^ ")");


(* Derive the initial equations from the case-split rules to meet the
users specification of the recursive function. *)
local
  fun get_related_thms i =
      map_filter ((fn (r,x) => if x = i then SOME r else NONE));

  fun solve_eq _ (_, [], _) =  error "derive_init_eqs: missing rules"
    | solve_eq _ (_, [a], i) = [(a, i)]
    | solve_eq ctxt (th, splitths, i) =
      (writeln "Proving unsplit equation...";
      [((Drule.export_without_context o Object_Logic.rulify_no_asm ctxt)
          (CaseSplit.splitto ctxt splitths th), i)])
      handle ERROR s =>
             (warning ("recdef (solve_eq): " ^ s); map (fn x => (x,i)) splitths);
in
fun derive_init_eqs ctxt rules eqs =
  map (Thm.trivial o Thm.cterm_of ctxt o HOLogic.mk_Trueprop) eqs
  |> map_index (fn (i, e) => solve_eq ctxt (e, (get_related_thms i rules), i))
  |> flat;
end;


(*---------------------------------------------------------------------------
 * Defining a function with an associated termination relation.
 *---------------------------------------------------------------------------*)
fun define_i strict congs wfs fid R eqs ctxt =
  let
    val thy = Proof_Context.theory_of ctxt
    val {functional, pats} = Prim.mk_functional thy eqs
    val (def, thy') = Prim.wfrec_definition0 fid R functional thy
    val ctxt' = Proof_Context.transfer thy' ctxt
    val (lhs, _) = Logic.dest_equals (Thm.prop_of def)
    val {induct, rules, tcs} = simplify_defn ctxt' strict congs wfs pats def
    val rules' = if strict then derive_init_eqs ctxt' rules eqs else rules
  in ({lhs = lhs, rules = rules', induct = induct, tcs = tcs}, ctxt') end;

fun define strict congs wfs fid R seqs ctxt =
  define_i strict congs wfs fid
    (Syntax.read_term ctxt R) (map (Syntax.read_term ctxt) seqs) ctxt
      handle Utils.ERR {mesg,...} => error mesg;

end;

end;



(*** wrappers for Isar ***)

(** recdef hints **)

(* type hints *)

type hints = {simps: thm list, congs: (string * thm) list, wfs: thm list};

fun mk_hints (simps, congs, wfs) = {simps = simps, congs = congs, wfs = wfs}: hints;
fun map_hints f ({simps, congs, wfs}: hints) = mk_hints (f (simps, congs, wfs));

fun map_simps f = map_hints (fn (simps, congs, wfs) => (f simps, congs, wfs));
fun map_congs f = map_hints (fn (simps, congs, wfs) => (simps, f congs, wfs));
fun map_wfs f = map_hints (fn (simps, congs, wfs) => (simps, congs, f wfs));


(* congruence rules *)

local

val cong_head =
  fst o Term.dest_Const o Term.head_of o fst o Logic.dest_equals o Thm.concl_of;

fun prep_cong raw_thm =
  let val thm = safe_mk_meta_eq raw_thm in (cong_head thm, thm) end;

in

fun add_cong raw_thm congs =
  let
    val (c, thm) = prep_cong raw_thm;
    val _ = if AList.defined (op =) congs c
      then warning ("Overwriting recdef congruence rule for " ^ quote c)
      else ();
  in AList.update (op =) (c, thm) congs end;

fun del_cong raw_thm congs =
  let
    val (c, _) = prep_cong raw_thm;
    val _ = if AList.defined (op =) congs c
      then ()
      else warning ("No recdef congruence rule for " ^ quote c);
  in AList.delete (op =) c congs end;

end;



(** global and local recdef data **)

(* theory data *)

type recdef_info = {lhs: term, simps: thm list, rules: thm list list, induct: thm, tcs: term list};

structure Data = Generic_Data
(
  type T = recdef_info Symtab.table * hints;
  val empty = (Symtab.empty, mk_hints ([], [], [])): T;
  val extend = I;
  fun merge
   ((tab1, {simps = simps1, congs = congs1, wfs = wfs1}),
    (tab2, {simps = simps2, congs = congs2, wfs = wfs2})) : T =
      (Symtab.merge (K true) (tab1, tab2),
        mk_hints (Thm.merge_thms (simps1, simps2),
          AList.merge (op =) (K true) (congs1, congs2),
          Thm.merge_thms (wfs1, wfs2)));
);

val get_recdef = Symtab.lookup o #1 o Data.get o Context.Theory;

fun put_recdef name info =
  (Context.theory_map o Data.map o apfst) (fn tab =>
    Symtab.update_new (name, info) tab
      handle Symtab.DUP _ => error ("Duplicate recursive function definition " ^ quote name));

val get_hints = #2 o Data.get o Context.Proof;
val map_hints = Data.map o apsnd;


(* attributes *)

fun attrib f = Thm.declaration_attribute (map_hints o f);

val simp_add = attrib (map_simps o Thm.add_thm);
val simp_del = attrib (map_simps o Thm.del_thm);
val cong_add = attrib (map_congs o add_cong);
val cong_del = attrib (map_congs o del_cong);
val wf_add = attrib (map_wfs o Thm.add_thm);
val wf_del = attrib (map_wfs o Thm.del_thm);


(* modifiers *)

val recdef_simpN = "recdef_simp";
val recdef_congN = "recdef_cong";
val recdef_wfN = "recdef_wf";

val recdef_modifiers =
 [Args.$$$ recdef_simpN -- Args.colon >> K (Method.modifier simp_add \<^here>),
  Args.$$$ recdef_simpN -- Args.add -- Args.colon >> K (Method.modifier simp_add \<^here>),
  Args.$$$ recdef_simpN -- Args.del -- Args.colon >> K (Method.modifier simp_del \<^here>),
  Args.$$$ recdef_congN -- Args.colon >> K (Method.modifier cong_add \<^here>),
  Args.$$$ recdef_congN -- Args.add -- Args.colon >> K (Method.modifier cong_add \<^here>),
  Args.$$$ recdef_congN -- Args.del -- Args.colon >> K (Method.modifier cong_del \<^here>),
  Args.$$$ recdef_wfN -- Args.colon >> K (Method.modifier wf_add \<^here>),
  Args.$$$ recdef_wfN -- Args.add -- Args.colon >> K (Method.modifier wf_add \<^here>),
  Args.$$$ recdef_wfN -- Args.del -- Args.colon >> K (Method.modifier wf_del \<^here>)] @
  Clasimp.clasimp_modifiers;



(** prepare hints **)

fun prepare_hints opt_src ctxt =
  let
    val ctxt' =
      (case opt_src of
        NONE => ctxt
      | SOME src => #2 (Token.syntax (Method.sections recdef_modifiers) src ctxt));
    val {simps, congs, wfs} = get_hints ctxt';
    val ctxt'' = ctxt' addsimps simps |> Simplifier.del_cong @{thm imp_cong};
  in ((rev (map snd congs), wfs), ctxt'') end;

fun prepare_hints_i () ctxt =
  let
    val {simps, congs, wfs} = get_hints ctxt;
    val ctxt' = ctxt addsimps simps |> Simplifier.del_cong @{thm imp_cong};
  in ((rev (map snd congs), wfs), ctxt') end;



(** add_recdef(_i) **)

fun gen_add_recdef tfl_fn prep_att prep_hints not_permissive raw_name R eq_srcs hints thy =
  let
    val _ = legacy_feature "Old 'recdef' command -- use 'fun' or 'function' instead";

    val name = Sign.intern_const thy raw_name;
    val bname = Long_Name.base_name name;
    val _ = writeln ("Defining recursive function " ^ quote name ^ " ...");

    val ((eq_names, eqs), raw_eq_atts) = apfst split_list (split_list eq_srcs);
    val eq_atts = map (map (prep_att thy)) raw_eq_atts;

    val ((congs, wfs), ctxt) = prep_hints hints (Proof_Context.init_global thy);
    (*We must remove imp_cong to prevent looping when the induction rule
      is simplified. Many induction rules have nested implications that would
      give rise to looping conditional rewriting.*)
    val ({lhs, rules = rules_idx, induct, tcs}, ctxt1) =
      tfl_fn not_permissive congs wfs name R eqs ctxt;
    val rules = (map o map) fst (partition_eq (eq_snd (op = : int * int -> bool)) rules_idx);
    val simp_att =
      if null tcs then [Simplifier.simp_add,
        Named_Theorems.add \<^named_theorems>\<open>nitpick_simp\<close>]
      else [];
    val ((simps' :: rules', [induct']), thy2) =
      Proof_Context.theory_of ctxt1
      |> Sign.add_path bname
      |> Global_Theory.add_thmss
        (((Binding.name "simps", flat rules), simp_att) :: ((eq_names ~~ rules) ~~ eq_atts))
      ||>> Global_Theory.add_thms [((Binding.name "induct", induct), [])]
      ||> Spec_Rules.add_global (Binding.name bname) Spec_Rules.equational_recdef [lhs] (flat rules)
      ||> null tcs ? Code.declare_default_eqns_global (map (rpair true) (flat rules));
    val result = {lhs = lhs, simps = simps', rules = rules', induct = induct', tcs = tcs};
    val thy3 =
      thy2
      |> put_recdef name result
      |> Sign.parent_path;
  in (thy3, result) end;

val add_recdef = gen_add_recdef Tfl.define Attrib.attribute_cmd_global prepare_hints;
fun add_recdef_i x y z w = gen_add_recdef Tfl.define_i (K I) prepare_hints_i x y z w ();



(** package setup **)

(* setup theory *)

val _ =
  Theory.setup
   (Attrib.setup \<^binding>\<open>recdef_simp\<close> (Attrib.add_del simp_add simp_del)
      "declaration of recdef simp rule" #>
    Attrib.setup \<^binding>\<open>recdef_cong\<close> (Attrib.add_del cong_add cong_del)
      "declaration of recdef cong rule" #>
    Attrib.setup \<^binding>\<open>recdef_wf\<close> (Attrib.add_del wf_add wf_del)
      "declaration of recdef wf rule");


(* outer syntax *)

val hints =
  \<^keyword>\<open>(\<close> |--
    Parse.!!! ((Parse.token \<^keyword>\<open>hints\<close> ::: Parse.args) --| \<^keyword>\<open>)\<close>);

val recdef_decl =
  Scan.optional
    (\<^keyword>\<open>(\<close> -- Parse.!!! (\<^keyword>\<open>permissive\<close> -- \<^keyword>\<open>)\<close>) >> K false) true --
  Parse.name -- Parse.term -- Scan.repeat1 (Parse_Spec.opt_thm_name ":" -- Parse.prop)
    -- Scan.option hints
  >> (fn ((((p, f), R), eqs), src) =>
      #1 o add_recdef p f R (map (fn ((x, y), z) => ((x, z), y)) eqs) src);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>recdef\<close> "define general recursive functions (obsolete TFL)"
    (recdef_decl >> Toplevel.theory);

end;
