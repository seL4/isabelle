(*  Title:      Tools/misc_legacy.ML

Misc legacy stuff -- to be phased out eventually.
*)

signature MISC_LEGACY =
sig
  val add_term_names: term * string list -> string list
  val add_typ_tvars: typ * (indexname * sort) list -> (indexname * sort) list
  val add_typ_tfree_names: typ * string list -> string list
  val add_typ_tfrees: typ * (string * sort) list -> (string * sort) list
  val add_term_tvars: term * (indexname * sort) list -> (indexname * sort) list
  val add_term_tfrees: term * (string * sort) list -> (string * sort) list
  val add_term_tfree_names: term * string list -> string list
  val typ_tfrees: typ -> (string * sort) list
  val typ_tvars: typ -> (indexname * sort) list
  val term_tfrees: term -> (string * sort) list
  val term_tvars: term -> (indexname * sort) list
  val add_term_vars: term * term list -> term list
  val term_vars: term -> term list
  val add_term_frees: term * term list -> term list
  val term_frees: term -> term list
  val mk_defpair: term * term -> string * term
  val get_def: theory -> xstring -> thm
  val simple_read_term: theory -> typ -> string -> term
  val METAHYPS: (thm list -> tactic) -> int -> tactic
end;

structure Misc_Legacy: MISC_LEGACY =
struct

(*iterate a function over all types in a term*)
fun it_term_types f =
let fun iter(Const(_,T), a) = f(T,a)
      | iter(Free(_,T), a) = f(T,a)
      | iter(Var(_,T), a) = f(T,a)
      | iter(Abs(_,T,t), a) = iter(t,f(T,a))
      | iter(f$u, a) = iter(f, iter(u, a))
      | iter(Bound _, a) = a
in iter end

(*Accumulates the names in the term, suppressing duplicates.
  Includes Frees and Consts.  For choosing unambiguous bound var names.*)
fun add_term_names (Const(a,_), bs) = insert (op =) (Long_Name.base_name a) bs
  | add_term_names (Free(a,_), bs) = insert (op =) a bs
  | add_term_names (f$u, bs) = add_term_names (f, add_term_names(u, bs))
  | add_term_names (Abs(_,_,t), bs) = add_term_names(t,bs)
  | add_term_names (_, bs) = bs;

(*Accumulates the TVars in a type, suppressing duplicates.*)
fun add_typ_tvars(Type(_,Ts),vs) = List.foldr add_typ_tvars vs Ts
  | add_typ_tvars(TFree(_),vs) = vs
  | add_typ_tvars(TVar(v),vs) = insert (op =) v vs;

(*Accumulates the TFrees in a type, suppressing duplicates.*)
fun add_typ_tfree_names(Type(_,Ts),fs) = List.foldr add_typ_tfree_names fs Ts
  | add_typ_tfree_names(TFree(f,_),fs) = insert (op =) f fs
  | add_typ_tfree_names(TVar(_),fs) = fs;

fun add_typ_tfrees(Type(_,Ts),fs) = List.foldr add_typ_tfrees fs Ts
  | add_typ_tfrees(TFree(f),fs) = insert (op =) f fs
  | add_typ_tfrees(TVar(_),fs) = fs;

(*Accumulates the TVars in a term, suppressing duplicates.*)
val add_term_tvars = it_term_types add_typ_tvars;

(*Accumulates the TFrees in a term, suppressing duplicates.*)
val add_term_tfrees = it_term_types add_typ_tfrees;
val add_term_tfree_names = it_term_types add_typ_tfree_names;

(*Non-list versions*)
fun typ_tfrees T = add_typ_tfrees(T,[]);
fun typ_tvars T = add_typ_tvars(T,[]);
fun term_tfrees t = add_term_tfrees(t,[]);
fun term_tvars t = add_term_tvars(t,[]);


(*Accumulates the Vars in the term, suppressing duplicates.*)
fun add_term_vars (t, vars: term list) = case t of
    Var   _ => Ord_List.insert Term_Ord.term_ord t vars
  | Abs (_,_,body) => add_term_vars(body,vars)
  | f$t =>  add_term_vars (f, add_term_vars(t, vars))
  | _ => vars;

fun term_vars t = add_term_vars(t,[]);

(*Accumulates the Frees in the term, suppressing duplicates.*)
fun add_term_frees (t, frees: term list) = case t of
    Free   _ => Ord_List.insert Term_Ord.term_ord t frees
  | Abs (_,_,body) => add_term_frees(body,frees)
  | f$t =>  add_term_frees (f, add_term_frees(t, frees))
  | _ => frees;

fun term_frees t = add_term_frees(t,[]);


fun mk_defpair (lhs, rhs) =
  (case Term.head_of lhs of
    Const (name, _) =>
      (Long_Name.base_name name ^ "_def", Logic.mk_equals (lhs, rhs))
  | _ => raise TERM ("Malformed definition: head of lhs not a constant", [lhs, rhs]));


fun get_def thy = Thm.axiom thy o Name_Space.intern (Theory.axiom_space thy) o Thm.def_name;


fun simple_read_term thy T s =
  let
    val ctxt = Proof_Context.init_global thy
      |> Proof_Context.allow_dummies
      |> Proof_Context.set_mode Proof_Context.mode_schematic;
    val parse = if T = propT then Syntax.parse_prop else Syntax.parse_term;
  in parse ctxt s |> Type.constraint T |> Syntax.check_term ctxt end;


(**** METAHYPS -- tactical for using hypotheses as meta-level assumptions
       METAHYPS (fn prems => tac prems) i

converts subgoal i, of the form !!x1...xm. [| A1;...;An] ==> A into a new
proof state A==>A, supplying A1,...,An as meta-level assumptions (in
"prems").  The parameters x1,...,xm become free variables.  If the
resulting proof state is [| B1;...;Bk] ==> C (possibly assuming A1,...,An)
then it is lifted back into the original context, yielding k subgoals.

Replaces unknowns in the context by Frees having the prefix METAHYP_
New unknowns in [| B1;...;Bk] ==> C are lifted over x1,...,xm.
DOES NOT HANDLE TYPE UNKNOWNS.


NOTE: This version does not observe the proof context, and thus cannot
work reliably.  See also Subgoal.SUBPROOF and Subgoal.FOCUS for
properly localized variants of the same idea.
****)

local

(*Strips assumptions in goal yielding  ( [x1,...,xm], [H1,...,Hn], B )
    H1,...,Hn are the hypotheses;  x1...xm are variants of the parameters.
  Main difference from strip_assums concerns parameters:
    it replaces the bound variables by free variables.  *)
fun strip_context_aux (params, Hs, Const ("==>", _) $ H $ B) =
      strip_context_aux (params, H :: Hs, B)
  | strip_context_aux (params, Hs, Const ("all",_) $ Abs (a, T, t)) =
      let val (b, u) = Syntax_Trans.variant_abs (a, T, t)
      in strip_context_aux ((b, T) :: params, Hs, u) end
  | strip_context_aux (params, Hs, B) = (rev params, rev Hs, B);

fun strip_context A = strip_context_aux ([], [], A);

(*Left-to-right replacements: ctpairs = [...,(vi,ti),...].
  Instantiates distinct free variables by terms of same type.*)
fun free_instantiate ctpairs =
  forall_elim_list (map snd ctpairs) o forall_intr_list (map fst ctpairs);

fun free_of s ((a, i), T) =
  Free (s ^ (case i of 0 => a | _ => a ^ "_" ^ string_of_int i), T)

fun mk_inst v = (Var v, free_of "METAHYP1_" v)

fun metahyps_split_prem prem =
  let (*find all vars in the hyps -- should find tvars also!*)
      val hyps_vars = fold Term.add_vars (Logic.strip_assums_hyp prem) []
      val insts = map mk_inst hyps_vars
      (*replace the hyps_vars by Frees*)
      val prem' = subst_atomic insts prem
      val (params,hyps,concl) = strip_context prem'
  in (insts,params,hyps,concl)  end;

fun metahyps_aux_tac tacf (prem,gno) state =
  let val (insts,params,hyps,concl) = metahyps_split_prem prem
      val maxidx = Thm.maxidx_of state
      val cterm = Thm.cterm_of (Thm.theory_of_thm state)
      val chyps = map cterm hyps
      val hypths = map Thm.assume chyps
      val subprems = map (Thm.forall_elim_vars 0) hypths
      val fparams = map Free params
      val cparams = map cterm fparams
      fun swap_ctpair (t,u) = (cterm u, cterm t)
      (*Subgoal variables: make Free; lift type over params*)
      fun mk_subgoal_inst concl_vars (v, T) =
          if member (op =) concl_vars (v, T)
          then ((v, T), true, free_of "METAHYP2_" (v, T))
          else ((v, T), false, free_of "METAHYP2_" (v, map #2 params ---> T))
      (*Instantiate subgoal vars by Free applied to params*)
      fun mk_ctpair (v, in_concl, u) =
          if in_concl then (cterm (Var v), cterm u)
          else (cterm (Var v), cterm (list_comb (u, fparams)))
      (*Restore Vars with higher type and index*)
      fun mk_subgoal_swap_ctpair (((a, i), T), in_concl, u as Free (_, U)) =
          if in_concl then (cterm u, cterm (Var ((a, i), T)))
          else (cterm u, cterm (Var ((a, i + maxidx), U)))
      (*Embed B in the original context of params and hyps*)
      fun embed B = list_all_free (params, Logic.list_implies (hyps, B))
      (*Strip the context using elimination rules*)
      fun elim Bhyp = implies_elim_list (forall_elim_list cparams Bhyp) hypths
      (*A form of lifting that discharges assumptions.*)
      fun relift st =
        let val prop = Thm.prop_of st
            val subgoal_vars = (*Vars introduced in the subgoals*)
              fold Term.add_vars (Logic.strip_imp_prems prop) []
            and concl_vars = Term.add_vars (Logic.strip_imp_concl prop) []
            val subgoal_insts = map (mk_subgoal_inst concl_vars) subgoal_vars
            val st' = Thm.instantiate ([], map mk_ctpair subgoal_insts) st
            val emBs = map (cterm o embed) (prems_of st')
            val Cth  = implies_elim_list st' (map (elim o Thm.assume) emBs)
        in  (*restore the unknowns to the hypotheses*)
            free_instantiate (map swap_ctpair insts @
                              map mk_subgoal_swap_ctpair subgoal_insts)
                (*discharge assumptions from state in same order*)
                (implies_intr_list emBs
                  (forall_intr_list cparams (implies_intr_list chyps Cth)))
        end
      (*function to replace the current subgoal*)
      fun next st = Thm.bicompose false (false, relift st, nprems_of st) gno state
  in Seq.maps next (tacf subprems (Thm.trivial (cterm concl))) end;

fun print_vars_terms n thm =
  let
    val thy = theory_of_thm thm
    fun typed s ty =
      "  " ^ s ^ " has type: " ^ Syntax.string_of_typ_global thy ty;
    fun find_vars (Const (c, ty)) =
          if null (Term.add_tvarsT ty []) then I
          else insert (op =) (typed c ty)
      | find_vars (Var (xi, ty)) =
          insert (op =) (typed (Term.string_of_vname xi) ty)
      | find_vars (Free _) = I
      | find_vars (Bound _) = I
      | find_vars (Abs (_, _, t)) = find_vars t
      | find_vars (t1 $ t2) = find_vars t1 #> find_vars t2;
    val prem = Logic.nth_prem (n, Thm.prop_of thm)
    val tms = find_vars prem []
  in warning (cat_lines ("Found schematic vars in assumptions:" :: tms)) end;

in

fun METAHYPS tacf n thm = SUBGOAL (metahyps_aux_tac tacf) n thm
  handle THM("assume: variables",_,_) => (print_vars_terms n thm; Seq.empty)

end;

end;

