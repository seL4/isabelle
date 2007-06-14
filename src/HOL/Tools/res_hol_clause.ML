(* ID: $Id$ 
   Author: Jia Meng, NICTA

FOL clauses translated from HOL formulae.  

The combinator code needs to be deleted after the translation paper has been published.
It cannot be used with proof reconstruction because combinators are not introduced by proof.
The Turner combinators (B', C', S') yield no improvement and should be deleted.
*)

structure ResHolClause =

struct

structure RC = ResClause;

(* theorems for combinators and function extensionality *)
val ext = thm "HOL.ext";
val comb_I = thm "ATP_Linkup.COMBI_def";
val comb_K = thm "ATP_Linkup.COMBK_def";
val comb_B = thm "ATP_Linkup.COMBB_def";
val comb_C = thm "ATP_Linkup.COMBC_def";
val comb_S = thm "ATP_Linkup.COMBS_def";
val comb_B' = thm "ATP_Linkup.COMBB'_def";
val comb_C' = thm "ATP_Linkup.COMBC'_def";
val comb_S' = thm "ATP_Linkup.COMBS'_def";
val fequal_imp_equal = thm "ATP_Linkup.fequal_imp_equal";
val equal_imp_fequal = thm "ATP_Linkup.equal_imp_fequal";


(*The different translations of types*)
datatype type_level = T_FULL | T_PARTIAL | T_CONST;

val typ_level = ref T_CONST;

fun full_types () = (typ_level:=T_FULL);
fun partial_types () = (typ_level:=T_PARTIAL);
fun const_types_only () = (typ_level:=T_CONST);

(*A flag to set if we use the Turner optimizations. Currently FALSE, as the 5 standard
  combinators appear to work best.*)
val use_Turner = ref false;

(*If true, each function will be directly applied to as many arguments as possible, avoiding
  use of the "apply" operator. Use of hBOOL is also minimized. It only works for the 
  constant-typed translation, though it could be tried for the partially-typed one.*)
val minimize_applies = ref true;

val const_typargs = ref (Library.K [] : (string*typ -> typ list));

val const_min_arity = ref (Symtab.empty : int Symtab.table);

val const_needs_hBOOL = ref (Symtab.empty : bool Symtab.table);

fun min_arity_of c = getOpt (Symtab.lookup(!const_min_arity) c, 0);

(*True if the constant ever appears outside of the top-level position in literals.
  If false, the constant always receives all of its arguments and is used as a predicate.*)
fun needs_hBOOL c = not (!minimize_applies) orelse !typ_level=T_PARTIAL orelse
                    getOpt (Symtab.lookup(!const_needs_hBOOL) c, false);

fun init thy = (const_typargs := Sign.const_typargs thy);

(**********************************************************************)
(* convert a Term.term with lambdas into a Term.term with combinators *) 
(**********************************************************************)

fun is_free (Bound(a)) n = (a = n)
  | is_free (Abs(x,_,b)) n = (is_free b (n+1))
  | is_free (P $ Q) n = ((is_free P n) orelse (is_free Q n))
  | is_free _ _ = false;

fun mk_compact_comb (tm as (Const("ATP_Linkup.COMBB",_)$p) $ (Const("ATP_Linkup.COMBB",_)$q$r)) bnds =
      let val tp_p = Term.type_of1(bnds,p)
	  val tp_q = Term.type_of1(bnds,q)
	  val tp_r = Term.type_of1(bnds,r)
	  val typ_B' = [tp_p,tp_q,tp_r] ---> Term.type_of1(bnds,tm)
      in
	  Const("ATP_Linkup.COMBB'",typ_B') $ p $ q $ r
      end
  | mk_compact_comb (tm as (Const("ATP_Linkup.COMBC",_) $ (Const("ATP_Linkup.COMBB",_)$p$q) $ r)) bnds =
      let val tp_p = Term.type_of1(bnds,p)
	  val tp_q = Term.type_of1(bnds,q)
	  val tp_r = Term.type_of1(bnds,r)
	  val typ_C' = [tp_p,tp_q,tp_r] ---> Term.type_of1(bnds,tm)
      in
	  Const("ATP_Linkup.COMBC'",typ_C') $ p $ q $ r
      end
  | mk_compact_comb (tm as (Const("ATP_Linkup.COMBS",_) $ (Const("ATP_Linkup.COMBB",_)$p$q) $ r)) bnds =
      let val tp_p = Term.type_of1(bnds,p)
	  val tp_q = Term.type_of1(bnds,q)
	  val tp_r = Term.type_of1(bnds,r)
	  val typ_S' = [tp_p,tp_q,tp_r] ---> Term.type_of1(bnds,tm)
      in
	  Const("ATP_Linkup.COMBS'",typ_S') $ p $ q $ r
      end
  | mk_compact_comb tm _ = tm;

fun compact_comb t bnds = 
  if !use_Turner then mk_compact_comb t bnds else t;

fun lam2comb (Abs(x,tp,Bound 0)) _ = Const("ATP_Linkup.COMBI",tp-->tp) 
  | lam2comb (Abs(x,tp,Bound n)) bnds = 
      let val tb = List.nth(bnds,n-1)
      in  Const("ATP_Linkup.COMBK", [tb,tp] ---> tb) $ Bound (n-1)  end
  | lam2comb (Abs(x,t1,Const(c,t2))) _ = Const("ATP_Linkup.COMBK",[t2,t1] ---> t2) $ Const(c,t2) 
  | lam2comb (Abs(x,t1,Free(v,t2))) _ = Const("ATP_Linkup.COMBK",[t2,t1] ---> t2) $ Free(v,t2)
  | lam2comb (Abs(x,t1,Var(ind,t2))) _ = Const("ATP_Linkup.COMBK", [t2,t1] ---> t2) $ Var(ind,t2)
  | lam2comb (t as (Abs(x,t1,P$(Bound 0)))) bnds =
      if is_free P 0 then 
	  let val tI = [t1] ---> t1
	      val P' = lam2comb (Abs(x,t1,P)) bnds
	      val tp' = Term.type_of1(bnds,P')
	      val tS = [tp',tI] ---> Term.type_of1(t1::bnds,P)
	  in
	      compact_comb (Const("ATP_Linkup.COMBS",tS) $ P' $ 
	                     Const("ATP_Linkup.COMBI",tI)) bnds
	  end
      else incr_boundvars ~1 P
  | lam2comb (t as (Abs(x,t1,P$Q))) bnds =
      let val nfreeP = not(is_free P 0)
	  and nfreeQ = not(is_free Q 0)
	  val tpq = Term.type_of1(t1::bnds, P$Q) 
      in
	  if nfreeP andalso nfreeQ 
	  then 
	    let val tK = [tpq,t1] ---> tpq
	    in  Const("ATP_Linkup.COMBK",tK) $ incr_boundvars ~1 (P $ Q)  end
	  else if nfreeP then 
	    let val Q' = lam2comb (Abs(x,t1,Q)) bnds
		val P' = incr_boundvars ~1 P
		val tp = Term.type_of1(bnds,P')
		val tq' = Term.type_of1(bnds, Q')
		val tB = [tp,tq',t1] ---> tpq
	    in  compact_comb (Const("ATP_Linkup.COMBB",tB) $ P' $ Q') bnds  end
	  else if nfreeQ then 
	    let val P' = lam2comb (Abs(x,t1,P)) bnds
		val Q' = incr_boundvars ~1 Q
		val tq = Term.type_of1(bnds,Q')
		val tp' = Term.type_of1(bnds, P')
		val tC = [tp',tq,t1] ---> tpq
	    in  compact_comb (Const("ATP_Linkup.COMBC",tC) $ P' $ Q') bnds  end
          else
	    let val P' = lam2comb (Abs(x,t1,P)) bnds
		val Q' = lam2comb (Abs(x,t1,Q)) bnds 
		val tp' = Term.type_of1(bnds,P')
		val tq' = Term.type_of1(bnds,Q')
		val tS = [tp',tq',t1] ---> tpq
	    in  compact_comb (Const("ATP_Linkup.COMBS",tS) $ P' $ Q') bnds  end
      end
  | lam2comb (t as (Abs(x,t1,_))) _ = raise RC.CLAUSE("HOL CLAUSE",t);

fun to_comb (Abs(x,tp,b)) bnds = lam2comb (Abs(x, tp, to_comb b (tp::bnds))) bnds 
  | to_comb (P $ Q) bnds = (to_comb P bnds) $ (to_comb Q bnds)
  | to_comb t _ = t;


(******************************************************)
(* data types for typed combinator expressions        *)
(******************************************************)

type axiom_name = string;
type polarity = bool;
type clause_id = int;

datatype combterm = CombConst of string * RC.fol_type * RC.fol_type list (*Const and Free*)
		  | CombVar of string * RC.fol_type
		  | CombApp of combterm * combterm
		  
datatype literal = Literal of polarity * combterm;

datatype clause = 
	 Clause of {clause_id: clause_id,
		    axiom_name: axiom_name,
		    th: thm,
		    kind: RC.kind,
		    literals: literal list,
		    ctypes_sorts: (RC.typ_var * Term.sort) list, 
                    ctvar_type_literals: RC.type_literal list, 
                    ctfree_type_literals: RC.type_literal list};


(*********************************************************************)
(* convert a clause with type Term.term to a clause with type clause *)
(*********************************************************************)

fun isFalse (Literal(pol, CombConst(c,_,_))) =
      (pol andalso c = "c_False") orelse
      (not pol andalso c = "c_True")
  | isFalse _ = false;

fun isTrue (Literal (pol, CombConst(c,_,_))) =
      (pol andalso c = "c_True") orelse
      (not pol andalso c = "c_False")
  | isTrue _ = false;
  
fun isTaut (Clause {literals,...}) = exists isTrue literals;  

fun type_of (Type (a, Ts)) =
      let val (folTypes,ts) = types_of Ts
      in  (RC.Comp(RC.make_fixed_type_const a, folTypes), ts)  end
  | type_of (tp as (TFree(a,s))) =
      (RC.AtomF (RC.make_fixed_type_var a), [RC.mk_typ_var_sort tp])
  | type_of (tp as (TVar(v,s))) =
      (RC.AtomV (RC.make_schematic_type_var v), [RC.mk_typ_var_sort tp])
and types_of Ts =
      let val (folTyps,ts) = ListPair.unzip (map type_of Ts)
      in  (folTyps, RC.union_all ts)  end;

(* same as above, but no gathering of sort information *)
fun simp_type_of (Type (a, Ts)) = 
      RC.Comp(RC.make_fixed_type_const a, map simp_type_of Ts)
  | simp_type_of (TFree (a,s)) = RC.AtomF(RC.make_fixed_type_var a)
  | simp_type_of (TVar (v,s)) = RC.AtomV(RC.make_schematic_type_var v);


fun const_type_of (c,t) =
      let val (tp,ts) = type_of t
      in  (tp, ts, map simp_type_of (!const_typargs(c,t))) end;

(* convert a Term.term (with combinators) into a combterm, also accummulate sort info *)
fun combterm_of (Const(c,t)) =
      let val (tp,ts,tvar_list) = const_type_of (c,t)
	  val c' = CombConst(RC.make_fixed_const c, tp, tvar_list)
      in  (c',ts)  end
  | combterm_of (Free(v,t)) =
      let val (tp,ts) = type_of t
	  val v' = if RC.isMeta v then CombVar(RC.make_schematic_var(v,0),tp)
		   else CombConst(RC.make_fixed_var v, tp, [])
      in  (v',ts)  end
  | combterm_of (Var(v,t)) =
      let val (tp,ts) = type_of t
	  val v' = CombVar(RC.make_schematic_var v,tp)
      in  (v',ts)  end
  | combterm_of (t as (P $ Q)) =
      let val (P',tsP) = combterm_of P
	  val (Q',tsQ) = combterm_of Q
      in  (CombApp(P',Q'), tsP union tsQ)  end;

fun predicate_of ((Const("Not",_) $ P), polarity) = predicate_of (P, not polarity)
  | predicate_of (t,polarity) = (combterm_of t, polarity);

fun literals_of_term1 args (Const("Trueprop",_) $ P) = literals_of_term1 args P
  | literals_of_term1 args (Const("op |",_) $ P $ Q) = 
      literals_of_term1 (literals_of_term1 args P) Q
  | literals_of_term1 (lits,ts) P =
      let val ((pred,ts'),pol) = predicate_of (P,true)
      in
	  (Literal(pol,pred)::lits, ts union ts')
      end;

fun literals_of_term P = literals_of_term1 ([],[]) P;

(* making axiom and conjecture clauses *)
fun make_clause(clause_id,axiom_name,kind,th) =
    let val (lits,ctypes_sorts) = literals_of_term (to_comb (prop_of th) [])
	val (ctvar_lits,ctfree_lits) = RC.add_typs_aux ctypes_sorts
    in
	if forall isFalse lits
	then error "Problem too trivial for resolution (empty clause)"
	else
	    Clause {clause_id = clause_id, axiom_name = axiom_name, th = th, kind = kind,
		    literals = lits, ctypes_sorts = ctypes_sorts, 
		    ctvar_type_literals = ctvar_lits,
		    ctfree_type_literals = ctfree_lits}
    end;


fun add_axiom_clause ((th,(name,id)), pairs) =
  let val cls = make_clause(id, name, RC.Axiom, th)
  in
      if isTaut cls then pairs else (name,cls)::pairs
  end;

val make_axiom_clauses = foldl add_axiom_clause [];

fun make_conjecture_clauses_aux _ [] = []
  | make_conjecture_clauses_aux n (th::ths) =
      make_clause(n,"conjecture", RC.Conjecture, th) ::
      make_conjecture_clauses_aux (n+1) ths;

val make_conjecture_clauses = make_conjecture_clauses_aux 0;


(**********************************************************************)
(* convert clause into ATP specific formats:                          *)
(* TPTP used by Vampire and E                                         *)
(* DFG used by SPASS                                                  *)
(**********************************************************************)

(*Result of a function type; no need to check that the argument type matches.*)
fun result_type (RC.Comp ("tc_fun", [_, tp2])) = tp2
  | result_type _ = raise ERROR "result_type"

fun type_of_combterm (CombConst(c,tp,_)) = tp
  | type_of_combterm (CombVar(v,tp)) = tp
  | type_of_combterm (CombApp(t1,t2)) = result_type (type_of_combterm t1);

(*gets the head of a combinator application, along with the list of arguments*)
fun strip_comb u =
    let fun stripc (CombApp(t,u), ts) = stripc (t, u::ts)
        |   stripc  x =  x
    in  stripc(u,[])  end;

val type_wrapper = "ti";

fun head_needs_hBOOL (CombConst(c,_,_)) = needs_hBOOL c
  | head_needs_hBOOL _ = true;

fun wrap_type (s, tp) = 
  if !typ_level=T_FULL then
      type_wrapper ^ RC.paren_pack [s, RC.string_of_fol_type tp]
  else s;
    
fun apply ss = "hAPP" ^ RC.paren_pack ss;

(*Full (non-optimized) and partial-typed transations*)
fun string_of_combterm1 (CombConst(c,tp,_)) = 
      let val c' = if c = "equal" then "c_fequal" else c
      in  wrap_type (c',tp)  end
  | string_of_combterm1 (CombVar(v,tp)) = wrap_type (v,tp)
  | string_of_combterm1 (CombApp(t1,t2)) =
      let val s1 = string_of_combterm1 t1
	  and s2 = string_of_combterm1 t2
      in
	  case !typ_level of
	      T_FULL => wrap_type (apply [s1,s2], result_type (type_of_combterm t1))
	    | T_PARTIAL => apply [s1,s2, RC.string_of_fol_type (type_of_combterm t1)]
	    | T_CONST => raise ERROR "string_of_combterm1"
      end;

fun rev_apply (v, []) = v
  | rev_apply (v, arg::args) = apply [rev_apply (v, args), arg];

fun string_apply (v, args) = rev_apply (v, rev args);

(*Apply an operator to the argument strings, using either the "apply" operator or
  direct function application.*)
fun string_of_applic (CombConst(c,tp,tvars), args) =
      let val c = if c = "equal" then "c_fequal" else c
          val nargs = min_arity_of c
          val args1 = List.take(args, nargs)
            handle Subscript => raise ERROR ("string_of_applic: " ^ c ^ " has arity " ^
					     Int.toString nargs ^ " but is applied to " ^ 
					     space_implode ", " args) 
          val args2 = List.drop(args, nargs)
          val targs = if !typ_level = T_CONST then map RC.string_of_fol_type tvars
                      else []
      in
	  string_apply (c ^ RC.paren_pack (args1@targs), args2)
      end
  | string_of_applic (CombVar(v,tp), args) = string_apply (v, args)
  | string_of_applic _ = raise ERROR "string_of_applic";

fun wrap_type_if (head, s, tp) = if head_needs_hBOOL head then wrap_type (s, tp) else s;
    
(*Full (if optimized) and constant-typed transations*)
fun string_of_combterm2 t = 
  let val (head, args) = strip_comb t
  in  wrap_type_if (head, 
                    string_of_applic (head, map string_of_combterm2 args), 
                    type_of_combterm t)
  end;

fun string_of_combterm t = 
    case (!typ_level,!minimize_applies) of
         (T_PARTIAL, _) => string_of_combterm1 t
       | (T_FULL, false) => string_of_combterm1 t
       | _ => string_of_combterm2 t;

(*Boolean-valued terms are here converted to literals.*)
fun boolify t = "hBOOL" ^ RC.paren_pack [string_of_combterm t];

fun string_of_predicate t = 
  case t of
      (CombApp(CombApp(CombConst("equal",_,_), t1), t2)) =>
	  (*DFG only: new TPTP prefers infix equality*)
	  ("equal" ^ RC.paren_pack [string_of_combterm t1, string_of_combterm t2])
    | _ => 
          case #1 (strip_comb t) of
              CombConst(c,_,_) => if needs_hBOOL c then boolify t else string_of_combterm t
            | _ => boolify t;

fun string_of_clausename (cls_id,ax_name) = 
    RC.clause_prefix ^ RC.ascii_of ax_name ^ "_" ^ Int.toString cls_id;

fun string_of_type_clsname (cls_id,ax_name,idx) = 
    string_of_clausename (cls_id,ax_name) ^ "_tcs" ^ (Int.toString idx);


(*** tptp format ***)

fun tptp_of_equality pol (t1,t2) =
  let val eqop = if pol then " = " else " != "
  in  string_of_combterm t1 ^ eqop ^ string_of_combterm t2  end;

fun tptp_literal (Literal(pol, CombApp(CombApp(CombConst("equal",_,_), t1), t2))) = 
      tptp_of_equality pol (t1,t2)
  | tptp_literal (Literal(pol,pred)) = 
      RC.tptp_sign pol (string_of_predicate pred);
 
(*Given a clause, returns its literals paired with a list of literals concerning TFrees;
  the latter should only occur in conjecture clauses.*)
fun tptp_type_lits (Clause cls) = 
    let val lits = map tptp_literal (#literals cls)
	val ctvar_lits_strs = map RC.tptp_of_typeLit (#ctvar_type_literals cls)
	val ctfree_lits = map RC.tptp_of_typeLit (#ctfree_type_literals cls)
    in
	(ctvar_lits_strs @ lits, ctfree_lits)
    end; 
    
fun clause2tptp (cls as Clause{axiom_name,clause_id,kind,ctypes_sorts,...}) =
    let val (lits,ctfree_lits) = tptp_type_lits cls
	val cls_str = RC.gen_tptp_cls(clause_id,axiom_name,kind,lits)
    in
	(cls_str,ctfree_lits)
    end;


(*** dfg format ***)

fun dfg_literal (Literal(pol,pred)) = RC.dfg_sign pol (string_of_predicate pred);

fun dfg_clause_aux (Clause{literals, ctypes_sorts, ...}) = 
  let val lits = map dfg_literal literals
      val (tvar_lits,tfree_lits) = RC.add_typs_aux ctypes_sorts
      val tvar_lits_strs = map RC.dfg_of_typeLit tvar_lits
      val tfree_lits = map RC.dfg_of_typeLit tfree_lits 
  in
      (tvar_lits_strs @ lits, tfree_lits)
  end; 

fun get_uvars (CombConst _) vars = vars
  | get_uvars (CombVar(v,_)) vars = (v::vars)
  | get_uvars (CombApp(P,Q)) vars = get_uvars P (get_uvars Q vars);

fun get_uvars_l (Literal(_,c)) = get_uvars c [];

fun dfg_vars (Clause {literals,...}) = RC.union_all (map get_uvars_l literals);
 
fun clause2dfg (cls as Clause{axiom_name,clause_id,kind,ctypes_sorts,...}) =
    let val (lits,tfree_lits) = dfg_clause_aux cls 
        val vars = dfg_vars cls
        val tvars = RC.get_tvar_strs ctypes_sorts
	val knd = RC.name_of_kind kind
	val lits_str = commas lits
	val cls_str = RC.gen_dfg_cls(clause_id, axiom_name, knd, lits_str, tvars@vars) 
    in (cls_str, tfree_lits) end;

(** For DFG format: accumulate function and predicate declarations **)

fun addtypes tvars tab = foldl RC.add_foltype_funcs tab tvars;

fun add_decls (CombConst(c,tp,tvars), (funcs,preds)) =
      if c = "equal" then (addtypes tvars funcs, preds)
      else
	(case !typ_level of
            T_PARTIAL => (RC.add_foltype_funcs (tp, Symtab.update(c,0) funcs), preds)
	  | _ => 
               let val arity = min_arity_of c 
                   val ntys = if !typ_level = T_CONST then length tvars else 0
                   val addit = Symtab.update(c, arity+ntys) 
               in
                   if needs_hBOOL c then (addtypes tvars (addit funcs), preds)
                   else (addtypes tvars funcs, addit preds)
               end)
  | add_decls (CombVar(_,ctp), (funcs,preds)) = 
      (RC.add_foltype_funcs (ctp,funcs), preds)
  | add_decls (CombApp(P,Q),decls) = add_decls(P,add_decls (Q,decls));

fun add_literal_decls (Literal(_,c), decls) = add_decls (c,decls);

fun add_clause_decls (Clause {literals, ...}, decls) =
    foldl add_literal_decls decls literals
    handle Symtab.DUP a => raise ERROR ("function " ^ a ^ " has multiple arities")

fun decls_of_clauses clauses arity_clauses =
  let val happ_ar = case !typ_level of T_PARTIAL => 3 | _ => 2
      val init_functab = Symtab.update (type_wrapper,2) (Symtab.update ("hAPP",happ_ar) RC.init_functab)
      val init_predtab = Symtab.update ("hBOOL",1) Symtab.empty
      val (functab,predtab) = (foldl add_clause_decls (init_functab, init_predtab) clauses)
  in
      (Symtab.dest (foldl RC.add_arityClause_funcs functab arity_clauses), 
       Symtab.dest predtab)
  end;

fun add_clause_preds (Clause {ctypes_sorts, ...}, preds) =
  foldl RC.add_type_sort_preds preds ctypes_sorts
  handle Symtab.DUP a => raise ERROR ("predicate " ^ a ^ " has multiple arities")

(*Higher-order clauses have only the predicates hBOOL and type classes.*)
fun preds_of_clauses clauses clsrel_clauses arity_clauses = 
    Symtab.dest
	(foldl RC.add_classrelClause_preds 
	       (foldl RC.add_arityClause_preds
		      (foldl add_clause_preds Symtab.empty clauses) 
		      arity_clauses)
	       clsrel_clauses)



(**********************************************************************)
(* write clauses to files                                             *)
(**********************************************************************)


val init_counters =
    Symtab.make [("c_COMBI", 0), ("c_COMBK", 0),
		 ("c_COMBB", 0), ("c_COMBC", 0),
		 ("c_COMBS", 0), ("c_COMBB_e", 0),
		 ("c_COMBC_e", 0), ("c_COMBS_e", 0)];
                
fun count_combterm (CombConst(c,tp,_), ct) = 
     (case Symtab.lookup ct c of NONE => ct  (*no counter*)
                               | SOME n => Symtab.update (c,n+1) ct)
  | count_combterm (CombVar(v,tp), ct) = ct
  | count_combterm (CombApp(t1,t2), ct) = count_combterm(t1, count_combterm(t2, ct));

fun count_literal (Literal(_,t), ct) = count_combterm(t,ct);

fun count_clause (Clause{literals,...}, ct) = foldl count_literal ct literals;

fun count_user_clause user_lemmas (Clause{axiom_name,literals,...}, ct) = 
  if axiom_name mem_string user_lemmas then foldl count_literal ct literals
  else ct;

val cnf_helper_thms = ResAxioms.cnf_rules_pairs o (map ResAxioms.pairname)

fun get_helper_clauses isFO (conjectures, axclauses, user_lemmas) =
  if isFO then []  (*first-order*)
  else
    let val ct0 = foldl count_clause init_counters conjectures
        val ct = foldl (count_user_clause user_lemmas) ct0 axclauses
        fun needed c = valOf (Symtab.lookup ct c) > 0
        val IK = if needed "c_COMBI" orelse needed "c_COMBK" 
                 then (Output.debug (fn () => "Include combinator I K"); cnf_helper_thms [comb_I,comb_K]) 
                 else []
	val BC = if needed "c_COMBB" orelse needed "c_COMBC" 
	         then (Output.debug (fn () => "Include combinator B C"); cnf_helper_thms [comb_B,comb_C]) 
	         else []
	val S = if needed "c_COMBS" 
	        then (Output.debug (fn () => "Include combinator S"); cnf_helper_thms [comb_S]) 
	        else []
	val B'C' = if needed "c_COMBB_e" orelse needed "c_COMBC_e" 
	           then (Output.debug (fn () => "Include combinator B' C'"); cnf_helper_thms [comb_B', comb_C']) 
	           else []
	val S' = if needed "c_COMBS_e" 
	         then (Output.debug (fn () => "Include combinator S'"); cnf_helper_thms [comb_S']) 
	         else []
	val other = cnf_helper_thms [ext,fequal_imp_equal,equal_imp_fequal]
    in
	map #2 (make_axiom_clauses (other @ IK @ BC @ S @ B'C' @ S'))
    end;

(*Find the minimal arity of each function mentioned in the term. Also, note which uses
  are not at top level, to see if hBOOL is needed.*)
fun count_constants_term toplev t =
  let val (head, args) = strip_comb t
      val n = length args
      val _ = List.app (count_constants_term false) args
  in
      case head of
	  CombConst (a,_,_) => (*predicate or function version of "equal"?*)
	    let val a = if a="equal" andalso not toplev then "c_fequal" else a
	    in  
	      const_min_arity := Symtab.map_default (a,n) (curry Int.min n) (!const_min_arity);
	      if toplev then ()
	      else const_needs_hBOOL := Symtab.update (a,true) (!const_needs_hBOOL)
	    end
	| ts => ()
  end;

(*A literal is a top-level term*)
fun count_constants_lit (Literal (_,t)) = count_constants_term true t;

fun count_constants_clause (Clause{literals,...}) = List.app count_constants_lit literals;

fun display_arity (c,n) =
  Output.debug (fn () => "Constant: " ^ c ^ " arity:\t" ^ Int.toString n ^ 
                (if needs_hBOOL c then " needs hBOOL" else ""));

fun count_constants (conjectures, axclauses, helper_clauses) = 
  if !minimize_applies andalso !typ_level<>T_PARTIAL then
    (const_min_arity := Symtab.empty; 
     const_needs_hBOOL := Symtab.empty;
     List.app count_constants_clause conjectures;
     List.app count_constants_clause axclauses;
     List.app count_constants_clause helper_clauses;
     List.app display_arity (Symtab.dest (!const_min_arity)))
  else ();

(* tptp format *)
						  
(* write TPTP format to a single file *)
fun tptp_write_file isFO thms filename (ax_tuples,classrel_clauses,arity_clauses) user_lemmas =
    let val _ = Output.debug (fn () => ("Preparing to write the TPTP file " ^ filename))
        val _ = RC.dfg_format := false
        val conjectures = make_conjecture_clauses thms
        val (clnames,axclauses) = ListPair.unzip (make_axiom_clauses ax_tuples)
	val helper_clauses = get_helper_clauses isFO (conjectures, axclauses, user_lemmas)
	val _ = count_constants (conjectures, axclauses, helper_clauses);
	val (tptp_clss,tfree_litss) = ListPair.unzip (map clause2tptp conjectures)
	val tfree_clss = map RC.tptp_tfree_clause (foldl (op union_string) [] tfree_litss)
        val out = TextIO.openOut filename
    in
	List.app (curry TextIO.output out o #1 o clause2tptp) axclauses;
	RC.writeln_strs out tfree_clss;
	RC.writeln_strs out tptp_clss;
	List.app (curry TextIO.output out o RC.tptp_classrelClause) classrel_clauses;
	List.app (curry TextIO.output out o RC.tptp_arity_clause) arity_clauses;
	List.app (curry TextIO.output out o #1 o clause2tptp) helper_clauses;
	TextIO.closeOut out;
	clnames
    end;



(* dfg format *)

fun dfg_write_file isFO thms filename (ax_tuples,classrel_clauses,arity_clauses) user_lemmas =
    let val _ = Output.debug (fn () => ("Preparing to write the DFG file " ^ filename))
        val _ = RC.dfg_format := true
        val conjectures = make_conjecture_clauses thms
        val (clnames,axclauses) = ListPair.unzip (make_axiom_clauses ax_tuples)
	val helper_clauses = get_helper_clauses isFO (conjectures, axclauses, user_lemmas)
	val _ = count_constants (conjectures, axclauses, helper_clauses);
	val (dfg_clss,tfree_litss) = ListPair.unzip (map clause2dfg conjectures)
	and probname = Path.implode (Path.base (Path.explode filename))
	val axstrs = map (#1 o clause2dfg) axclauses
	val tfree_clss = map RC.dfg_tfree_clause (RC.union_all tfree_litss)
	val out = TextIO.openOut filename
	val helper_clauses_strs = map (#1 o clause2dfg) helper_clauses
	val (funcs,cl_preds) = decls_of_clauses (helper_clauses @ conjectures @ axclauses) arity_clauses
	and ty_preds = preds_of_clauses axclauses classrel_clauses arity_clauses
    in
	TextIO.output (out, RC.string_of_start probname); 
	TextIO.output (out, RC.string_of_descrip probname); 
	TextIO.output (out, RC.string_of_symbols 
	                      (RC.string_of_funcs funcs) 
	                      (RC.string_of_preds (cl_preds @ ty_preds))); 
	TextIO.output (out, "list_of_clauses(axioms,cnf).\n");
	RC.writeln_strs out axstrs;
	List.app (curry TextIO.output out o RC.dfg_classrelClause) classrel_clauses;
	List.app (curry TextIO.output out o RC.dfg_arity_clause) arity_clauses;
	RC.writeln_strs out helper_clauses_strs;
	TextIO.output (out, "end_of_list.\n\nlist_of_clauses(conjectures,cnf).\n");
	RC.writeln_strs out tfree_clss;
	RC.writeln_strs out dfg_clss;
	TextIO.output (out, "end_of_list.\n\n");
	(*VarWeight=3 helps the HO problems, probably by counteracting the presence of hAPP*)
	TextIO.output (out, "list_of_settings(SPASS).\n{*\nset_flag(VarWeight,3).\n*}\nend_of_list.\n\n");
	TextIO.output (out, "end_problem.\n");
	TextIO.closeOut out;
	clnames
    end;

end
