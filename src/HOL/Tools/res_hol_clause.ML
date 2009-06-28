(*
   Author: Jia Meng, NICTA

FOL clauses translated from HOL formulae.
*)

signature RES_HOL_CLAUSE =
sig
  val ext: thm
  val comb_I: thm
  val comb_K: thm
  val comb_B: thm
  val comb_C: thm
  val comb_S: thm
  val minimize_applies: bool
  type axiom_name = string
  type polarity = bool
  type clause_id = int
  datatype combterm =
      CombConst of string * ResClause.fol_type * ResClause.fol_type list (*Const and Free*)
    | CombVar of string * ResClause.fol_type
    | CombApp of combterm * combterm
  datatype literal = Literal of polarity * combterm
  datatype clause = Clause of {clause_id: clause_id, axiom_name: axiom_name, th: thm,
                    kind: ResClause.kind,literals: literal list, ctypes_sorts: typ list}
  val strip_comb: combterm -> combterm * combterm list
  val literals_of_term: theory -> term -> literal list * typ list
  exception TOO_TRIVIAL
  val make_conjecture_clauses:  bool -> theory -> thm list -> clause list
  val make_axiom_clauses: bool ->
       theory ->
       (thm * (axiom_name * clause_id)) list -> (axiom_name * clause) list
  val get_helper_clauses: bool ->
       theory ->
       bool ->
       clause list * (thm * (axiom_name * clause_id)) list * string list ->
       clause list
  val tptp_write_file: bool -> Path.T ->
    clause list * clause list * clause list * ResClause.classrelClause list * ResClause.arityClause list -> unit
  val dfg_write_file: bool -> Path.T ->
    clause list * clause list * clause list * ResClause.classrelClause list * ResClause.arityClause list -> unit
end

structure ResHolClause: RES_HOL_CLAUSE =
struct

structure RC = ResClause;

(* theorems for combinators and function extensionality *)
val ext = thm "HOL.ext";
val comb_I = thm "ATP_Linkup.COMBI_def";
val comb_K = thm "ATP_Linkup.COMBK_def";
val comb_B = thm "ATP_Linkup.COMBB_def";
val comb_C = thm "ATP_Linkup.COMBC_def";
val comb_S = thm "ATP_Linkup.COMBS_def";
val fequal_imp_equal = thm "ATP_Linkup.fequal_imp_equal";
val equal_imp_fequal = thm "ATP_Linkup.equal_imp_fequal";


(* Parameter t_full below indicates that full type information is to be
exported *)

(*If true, each function will be directly applied to as many arguments as possible, avoiding
  use of the "apply" operator. Use of hBOOL is also minimized.*)
val minimize_applies = true;

fun min_arity_of const_min_arity c = getOpt (Symtab.lookup const_min_arity c, 0);

(*True if the constant ever appears outside of the top-level position in literals.
  If false, the constant always receives all of its arguments and is used as a predicate.*)
fun needs_hBOOL const_needs_hBOOL c = not minimize_applies orelse
                    getOpt (Symtab.lookup const_needs_hBOOL c, false);


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
                    ctypes_sorts: typ list};


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

fun type_of dfg (Type (a, Ts)) =
      let val (folTypes,ts) = types_of dfg Ts
      in  (RC.Comp(RC.make_fixed_type_const dfg a, folTypes), ts)  end
  | type_of dfg (tp as (TFree(a,s))) =
      (RC.AtomF (RC.make_fixed_type_var a), [tp])
  | type_of dfg (tp as (TVar(v,s))) =
      (RC.AtomV (RC.make_schematic_type_var v), [tp])
and types_of dfg Ts =
      let val (folTyps,ts) = ListPair.unzip (map (type_of dfg) Ts)
      in  (folTyps, RC.union_all ts)  end;

(* same as above, but no gathering of sort information *)
fun simp_type_of dfg (Type (a, Ts)) =
      RC.Comp(RC.make_fixed_type_const dfg a, map (simp_type_of dfg) Ts)
  | simp_type_of dfg (TFree (a,s)) = RC.AtomF(RC.make_fixed_type_var a)
  | simp_type_of dfg (TVar (v,s)) = RC.AtomV(RC.make_schematic_type_var v);


fun const_type_of dfg thy (c,t) =
      let val (tp,ts) = type_of dfg t
      in  (tp, ts, map (simp_type_of dfg) (Sign.const_typargs thy (c,t))) end;

(* convert a Term.term (with combinators) into a combterm, also accummulate sort info *)
fun combterm_of dfg thy (Const(c,t)) =
      let val (tp,ts,tvar_list) = const_type_of dfg thy (c,t)
          val c' = CombConst(RC.make_fixed_const dfg c, tp, tvar_list)
      in  (c',ts)  end
  | combterm_of dfg thy (Free(v,t)) =
      let val (tp,ts) = type_of dfg t
          val v' = CombConst(RC.make_fixed_var v, tp, [])
      in  (v',ts)  end
  | combterm_of dfg thy (Var(v,t)) =
      let val (tp,ts) = type_of dfg t
          val v' = CombVar(RC.make_schematic_var v,tp)
      in  (v',ts)  end
  | combterm_of dfg thy (P $ Q) =
      let val (P',tsP) = combterm_of dfg thy P
          val (Q',tsQ) = combterm_of dfg thy Q
      in  (CombApp(P',Q'), tsP union tsQ)  end
  | combterm_of _ thy (t as Abs _) = raise RC.CLAUSE("HOL CLAUSE",t);

fun predicate_of dfg thy ((Const("Not",_) $ P), polarity) = predicate_of dfg thy (P, not polarity)
  | predicate_of dfg thy (t,polarity) = (combterm_of dfg thy (Envir.eta_contract t), polarity);

fun literals_of_term1 dfg thy args (Const("Trueprop",_) $ P) = literals_of_term1 dfg thy args P
  | literals_of_term1 dfg thy args (Const("op |",_) $ P $ Q) =
      literals_of_term1 dfg thy (literals_of_term1 dfg thy args P) Q
  | literals_of_term1 dfg thy (lits,ts) P =
      let val ((pred,ts'),pol) = predicate_of dfg thy (P,true)
      in
          (Literal(pol,pred)::lits, ts union ts')
      end;

fun literals_of_term_dfg dfg thy P = literals_of_term1 dfg thy ([],[]) P;
val literals_of_term = literals_of_term_dfg false;

(* Problem too trivial for resolution (empty clause) *)
exception TOO_TRIVIAL;

(* making axiom and conjecture clauses *)
fun make_clause dfg thy (clause_id,axiom_name,kind,th) =
    let val (lits,ctypes_sorts) = literals_of_term_dfg dfg thy (prop_of th)
    in
        if forall isFalse lits
        then raise TOO_TRIVIAL
        else
            Clause {clause_id = clause_id, axiom_name = axiom_name, th = th, kind = kind,
                    literals = lits, ctypes_sorts = ctypes_sorts}
    end;


fun add_axiom_clause dfg thy ((th,(name,id)), pairs) =
  let val cls = make_clause dfg thy (id, name, RC.Axiom, th)
  in
      if isTaut cls then pairs else (name,cls)::pairs
  end;

fun make_axiom_clauses dfg thy = List.foldl (add_axiom_clause dfg thy) [];

fun make_conjecture_clauses_aux dfg _ _ [] = []
  | make_conjecture_clauses_aux dfg thy n (th::ths) =
      make_clause dfg thy (n,"conjecture", RC.Conjecture, th) ::
      make_conjecture_clauses_aux dfg thy (n+1) ths;

fun make_conjecture_clauses dfg thy = make_conjecture_clauses_aux dfg thy 0;


(**********************************************************************)
(* convert clause into ATP specific formats:                          *)
(* TPTP used by Vampire and E                                         *)
(* DFG used by SPASS                                                  *)
(**********************************************************************)

(*Result of a function type; no need to check that the argument type matches.*)
fun result_type (RC.Comp ("tc_fun", [_, tp2])) = tp2
  | result_type _ = error "result_type"

fun type_of_combterm (CombConst(c,tp,_)) = tp
  | type_of_combterm (CombVar(v,tp)) = tp
  | type_of_combterm (CombApp(t1,t2)) = result_type (type_of_combterm t1);

(*gets the head of a combinator application, along with the list of arguments*)
fun strip_comb u =
    let fun stripc (CombApp(t,u), ts) = stripc (t, u::ts)
        |   stripc  x =  x
    in  stripc(u,[])  end;

val type_wrapper = "ti";

fun head_needs_hBOOL const_needs_hBOOL (CombConst(c,_,_)) = needs_hBOOL const_needs_hBOOL c
  | head_needs_hBOOL const_needs_hBOOL _ = true;

fun wrap_type t_full (s, tp) =
  if t_full then
      type_wrapper ^ RC.paren_pack [s, RC.string_of_fol_type tp]
  else s;

fun apply ss = "hAPP" ^ RC.paren_pack ss;

fun rev_apply (v, []) = v
  | rev_apply (v, arg::args) = apply [rev_apply (v, args), arg];

fun string_apply (v, args) = rev_apply (v, rev args);

(*Apply an operator to the argument strings, using either the "apply" operator or
  direct function application.*)
fun string_of_applic t_full cma (CombConst(c,tp,tvars), args) =
      let val c = if c = "equal" then "c_fequal" else c
          val nargs = min_arity_of cma c
          val args1 = List.take(args, nargs)
            handle Subscript => error ("string_of_applic: " ^ c ^ " has arity " ^
                                         Int.toString nargs ^ " but is applied to " ^
                                         space_implode ", " args)
          val args2 = List.drop(args, nargs)
          val targs = if not t_full then map RC.string_of_fol_type tvars
                      else []
      in
          string_apply (c ^ RC.paren_pack (args1@targs), args2)
      end
  | string_of_applic _ cma (CombVar(v,tp), args) = string_apply (v, args)
  | string_of_applic _ _ _ = error "string_of_applic";

fun wrap_type_if t_full cnh (head, s, tp) =
  if head_needs_hBOOL cnh head then wrap_type t_full (s, tp) else s;

fun string_of_combterm (params as (t_full, cma, cnh)) t =
  let val (head, args) = strip_comb t
  in  wrap_type_if t_full cnh (head,
                    string_of_applic t_full cma (head, map (string_of_combterm (params)) args),
                    type_of_combterm t)
  end;

(*Boolean-valued terms are here converted to literals.*)
fun boolify params t =
  "hBOOL" ^ RC.paren_pack [string_of_combterm params t];

fun string_of_predicate (params as (_,_,cnh)) t =
  case t of
      (CombApp(CombApp(CombConst("equal",_,_), t1), t2)) =>
          (*DFG only: new TPTP prefers infix equality*)
          ("equal" ^ RC.paren_pack [string_of_combterm params t1, string_of_combterm params t2])
    | _ =>
          case #1 (strip_comb t) of
              CombConst(c,_,_) => if needs_hBOOL cnh c then boolify params t else string_of_combterm params t
            | _ => boolify params t;

fun string_of_clausename (cls_id,ax_name) =
    RC.clause_prefix ^ RC.ascii_of ax_name ^ "_" ^ Int.toString cls_id;

fun string_of_type_clsname (cls_id,ax_name,idx) =
    string_of_clausename (cls_id,ax_name) ^ "_tcs" ^ (Int.toString idx);


(*** tptp format ***)

fun tptp_of_equality params pol (t1,t2) =
  let val eqop = if pol then " = " else " != "
  in  string_of_combterm params t1 ^ eqop ^ string_of_combterm params t2  end;

fun tptp_literal params (Literal(pol, CombApp(CombApp(CombConst("equal",_,_), t1), t2))) =
      tptp_of_equality params pol (t1,t2)
  | tptp_literal params (Literal(pol,pred)) =
      RC.tptp_sign pol (string_of_predicate params pred);

(*Given a clause, returns its literals paired with a list of literals concerning TFrees;
  the latter should only occur in conjecture clauses.*)
fun tptp_type_lits params pos (Clause{literals, ctypes_sorts, ...}) =
      (map (tptp_literal params) literals, 
       map (RC.tptp_of_typeLit pos) (RC.add_typs ctypes_sorts));

fun clause2tptp params (cls as Clause{axiom_name,clause_id,kind,ctypes_sorts,...}) =
  let val (lits,tylits) = tptp_type_lits params (kind = RC.Conjecture) cls
  in
      (RC.gen_tptp_cls(clause_id,axiom_name,kind,lits,tylits), tylits)
  end;


(*** dfg format ***)

fun dfg_literal params (Literal(pol,pred)) = RC.dfg_sign pol (string_of_predicate params pred);

fun dfg_type_lits params pos (Clause{literals, ctypes_sorts, ...}) =
      (map (dfg_literal params) literals, 
       map (RC.dfg_of_typeLit pos) (RC.add_typs ctypes_sorts));

fun get_uvars (CombConst _) vars = vars
  | get_uvars (CombVar(v,_)) vars = (v::vars)
  | get_uvars (CombApp(P,Q)) vars = get_uvars P (get_uvars Q vars);

fun get_uvars_l (Literal(_,c)) = get_uvars c [];

fun dfg_vars (Clause {literals,...}) = RC.union_all (map get_uvars_l literals);

fun clause2dfg params (cls as Clause{axiom_name,clause_id,kind,ctypes_sorts,...}) =
  let val (lits,tylits) = dfg_type_lits params (kind = RC.Conjecture) cls
      val vars = dfg_vars cls
      val tvars = RC.get_tvar_strs ctypes_sorts
  in
      (RC.gen_dfg_cls(clause_id, axiom_name, kind, lits, tylits, tvars@vars), tylits)
  end;


(** For DFG format: accumulate function and predicate declarations **)

fun addtypes tvars tab = List.foldl RC.add_foltype_funcs tab tvars;

fun add_decls (t_full, cma, cnh) (CombConst(c,tp,tvars), (funcs,preds)) =
      if c = "equal" then (addtypes tvars funcs, preds)
      else
	let val arity = min_arity_of cma c
	    val ntys = if not t_full then length tvars else 0
	    val addit = Symtab.update(c, arity+ntys)
	in
	    if needs_hBOOL cnh c then (addtypes tvars (addit funcs), preds)
	    else (addtypes tvars funcs, addit preds)
	end
  | add_decls _ (CombVar(_,ctp), (funcs,preds)) =
      (RC.add_foltype_funcs (ctp,funcs), preds)
  | add_decls params (CombApp(P,Q),decls) = add_decls params (P,add_decls params (Q,decls));

fun add_literal_decls params (Literal(_,c), decls) = add_decls params (c,decls);

fun add_clause_decls params (Clause {literals, ...}, decls) =
    List.foldl (add_literal_decls params) decls literals
    handle Symtab.DUP a => error ("function " ^ a ^ " has multiple arities")

fun decls_of_clauses params clauses arity_clauses =
  let val init_functab = Symtab.update (type_wrapper,2) (Symtab.update ("hAPP",2) RC.init_functab)
      val init_predtab = Symtab.update ("hBOOL",1) Symtab.empty
      val (functab,predtab) = (List.foldl (add_clause_decls params) (init_functab, init_predtab) clauses)
  in
      (Symtab.dest (List.foldl RC.add_arityClause_funcs functab arity_clauses),
       Symtab.dest predtab)
  end;

fun add_clause_preds (Clause {ctypes_sorts, ...}, preds) =
  List.foldl RC.add_type_sort_preds preds ctypes_sorts
  handle Symtab.DUP a => error ("predicate " ^ a ^ " has multiple arities")

(*Higher-order clauses have only the predicates hBOOL and type classes.*)
fun preds_of_clauses clauses clsrel_clauses arity_clauses =
    Symtab.dest
        (List.foldl RC.add_classrelClause_preds
               (List.foldl RC.add_arityClause_preds
                      (List.foldl add_clause_preds Symtab.empty clauses)
                      arity_clauses)
               clsrel_clauses)


(**********************************************************************)
(* write clauses to files                                             *)
(**********************************************************************)

val init_counters =
    Symtab.make [("c_COMBI", 0), ("c_COMBK", 0),
                 ("c_COMBB", 0), ("c_COMBC", 0),
                 ("c_COMBS", 0)];

fun count_combterm (CombConst(c,tp,_), ct) =
     (case Symtab.lookup ct c of NONE => ct  (*no counter*)
                               | SOME n => Symtab.update (c,n+1) ct)
  | count_combterm (CombVar(v,tp), ct) = ct
  | count_combterm (CombApp(t1,t2), ct) = count_combterm(t1, count_combterm(t2, ct));

fun count_literal (Literal(_,t), ct) = count_combterm(t,ct);

fun count_clause (Clause{literals,...}, ct) = List.foldl count_literal ct literals;

fun count_user_clause user_lemmas (Clause{axiom_name,literals,...}, ct) =
  if axiom_name mem_string user_lemmas then List.foldl count_literal ct literals
  else ct;

fun cnf_helper_thms thy =
  ResAxioms.cnf_rules_pairs thy o map ResAxioms.pairname

fun get_helper_clauses dfg thy isFO (conjectures, axcls, user_lemmas) =
  if isFO then []  (*first-order*)
  else
    let
        val axclauses = map #2 (make_axiom_clauses dfg thy axcls)
        val ct0 = List.foldl count_clause init_counters conjectures
        val ct = List.foldl (count_user_clause user_lemmas) ct0 axclauses
        fun needed c = valOf (Symtab.lookup ct c) > 0
        val IK = if needed "c_COMBI" orelse needed "c_COMBK"
                 then (Output.debug (fn () => "Include combinator I K"); cnf_helper_thms thy [comb_I,comb_K])
                 else []
        val BC = if needed "c_COMBB" orelse needed "c_COMBC"
                 then (Output.debug (fn () => "Include combinator B C"); cnf_helper_thms thy [comb_B,comb_C])
                 else []
        val S = if needed "c_COMBS"
                then (Output.debug (fn () => "Include combinator S"); cnf_helper_thms thy [comb_S])
                else []
        val other = cnf_helper_thms thy [fequal_imp_equal,equal_imp_fequal]
    in
        map #2 (make_axiom_clauses dfg thy (other @ IK @ BC @ S))
    end;

(*Find the minimal arity of each function mentioned in the term. Also, note which uses
  are not at top level, to see if hBOOL is needed.*)
fun count_constants_term toplev t (const_min_arity, const_needs_hBOOL) =
  let val (head, args) = strip_comb t
      val n = length args
      val (const_min_arity, const_needs_hBOOL) = fold (count_constants_term false) args (const_min_arity, const_needs_hBOOL)
  in
      case head of
          CombConst (a,_,_) => (*predicate or function version of "equal"?*)
            let val a = if a="equal" andalso not toplev then "c_fequal" else a
            val const_min_arity = Symtab.map_default (a,n) (curry Int.min n) const_min_arity
            in
              if toplev then (const_min_arity, const_needs_hBOOL)
              else (const_min_arity, Symtab.update (a,true) (const_needs_hBOOL))
            end
        | ts => (const_min_arity, const_needs_hBOOL)
  end;

(*A literal is a top-level term*)
fun count_constants_lit (Literal (_,t)) (const_min_arity, const_needs_hBOOL) =
  count_constants_term true t (const_min_arity, const_needs_hBOOL);

fun count_constants_clause (Clause{literals,...}) (const_min_arity, const_needs_hBOOL) =
  fold count_constants_lit literals (const_min_arity, const_needs_hBOOL);

fun display_arity const_needs_hBOOL (c,n) =
  Output.debug (fn () => "Constant: " ^ c ^ " arity:\t" ^ Int.toString n ^
                (if needs_hBOOL const_needs_hBOOL c then " needs hBOOL" else ""));

fun count_constants (conjectures, axclauses, helper_clauses, _, _) =
  if minimize_applies then
     let val (const_min_arity, const_needs_hBOOL) =
          fold count_constants_clause conjectures (Symtab.empty, Symtab.empty)
       |> fold count_constants_clause axclauses
       |> fold count_constants_clause helper_clauses
     val _ = List.app (display_arity const_needs_hBOOL) (Symtab.dest (const_min_arity))
     in (const_min_arity, const_needs_hBOOL) end
  else (Symtab.empty, Symtab.empty);

(* tptp format *)

fun tptp_write_file t_full file clauses =
  let
    val (conjectures, axclauses, helper_clauses, classrel_clauses, arity_clauses) = clauses
    val (cma, cnh) = count_constants clauses
    val params = (t_full, cma, cnh)
    val (tptp_clss,tfree_litss) = ListPair.unzip (map (clause2tptp params) conjectures)
    val tfree_clss = map RC.tptp_tfree_clause (List.foldl (op union_string) [] tfree_litss)
  in
    File.write_list file (
      map (#1 o (clause2tptp params)) axclauses @
      tfree_clss @
      tptp_clss @
      map RC.tptp_classrelClause classrel_clauses @
      map RC.tptp_arity_clause arity_clauses @
      map (#1 o (clause2tptp params)) helper_clauses)
  end;


(* dfg format *)

fun dfg_write_file t_full file clauses =
  let
    val (conjectures, axclauses, helper_clauses, classrel_clauses, arity_clauses) = clauses
    val (cma, cnh) = count_constants clauses
    val params = (t_full, cma, cnh)
    val (dfg_clss, tfree_litss) = ListPair.unzip (map (clause2dfg params) conjectures)
    and probname = Path.implode (Path.base file)
    val axstrs = map (#1 o (clause2dfg params)) axclauses
    val tfree_clss = map RC.dfg_tfree_clause (RC.union_all tfree_litss)
    val helper_clauses_strs = map (#1 o (clause2dfg params)) helper_clauses
    val (funcs,cl_preds) = decls_of_clauses params (helper_clauses @ conjectures @ axclauses) arity_clauses
    and ty_preds = preds_of_clauses axclauses classrel_clauses arity_clauses
  in
    File.write_list file (
      RC.string_of_start probname ::
      RC.string_of_descrip probname ::
      RC.string_of_symbols (RC.string_of_funcs funcs)
        (RC.string_of_preds (cl_preds @ ty_preds)) ::
      "list_of_clauses(axioms,cnf).\n" ::
      axstrs @
      map RC.dfg_classrelClause classrel_clauses @
      map RC.dfg_arity_clause arity_clauses @
      helper_clauses_strs @
      ["end_of_list.\n\nlist_of_clauses(conjectures,cnf).\n"] @
      tfree_clss @
      dfg_clss @
      ["end_of_list.\n\n",
      (*VarWeight=3 helps the HO problems, probably by counteracting the presence of hAPP*)
       "list_of_settings(SPASS).\n{*\nset_flag(VarWeight,3).\n*}\nend_of_list.\n\n",
       "end_problem.\n"])
  end;

end
