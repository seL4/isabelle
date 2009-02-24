(* ID: $Id$
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
  datatype type_level = T_FULL | T_CONST
  val typ_level: type_level ref
  val minimize_applies: bool ref
  type axiom_name = string
  type polarity = bool
  type clause_id = int
  datatype combterm =
      CombConst of string * ResClause.fol_type * ResClause.fol_type list (*Const and Free*)
    | CombVar of string * ResClause.fol_type
    | CombApp of combterm * combterm
  datatype literal = Literal of polarity * combterm
  val strip_comb: combterm -> combterm * combterm list
  val literals_of_term: theory -> term -> literal list * typ list
  exception TOO_TRIVIAL
  val tptp_write_file: theory -> bool -> thm list -> string ->
    (thm * (axiom_name * clause_id)) list * ResClause.classrelClause list *
      ResClause.arityClause list -> string list -> axiom_name list
  val dfg_write_file: theory -> bool -> thm list -> string ->
    (thm * (axiom_name * clause_id)) list * ResClause.classrelClause list *
      ResClause.arityClause list -> string list -> axiom_name list
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


(*The different translations of types*)
datatype type_level = T_FULL | T_CONST;

val typ_level = ref T_CONST;

(*If true, each function will be directly applied to as many arguments as possible, avoiding
  use of the "apply" operator. Use of hBOOL is also minimized.*)
val minimize_applies = ref true;

val const_needs_hBOOL = ref (Symtab.empty : bool Symtab.table);

fun min_arity_of const_min_arity c = getOpt (Symtab.lookup const_min_arity c, 0);

(*True if the constant ever appears outside of the top-level position in literals.
  If false, the constant always receives all of its arguments and is used as a predicate.*)
fun needs_hBOOL c = not (!minimize_applies) orelse
                    getOpt (Symtab.lookup(!const_needs_hBOOL) c, false);


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

fun type_of (Type (a, Ts)) =
      let val (folTypes,ts) = types_of Ts
      in  (RC.Comp(RC.make_fixed_type_const a, folTypes), ts)  end
  | type_of (tp as (TFree(a,s))) =
      (RC.AtomF (RC.make_fixed_type_var a), [tp])
  | type_of (tp as (TVar(v,s))) =
      (RC.AtomV (RC.make_schematic_type_var v), [tp])
and types_of Ts =
      let val (folTyps,ts) = ListPair.unzip (map type_of Ts)
      in  (folTyps, RC.union_all ts)  end;

(* same as above, but no gathering of sort information *)
fun simp_type_of (Type (a, Ts)) =
      RC.Comp(RC.make_fixed_type_const a, map simp_type_of Ts)
  | simp_type_of (TFree (a,s)) = RC.AtomF(RC.make_fixed_type_var a)
  | simp_type_of (TVar (v,s)) = RC.AtomV(RC.make_schematic_type_var v);


fun const_type_of thy (c,t) =
      let val (tp,ts) = type_of t
      in  (tp, ts, map simp_type_of (Sign.const_typargs thy (c,t))) end;

(* convert a Term.term (with combinators) into a combterm, also accummulate sort info *)
fun combterm_of thy (Const(c,t)) =
      let val (tp,ts,tvar_list) = const_type_of thy (c,t)
          val c' = CombConst(RC.make_fixed_const c, tp, tvar_list)
      in  (c',ts)  end
  | combterm_of thy (Free(v,t)) =
      let val (tp,ts) = type_of t
          val v' = CombConst(RC.make_fixed_var v, tp, [])
      in  (v',ts)  end
  | combterm_of thy (Var(v,t)) =
      let val (tp,ts) = type_of t
          val v' = CombVar(RC.make_schematic_var v,tp)
      in  (v',ts)  end
  | combterm_of thy (P $ Q) =
      let val (P',tsP) = combterm_of thy P
          val (Q',tsQ) = combterm_of thy Q
      in  (CombApp(P',Q'), tsP union tsQ)  end
  | combterm_of thy (t as Abs _) = raise RC.CLAUSE("HOL CLAUSE",t);

fun predicate_of thy ((Const("Not",_) $ P), polarity) = predicate_of thy (P, not polarity)
  | predicate_of thy (t,polarity) = (combterm_of thy (Envir.eta_contract t), polarity);

fun literals_of_term1 thy args (Const("Trueprop",_) $ P) = literals_of_term1 thy args P
  | literals_of_term1 thy args (Const("op |",_) $ P $ Q) =
      literals_of_term1 thy (literals_of_term1 thy args P) Q
  | literals_of_term1 thy (lits,ts) P =
      let val ((pred,ts'),pol) = predicate_of thy (P,true)
      in
          (Literal(pol,pred)::lits, ts union ts')
      end;

fun literals_of_term thy P = literals_of_term1 thy ([],[]) P;

(* Problem too trivial for resolution (empty clause) *)
exception TOO_TRIVIAL;

(* making axiom and conjecture clauses *)
fun make_clause thy (clause_id,axiom_name,kind,th) =
    let val (lits,ctypes_sorts) = literals_of_term thy (prop_of th)
    in
        if forall isFalse lits
        then raise TOO_TRIVIAL
        else
            Clause {clause_id = clause_id, axiom_name = axiom_name, th = th, kind = kind,
                    literals = lits, ctypes_sorts = ctypes_sorts}
    end;


fun add_axiom_clause thy ((th,(name,id)), pairs) =
  let val cls = make_clause thy (id, name, RC.Axiom, th)
  in
      if isTaut cls then pairs else (name,cls)::pairs
  end;

fun make_axiom_clauses thy = foldl (add_axiom_clause thy) [];

fun make_conjecture_clauses_aux _ _ [] = []
  | make_conjecture_clauses_aux thy n (th::ths) =
      make_clause thy (n,"conjecture", RC.Conjecture, th) ::
      make_conjecture_clauses_aux thy (n+1) ths;

fun make_conjecture_clauses thy = make_conjecture_clauses_aux thy 0;


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

fun head_needs_hBOOL (CombConst(c,_,_)) = needs_hBOOL c
  | head_needs_hBOOL _ = true;

fun wrap_type (s, tp) =
  if !typ_level=T_FULL then
      type_wrapper ^ RC.paren_pack [s, RC.string_of_fol_type tp]
  else s;

fun apply ss = "hAPP" ^ RC.paren_pack ss;

fun rev_apply (v, []) = v
  | rev_apply (v, arg::args) = apply [rev_apply (v, args), arg];

fun string_apply (v, args) = rev_apply (v, rev args);

(*Apply an operator to the argument strings, using either the "apply" operator or
  direct function application.*)
fun string_of_applic const_min_arity (CombConst(c,tp,tvars), args) =
      let val c = if c = "equal" then "c_fequal" else c
          val nargs = min_arity_of const_min_arity c
          val args1 = List.take(args, nargs)
            handle Subscript => error ("string_of_applic: " ^ c ^ " has arity " ^
                                         Int.toString nargs ^ " but is applied to " ^
                                         space_implode ", " args)
          val args2 = List.drop(args, nargs)
          val targs = if !typ_level = T_CONST then map RC.string_of_fol_type tvars
                      else []
      in
          string_apply (c ^ RC.paren_pack (args1@targs), args2)
      end
  | string_of_applic const_min_arity (CombVar(v,tp), args) = string_apply (v, args)
  | string_of_applic _ _ = error "string_of_applic";

fun wrap_type_if (head, s, tp) = if head_needs_hBOOL head then wrap_type (s, tp) else s;

fun string_of_combterm const_min_arity t =
  let val (head, args) = strip_comb t
  in  wrap_type_if (head,
                    string_of_applic const_min_arity (head, map (string_of_combterm const_min_arity) args),
                    type_of_combterm t)
  end;

(*Boolean-valued terms are here converted to literals.*)
fun boolify const_min_arity t = "hBOOL" ^ RC.paren_pack [string_of_combterm const_min_arity t];

fun string_of_predicate const_min_arity t =
  case t of
      (CombApp(CombApp(CombConst("equal",_,_), t1), t2)) =>
          (*DFG only: new TPTP prefers infix equality*)
          ("equal" ^ RC.paren_pack [string_of_combterm const_min_arity t1, string_of_combterm const_min_arity t2])
    | _ =>
          case #1 (strip_comb t) of
              CombConst(c,_,_) => if needs_hBOOL c then boolify const_min_arity t else string_of_combterm const_min_arity t
            | _ => boolify const_min_arity t;

fun string_of_clausename (cls_id,ax_name) =
    RC.clause_prefix ^ RC.ascii_of ax_name ^ "_" ^ Int.toString cls_id;

fun string_of_type_clsname (cls_id,ax_name,idx) =
    string_of_clausename (cls_id,ax_name) ^ "_tcs" ^ (Int.toString idx);


(*** tptp format ***)

fun tptp_of_equality const_min_arity pol (t1,t2) =
  let val eqop = if pol then " = " else " != "
  in  string_of_combterm const_min_arity t1 ^ eqop ^ string_of_combterm const_min_arity t2  end;

fun tptp_literal const_min_arity (Literal(pol, CombApp(CombApp(CombConst("equal",_,_), t1), t2))) =
      tptp_of_equality const_min_arity pol (t1,t2)
  | tptp_literal const_min_arity (Literal(pol,pred)) =
      RC.tptp_sign pol (string_of_predicate const_min_arity pred);

(*Given a clause, returns its literals paired with a list of literals concerning TFrees;
  the latter should only occur in conjecture clauses.*)
fun tptp_type_lits const_min_arity pos (Clause{literals, ctypes_sorts, ...}) =
      (map (tptp_literal const_min_arity) literals, 
       map (RC.tptp_of_typeLit pos) (RC.add_typs ctypes_sorts));

fun clause2tptp const_min_arity (cls as Clause{axiom_name,clause_id,kind,ctypes_sorts,...}) =
  let val (lits,tylits) = tptp_type_lits const_min_arity (kind = RC.Conjecture) cls
  in
      (RC.gen_tptp_cls(clause_id,axiom_name,kind,lits,tylits), tylits)
  end;


(*** dfg format ***)

fun dfg_literal const_min_arity (Literal(pol,pred)) = RC.dfg_sign pol (string_of_predicate const_min_arity pred);

fun dfg_type_lits const_min_arity pos (Clause{literals, ctypes_sorts, ...}) =
      (map (dfg_literal const_min_arity) literals, 
       map (RC.dfg_of_typeLit pos) (RC.add_typs ctypes_sorts));

fun get_uvars (CombConst _) vars = vars
  | get_uvars (CombVar(v,_)) vars = (v::vars)
  | get_uvars (CombApp(P,Q)) vars = get_uvars P (get_uvars Q vars);

fun get_uvars_l (Literal(_,c)) = get_uvars c [];

fun dfg_vars (Clause {literals,...}) = RC.union_all (map get_uvars_l literals);

fun clause2dfg const_min_arity (cls as Clause{axiom_name,clause_id,kind,ctypes_sorts,...}) =
  let val (lits,tylits) = dfg_type_lits const_min_arity (kind = RC.Conjecture) cls
      val vars = dfg_vars cls
      val tvars = RC.get_tvar_strs ctypes_sorts
  in
      (RC.gen_dfg_cls(clause_id, axiom_name, kind, lits, tylits, tvars@vars), tylits)
  end;


(** For DFG format: accumulate function and predicate declarations **)

fun addtypes tvars tab = foldl RC.add_foltype_funcs tab tvars;

fun add_decls const_min_arity (CombConst(c,tp,tvars), (funcs,preds)) =
      if c = "equal" then (addtypes tvars funcs, preds)
      else
	let val arity = min_arity_of const_min_arity c
	    val ntys = if !typ_level = T_CONST then length tvars else 0
	    val addit = Symtab.update(c, arity+ntys)
	in
	    if needs_hBOOL c then (addtypes tvars (addit funcs), preds)
	    else (addtypes tvars funcs, addit preds)
	end
  | add_decls _ (CombVar(_,ctp), (funcs,preds)) =
      (RC.add_foltype_funcs (ctp,funcs), preds)
  | add_decls const_min_arity (CombApp(P,Q),decls) = add_decls const_min_arity (P,add_decls const_min_arity (Q,decls));

fun add_literal_decls const_min_arity (Literal(_,c), decls) = add_decls const_min_arity (c,decls);

fun add_clause_decls const_min_arity (Clause {literals, ...}, decls) =
    foldl (add_literal_decls const_min_arity) decls literals
    handle Symtab.DUP a => error ("function " ^ a ^ " has multiple arities")

fun decls_of_clauses const_min_arity clauses arity_clauses =
  let val init_functab = Symtab.update (type_wrapper,2) (Symtab.update ("hAPP",2) RC.init_functab)
      val init_predtab = Symtab.update ("hBOOL",1) Symtab.empty
      val (functab,predtab) = (foldl (add_clause_decls const_min_arity) (init_functab, init_predtab) clauses)
  in
      (Symtab.dest (foldl RC.add_arityClause_funcs functab arity_clauses),
       Symtab.dest predtab)
  end;

fun add_clause_preds (Clause {ctypes_sorts, ...}, preds) =
  foldl RC.add_type_sort_preds preds ctypes_sorts
  handle Symtab.DUP a => error ("predicate " ^ a ^ " has multiple arities")

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
                 ("c_COMBS", 0)];

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

fun cnf_helper_thms thy =
  ResAxioms.cnf_rules_pairs thy o map ResAxioms.pairname

fun get_helper_clauses thy isFO (conjectures, axclauses, user_lemmas) =
  if isFO then []  (*first-order*)
  else
    let val ct0 = foldl count_clause init_counters conjectures
        val ct = foldl (count_user_clause user_lemmas) ct0 axclauses
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
        val other = cnf_helper_thms thy [ext,fequal_imp_equal,equal_imp_fequal]
    in
        map #2 (make_axiom_clauses thy (other @ IK @ BC @ S))
    end;

(*Find the minimal arity of each function mentioned in the term. Also, note which uses
  are not at top level, to see if hBOOL is needed.*)
fun count_constants_term toplev t const_min_arity =
  let val (head, args) = strip_comb t
      val n = length args
      val const_min_arity = fold (count_constants_term false) args const_min_arity
  in
      case head of
          CombConst (a,_,_) => (*predicate or function version of "equal"?*)
            let val a = if a="equal" andalso not toplev then "c_fequal" else a
            val const_min_arity = Symtab.map_default (a,n) (curry Int.min n) const_min_arity
            in
              if toplev then const_min_arity
              else (const_needs_hBOOL := Symtab.update (a,true) (!const_needs_hBOOL);
                const_min_arity)
            end
        | ts => const_min_arity
  end;

(*A literal is a top-level term*)
fun count_constants_lit (Literal (_,t)) const_min_arity = count_constants_term true t const_min_arity;

fun count_constants_clause (Clause{literals,...}) const_min_arity =
  fold count_constants_lit literals const_min_arity;

fun display_arity (c,n) =
  Output.debug (fn () => "Constant: " ^ c ^ " arity:\t" ^ Int.toString n ^
                (if needs_hBOOL c then " needs hBOOL" else ""));

fun count_constants (conjectures, axclauses, helper_clauses) =
  if !minimize_applies then
    (const_needs_hBOOL := Symtab.empty;
     let val const_min_arity =
          fold count_constants_clause conjectures Symtab.empty
       |> fold count_constants_clause axclauses
       |> fold count_constants_clause helper_clauses
     val _ = List.app display_arity (Symtab.dest (const_min_arity))
     in const_min_arity end) 
  else Symtab.empty;

(* tptp format *)

(* write TPTP format to a single file *)
fun tptp_write_file thy isFO thms filename (ax_tuples,classrel_clauses,arity_clauses) user_lemmas =
    let val _ = Output.debug (fn () => ("Preparing to write the TPTP file " ^ filename))
        val _ = RC.dfg_format := false
        val conjectures = make_conjecture_clauses thy thms
        val (clnames,axclauses) = ListPair.unzip (make_axiom_clauses thy ax_tuples)
        val helper_clauses = get_helper_clauses thy isFO (conjectures, axclauses, user_lemmas)
        val const_min_arity = count_constants (conjectures, axclauses, helper_clauses);
        val (tptp_clss,tfree_litss) = ListPair.unzip (map (clause2tptp const_min_arity) conjectures)
        val tfree_clss = map RC.tptp_tfree_clause (foldl (op union_string) [] tfree_litss)
        val out = TextIO.openOut filename
    in
        List.app (curry TextIO.output out o #1 o (clause2tptp const_min_arity)) axclauses;
        RC.writeln_strs out tfree_clss;
        RC.writeln_strs out tptp_clss;
        List.app (curry TextIO.output out o RC.tptp_classrelClause) classrel_clauses;
        List.app (curry TextIO.output out o RC.tptp_arity_clause) arity_clauses;
        List.app (curry TextIO.output out o #1 o (clause2tptp const_min_arity)) helper_clauses;
        TextIO.closeOut out;
        clnames
    end;


(* dfg format *)

fun dfg_write_file thy isFO thms filename (ax_tuples,classrel_clauses,arity_clauses) user_lemmas =
    let val _ = Output.debug (fn () => ("Preparing to write the DFG file " ^ filename))
        val _ = RC.dfg_format := true
        val conjectures = make_conjecture_clauses thy thms
        val (clnames,axclauses) = ListPair.unzip (make_axiom_clauses thy ax_tuples)
        val helper_clauses = get_helper_clauses thy isFO (conjectures, axclauses, user_lemmas)
        val const_min_arity = count_constants (conjectures, axclauses, helper_clauses);
        val (dfg_clss, tfree_litss) = ListPair.unzip (map (clause2dfg const_min_arity) conjectures)
        and probname = Path.implode (Path.base (Path.explode filename))
        val axstrs = map (#1 o (clause2dfg const_min_arity)) axclauses
        val tfree_clss = map RC.dfg_tfree_clause (RC.union_all tfree_litss)
        val out = TextIO.openOut filename
        val helper_clauses_strs = map (#1 o (clause2dfg const_min_arity)) helper_clauses
        val (funcs,cl_preds) = decls_of_clauses const_min_arity (helper_clauses @ conjectures @ axclauses) arity_clauses
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
