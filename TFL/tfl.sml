(*  Title:      TFL/tfl
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Main module
*)

structure Prim : TFL_sig =
struct

(* Abbreviations *)
structure R = Rules;
structure S = USyntax;
structure U = S.Utils;

val concl = #2 o R.dest_thm;
val hyp = #1 o R.dest_thm;

val list_mk_type = U.end_itlist (curry(op -->));

fun gtake f =
  let fun grab(0,rst) = ([],rst)
        | grab(n, x::rst) = 
             let val (taken,left) = grab(n-1,rst)
             in (f x::taken, left) end
  in grab
  end;

fun enumerate L = 
 rev(#1(U.rev_itlist (fn x => fn (alist,i) => ((x,i)::alist, i+1)) L ([],0)));

fun stringize [] = ""
  | stringize [i] = Int.toString i
  | stringize (h::t) = (Int.toString h^", "^stringize t);


fun TFL_ERR{func,mesg} = U.ERR{module = "Tfl", func = func, mesg = mesg};


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
  let val slist = ref names
      val vname = ref "u"
      fun new() = 
         if !vname mem_string (!slist)
         then (vname := bump_string (!vname);  new())
         else (slist := !vname :: !slist;  !vname)
  in 
  fn ty => Free(new(), ty)
  end;


(*---------------------------------------------------------------------------
 * Used in induction theorem production. This is the simple case of
 * partitioning up pattern rows by the leading constructor.
 *---------------------------------------------------------------------------*)
fun ipartition gv (constructors,rows) =
  let fun pfail s = raise TFL_ERR{func = "partition.part", mesg = s}
      fun part {constrs = [],   rows = [],   A} = rev A
        | part {constrs = [],   rows = _::_, A} = pfail"extra cases in defn"
        | part {constrs = _::_, rows = [],   A} = pfail"cases missing in defn"
        | part {constrs = c::crst, rows,     A} =
          let val (Name,Ty) = dest_Const c
              val L = binder_types Ty
              val (in_group, not_in_group) =
               U.itlist (fn (row as (p::rst, rhs)) =>
                         fn (in_group,not_in_group) =>
                  let val (pc,args) = S.strip_comb p
                  in if (#1(dest_Const pc) = Name)
                     then ((args@rst, rhs)::in_group, not_in_group)
                     else (in_group, row::not_in_group)
                  end)      rows ([],[])
              val col_types = U.take type_of (length L, #1(hd in_group))
          in 
          part{constrs = crst, rows = not_in_group, 
               A = {constructor = c, 
                    new_formals = map gv col_types,
                    group = in_group}::A}
          end
  in part{constrs = constructors, rows = rows, A = []}
  end;



(*---------------------------------------------------------------------------
 * This datatype carries some information about the origin of a
 * clause in a function definition.
 *---------------------------------------------------------------------------*)
datatype pattern = GIVEN   of term * int
                 | OMITTED of term * int

fun pattern_map f (GIVEN (tm,i)) = GIVEN(f tm, i)
  | pattern_map f (OMITTED (tm,i)) = OMITTED(f tm, i);

fun pattern_subst theta = pattern_map (subst_free theta);

fun dest_pattern (GIVEN (tm,i)) = ((GIVEN,i),tm)
  | dest_pattern (OMITTED (tm,i)) = ((OMITTED,i),tm);

val pat_of = #2 o dest_pattern;
val row_of_pat = #2 o #1 o dest_pattern;

(*---------------------------------------------------------------------------
 * Produce an instance of a constructor, plus genvars for its arguments.
 *---------------------------------------------------------------------------*)
fun fresh_constr ty_match colty gv c =
  let val (_,Ty) = dest_Const c
      val L = binder_types Ty
      and ty = body_type Ty
      val ty_theta = ty_match ty colty
      val c' = S.inst ty_theta c
      val gvars = map (S.inst ty_theta o gv) L
  in (c', gvars)
  end;


(*---------------------------------------------------------------------------
 * Goes through a list of rows and picks out the ones beginning with a
 * pattern with constructor = Name.
 *---------------------------------------------------------------------------*)
fun mk_group Name rows =
  U.itlist (fn (row as ((prefix, p::rst), rhs)) =>
            fn (in_group,not_in_group) =>
               let val (pc,args) = S.strip_comb p
               in if ((#1(dest_Const pc) = Name) handle _ => false)
                  then (((prefix,args@rst), rhs)::in_group, not_in_group)
                  else (in_group, row::not_in_group) end)
      rows ([],[]);

(*---------------------------------------------------------------------------
 * Partition the rows. Not efficient: we should use hashing.
 *---------------------------------------------------------------------------*)
fun partition _ _ (_,_,_,[]) = raise TFL_ERR{func="partition", mesg="no rows"}
  | partition gv ty_match
              (constructors, colty, res_ty, rows as (((prefix,_),_)::_)) =
let val fresh = fresh_constr ty_match colty gv
     fun part {constrs = [],      rows, A} = rev A
       | part {constrs = c::crst, rows, A} =
         let val (c',gvars) = fresh c
             val (Name,Ty) = dest_Const c'
             val (in_group, not_in_group) = mk_group Name rows
             val in_group' =
                 if (null in_group)  (* Constructor not given *)
                 then [((prefix, #2(fresh c)), OMITTED (S.ARB res_ty, ~1))]
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
      fun build (prefix,tag,plist) =
          let val args   = take (L,plist)
              and plist' = drop(L,plist)
          in (prefix,tag,list_comb(c,args)::plist') end
  in map build l end;

fun v_to_prefix (prefix, v::pats) = (v::prefix,pats)
  | v_to_prefix _ = raise TFL_ERR{func="mk_case", mesg="v_to_prefix"};

fun v_to_pats (v::prefix,tag, pats) = (prefix, tag, v::pats)
  | v_to_pats _ = raise TFL_ERR{func="mk_case", mesg="v_to_pats"};
 

(*----------------------------------------------------------------------------
 * Translation of pattern terms into nested case expressions.
 *
 * This performs the translation and also builds the full set of patterns. 
 * Thus it supports the construction of induction theorems even when an 
 * incomplete set of patterns is given.
 *---------------------------------------------------------------------------*)

fun mk_case ty_info ty_match usednames range_ty =
 let 
 fun mk_case_fail s = raise TFL_ERR{func = "mk_case", mesg = s}
 val fresh_var = gvvariant usednames 
 val divide = partition fresh_var ty_match
 fun expand constructors ty ((_,[]), _) = mk_case_fail"expand_var_row"
   | expand constructors ty (row as ((prefix, p::rst), rhs)) = 
       if (is_Free p) 
       then let val fresh = fresh_constr ty_match ty fresh_var
                fun expnd (c,gvs) = 
                  let val capp = list_comb(c,gvs)
                  in ((prefix, capp::rst), pattern_subst[(p,capp)] rhs)
                  end
            in map expnd (map fresh constructors)  end
       else [row]
 fun mk{rows=[],...} = mk_case_fail"no rows"
   | mk{path=[], rows = ((prefix, []), rhs)::_} =  (* Done *)
        let val (tag,tm) = dest_pattern rhs
        in ([(prefix,tag,[])], tm)
        end
   | mk{path=[], rows = _::_} = mk_case_fail"blunder"
   | mk{path as u::rstp, rows as ((prefix, []), rhs)::rst} = 
        mk{path = path, 
           rows = ((prefix, [fresh_var(type_of u)]), rhs)::rst}
   | mk{path = u::rstp, rows as ((_, p::_), _)::_} =
     let val (pat_rectangle,rights) = ListPair.unzip rows
         val col0 = map(hd o #2) pat_rectangle
     in 
     if (forall is_Free col0) 
     then let val rights' = map (fn(v,e) => pattern_subst[(v,u)] e)
                                (ListPair.zip (col0, rights))
              val pat_rectangle' = map v_to_prefix pat_rectangle
              val (pref_patl,tm) = mk{path = rstp,
                                      rows = ListPair.zip (pat_rectangle',
                                                           rights')}
          in (map v_to_pats pref_patl, tm)
          end
     else
     let val pty as Type (ty_name,_) = type_of p
     in
     case (ty_info ty_name)
     of None => mk_case_fail("Not a known datatype: "^ty_name)
      | Some{case_const,constructors} =>
        let val case_const_name = #1(dest_Const case_const)
            val nrows = List_.concat (map (expand constructors pty) rows)
            val subproblems = divide(constructors, pty, range_ty, nrows)
            val groups      = map #group subproblems
            and new_formals = map #new_formals subproblems
            and constructors' = map #constructor subproblems
            val news = map (fn (nf,rows) => {path = nf@rstp, rows=rows})
                           (ListPair.zip (new_formals, groups))
            val rec_calls = map mk news
            val (pat_rect,dtrees) = ListPair.unzip rec_calls
            val case_functions = map S.list_mk_abs
                                  (ListPair.zip (new_formals, dtrees))
            val types = map type_of (case_functions@[u]) @ [range_ty]
            val case_const' = Const(case_const_name, list_mk_type types)
            val tree = list_comb(case_const', case_functions@[u])
            val pat_rect1 = List_.concat
                              (ListPair.map mk_pat (constructors', pat_rect))
        in (pat_rect1,tree)
        end 
     end end
 in mk
 end;


(* Repeated variable occurrences in a pattern are not allowed. *)
fun FV_multiset tm = 
   case (S.dest_term tm)
     of S.VAR{Name,Ty} => [Free(Name,Ty)]
      | S.CONST _ => []
      | S.COMB{Rator, Rand} => FV_multiset Rator @ FV_multiset Rand
      | S.LAMB _ => raise TFL_ERR{func = "FV_multiset", mesg = "lambda"};

fun no_repeat_vars thy pat =
 let fun check [] = true
       | check (v::rst) =
         if mem_term (v,rst) then
	    raise TFL_ERR{func = "no_repeat_vars",
			  mesg = quote(#1(dest_Free v)) ^
			  " occurs repeatedly in the pattern " ^
			  quote (string_of_cterm (Thry.typecheck thy pat))}
         else check rst
 in check (FV_multiset pat)
 end;

local fun mk_functional_err s = raise TFL_ERR{func = "mk_functional", mesg=s}
      fun single [f] = f
        | single fs  = mk_functional_err (Int.toString (length fs) ^ 
                                          " distinct function names!")
in
fun mk_functional thy clauses =
 let val (L,R) = ListPair.unzip 
                    (map (fn (Const("op =",_) $ t $ u) => (t,u)) clauses)
     val (funcs,pats) = ListPair.unzip (map (fn (t$u) =>(t,u)) L)
     val fcon as Const (fname, ftype) = single (gen_distinct (op aconv) funcs)
     val dummy = map (no_repeat_vars thy) pats
     val rows = ListPair.zip (map (fn x => ([],[x])) pats,
                              map GIVEN (enumerate R))
     val names = foldr add_term_names (R,[])
     val atype = type_of(hd pats)
     and aname = variant names "a"
     val a = Free(aname,atype)
     val ty_info = Thry.match_info thy
     val ty_match = Thry.match_type thy
     val range_ty = type_of (hd R)
     val (patts, case_tm) = mk_case ty_info ty_match (aname::names) range_ty 
                                    {path=[a], rows=rows}
     val patts1 = map (fn (_,(tag,i),[pat]) => tag (pat,i)) patts 
	  handle _ => mk_functional_err "error in pattern-match translation"
     val patts2 = U.sort(fn p1=>fn p2=> row_of_pat p1 < row_of_pat p2) patts1
     val finals = map row_of_pat patts2
     val originals = map (row_of_pat o #2) rows
     val dummy = case (originals\\finals)
             of [] => ()
          | L => mk_functional_err("The following rows (counting from zero)\
                                   \ are inaccessible: "^stringize L)
 in {functional = Abs(fname, ftype, 
		      abstract_over (fcon, 
				     absfree(aname,atype, case_tm))),
     pats = patts2}
end end;


(*----------------------------------------------------------------------------
 *
 *                    PRINCIPLES OF DEFINITION
 *
 *---------------------------------------------------------------------------*)


(*Make all TVars available for instantiation by adding a ? to the front*)
fun poly_tvars (Type(a,Ts)) = Type(a, map (poly_tvars) Ts)
  | poly_tvars (TFree (a,sort)) = TVar (("?" ^ a, 0), sort)
  | poly_tvars (TVar ((a,i),sort)) = TVar (("?" ^ a, i+1), sort);

local val f_eq_wfrec_R_M = 
           #ant(S.dest_imp(#2(S.strip_forall (concl Thms.WFREC_COROLLARY))))
      val {lhs=f, rhs} = S.dest_eq f_eq_wfrec_R_M
      val (fname,_) = dest_Free f
      val (wfrec,_) = S.strip_comb rhs
in
fun wfrec_definition0 thy fid R (functional as Abs(Name, Ty, _)) =
 let val def_name = if Name<>fid then 
			raise TFL_ERR{func = "wfrec_definition0",
				      mesg = "Expected a definition of " ^ 
					     quote fid ^ " but found one of " ^
				      quote Name}
		    else Name ^ "_def"
     val wfrec_R_M =  map_term_types poly_tvars 
	                  (wfrec $ map_term_types poly_tvars R) 
	              $ functional
     val (_, def_term, _) = 
	 Sign.infer_types (sign_of thy) (K None) (K None) [] false
	       ([Const("==",dummyT) $ Const(Name,Ty) $ wfrec_R_M], 
		propT)
  in  add_defs_i [(def_name, def_term)] thy  end
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
            | insrt[] = raise TFL_ERR{func="merge.insert",
				      mesg="pattern not found"}
      in insrt end
    fun pass ([],ptcl_final) = ptcl_final
      | pass (ptcs::tcl, ptcl) = pass(tcl, insert ptcs ptcl)
in 
  pass (TCs, map (fn p => (p,[])) full_pats)
end;


fun givens [] = []
  | givens (GIVEN(tm,_)::pats) = tm :: givens pats
  | givens (OMITTED _::pats)   = givens pats;

fun post_definition (ss, tflCongs) (theory, (def, pats)) =
 let val tych = Thry.typecheck theory 
     val f = #lhs(S.dest_eq(concl def))
     val corollary = R.MATCH_MP Thms.WFREC_COROLLARY def
     val given_pats = givens pats
     val WFR = #ant(S.dest_imp(concl corollary))
     val R = #Rand(S.dest_comb WFR)
     val corollary' = R.UNDISCH corollary  (* put WF R on assums *)
     val corollaries = map (fn pat => R.SPEC (tych pat) corollary') 
	                   given_pats
     val (case_rewrites,context_congs) = extraction_thms theory
     val corollaries' = map(rewrite_rule case_rewrites) corollaries
     val extract = R.CONTEXT_REWRITE_RULE 
	             (ss, f, R,
		      R.ISPECL (map tych [f,R]) Thms.CUT_LEMMA,
		      tflCongs@context_congs)
     val (rules, TCs) = ListPair.unzip (map extract corollaries')
     val rules0 = map (rewrite_rule [Thms.CUT_DEF]) rules
     val mk_cond_rule = R.FILTER_DISCH_ALL(not o curry (op aconv) WFR)
     val rules1 = R.LIST_CONJ(map mk_cond_rule rules0)
 in
 {theory = theory,   (* holds def, if it's needed *)
  rules = rules1,
  full_pats_TCs = merge (map pat_of pats) 
                        (ListPair.zip (given_pats, TCs)), 
  TCs = TCs, 
  patterns = pats}
 end;

(*---------------------------------------------------------------------------
 * Perform the extraction without making the definition. Definition and
 * extraction commute for the non-nested case. For hol90 users, this 
 * function can be invoked without being in draft mode.
 * CURRENTLY UNUSED
fun wfrec_eqns (ss, tflCongs) thy eqns =
 let val {functional,pats} = mk_functional thy eqns
     val given_pats = givens pats
     val {Bvar = f, Body} = S.dest_abs functional
     val {Bvar = x, ...} = S.dest_abs Body
     val (Name, Type("fun", [f_dty, f_rty])) = dest_Free f
     val (case_rewrites,context_congs) = extraction_thms thy
     val tych = Thry.typecheck thy
     val WFREC_THM0 = R.ISPEC (tych functional) Thms.WFREC_COROLLARY
     val Const("All",_) $ Abs(Rname,Rtype,_) = concl WFREC_THM0
     val R = Free (variant (foldr add_term_names (eqns,[])) Rname,
		   Rtype)
     val WFREC_THM = R.ISPECL [tych R, tych f] WFREC_THM0
     val ([proto_def, WFR],_) = S.strip_imp(concl WFREC_THM)
     val R1 = S.rand WFR
     val corollary' = R.UNDISCH(R.UNDISCH WFREC_THM)
     val corollaries = map (fn pat => R.SPEC (tych pat) corollary') given_pats
     val corollaries' = map (rewrite_rule case_rewrites) corollaries
     val extract = R.CONTEXT_REWRITE_RULE 
	               (ss, f, R1, 
		        R.ISPECL (map tych [f,R1]) Thms.CUT_LEMMA, 
			tflCongs@context_congs)
 in {proto_def=proto_def, 
     WFR=WFR, 
     pats=pats,
     extracta = map extract corollaries'}
 end;
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
 * Define the constant after extracting the termination conditions. The 
 * wellfounded relation used in the definition is computed by using the
 * choice operator on the extracted conditions (plus the condition that
 * such a relation must be wellfounded).
 * CURRENTLY UNUSED
fun lazyR_def ss thy eqns =
 let val {proto_def,WFR,pats,extracta} = wfrec_eqns ss thy eqns
     val R1 = S.rand WFR
     val f = S.lhs proto_def
     val (Name,_) = dest_Free f
     val (extractants,TCl) = ListPair.unzip extracta
     val TCs = foldr (gen_union (op aconv)) (TCl, [])
     val full_rqt = WFR::TCs
     val R' = S.mk_select{Bvar=R1, Body=S.list_mk_conj full_rqt}
     val R'abs = S.rand R'
     val theory = add_defs_i [(Name ^ "_def", subst_free[(R1,R')] proto_def)]
	                     thy
     val def = freezeT((get_axiom theory (Name ^ "_def")) RS meta_eq_to_obj_eq)
     val fconst = #lhs(S.dest_eq(concl def)) 
     val tych = Thry.typecheck theory
     val baz = R.DISCH (tych proto_def)
                 (U.itlist (R.DISCH o tych) full_rqt (R.LIST_CONJ extractants))
     val def' = R.MP (R.SPEC (tych fconst) 
                             (R.SPEC (tych R') (R.GENL[tych R1, tych f] baz)))
                     def
     val body_th = R.LIST_CONJ (map (R.ASSUME o tych) full_rqt)
     val bar = R.MP (R.ISPECL[tych R'abs, tych R1] Thms.SELECT_AX)
                    body_th
 in {theory = theory, R=R1,
     rules = U.rev_itlist (U.C R.MP) (R.CONJUNCTS bar) def',
     full_pats_TCs = merge (map pat_of pats) (ListPair.zip (givens pats, TCl)),
     patterns = pats}
 end;
 *---------------------------------------------------------------------------*)



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
  let val (qvars,body) = S.strip_exists tm
      val vlist = #2(S.strip_comb (S.rhs body))
      val plist = ListPair.zip (vlist, xlist)
      val args = map (fn qv => the (gen_assoc (op aconv) (plist, qv))) qvars
                   handle OPTION _ => error 
                       "TFL fault [alpha_ex_unroll]: no correspondence"
      fun build ex      []   = []
        | build (_$rex) (v::rst) =
           let val ex1 = betapply(rex, v)
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

fun mk_case ty_info usednames thy =
 let 
 val divide = ipartition (gvvariant usednames)
 val tych = Thry.typecheck thy
 fun tych_binding(x,y) = (tych x, tych y)
 fun fail s = raise TFL_ERR{func = "mk_case", mesg = s}
 fun mk{rows=[],...} = fail"no rows"
   | mk{path=[], rows = [([], (thm, bindings))]} = 
                         R.IT_EXISTS (map tych_binding bindings) thm
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
     of None => fail("Not a known datatype: "^ty_name)
      | Some{constructors,nchotomy} =>
        let val thm' = R.ISPEC (tych u) nchotomy
            val disjuncts = S.strip_disj (concl thm')
            val subproblems = divide(constructors, rows)
            val groups      = map #group subproblems
            and new_formals = map #new_formals subproblems
            val existentials = ListPair.map alpha_ex_unroll
                                   (new_formals, disjuncts)
            val constraints = map #1 existentials
            val vexl = map #2 existentials
            fun expnd tm (pats,(th,b)) = (pats,(R.SUBS[R.ASSUME(tych tm)]th,b))
            val news = map (fn (nf,rows,c) => {path = nf@rstp, 
                                               rows = map (expnd c) rows})
                           (U.zip3 new_formals groups constraints)
            val recursive_thms = map mk news
            val build_exists = foldr
                                (fn((x,t), th) => 
                                 R.CHOOSE (tych x, R.ASSUME (tych t)) th)
            val thms' = ListPair.map build_exists (vexl, recursive_thms)
            val same_concls = R.EVEN_ORS thms'
        in R.DISJ_CASESL thm' same_concls
        end 
     end end
 in mk
 end;


fun complete_cases thy =
 let val tych = Thry.typecheck thy
     val ty_info = Thry.induct_info thy
 in fn pats =>
 let val names = foldr add_term_names (pats,[])
     val T = type_of (hd pats)
     val aname = Term.variant names "a"
     val vname = Term.variant (aname::names) "v"
     val a = Free (aname, T)
     val v = Free (vname, T)
     val a_eq_v = HOLogic.mk_eq(a,v)
     val ex_th0 = R.EXISTS (tych (S.mk_exists{Bvar=v,Body=a_eq_v}), tych a)
                           (R.REFL (tych a))
     val th0 = R.ASSUME (tych a_eq_v)
     val rows = map (fn x => ([x], (th0,[]))) pats
 in
 R.GEN (tych a) 
       (R.RIGHT_ASSOC
          (R.CHOOSE(tych v, ex_th0)
                (mk_case ty_info (vname::aname::names)
		 thy {path=[v], rows=rows})))
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
      fun (tm1 ==> tm2) = S.mk_imp{ant = tm1, conseq = tm2}
in
fun build_ih f P (pat,TCs) = 
 let val globals = S.free_vars_lr pat
     fun nested tm = is_some (S.find_term (curry (op aconv) f) tm)
     fun dest_TC tm = 
         let val (cntxt,R_y_pat) = S.strip_imp(#2(S.strip_forall tm))
             val (R,y,_) = S.dest_relation R_y_pat
             val P_y = if (nested tm) then R_y_pat ==> P$y else P$y
         in case cntxt 
              of [] => (P_y, (tm,[]))
               | _  => let 
                    val imp = S.list_mk_conj cntxt ==> P_y
                    val lvs = gen_rems (op aconv) (S.free_vars_lr imp, globals)
                    val locals = #2(U.pluck (curry (op aconv) P) lvs) handle _ => lvs
                    in (S.list_mk_forall(locals,imp), (tm,locals)) end
         end
 in case TCs
    of [] => (S.list_mk_forall(globals, P$pat), [])
     |  _ => let val (ihs, TCs_locals) = ListPair.unzip(map dest_TC TCs)
                 val ind_clause = S.list_mk_conj ihs ==> P$pat
             in (S.list_mk_forall(globals,ind_clause), TCs_locals)
             end
 end
end;



(*---------------------------------------------------------------------------
 * This function makes good on the promise made in "build_ih: we prove
 * <something>.
 *
 * Input  is tm = "(!y. R y pat ==> P y) ==> P pat",  
 *           TCs = TC_1[pat] ... TC_n[pat]
 *           thm = ih1 /\ ... /\ ih_n |- ih[pat]
 *---------------------------------------------------------------------------*)
fun prove_case f thy (tm,TCs_locals,thm) =
 let val tych = Thry.typecheck thy
     val antc = tych(#ant(S.dest_imp tm))
     val thm' = R.SPEC_ALL thm
     fun nested tm = is_some (S.find_term (curry (op aconv) f) tm)
     fun get_cntxt TC = tych(#ant(S.dest_imp(#2(S.strip_forall(concl TC)))))
     fun mk_ih ((TC,locals),th2,nested) =
         R.GENL (map tych locals)
            (if nested 
              then R.DISCH (get_cntxt TC) th2 handle _ => th2
               else if S.is_imp(concl TC) 
                     then R.IMP_TRANS TC th2 
                      else R.MP th2 TC)
 in 
 R.DISCH antc
 (if S.is_imp(concl thm') (* recursive calls in this clause *)
  then let val th1 = R.ASSUME antc
           val TCs = map #1 TCs_locals
           val ylist = map (#2 o S.dest_relation o #2 o S.strip_imp o 
                            #2 o S.strip_forall) TCs
           val TClist = map (fn(TC,lvs) => (R.SPEC_ALL(R.ASSUME(tych TC)),lvs))
                            TCs_locals
           val th2list = map (U.C R.SPEC th1 o tych) ylist
           val nlist = map nested TCs
           val triples = U.zip3 TClist th2list nlist
           val Pylist = map mk_ih triples
       in R.MP thm' (R.LIST_CONJ Pylist) end
  else thm')
 end;


(*---------------------------------------------------------------------------
 *
 *         x = (v1,...,vn)  |- M[x]
 *    ---------------------------------------------
 *      ?v1 ... vn. x = (v1,...,vn) |- M[x]
 *
 *---------------------------------------------------------------------------*)
fun LEFT_ABS_VSTRUCT tych thm = 
  let fun CHOOSER v (tm,thm) = 
        let val ex_tm = S.mk_exists{Bvar=v,Body=tm}
        in (ex_tm, R.CHOOSE(tych v, R.ASSUME (tych ex_tm)) thm)
        end
      val [veq] = filter (U.can S.dest_eq) (#1 (R.dest_thm thm))
      val {lhs,rhs} = S.dest_eq veq
      val L = S.free_vars_lr rhs
  in  #2 (U.itlist CHOOSER L (veq,thm))  end;


(*----------------------------------------------------------------------------
 * Input : f, R,  and  [(pat1,TCs1),..., (patn,TCsn)]
 *
 * Instantiates WF_INDUCTION_THM, getting Sinduct and then tries to prove
 * recursion induction (Rinduct) by proving the antecedent of Sinduct from 
 * the antecedent of Rinduct.
 *---------------------------------------------------------------------------*)
fun mk_induction thy f R pat_TCs_list =
let val tych = Thry.typecheck thy
    val Sinduction = R.UNDISCH (R.ISPEC (tych R) Thms.WF_INDUCTION_THM)
    val (pats,TCsl) = ListPair.unzip pat_TCs_list
    val case_thm = complete_cases thy pats
    val domain = (type_of o hd) pats
    val Pname = Term.variant (foldr (foldr add_term_names) 
			      (pats::TCsl, [])) "P"
    val P = Free(Pname, domain --> HOLogic.boolT)
    val Sinduct = R.SPEC (tych P) Sinduction
    val Sinduct_assumf = S.rand ((#ant o S.dest_imp o concl) Sinduct)
    val Rassums_TCl' = map (build_ih f P) pat_TCs_list
    val (Rassums,TCl') = ListPair.unzip Rassums_TCl'
    val Rinduct_assum = R.ASSUME (tych (S.list_mk_conj Rassums))
    val cases = map (fn pat => betapply (Sinduct_assumf, pat)) pats
    val tasks = U.zip3 cases TCl' (R.CONJUNCTS Rinduct_assum)
    val proved_cases = map (prove_case f thy) tasks
    val v = Free (variant (foldr add_term_names (map concl proved_cases, []))
		    "v",
		  domain)
    val vtyped = tych v
    val substs = map (R.SYM o R.ASSUME o tych o (curry HOLogic.mk_eq v)) pats
    val proved_cases1 = ListPair.map (fn (th,th') => R.SUBS[th]th') 
                          (substs, proved_cases)
    val abs_cases = map (LEFT_ABS_VSTRUCT tych) proved_cases1
    val dant = R.GEN vtyped (R.DISJ_CASESL (R.ISPEC vtyped case_thm) abs_cases)
    val dc = R.MP Sinduct dant
    val Parg_ty = type_of(#Bvar(S.dest_forall(concl dc)))
    val vars = map (gvvariant[Pname]) (S.strip_prod_type Parg_ty)
    val dc' = U.itlist (R.GEN o tych) vars
                       (R.SPEC (tych(S.mk_vstruct Parg_ty vars)) dc)
in 
   R.GEN (tych P) (R.DISCH (tych(concl Rinduct_assum)) dc')
end
handle _ => raise TFL_ERR{func = "mk_induction", mesg = "failed derivation"};




(*---------------------------------------------------------------------------
 * 
 *                        POST PROCESSING
 *
 *---------------------------------------------------------------------------*)


fun simplify_induction thy hth ind = 
  let val tych = Thry.typecheck thy
      val (asl,_) = R.dest_thm ind
      val (_,tc_eq_tc') = R.dest_thm hth
      val tc = S.lhs tc_eq_tc'
      fun loop [] = ind
        | loop (asm::rst) = 
          if (U.can (Thry.match_term thy asm) tc)
          then R.UNDISCH
                 (R.MATCH_MP
                     (R.MATCH_MP Thms.simp_thm (R.DISCH (tych asm) ind)) 
                     hth)
         else loop rst
  in loop asl
end;


(*---------------------------------------------------------------------------
 * The termination condition is an antecedent to the rule, and an 
 * assumption to the theorem.
 *---------------------------------------------------------------------------*)
fun elim_tc tcthm (rule,induction) = 
   (R.MP rule tcthm, R.PROVE_HYP tcthm induction)


fun postprocess{WFtac, terminator, simplifier} theory {rules,induction,TCs} =
let val tych = Thry.typecheck theory

   (*---------------------------------------------------------------------
    * Attempt to eliminate WF condition. It's the only assumption of rules
    *---------------------------------------------------------------------*)
   val (rules1,induction1)  = 
       let val thm = R.prove(tych(HOLogic.mk_Trueprop 
				  (hd(#1(R.dest_thm rules)))),
			     WFtac)
       in (R.PROVE_HYP thm rules,  R.PROVE_HYP thm induction)
       end handle _ => (rules,induction)

   (*----------------------------------------------------------------------
    * The termination condition (tc) is simplified to |- tc = tc' (there
    * might not be a change!) and then 3 attempts are made:
    *
    *   1. if |- tc = T, then eliminate it with eqT; otherwise,
    *   2. apply the terminator to tc'. If |- tc' = T then eliminate; else
    *   3. replace tc by tc' in both the rules and the induction theorem.
    *---------------------------------------------------------------------*)
   fun simplify_tc tc (r,ind) =
       let val tc_eq = simplifier (tych tc)
       in 
       elim_tc (R.MATCH_MP Thms.eqT tc_eq) (r,ind)
       handle _ => 
        (elim_tc (R.MATCH_MP(R.MATCH_MP Thms.rev_eq_mp tc_eq)
		  (R.prove(tych(HOLogic.mk_Trueprop(S.rhs(concl tc_eq))), 
			   terminator)))
                 (r,ind)
         handle _ => 
          (R.UNDISCH(R.MATCH_MP (R.MATCH_MP Thms.simp_thm r) tc_eq), 
           simplify_induction theory tc_eq ind))
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
      let val tc_eq = simplifier (tych (#2 (S.strip_forall tc)))
      in
      R.GEN_ALL
       (R.MATCH_MP Thms.eqT tc_eq
        handle _
        => (R.MATCH_MP(R.MATCH_MP Thms.rev_eq_mp tc_eq)
                      (R.prove(tych(HOLogic.mk_Trueprop (S.rhs(concl tc_eq))),
			       terminator))
            handle _ => tc_eq))
      end

   (*-------------------------------------------------------------------
    * Attempt to simplify the termination conditions in each rule and 
    * in the induction theorem.
    *-------------------------------------------------------------------*)
   fun strip_imp tm = if S.is_neg tm then ([],tm) else S.strip_imp tm
   fun loop ([],extras,R,ind) = (rev R, ind, extras)
     | loop ((r,ftcs)::rst, nthms, R, ind) =
        let val tcs = #1(strip_imp (concl r))
            val extra_tcs = gen_rems (op aconv) (ftcs, tcs)
            val extra_tc_thms = map simplify_nested_tc extra_tcs
            val (r1,ind1) = U.rev_itlist simplify_tc tcs (r,ind)
            val r2 = R.FILTER_DISCH_ALL(not o S.is_WFR) r1
        in loop(rst, nthms@extra_tc_thms, r2::R, ind1)
        end
   val rules_tcs = ListPair.zip (R.CONJUNCTS rules1, TCs)
   val (rules2,ind2,extras) = loop(rules_tcs,[],[],induction1)
in
  {induction = ind2, rules = R.LIST_CONJ rules2, nested_tcs = extras}
end;

end; (* TFL *)
