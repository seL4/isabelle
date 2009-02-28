(*  Title:      HOLCF/Tools/fixrec_package.ML
    Author:     Amber Telfer and Brian Huffman

Recursive function definition package for HOLCF.
*)

signature FIXREC_PACKAGE =
sig
  val legacy_infer_term: theory -> term -> term
  val legacy_infer_prop: theory -> term -> term

  val add_fixrec: bool -> (Attrib.binding * string) list list -> theory -> theory
  val add_fixrec_i: bool -> ((binding * attribute list) * term) list list -> theory -> theory
  val add_fixpat: Attrib.binding * string list -> theory -> theory
  val add_fixpat_i: (binding * attribute list) * term list -> theory -> theory
  val add_matchers: (string * string) list -> theory -> theory
  val setup: theory -> theory
end;

structure FixrecPackage: FIXREC_PACKAGE =
struct

(* legacy type inference *)
(* used by the domain package *)
fun legacy_infer_term thy t =
  singleton (Syntax.check_terms (ProofContext.init thy)) (Sign.intern_term thy t);

fun legacy_infer_prop thy t = legacy_infer_term thy (TypeInfer.constrain propT t);


val fix_eq2 = @{thm fix_eq2};
val def_fix_ind = @{thm def_fix_ind};


fun fixrec_err s = error ("fixrec definition error:\n" ^ s);
fun fixrec_eq_err thy s eq =
  fixrec_err (s ^ "\nin\n" ^ quote (Syntax.string_of_term_global thy eq));

(*************************************************************************)
(***************************** building types ****************************)
(*************************************************************************)

(* ->> is taken from holcf_logic.ML *)
fun cfunT (T, U) = Type(@{type_name "->"}, [T, U]);

infixr 6 ->>; val (op ->>) = cfunT;

fun dest_cfunT (Type(@{type_name "->"}, [T, U])) = (T, U)
  | dest_cfunT T = raise TYPE ("dest_cfunT", [T], []);

fun binder_cfun (Type(@{type_name "->"},[T, U])) = T :: binder_cfun U
  | binder_cfun _   =  [];

fun body_cfun (Type(@{type_name "->"},[T, U])) = body_cfun U
  | body_cfun T   =  T;

fun strip_cfun T : typ list * typ =
  (binder_cfun T, body_cfun T);

fun maybeT T = Type(@{type_name "maybe"}, [T]);

fun dest_maybeT (Type(@{type_name "maybe"}, [T])) = T
  | dest_maybeT T = raise TYPE ("dest_maybeT", [T], []);

fun tupleT [] = @{typ "unit"}
  | tupleT [T] = T
  | tupleT (T :: Ts) = HOLogic.mk_prodT (T, tupleT Ts);

fun matchT T = body_cfun T ->> maybeT (tupleT (binder_cfun T));

(*************************************************************************)
(***************************** building terms ****************************)
(*************************************************************************)

val mk_trp = HOLogic.mk_Trueprop;

(* splits a cterm into the right and lefthand sides of equality *)
fun dest_eqs t = HOLogic.dest_eq (HOLogic.dest_Trueprop t);

(* similar to Thm.head_of, but for continuous application *)
fun chead_of (Const(@{const_name Rep_CFun},_)$f$t) = chead_of f
  | chead_of u = u;

fun capply_const (S, T) =
  Const(@{const_name Rep_CFun}, (S ->> T) --> (S --> T));

fun cabs_const (S, T) =
  Const(@{const_name Abs_CFun}, (S --> T) --> (S ->> T));

fun mk_capply (t, u) =
  let val (S, T) =
    case Term.fastype_of t of
        Type(@{type_name "->"}, [S, T]) => (S, T)
      | _ => raise TERM ("mk_capply " ^ ML_Syntax.print_list ML_Syntax.print_term [t, u], [t, u]);
  in capply_const (S, T) $ t $ u end;

infix 0 ==;  val (op ==) = Logic.mk_equals;
infix 1 ===; val (op ===) = HOLogic.mk_eq;
infix 9 `  ; val (op `) = mk_capply;


fun mk_cpair (t, u) =
  let val T = Term.fastype_of t
      val U = Term.fastype_of u
      val cpairT = T ->> U ->> HOLogic.mk_prodT (T, U)
  in Const(@{const_name cpair}, cpairT) ` t ` u end;

fun mk_cfst t =
  let val T = Term.fastype_of t;
      val (U, _) = HOLogic.dest_prodT T;
  in Const(@{const_name cfst}, T ->> U) ` t end;

fun mk_csnd t =
  let val T = Term.fastype_of t;
      val (_, U) = HOLogic.dest_prodT T;
  in Const(@{const_name csnd}, T ->> U) ` t end;

fun mk_csplit t =
  let val (S, TU) = dest_cfunT (Term.fastype_of t);
      val (T, U) = dest_cfunT TU;
      val csplitT = (S ->> T ->> U) ->> HOLogic.mk_prodT (S, T) ->> U;
  in Const(@{const_name csplit}, csplitT) ` t end;

(* builds the expression (LAM v. rhs) *)
fun big_lambda v rhs =
  cabs_const (Term.fastype_of v, Term.fastype_of rhs) $ Term.lambda v rhs;

(* builds the expression (LAM v1 v2 .. vn. rhs) *)
fun big_lambdas [] rhs = rhs
  | big_lambdas (v::vs) rhs = big_lambda v (big_lambdas vs rhs);

(* builds the expression (LAM <v1,v2,..,vn>. rhs) *)
fun lambda_ctuple [] rhs = big_lambda (Free("unit", HOLogic.unitT)) rhs
  | lambda_ctuple (v::[]) rhs = big_lambda v rhs
  | lambda_ctuple (v::vs) rhs =
      mk_csplit (big_lambda v (lambda_ctuple vs rhs));

(* builds the expression <v1,v2,..,vn> *)
fun mk_ctuple [] = @{term "UU::unit"}
|   mk_ctuple (t::[]) = t
|   mk_ctuple (t::ts) = mk_cpair (t, mk_ctuple ts);

fun mk_return t =
  let val T = Term.fastype_of t
  in Const(@{const_name Fixrec.return}, T ->> maybeT T) ` t end;

fun mk_bind (t, u) =
  let val (T, mU) = dest_cfunT (Term.fastype_of u);
      val bindT = maybeT T ->> (T ->> mU) ->> mU;
  in Const(@{const_name Fixrec.bind}, bindT) ` t ` u end;

fun mk_mplus (t, u) =
  let val mT = Term.fastype_of t
  in Const(@{const_name Fixrec.mplus}, mT ->> mT ->> mT) ` t ` u end;

fun mk_run t =
  let val mT = Term.fastype_of t
      val T = dest_maybeT mT
  in Const(@{const_name Fixrec.run}, mT ->> T) ` t end;

fun mk_fix t =
  let val (T, _) = dest_cfunT (Term.fastype_of t)
  in Const(@{const_name fix}, (T ->> T) ->> T) ` t end;

(*************************************************************************)
(************* fixed-point definitions and unfolding theorems ************)
(*************************************************************************)

fun add_fixdefs eqs thy =
  let
    val (lhss,rhss) = ListPair.unzip (map dest_eqs eqs);
    val fixpoint = mk_fix (lambda_ctuple lhss (mk_ctuple rhss));
    
    fun one_def (l as Const(n,T)) r =
          let val b = Sign.base_name n in (b, (b^"_def", l == r)) end
      | one_def _ _ = fixrec_err "fixdefs: lhs not of correct form";
    fun defs [] _ = []
      | defs (l::[]) r = [one_def l r]
      | defs (l::ls) r = one_def l (mk_cfst r) :: defs ls (mk_csnd r);
    val (names, fixdefs) = ListPair.unzip (defs lhss fixpoint);
    
    val (fixdef_thms, thy') =
      PureThy.add_defs false (map (Thm.no_attributes o apfst Binding.name) fixdefs) thy;
    val ctuple_fixdef_thm = foldr1 (fn (x,y) => @{thm cpair_equalI} OF [x,y]) fixdef_thms;
    
    val ctuple_unfold = mk_trp (mk_ctuple lhss === mk_ctuple rhss);
    val ctuple_unfold_thm = Goal.prove_global thy' [] [] ctuple_unfold
          (fn _ => EVERY [rtac (ctuple_fixdef_thm RS fix_eq2 RS trans) 1,
                    simp_tac (simpset_of thy') 1]);
    val ctuple_induct_thm =
          (space_implode "_" names ^ "_induct", ctuple_fixdef_thm RS def_fix_ind);
    
    fun unfolds [] thm = []
      | unfolds (n::[]) thm = [(n^"_unfold", thm)]
      | unfolds (n::ns) thm = let
          val thmL = thm RS @{thm cpair_eqD1};
          val thmR = thm RS @{thm cpair_eqD2};
        in (n^"_unfold", thmL) :: unfolds ns thmR end;
    val unfold_thms = unfolds names ctuple_unfold_thm;
    val thms = ctuple_induct_thm :: unfold_thms;
    val (_, thy'') = PureThy.add_thms (map (Thm.no_attributes o apfst Binding.name) thms) thy';
  in
    (thy'', names, fixdef_thms, map snd unfold_thms)
  end;

(*************************************************************************)
(*********** monadic notation and pattern matching compilation ***********)
(*************************************************************************)

structure FixrecMatchData = TheoryDataFun (
  type T = string Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ tabs : T = Symtab.merge (K true) tabs;
);

(* associate match functions with pattern constants *)
fun add_matchers ms = FixrecMatchData.map (fold Symtab.update ms);

fun taken_names (t : term) : bstring list =
  let
    fun taken (Const(a,_), bs) = insert (op =) (Sign.base_name a) bs
      | taken (Free(a,_) , bs) = insert (op =) a bs
      | taken (f $ u     , bs) = taken (f, taken (u, bs))
      | taken (Abs(a,_,t), bs) = taken (t, insert (op =) a bs)
      | taken (_         , bs) = bs;
  in
    taken (t, [])
  end;

(* builds a monadic term for matching a constructor pattern *)
fun pre_build match_name pat rhs vs taken =
  case pat of
    Const(@{const_name Rep_CFun},_)$f$(v as Free(n,T)) =>
      pre_build match_name f rhs (v::vs) taken
  | Const(@{const_name Rep_CFun},_)$f$x =>
      let val (rhs', v, taken') = pre_build match_name x rhs [] taken;
      in pre_build match_name f rhs' (v::vs) taken' end
  | Const(c,T) =>
      let
        val n = Name.variant taken "v";
        fun result_type (Type(@{type_name "->"},[_,T])) (x::xs) = result_type T xs
          | result_type T _ = T;
        val v = Free(n, result_type T vs);
        val m = Const(match_name c, matchT T);
        val k = lambda_ctuple vs rhs;
      in
        (mk_bind (m`v, k), v, n::taken)
      end
  | Free(n,_) => fixrec_err ("expected constructor, found free variable " ^ quote n)
  | _ => fixrec_err "pre_build: invalid pattern";

(* builds a monadic term for matching a function definition pattern *)
(* returns (name, arity, matcher) *)
fun building match_name pat rhs vs taken =
  case pat of
    Const(@{const_name Rep_CFun}, _)$f$(v as Free(n,T)) =>
      building match_name f rhs (v::vs) taken
  | Const(@{const_name Rep_CFun}, _)$f$x =>
      let val (rhs', v, taken') = pre_build match_name x rhs [] taken;
      in building match_name f rhs' (v::vs) taken' end
  | Const(name,_) => (pat, length vs, big_lambdas vs rhs)
  | _ => fixrec_err "function is not declared as constant in theory";

fun match_eq match_name eq = 
  let val (lhs,rhs) = dest_eqs eq;
  in
    building match_name lhs (mk_return rhs) [] (taken_names eq)
  end;

(* returns the sum (using +++) of the terms in ms *)
(* also applies "run" to the result! *)
fun fatbar arity ms =
  let
    fun LAM_Ts 0 t = ([], Term.fastype_of t)
      | LAM_Ts n (_ $ Abs(_,T,t)) =
          let val (Ts, U) = LAM_Ts (n-1) t in (T::Ts, U) end
      | LAM_Ts _ _ = fixrec_err "fatbar: internal error, not enough LAMs";
    fun unLAM 0 t = t
      | unLAM n (_$Abs(_,_,t)) = unLAM (n-1) t
      | unLAM _ _ = fixrec_err "fatbar: internal error, not enough LAMs";
    fun reLAM ([], U) t = t
      | reLAM (T::Ts, U) t = reLAM (Ts, T ->> U) (cabs_const(T,U)$Abs("",T,t));
    val msum = foldr1 mk_mplus (map (unLAM arity) ms);
    val (Ts, U) = LAM_Ts arity (hd ms)
  in
    reLAM (rev Ts, dest_maybeT U) (mk_run msum)
  end;

fun unzip3 [] = ([],[],[])
  | unzip3 ((x,y,z)::ts) =
      let val (xs,ys,zs) = unzip3 ts
      in (x::xs, y::ys, z::zs) end;

(* this is the pattern-matching compiler function *)
fun compile_pats match_name eqs = 
  let
    val ((n::names),(a::arities),mats) = unzip3 (map (match_eq match_name) eqs);
    val cname = if forall (fn x => n=x) names then n
          else fixrec_err "all equations in block must define the same function";
    val arity = if forall (fn x => a=x) arities then a
          else fixrec_err "all equations in block must have the same arity";
    val rhs = fatbar arity mats;
  in
    mk_trp (cname === rhs)
  end;

(*************************************************************************)
(********************** Proving associated theorems **********************)
(*************************************************************************)

(* proves a block of pattern matching equations as theorems, using unfold *)
fun make_simps thy (unfold_thm, eqns) =
  let
    val tacs = [rtac (unfold_thm RS @{thm ssubst_lhs}) 1, asm_simp_tac (simpset_of thy) 1];
    fun prove_term t = Goal.prove_global thy [] [] t (K (EVERY tacs));
    fun prove_eqn ((name, eqn_t), atts) = ((name, prove_term eqn_t), atts);
  in
    map prove_eqn eqns
  end;

(*************************************************************************)
(************************* Main fixrec function **************************)
(*************************************************************************)

fun gen_add_fixrec prep_prop prep_attrib strict blocks thy =
  let
    val eqns = List.concat blocks;
    val lengths = map length blocks;
    
    val ((bindings, srcss), strings) = apfst split_list (split_list eqns);
    val names = map Binding.base_name bindings;
    val atts = map (map (prep_attrib thy)) srcss;
    val eqn_ts = map (prep_prop thy) strings;
    val rec_ts = map (fn eq => chead_of (fst (dest_eqs (Logic.strip_imp_concl eq)))
      handle TERM _ => fixrec_eq_err thy "not a proper equation" eq) eqn_ts;
    val (_, eqn_ts') = OldPrimrecPackage.unify_consts thy rec_ts eqn_ts;
    
    fun unconcat [] _ = []
      | unconcat (n::ns) xs = List.take (xs,n) :: unconcat ns (List.drop (xs,n));
    val matcher_tab = FixrecMatchData.get thy;
    fun match_name c =
          case Symtab.lookup matcher_tab c of SOME m => m
            | NONE => fixrec_err ("unknown pattern constructor: " ^ c);

    val pattern_blocks = unconcat lengths (map Logic.strip_imp_concl eqn_ts');
    val compiled_ts =
          map (compile_pats match_name) pattern_blocks;
    val (thy', cnames, fixdef_thms, unfold_thms) = add_fixdefs compiled_ts thy;
  in
    if strict then let (* only prove simp rules if strict = true *)
      val eqn_blocks = unconcat lengths ((names ~~ eqn_ts') ~~ atts);
      val simps = maps (make_simps thy') (unfold_thms ~~ eqn_blocks);
      val (simp_thms, thy'') = PureThy.add_thms ((map o apfst o apfst) Binding.name simps) thy';
      
      val simp_names = map (fn name => name^"_simps") cnames;
      val simp_attribute = rpair [Simplifier.simp_add];
      val simps' = map simp_attribute (simp_names ~~ unconcat lengths simp_thms);
    in
      (snd o PureThy.add_thmss ((map o apfst o apfst) Binding.name simps')) thy''
    end
    else thy'
  end;

val add_fixrec = gen_add_fixrec Syntax.read_prop_global Attrib.attribute;
val add_fixrec_i = gen_add_fixrec Sign.cert_prop (K I);


(*************************************************************************)
(******************************** Fixpat *********************************)
(*************************************************************************)

fun fix_pat thy t = 
  let
    val T = fastype_of t;
    val eq = mk_trp (HOLogic.eq_const T $ t $ Var (("x",0),T));
    val cname = case chead_of t of Const(c,_) => c | _ =>
              fixrec_err "function is not declared as constant in theory";
    val unfold_thm = PureThy.get_thm thy (cname^"_unfold");
    val simp = Goal.prove_global thy [] [] eq
          (fn _ => EVERY [stac unfold_thm 1, simp_tac (simpset_of thy) 1]);
  in simp end;

fun gen_add_fixpat prep_term prep_attrib ((name, srcs), strings) thy =
  let
    val atts = map (prep_attrib thy) srcs;
    val ts = map (prep_term thy) strings;
    val simps = map (fix_pat thy) ts;
  in
    (snd o PureThy.add_thmss [((name, simps), atts)]) thy
  end;

val add_fixpat = gen_add_fixpat Syntax.read_term_global Attrib.attribute;
val add_fixpat_i = gen_add_fixpat Sign.cert_term (K I);


(*************************************************************************)
(******************************** Parsers ********************************)
(*************************************************************************)

local structure P = OuterParse and K = OuterKeyword in

val fixrec_eqn = SpecParse.opt_thm_name ":" -- P.prop;

val fixrec_strict = P.opt_keyword "permissive" >> not;

val fixrec_decl = fixrec_strict -- P.and_list1 (Scan.repeat1 fixrec_eqn);

(* this builds a parser for a new keyword, fixrec, whose functionality 
is defined by add_fixrec *)
val _ =
  OuterSyntax.command "fixrec" "define recursive functions (HOLCF)" K.thy_decl
    (fixrec_decl >> (Toplevel.theory o uncurry add_fixrec));

(* fixpat parser *)
val fixpat_decl = SpecParse.opt_thm_name ":" -- Scan.repeat1 P.prop;

val _ =
  OuterSyntax.command "fixpat" "define rewrites for fixrec functions" K.thy_decl
    (fixpat_decl >> (Toplevel.theory o add_fixpat));

end; (* local structure *)

val setup = FixrecMatchData.init;

end;
