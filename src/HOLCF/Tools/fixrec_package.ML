(*  Title:      HOLCF/Tools/fixrec_package.ML
    Author:     Amber Telfer and Brian Huffman

Recursive function definition package for HOLCF.
*)

signature FIXREC_PACKAGE =
sig
  val add_fixrec: bool -> (binding * typ option * mixfix) list
    -> (Attrib.binding * term) list -> local_theory -> local_theory
  val add_fixrec_cmd: bool -> (binding * string option * mixfix) list
    -> (Attrib.binding * string) list -> local_theory -> local_theory
  val add_fixpat: Thm.binding * term list -> theory -> theory
  val add_fixpat_cmd: Attrib.binding * string list -> theory -> theory
  val add_matchers: (string * string) list -> theory -> theory
  val setup: theory -> theory
end;

structure FixrecPackage: FIXREC_PACKAGE =
struct

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

fun cfunsT (Ts, U) = foldr cfunT U Ts;

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

fun matchT (T, U) =
  body_cfun T ->> cfunsT (binder_cfun T, U) ->> U;


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

fun add_fixdefs
  (fixes : ((binding * typ) * mixfix) list)
  (spec : (Attrib.binding * term) list)
  (lthy : local_theory) =
  let
    val names = map (Binding.name_of o fst o fst) fixes;
    val all_names = space_implode "_" names;
    val (lhss,rhss) = ListPair.unzip (map (dest_eqs o snd) spec);
    val fixpoint = mk_fix (lambda_ctuple lhss (mk_ctuple rhss));
    
    fun one_def (l as Free(n,_)) r =
          let val b = Long_Name.base_name n
          in ((Binding.name (b^"_def"), []), r) end
      | one_def _ _ = fixrec_err "fixdefs: lhs not of correct form";
    fun defs [] _ = []
      | defs (l::[]) r = [one_def l r]
      | defs (l::ls) r = one_def l (mk_cfst r) :: defs ls (mk_csnd r);
    val fixdefs = defs lhss fixpoint;
    val define_all = fold_map (LocalTheory.define Thm.definitionK);
    val (fixdef_thms : (term * (string * thm)) list, lthy') = lthy
      |> define_all (map (apfst fst) fixes ~~ fixdefs);
    fun cpair_equalI (thm1, thm2) = @{thm cpair_equalI} OF [thm1, thm2];
    val ctuple_fixdef_thm = foldr1 cpair_equalI (map (snd o snd) fixdef_thms);
    val ctuple_induct_thm = ctuple_fixdef_thm RS def_fix_ind;
    val ctuple_unfold_thm =
      Goal.prove lthy' [] [] (mk_trp (mk_ctuple lhss === mk_ctuple rhss))
        (fn _ => EVERY [rtac (ctuple_fixdef_thm RS fix_eq2 RS trans) 1,
                   simp_tac (local_simpset_of lthy') 1]);
    fun unfolds [] thm = []
      | unfolds (n::[]) thm = [(n^"_unfold", thm)]
      | unfolds (n::ns) thm = let
          val thmL = thm RS @{thm cpair_eqD1};
          val thmR = thm RS @{thm cpair_eqD2};
        in (n^"_unfold", thmL) :: unfolds ns thmR end;
    val unfold_thms = unfolds names ctuple_unfold_thm;
    fun mk_note (n, thm) = ((Binding.name n, []), [thm]);
    val (thmss, lthy'') = lthy'
      |> fold_map (LocalTheory.note Thm.theoremK o mk_note)
        ((all_names ^ "_induct", ctuple_induct_thm) :: unfold_thms);
  in
    (lthy'', names, fixdef_thms, map snd unfold_thms)
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
    fun taken (Const(a,_), bs) = insert (op =) (Long_Name.base_name a) bs
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
        val m = Const(match_name c, matchT (T, fastype_of rhs));
        val k = big_lambdas vs rhs;
      in
        (m`v`k, v, n::taken)
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
  | Free(_,_) => ((pat, length vs), big_lambdas vs rhs)
  | Const(_,_) => ((pat, length vs), big_lambdas vs rhs)
  | _ => fixrec_err ("function is not declared as constant in theory: "
                    ^ ML_Syntax.print_term pat);

fun strip_alls t =
  if Logic.is_all t then strip_alls (snd (Logic.dest_all t)) else t;

fun match_eq match_name eq =
  let
    val (lhs,rhs) = dest_eqs (Logic.strip_imp_concl (strip_alls eq));
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

(* this is the pattern-matching compiler function *)
fun compile_pats match_name eqs =
  let
    val (((n::names),(a::arities)),mats) =
      apfst ListPair.unzip (ListPair.unzip (map (match_eq match_name) eqs));
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
fun make_simps lthy (unfold_thm, eqns : (Attrib.binding * term) list) =
  let
    val tacs =
      [rtac (unfold_thm RS @{thm ssubst_lhs}) 1,
       asm_simp_tac (local_simpset_of lthy) 1];
    fun prove_term t = Goal.prove lthy [] [] t (K (EVERY tacs));
    fun prove_eqn (bind, eqn_t) = (bind, prove_term eqn_t);
  in
    map prove_eqn eqns
  end;

(*************************************************************************)
(************************* Main fixrec function **************************)
(*************************************************************************)

local
(* code adapted from HOL/Tools/primrec_package.ML *)

fun gen_fixrec
  (set_group : bool)
  prep_spec
  (strict : bool)
  raw_fixes
  raw_spec
  (lthy : local_theory) =
  let
    val (fixes : ((binding * typ) * mixfix) list,
         spec : (Attrib.binding * term) list) =
          fst (prep_spec raw_fixes raw_spec lthy);
    val chead_of_spec =
      chead_of o fst o dest_eqs o Logic.strip_imp_concl o strip_alls o snd;
    fun name_of (Free (n, _)) = n
      | name_of t = fixrec_err ("unknown term");
    val all_names = map (name_of o chead_of_spec) spec;
    val names = distinct (op =) all_names;
    fun block_of_name n =
      map_filter
        (fn (m,eq) => if m = n then SOME eq else NONE)
        (all_names ~~ spec);
    val blocks = map block_of_name names;

    val matcher_tab = FixrecMatchData.get (ProofContext.theory_of lthy);
    fun match_name c =
      case Symtab.lookup matcher_tab c of SOME m => m
        | NONE => fixrec_err ("unknown pattern constructor: " ^ c);

    val matches = map (compile_pats match_name) (map (map snd) blocks);
    val spec' = map (pair Attrib.empty_binding) matches;
    val (lthy', cnames, fixdef_thms, unfold_thms) =
      add_fixdefs fixes spec' lthy;
  in
    if strict then let (* only prove simp rules if strict = true *)
      val simps : (Attrib.binding * thm) list list =
        map (make_simps lthy') (unfold_thms ~~ blocks);
      fun mk_bind n : Attrib.binding =
       (Binding.name (n ^ "_simps"),
         [Attrib.internal (K Simplifier.simp_add)]);
      val simps1 : (Attrib.binding * thm list) list =
        map (fn (n,xs) => (mk_bind n, map snd xs)) (names ~~ simps);
      val simps2 : (Attrib.binding * thm list) list =
        map (apsnd (fn thm => [thm])) (List.concat simps);
      val (_, lthy'') = lthy'
        |> fold_map (LocalTheory.note Thm.theoremK) (simps1 @ simps2);
    in
      lthy''
    end
    else lthy'
  end;

in

val add_fixrec = gen_fixrec false Specification.check_spec;
val add_fixrec_cmd = gen_fixrec true Specification.read_spec;

end; (* local *)

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

val add_fixpat = gen_add_fixpat Sign.cert_term (K I);
val add_fixpat_cmd = gen_add_fixpat Syntax.read_term_global Attrib.attribute;


(*************************************************************************)
(******************************** Parsers ********************************)
(*************************************************************************)

local structure P = OuterParse and K = OuterKeyword in

val _ = OuterSyntax.local_theory "fixrec" "define recursive functions (HOLCF)" K.thy_decl
  ((P.opt_keyword "permissive" >> not) -- P.fixes -- SpecParse.where_alt_specs
    >> (fn ((strict, fixes), specs) => add_fixrec_cmd strict fixes specs));

val _ = OuterSyntax.command "fixpat" "define rewrites for fixrec functions" K.thy_decl
  (SpecParse.specs >> (Toplevel.theory o add_fixpat_cmd));
  
end;

val setup = FixrecMatchData.init;

end;
