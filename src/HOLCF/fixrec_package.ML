(*  Title:      HOLCF/fixrec_package.ML
    ID:         $Id$
    Author:     Amber Telfer and Brian Huffman

Recursive function definition package for HOLCF.
*)

signature FIXREC_PACKAGE =
sig
  val add_fixrec: ((string * Attrib.src list) * string) list list -> theory -> theory
  val add_fixrec_i: ((string * theory attribute list) * term) list list -> theory -> theory
  val add_fixpat: ((string * Attrib.src list) * string) list -> theory -> theory
  val add_fixpat_i: ((string * theory attribute list) * term) list -> theory -> theory
end;

structure FixrecPackage: FIXREC_PACKAGE =
struct

(* ->> is taken from holcf_logic.ML *)
(* TODO: fix dependencies so we can import HOLCFLogic here *)
infixr 6 ->>;
fun S ->> T = Type ("Cfun.->",[S,T]);

(* extern_name is taken from domain/library.ML *)
fun extern_name con = case Symbol.explode con of 
		   ("o"::"p"::" "::rest) => implode rest
		   | _ => con;

val mk_trp = HOLogic.mk_Trueprop;

(* splits a cterm into the right and lefthand sides of equality *)
fun dest_eqs (Const ("==", _)$lhs$rhs) = (lhs, rhs)
  | dest_eqs (Const ("Trueprop", _)$(Const ("op =", _)$lhs$rhs)) = (lhs,rhs)
  | dest_eqs t = sys_error (Sign.string_of_term (sign_of (the_context())) t);

(* similar to Thm.head_of, but for continuous application *)
fun chead_of (Const("Cfun.Rep_CFun",_)$f$t) = chead_of f
  | chead_of u = u;

(* these are helpful functions copied from HOLCF/domain/library.ML *)
fun %: s = Free(s,dummyT);
fun %%: s = Const(s,dummyT);
infix 0 ==;  fun S ==  T = %%:"==" $ S $ T;
infix 1 ===; fun S === T = %%:"op =" $ S $ T;
infix 9 `  ; fun f ` x = %%:"Cfun.Rep_CFun" $ f $ x;

(* infers the type of a term *)
(* similar to Theory.inferT_axm, but allows any type, not just propT *)
fun infer sg t =
  fst (Sign.infer_types (Sign.pp sg) sg (K NONE) (K NONE) [] true ([t],dummyT));

(* Similar to Term.lambda, but also allows abstraction over constants *)
fun lambda' (v as Free (x, T)) t = Abs (x, T, abstract_over (v, t))
  | lambda' (v as Var ((x, _), T)) t = Abs (x, T, abstract_over (v, t))
  | lambda' (v as Const (x, T)) t = Abs (Sign.base_name x, T, abstract_over (v, t))
  | lambda' v t = raise TERM ("lambda'", [v, t]);

(* builds the expression (LAM v. rhs) *)
fun big_lambda v rhs = %%:"Cfun.Abs_CFun"$(lambda' v rhs);

(* builds the expression (LAM v1 v2 .. vn. rhs) *)
fun big_lambdas [] rhs = rhs
  | big_lambdas (v::vs) rhs = big_lambda v (big_lambdas vs rhs);

(* builds the expression (LAM <v1,v2,..,vn>. rhs) *)
fun lambda_ctuple [] rhs = big_lambda (%:"unit") rhs
  | lambda_ctuple (v::[]) rhs = big_lambda v rhs
  | lambda_ctuple (v::vs) rhs =
      %%:"Cprod.csplit"`(big_lambda v (lambda_ctuple vs rhs));

(* builds the expression <v1,v2,..,vn> *)
fun mk_ctuple [] = %%:"UU"
|   mk_ctuple (t::[]) = t
|   mk_ctuple (t::ts) = %%:"Cprod.cpair"`t`(mk_ctuple ts);

(*************************************************************************)
(************* fixed-point definitions and unfolding theorems ************)
(*************************************************************************)

fun add_fixdefs eqs thy =
  let
    val (lhss,rhss) = ListPair.unzip (map dest_eqs eqs);
    val fixpoint = %%:"Fix.fix"`lambda_ctuple lhss (mk_ctuple rhss);
    
    fun one_def (l as Const(n,T)) r =
          let val b = Sign.base_name n in (b, (b^"_fixdef", l == r)) end
      | one_def _ _ = sys_error "fixdefs: lhs not of correct form";
    fun defs [] _ = []
      | defs (l::[]) r = [one_def l r]
      | defs (l::ls) r = one_def l (%%:"Cprod.cfst"`r) :: defs ls (%%:"Cprod.csnd"`r);
    val (names, pre_fixdefs) = ListPair.unzip (defs lhss fixpoint);
    
    val fixdefs = map (inferT_axm (sign_of thy)) pre_fixdefs;
    val (thy', fixdef_thms) =
      PureThy.add_defs_i false (map Thm.no_attributes fixdefs) thy;
    val ctuple_fixdef_thm = foldr1 (fn (x,y) => cpair_equalI OF [x,y]) fixdef_thms;
    
    fun mk_cterm t = let val sg' = sign_of thy' in cterm_of sg' (infer sg' t) end;
    val ctuple_unfold_ct = mk_cterm (mk_trp (mk_ctuple lhss === mk_ctuple rhss));
    val ctuple_unfold_thm = prove_goalw_cterm [] ctuple_unfold_ct
          (fn _ => [rtac (ctuple_fixdef_thm RS fix_eq2 RS trans) 1,
                    simp_tac (simpset_of thy') 1]);
    val ctuple_induct_thm =
          (space_implode "_" names ^ "_induct", ctuple_fixdef_thm RS def_fix_ind);
    
    fun unfolds [] thm = []
      | unfolds (n::[]) thm = [(n^"_unfold", thm)]
      | unfolds (n::ns) thm = let
          val thmL = thm RS cpair_eqD1;
          val thmR = thm RS cpair_eqD2;
        in (n^"_unfold", thmL) :: unfolds ns thmR end;
    val unfold_thms = unfolds names ctuple_unfold_thm;
    val thms = ctuple_induct_thm :: unfold_thms;
    val (thy'', _) = PureThy.add_thms (map Thm.no_attributes thms) thy';
  in
    (thy'', names, fixdef_thms, map snd unfold_thms)
  end;

(*************************************************************************)
(*********** monadic notation and pattern matching compilation ***********)
(*************************************************************************)

fun add_names (Const(a,_), bs) = Sign.base_name a ins_string bs
  | add_names (Free(a,_) , bs) = a ins_string bs
  | add_names (f $ u     , bs) = add_names (f, add_names(u, bs))
  | add_names (Abs(a,_,t), bs) = add_names (t, a ins_string bs)
  | add_names (_         , bs) = bs;

fun add_terms ts xs = foldr add_names xs ts;

(* builds a monadic term for matching a constructor pattern *)
fun pre_build pat rhs vs taken =
  case pat of
    Const("Cfun.Rep_CFun",_)$f$(v as Free(n,T)) =>
      pre_build f rhs (v::vs) taken
  | Const("Cfun.Rep_CFun",_)$f$x =>
      let val (rhs', v, taken') = pre_build x rhs [] taken;
      in pre_build f rhs' (v::vs) taken' end
  | Const(c,T) =>
      let
        val n = variant taken "v";
        fun result_type (Type("Cfun.->",[_,T])) (x::xs) = result_type T xs
          | result_type T _ = T;
        val v = Free(n, result_type T vs);
        val m = "match_"^(extern_name(Sign.base_name c));
        val k = lambda_ctuple vs rhs;
      in
        (%%:"Fixrec.bind"`(%%:m`v)`k, v, n::taken)
      end;

(* builds a monadic term for matching a function definition pattern *)
(* returns (name, arity, matcher) *)
fun building pat rhs vs taken =
  case pat of
    Const("Cfun.Rep_CFun", _)$f$(v as Free(n,T)) =>
      building f rhs (v::vs) taken
  | Const("Cfun.Rep_CFun", _)$f$x =>
      let val (rhs', v, taken') = pre_build x rhs [] taken;
      in building f rhs' (v::vs) taken' end
  | Const(_,_) => (pat, length vs, big_lambdas vs rhs)
  | _ => sys_error "function is not declared as constant in theory";

fun match_eq eq = 
  let
    val (lhs,rhs) = dest_eqs eq;
    val (Const(name,_), arity, term) =
      building lhs (%%:"Fixrec.return"`rhs) [] (add_terms [eq] []);
  in (name, arity, term) end;

(* returns the sum (using +++) of the terms in ms *)
(* also applies "run" to the result! *)
fun fatbar arity ms =
  let
    fun unLAM 0 t = t
      | unLAM n (_$Abs(_,_,t)) = unLAM (n-1) t
      | unLAM _ _ = sys_error "FIXREC: internal error, not enough LAMs";
    fun reLAM 0 t = t
      | reLAM n t = reLAM (n-1) (%%:"Abs_CFun" $ Abs("",dummyT,t));
    fun mplus (x,y) = %%:"Fixrec.mplus"`x`y;
    val msum = foldr1 mplus (map (unLAM arity) ms);
  in
    reLAM arity (%%:"Fixrec.run"`msum)
  end;

fun unzip3 [] = ([],[],[])
  | unzip3 ((x,y,z)::ts) =
      let val (xs,ys,zs) = unzip3 ts
      in (x::xs, y::ys, z::zs) end;

(* this is the pattern-matching compiler function *)
fun compile_pats eqs = 
  let
    val ((n::names),(a::arities),mats) = unzip3 (map match_eq eqs);
    val cname = if forall (fn x => n=x) names then n
          else sys_error "FIXREC: all equations must define the same function";
    val arity = if forall (fn x => a=x) arities then a
          else sys_error "FIXREC: all equations must have the same arity";
    val rhs = fatbar arity mats;
  in
    mk_trp (%%:cname === rhs)
  end;

(*************************************************************************)
(********************** Proving associated theorems **********************)
(*************************************************************************)

fun prove_simp thy unfold_thm t =
  let
    val ss = simpset_of thy;
    val ct = cterm_of thy t;
    val thm = prove_goalw_cterm [] ct
      (fn _ => [rtac (unfold_thm RS ssubst_lhs) 1, simp_tac ss 1]);
  in thm end;

(* this proves that each equation is a theorem *)
fun prove_simps thy (unfold_thm,ts) = map (prove_simp thy unfold_thm) ts;

(* proves the pattern matching equations as theorems, using unfold *)
fun make_simps cnames unfold_thms namess attss tss thy = 
  let
    val thm_names = map (fn name => name^"_simps") cnames;
    val rew_thmss = map (prove_simps thy) (unfold_thms ~~ tss);
    val thms = (List.concat namess ~~ List.concat rew_thmss) ~~ List.concat attss;
    val (thy',_) = PureThy.add_thms thms thy;
    val thmss = thm_names ~~ rew_thmss;
    val simp_attribute = rpair [Simplifier.simp_add_global];
  in
    (#1 o PureThy.add_thmss (map simp_attribute thmss)) thy'
  end;

(*************************************************************************)
(************************* Main fixrec function **************************)
(*************************************************************************)

(* this calls the main processing function and then returns the new state *)
fun gen_add_fixrec prep_prop prep_attrib blocks thy =
  let
    fun split_list2 xss = split_list (map split_list xss);
    val ((namess, srcsss), strss) = apfst split_list2 (split_list2 blocks);
    val attss = map (map (map (prep_attrib thy))) srcsss;
    val tss = map (map (prep_prop thy)) strss;
    val ts' = map (infer thy o compile_pats) tss;
    val (thy', cnames, fixdef_thms, unfold_thms) = add_fixdefs ts' thy;
  in
    make_simps cnames unfold_thms namess attss tss thy'
  end;

val add_fixrec = gen_add_fixrec Sign.read_prop Attrib.global_attribute;
val add_fixrec_i = gen_add_fixrec Sign.cert_prop (K I);


(*************************************************************************)
(******************************** Fixpat *********************************)
(*************************************************************************)

fun fix_pat prep_term thy pat = 
  let
    val t = prep_term thy pat;
    val T = fastype_of t;
    val eq = mk_trp (HOLogic.eq_const T $ t $ Var (("x",0),T));
    val cname = case chead_of t of Const(c,_) => c | _ =>
              sys_error "FIXPAT: function is not declared as constant in theory";
    val unfold_thm = PureThy.get_thm thy (Name (cname^"_unfold"));
    val rew = prove_goalw_cterm [] (cterm_of thy eq)
          (fn _ => [stac unfold_thm 1, simp_tac (simpset_of thy) 1]);
  in rew end;

fun gen_add_fixpat prep_term prep_attrib pats thy =
  let
    val ((names, srcss), strings) = apfst ListPair.unzip (ListPair.unzip pats);
    val atts = map (map (prep_attrib thy)) srcss;
    val simps = map (fix_pat prep_term thy) strings;
    val (thy', _) = PureThy.add_thms ((names ~~ simps) ~~ atts) thy;
  in thy' end;

val add_fixpat = gen_add_fixpat Sign.read_term Attrib.global_attribute;
val add_fixpat_i = gen_add_fixpat Sign.cert_term (K I);


(*************************************************************************)
(******************************** Parsers ********************************)
(*************************************************************************)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val fixrec_decl = P.and_list1 (Scan.repeat1 (P.opt_thm_name ":" -- P.prop));

(* this builds a parser for a new keyword, fixrec, whose functionality 
is defined by add_fixrec *)
val fixrecP =
  OuterSyntax.command "fixrec" "define recursive functions (HOLCF)" K.thy_decl
    (fixrec_decl >> (Toplevel.theory o add_fixrec));

(* this adds the parser for fixrec to the syntax *)
val _ = OuterSyntax.add_parsers [fixrecP];

(* fixpat parser *)
val fixpat_decl = Scan.repeat1 (P.opt_thm_name ":" -- P.prop);

val fixpatP =
  OuterSyntax.command "fixpat" "define rewrites for fixrec functions" K.thy_decl
    (fixpat_decl >> (Toplevel.theory o add_fixpat));

val _ = OuterSyntax.add_parsers [fixpatP];

end; (* local structure *)

end; (* struct *)
