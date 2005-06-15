(*  Title:      HOLCF/fixrec_package.ML
    ID:         $Id$
    Author:     Amber Telfer and Brian Huffman

Recursive function definition package for HOLCF.
*)

signature FIXREC_PACKAGE =
sig
  val add_fixrec: string list list -> theory -> theory
  val add_fixpat: string * string -> theory -> theory
end;

structure FixrecPackage: FIXREC_PACKAGE =
struct

local
open ThyParse in

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
  | dest_eqs (Const ("Trueprop", _)$(Const ("op =", _)$lhs$rhs))    = (lhs,rhs)
  | dest_eqs t = sys_error (Sign.string_of_term (sign_of (the_context())) t);

(* these are helpful functions copied from HOLCF/domain/library.ML *)
fun %: s = Free(s,dummyT);
fun %%: s = Const(s,dummyT);
infix 0 ==;  fun S ==  T = %%:"==" $ S $ T;
infix 1 ===; fun S === T = %%:"op =" $ S $ T;
infix 9 `  ; fun f ` x = %%:"Cfun.Rep_CFun" $ f $ x;

(* infers the type of a term *)
(* similar to Theory.inferT_axm, but allows any type *)
fun infer sg t =
  fst (Sign.infer_types (Sign.pp sg) sg (K NONE) (K NONE) [] true ([t],dummyT));

(* The next few functions build continuous lambda abstractions *)

(* Similar to Term.lambda, but allows abstraction over constants *)
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
(************************ fixed-point definitions ************************)
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
          (space_implode "_" names ^ "_induct", [ctuple_fixdef_thm RS def_fix_ind]);
    
    fun unfolds [] thm = []
      | unfolds (n::[]) thm = [(n^"_unfold", [thm])]
      | unfolds (n::ns) thm = let
          val thmL = thm RS cpair_eqD1;
          val thmR = thm RS cpair_eqD2;
        in (n^"_unfold", [thmL]) :: unfolds ns thmR end;
    val unfold_thmss = unfolds names ctuple_unfold_thm;
    val thmss = ctuple_induct_thm :: unfold_thmss;
    val (thy'', _) = PureThy.add_thmss (map Thm.no_attributes thmss) thy';
  in
    (thy'', names, fixdef_thms, List.concat (map snd unfold_thmss))
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

fun prove_rew thy unfold_thm ct =
  let
    val ss = simpset_of thy;
    val thm = prove_goalw_cterm [] ct
      (fn _ => [SOLVE(stac unfold_thm 1 THEN simp_tac ss 1)])
        handle _ => sys_error (string_of_cterm ct^" :: proof failed on this equation.");
  in thm end;

(* this proves that each equation is a theorem *)
fun prove_rews thy (unfold_thm,cts) = map (prove_rew thy unfold_thm) cts;

(* proves the pattern matching equations as theorems, using unfold *)
fun make_simps names unfold_thms ctss thy = 
  let
    val thm_names = map (fn name => name^"_rews") names;
    val rew_thmss = ListPair.map (prove_rews thy) (unfold_thms, ctss);
    val thmss = ListPair.zip (thm_names, rew_thmss);
  in
    (#1 o PureThy.add_thmss (map Thm.no_attributes thmss)) thy
  end;

(* this proves the def without fix is a theorem, this uses the fixpoint def *)
(*
fun make_simp name eqs ct fixdef_thm thy' = 
  let
    val ss = simpset_of thy';
    val eq_thm = fixdef_thm RS fix_eq2;
    val ind_thm = fixdef_thm RS def_fix_ind;
    val rew_thms = prove_list thy' unfold_thm eqs;
    val thmss =
      [ (basename^"_unfold", [unfold_thm])
      , (basename^"_ind", [ind_thm])
      , (basename^"_rews", rew_thms) ]
  in
    (#1 o PureThy.add_thmss (map Thm.no_attributes thmss)) thy'
  end;
*)
(*************************************************************************)
(************************* Main fixrec function **************************)
(*************************************************************************)

(* this calls the main processing function and then returns the new state *)
fun add_fixrec strss thy =
  let
    val sg = sign_of thy;
    val ctss = map (map (Thm.read_cterm sg o rpair propT)) strss;
    val tss = map (map term_of) ctss;
    val ts' = map (fn ts => infer sg (compile_pats ts)) tss;
    val (thy', names, fixdef_thms, unfold_thms) = add_fixdefs ts' thy;
  in
    make_simps names unfold_thms ctss thy'
  end;

(*************************************************************************)
(******************************** Fixpat *********************************)
(*************************************************************************)

fun fix_pat name pat thy = 
  let
    val sign = sign_of thy;
    val t = term_of (Thm.read_cterm sign (pat, dummyT));
    val T = fastype_of t;
    val eq = mk_trp (HOLogic.eq_const T $ t $ Var (("x",0),T));
    fun head_const (Const ("Cfun.Rep_CFun",_) $ f $ t) = head_const f
      | head_const (Const (c,_)) = c
      | head_const _ = sys_error "FIXPAT: function is not declared as constant in theory";
    val c = head_const t;
    val unfold_thm = Goals.get_thm thy (c^"_unfold");
    val thm = prove_goalw_cterm [] (cterm_of sign eq)
          (fn _ => [stac unfold_thm 1, simp_tac (simpset_of thy) 1]);
    val _ = print_thm thm;
  in
    (#1 o PureThy.add_thmss [Thm.no_attributes (name, [thm])]) thy
  end;

fun add_fixpat (name,pat) = fix_pat name pat;

(*************************************************************************)
(******************************** Parsers ********************************)
(*************************************************************************)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val fixrec_decl = P.and_list1 (Scan.repeat1 P.prop);

(* this builds a parser for a new keyword, fixrec, whose functionality 
is defined by add_fixrec *)
val fixrecP =
  OuterSyntax.command "fixrec" "parser for fixrec functions" K.thy_decl
    (fixrec_decl >> (Toplevel.theory o add_fixrec));

(* this adds the parser for fixrec to the syntax *)
val _ = OuterSyntax.add_parsers [fixrecP];

(* fixpat parser *)
val fixpat_decl = P.name -- P.prop;

val fixpatP =
  OuterSyntax.command "fixpat" "testing out this parser" K.thy_decl
    (fixpat_decl >> (Toplevel.theory o add_fixpat));

val _ = OuterSyntax.add_parsers [fixpatP];

end; (* local structure *)

end; (* local open *)

end; (* struct *)
