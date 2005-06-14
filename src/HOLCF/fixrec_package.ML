(*  Title:      HOLCF/fixrec_package.ML
    ID:         $Id$
    Author:     Amber Telfer and Brian Huffman

Recursive function definition package for HOLCF.
*)

signature FIXREC_PACKAGE =
sig
  val add_fixrec: string list -> theory -> theory
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

(* splits a cterm into the right and lefthand sides of equality *)
fun dest_eqs (Const ("==", _)$lhs$rhs) = (lhs, rhs)
  | dest_eqs (Const ("Trueprop", _)$(Const ("op =", _)$lhs$rhs))    = (lhs,rhs)
  | dest_eqs t = sys_error (Sign.string_of_term (sign_of (the_context())) t);

(* these are helpful functions copied from HOLCF/domain/library.ML *)
fun %: s = Free(s,dummyT);
fun %%: s = Const(s,dummyT);
infix 0 ==;  fun S ==  T = %%:"==" $ S $ T;
infix 1 ===; fun S === T = %%:"op =" $ S $ T;
infix 9 `  ; fun f ` x = %%:"Rep_CFun" $ f $ x;

(* infers the type of a term *)
fun infer t thy = #1 (Sign.infer_types (Sign.pp (sign_of thy)) (sign_of thy) (K NONE) (K NONE) [] true ([t],dummyT));

(*************************************************************************)
(************ fixed-point definitions and unfolding theorems *************)
(*************************************************************************)

fun func1 (lhs as Const(name,T), rhs) =
  let
    val basename = Sign.base_name name;
    val funcT = T ->> T;
    val functional = Const ("Cfun.Abs_CFun", (T --> T) --> funcT) $
          Abs (basename, T, abstract_over (lhs,rhs));
    val fix_type = funcT ->> T;
    val fix_const = Const ("Fix.fix", fix_type);
    val func_type = fix_type --> funcT --> T;
    val rhs' = Const ("Cfun.Rep_CFun",func_type)$fix_const$functional;
  in
    (name, (basename^"_fixdef", equals T $ lhs $ rhs'))
  end
  | func1 t = sys_error "func1: not of correct form";

(*************************************************************************)
(*********** monadic notation and pattern matching compilation ***********)
(*************************************************************************)

(* these 3 functions strip off parameters and destruct constructors *)
(*
fun strip_cpair (Const("Cfun.Rep_CFun",_) $
      (Const("Cfun.Rep_CFun",_) $ Const("Cprod.cpair",_) $ b) $ r) =
        b :: strip_cpair r
  | strip_cpair c = [c];
*)
fun big_lambda v rhs = %%:"Cfun.Abs_CFun"$(lambda v rhs);

fun big_lambdas [] rhs = rhs
  | big_lambdas (v::vs) rhs = big_lambda v (big_lambdas vs rhs);

(* builds a big lamdba expression with a tuple *)
fun lambda_tuple [] rhs = big_lambda (%:"unit") rhs
  | lambda_tuple [v] rhs = big_lambda v rhs
  | lambda_tuple (v::vs) rhs =
      %%:"Cprod.csplit"`(big_lambda v (lambda_tuple vs rhs));

fun add_names (Const(a,_), bs) = NameSpace.base a ins_string bs
  | add_names (Free(a,_), bs) = a ins_string bs
  | add_names (f$u, bs) = add_names (f, add_names(u, bs))
  | add_names (Abs(a,_,t), bs) = add_names(t,a ins_string bs)
  | add_names (_, bs) = bs;
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
        val m = "match_"^(extern_name(NameSpace.base c));
        val k = lambda_tuple vs rhs;
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
    HOLogic.mk_Trueprop (%%:cname === rhs)
  end;

(*************************************************************************)
(********************** Proving associated theorems **********************)
(*************************************************************************)

fun prove_thm thy unfold_thm ct =
  let
    val ss = simpset_of thy;
    val thm = prove_goalw_cterm [] ct
      (fn _ => [SOLVE(stac unfold_thm 1 THEN simp_tac ss 1)])
        handle _ => sys_error (string_of_cterm ct^" :: proof failed on this equation.");
  in thm end;

(* this proves that each equation is a theorem *)
fun prove_list thy unfold_thm [] = []
  | prove_list thy unfold_thm (x::xs) =
      prove_thm thy unfold_thm x :: prove_list thy unfold_thm xs;

(* this proves the def without fix is a theorem, this uses the fixpoint def *)
fun make_simp name eqs ct fixdef_thm thy' = 
  let
    val basename = NameSpace.base name;
    val ss = simpset_of thy';
    val eq_thm = fixdef_thm RS fix_eq2;
    val unfold_thm = prove_goalw_cterm [] ct
      (fn _ => [(rtac (eq_thm RS trans) 1) THEN (simp_tac ss 1)]);
    val ind_thm = fixdef_thm RS def_fix_ind;
    val rew_thms = prove_list thy' unfold_thm eqs;
    val thmss =
      [ (basename^"_unfold", [unfold_thm])
      , (basename^"_ind", [ind_thm])
      , (basename^"_rews", rew_thms) ]
  in
    (#1 o PureThy.add_thmss (map Thm.no_attributes thmss)) thy'
  end;

(*************************************************************************)
(************************* Main fixrec function **************************)
(*************************************************************************)

(* this calls the main processing function and then returns the new state *)
fun add_fixrec strs thy =
  let
    val sg = sign_of thy;
    val cts = map (Thm.read_cterm sg o rpair propT) strs;
    val eqs = map term_of cts;
    val funcc = infer (compile_pats eqs) thy;
    val _ = print_cterm (cterm_of sg funcc);
    val (name', fixdef_name_term) = func1 (dest_eqs funcc);
    val (thy', [fixdef_thm]) =
      PureThy.add_defs_i false [Thm.no_attributes fixdef_name_term] thy;
    val ct = cterm_of (sign_of thy') funcc;
  in
    make_simp name' cts ct fixdef_thm thy'
  end;

(*************************************************************************)
(******************************** Fixpat *********************************)
(*************************************************************************)

fun fix_pat name pat thy = 
  let
    val sign = sign_of thy;
    val t = term_of (Thm.read_cterm sign (pat, dummyT));
    val T = fastype_of t;
    val eq = HOLogic.mk_Trueprop (HOLogic.eq_const T $ t $ Var (("x",0),T));
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

val fixrec_decl = (*P.and_list1*) (Scan.repeat1 P.prop);

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
