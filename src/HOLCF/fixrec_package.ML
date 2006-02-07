(*  Title:      HOLCF/fixrec_package.ML
    ID:         $Id$
    Author:     Amber Telfer and Brian Huffman

Recursive function definition package for HOLCF.
*)

signature FIXREC_PACKAGE =
sig
  val add_fixrec: bool -> ((string * Attrib.src list) * string) list list -> theory -> theory
  val add_fixrec_i: bool -> ((string * attribute list) * term) list list -> theory -> theory
  val add_fixpat: (string * Attrib.src list) * string list -> theory -> theory
  val add_fixpat_i: (string * attribute list) * term list -> theory -> theory
end;

structure FixrecPackage: FIXREC_PACKAGE =
struct

fun fixrec_err s = error ("fixrec definition error:\n" ^ s);
fun fixrec_eq_err thy s eq =
  fixrec_err (s ^ "\nin\n" ^ quote (Sign.string_of_term thy eq));

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
fun dest_eqs t = HOLogic.dest_eq (HOLogic.dest_Trueprop t);
(*
fun dest_eqs (Const ("==", _)$lhs$rhs) = (lhs, rhs)
  | dest_eqs (Const ("Trueprop", _)$(Const ("op =", _)$lhs$rhs)) = (lhs,rhs)
  | dest_eqs t = fixrec_err (Sign.string_of_term (sign_of (the_context())) t);
*)
(* similar to Thm.head_of, but for continuous application *)
fun chead_of (Const("Cfun.Rep_CFun",_)$f$t) = chead_of f
  | chead_of u = u;

(* these are helpful functions copied from HOLCF/domain/library.ML *)
fun %: s = Free(s,dummyT);
fun %%: s = Const(s,dummyT);
infix 0 ==;  fun S ==  T = %%:"==" $ S $ T;
infix 1 ===; fun S === T = %%:"op =" $ S $ T;
infix 9 `  ; fun f ` x = %%:"Cfun.Rep_CFun" $ f $ x;

(* infers the type of a term *)  (* FIXME better avoid this low-level stuff *)
(* similar to Theory.inferT_axm, but allows any type, not just propT *)
fun infer sg t =
  fst (Sign.infer_types (Sign.pp sg) sg (Sign.consts_of sg) (K NONE) (K NONE) [] true
    ([t],dummyT));

(* builds the expression (LAM v. rhs) *)
fun big_lambda v rhs = %%:"Cfun.Abs_CFun"$(Term.lambda v rhs);

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
          let val b = Sign.base_name n in (b, (b^"_def", l == r)) end
      | one_def _ _ = fixrec_err "fixdefs: lhs not of correct form";
    fun defs [] _ = []
      | defs (l::[]) r = [one_def l r]
      | defs (l::ls) r = one_def l (%%:"Cprod.cfst"`r) :: defs ls (%%:"Cprod.csnd"`r);
    val (names, pre_fixdefs) = ListPair.unzip (defs lhss fixpoint);
    
    val fixdefs = map (inferT_axm thy) pre_fixdefs;
    val (fixdef_thms, thy') =
      PureThy.add_defs_i false (map Thm.no_attributes fixdefs) thy;
    val ctuple_fixdef_thm = foldr1 (fn (x,y) => cpair_equalI OF [x,y]) fixdef_thms;
    
    val ctuple_unfold = infer thy' (mk_trp (mk_ctuple lhss === mk_ctuple rhss));
    val ctuple_unfold_thm = standard (Goal.prove thy' [] [] ctuple_unfold
          (fn _ => EVERY [rtac (ctuple_fixdef_thm RS fix_eq2 RS trans) 1,
                    simp_tac (simpset_of thy') 1]));
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
    val (_, thy'') = PureThy.add_thms (map Thm.no_attributes thms) thy';
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
      end
  | Free(n,_) => fixrec_err ("expected constructor, found free variable " ^ quote n)
  | _ => fixrec_err "pre_build: invalid pattern";

(* builds a monadic term for matching a function definition pattern *)
(* returns (name, arity, matcher) *)
fun building pat rhs vs taken =
  case pat of
    Const("Cfun.Rep_CFun", _)$f$(v as Free(n,T)) =>
      building f rhs (v::vs) taken
  | Const("Cfun.Rep_CFun", _)$f$x =>
      let val (rhs', v, taken') = pre_build x rhs [] taken;
      in building f rhs' (v::vs) taken' end
  | Const(name,_) => (name, length vs, big_lambdas vs rhs)
  | _ => fixrec_err "function is not declared as constant in theory";

fun match_eq eq = 
  let val (lhs,rhs) = dest_eqs eq;
  in building lhs (%%:"Fixrec.return"`rhs) [] (add_terms [eq] []) end;

(* returns the sum (using +++) of the terms in ms *)
(* also applies "run" to the result! *)
fun fatbar arity ms =
  let
    fun unLAM 0 t = t
      | unLAM n (_$Abs(_,_,t)) = unLAM (n-1) t
      | unLAM _ _ = fixrec_err "fatbar: internal error, not enough LAMs";
    fun reLAM 0 t = t
      | reLAM n t = reLAM (n-1) (%%:"Cfun.Abs_CFun" $ Abs("",dummyT,t));
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
          else fixrec_err "all equations in block must define the same function";
    val arity = if forall (fn x => a=x) arities then a
          else fixrec_err "all equations in block must have the same arity";
    val rhs = fatbar arity mats;
  in
    mk_trp (%%:cname === rhs)
  end;

(*************************************************************************)
(********************** Proving associated theorems **********************)
(*************************************************************************)

(* proves a block of pattern matching equations as theorems, using unfold *)
fun make_simps thy (unfold_thm, eqns) =
  let
    val tacs = [rtac (unfold_thm RS ssubst_lhs) 1, asm_simp_tac (simpset_of thy) 1];
    fun prove_term t = standard (Goal.prove thy [] [] t (K (EVERY tacs)));
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
    
    val ((names, srcss), strings) = apfst split_list (split_list eqns);
    val atts = map (map (prep_attrib thy)) srcss;
    val eqn_ts = map (prep_prop thy) strings;
    val rec_ts = map (fn eq => chead_of (fst (dest_eqs (Logic.strip_imp_concl eq)))
      handle TERM _ => fixrec_eq_err thy "not a proper equation" eq) eqn_ts;
    val (_, eqn_ts') = InductivePackage.unify_consts thy rec_ts eqn_ts;
    
    fun unconcat [] _ = []
      | unconcat (n::ns) xs = List.take (xs,n) :: unconcat ns (List.drop (xs,n));
    val pattern_blocks = unconcat lengths (map Logic.strip_imp_concl eqn_ts');
    val compiled_ts = map (infer thy o compile_pats) pattern_blocks;
    val (thy', cnames, fixdef_thms, unfold_thms) = add_fixdefs compiled_ts thy;
  in
    if strict then let (* only prove simp rules if strict = true *)
      val eqn_blocks = unconcat lengths ((names ~~ eqn_ts') ~~ atts);
      val simps = List.concat (map (make_simps thy') (unfold_thms ~~ eqn_blocks));
      val (simp_thms, thy'') = PureThy.add_thms simps thy';
      
      val simp_names = map (fn name => name^"_simps") cnames;
      val simp_attribute = rpair [Simplifier.simp_add];
      val simps' = map simp_attribute (simp_names ~~ unconcat lengths simp_thms);
    in
      (snd o PureThy.add_thmss simps') thy''
    end
    else thy'
  end;

val add_fixrec = gen_add_fixrec Sign.read_prop Attrib.attribute;
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
    val unfold_thm = PureThy.get_thm thy (Name (cname^"_unfold"));
    val simp = standard (Goal.prove thy [] [] eq
          (fn _ => EVERY [stac unfold_thm 1, simp_tac (simpset_of thy) 1]));
  in simp end;

fun gen_add_fixpat prep_term prep_attrib ((name, srcs), strings) thy =
  let
    val atts = map (prep_attrib thy) srcs;
    val ts = map (prep_term thy) strings;
    val simps = map (fix_pat thy) ts;
  in
    (snd o PureThy.add_thmss [((name, simps), atts)]) thy
  end;

val add_fixpat = gen_add_fixpat Sign.read_term Attrib.attribute;
val add_fixpat_i = gen_add_fixpat Sign.cert_term (K I);


(*************************************************************************)
(******************************** Parsers ********************************)
(*************************************************************************)

local structure P = OuterParse and K = OuterKeyword in

val fixrec_eqn = P.opt_thm_name ":" -- P.prop;

val fixrec_strict = P.opt_keyword "permissive" >> not;

val fixrec_decl = fixrec_strict -- P.and_list1 (Scan.repeat1 fixrec_eqn);

(* this builds a parser for a new keyword, fixrec, whose functionality 
is defined by add_fixrec *)
val fixrecP =
  OuterSyntax.command "fixrec" "define recursive functions (HOLCF)" K.thy_decl
    (fixrec_decl >> (Toplevel.theory o uncurry add_fixrec));

(* fixpat parser *)
val fixpat_decl = P.opt_thm_name ":" -- Scan.repeat1 P.prop;

val fixpatP =
  OuterSyntax.command "fixpat" "define rewrites for fixrec functions" K.thy_decl
    (fixpat_decl >> (Toplevel.theory o add_fixpat));

val _ = OuterSyntax.add_parsers [fixrecP, fixpatP];

end; (* local structure *)

end; (* struct *)
