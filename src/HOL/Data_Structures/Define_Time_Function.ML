
signature TIMING_FUNCTIONS =
sig
type 'a converter = {
  constc : local_theory -> term list -> (term -> 'a) -> term -> 'a,
  funcc : local_theory -> term list -> (term -> 'a) -> term -> term list -> 'a,
  ifc : local_theory -> term list -> (term -> 'a) -> typ -> term -> term -> term -> 'a,
  casec : local_theory -> term list -> (term -> 'a) -> term -> term list -> 'a,
  letc : local_theory -> term list -> (term -> 'a) -> typ -> term -> string list -> typ list -> term -> 'a
};
val walk : local_theory -> term list -> 'a converter -> term -> 'a

type pfunc = { names : string list, terms : term list, typs : typ list }
val fun_pretty':  Proof.context -> pfunc -> Pretty.T
val fun_pretty:  Proof.context -> Function.info -> Pretty.T
val print_timing':  Proof.context -> pfunc -> pfunc -> unit
val print_timing:  Proof.context -> Function.info -> Function.info -> unit

val reg_and_proove_time_func: theory -> term list -> term list
      -> bool -> Function.info * theory
val reg_time_func: theory -> term list -> term list
      -> bool -> theory

val time_dom_tac: Proof.context -> thm -> thm list -> int -> tactic

end

structure Timing_Functions : TIMING_FUNCTIONS =
struct
(* Configure config variable to adjust the prefix *)
val bprefix = Attrib.setup_config_string @{binding "time_prefix"} (K "T_")

(* some default values to build terms easier *)
val zero = Const (@{const_name "Groups.zero"}, HOLogic.natT)
val one = Const (@{const_name "Groups.one"}, HOLogic.natT)
(* Extracts terms from function info *)
fun terms_of_info (info: Function.info) =
let
  val {simps, ...} = info
in
  map Thm.prop_of (case simps of SOME s => s | NONE => error "No terms of function found in info")
end;

type pfunc = {
  names : string list,
  terms : term list,
  typs : typ list
}
fun info_pfunc (info: Function.info): pfunc =
let
  val {defname, fs, ...} = info;
  val T = case hd fs of (Const (_,T)) => T | _ => error "Internal error: Invalid info to print"
in
  { names=[Binding.name_of defname], terms=terms_of_info info, typs=[T] }
end

(* Auxiliary functions for printing functions *)
fun fun_pretty' ctxt (pfunc: pfunc) =
let
  val {names, terms, typs} = pfunc;
  val header_beg = Pretty.str "fun ";
  fun prepHeadCont (nm,T) = [Pretty.str (nm ^ " :: "), (Pretty.quote (Syntax.pretty_typ ctxt T))]
  val header_content =
     List.concat (prepHeadCont (hd names,hd typs) :: map ((fn l => Pretty.str "\nand " :: l) o prepHeadCont) (ListPair.zip (tl names, tl typs)));
  val header_end = Pretty.str " where\n  ";
  val header = [header_beg] @ header_content @ [header_end];
  fun separate sep prts =
    flat (Library.separate [Pretty.str sep] (map single prts));
  val ptrms = (separate "\n| " (map (Syntax.pretty_term ctxt) terms));
in
  Pretty.text_fold (header @ ptrms)
end
fun fun_pretty ctxt = fun_pretty' ctxt o info_pfunc
fun print_timing' ctxt (opfunc: pfunc) (tpfunc: pfunc) =
let
  val {names, ...} = opfunc;
  val poriginal = Pretty.item [Pretty.str "Original function:\n", fun_pretty' ctxt opfunc]
  val ptiming = Pretty.item [Pretty.str ("Running time function:\n"), fun_pretty' ctxt tpfunc]
in
  Pretty.writeln (Pretty.text_fold [Pretty.str ("Converting " ^ (hd names) ^ (String.concat (map (fn nm => ", " ^ nm) (tl names))) ^ "\n"), poriginal, Pretty.str "\n", ptiming])
end
fun print_timing ctxt (oinfo: Function.info) (tinfo: Function.info) =
  print_timing' ctxt (info_pfunc oinfo) (info_pfunc tinfo)

val If_name = @{const_name "HOL.If"}
val Let_name = @{const_name "HOL.Let"}

fun contains l e = exists (fn e' => e' = e) l
fun zip [] [] = []
  | zip (x::xs) (y::ys) = (x, y) :: zip xs ys
  | zip _ _ = error "Internal error: Cannot zip lists with differing size"
fun index [] _ = 0
  | index (x::xs) el = (if x = el then 0 else 1 + index xs el)
fun used_for_const orig_used t i = orig_used (t,i)

(* returns true if it's an if term *)
fun is_if (Const (n,_)) = (n = If_name)
  | is_if _ = false
(* returns true if it's a case term *)
fun is_case (Const (n,_)) = String.isPrefix "case_" (List.last (String.fields (fn s => s = #".") n))
  | is_case _ = false
(* returns true if it's a let term *)
fun is_let (Const (n,_)) = (n = Let_name)
  | is_let _ = false
(* change type of original function to new type (_ \<Rightarrow> ... \<Rightarrow> _ to _ \<Rightarrow> ... \<Rightarrow> nat)
    and replace all function arguments f with (t*T_f) *)
fun change_typ' used i (Type ("fun", [T1, T2])) = 
      Type ("fun", [check_for_fun' (used i) T1, change_typ' used (i+1) T2])
  | change_typ' _ _ _ = HOLogic.natT
and check_for_fun' true (f as Type ("fun", [_,_])) = HOLogic.mk_prodT (f, change_typ' (K false) 0 f)
  | check_for_fun' false (f as Type ("fun", [_,_])) = change_typ' (K false) 0 f
  | check_for_fun' _ t = t
val change_typ = change_typ' (K false) 0
(* Convert string name of function to its timing equivalent *)
fun fun_name_to_time ctxt name =
let
  val prefix = Config.get ctxt bprefix
  fun replace_last_name [n] = [prefix ^ n]
    | replace_last_name (n::ns) = n :: (replace_last_name ns)
    | replace_last_name _ = error "Internal error: Invalid function name to convert"
  val parts = String.fields (fn s => s = #".") name
in
  String.concatWith "." (replace_last_name parts)
end
(* Count number of arguments of a function *)
fun count_args (Type (n, [_,res])) = (if n = "fun" then 1 + count_args res else 0)
  | count_args _ = 0
(* Check if number of arguments matches function *)
fun check_args s (Const (_,T), args) =
    (if length args = count_args T then () else error ("Partial applications/Lambdas not allowed (" ^ s ^ ")"))
  | check_args s (Free (_,T), args) =
    (if length args = count_args T then () else error ("Partial applications/Lambdas not allowed (" ^ s ^ ")"))
  | check_args s _ = error ("Partial applications/Lambdas not allowed (" ^ s ^ ")")
(* Removes Abs *)
fun rem_abs f (Abs (_,_,t)) = rem_abs f t
  | rem_abs f t = f t
(* Map right side of equation *)
fun map_r f (pT $ (eq $ l $ r)) = (pT $ (eq $ l $ f r))
  | map_r _ _ = error "Internal error: No right side of equation found"
(* Get left side of equation *)
fun get_l (_ $ (_ $ l $ _)) = l
  | get_l _ = error "Internal error: No left side of equation found"
(* Get right side of equation *)
fun get_r (_ $ (_ $ _ $ r)) = r
  | get_r _ = error "Internal error: No right side of equation found"
(* Return name of Const *)
fun Const_name (Const (nm,_)) = SOME nm
  | Const_name _ = NONE
fun is_Used (Type ("Product_Type.prod", _)) = true
  | is_Used _ = false

fun time_term ctxt (Const (nm,T)) =
let
  val T_nm = fun_name_to_time ctxt nm
  val T_T = change_typ T
in
(SOME (Syntax.check_term ctxt (Const (T_nm,T_T))))
  handle (ERROR _) =>
    case Syntax.read_term ctxt (Long_Name.base_name T_nm)
      of (Const (nm,T_T)) =>
        let
          fun col_Used i (Type ("fun", [Type ("fun", _), Ts])) (Type ("fun", [T', Ts'])) =
            (if is_Used T' then [i] else []) @ col_Used (i+1) Ts Ts'
            | col_Used i (Type ("fun", [_, Ts])) (Type ("fun", [_, Ts'])) = col_Used (i+1) Ts Ts'
            | col_Used _ _ _ = []
        in
          SOME (Const (nm,change_typ' (contains (col_Used 0 T T_T)) 0 T))
        end
       | _ => error ("Timing function of " ^ nm ^ " is not defined")
end
  | time_term _ _ = error "Internal error: No valid function given"

type 'a converter = {
  constc : local_theory -> term list -> (term -> 'a) -> term -> 'a,
  funcc : local_theory -> term list -> (term -> 'a) -> term -> term list -> 'a,
  ifc : local_theory -> term list -> (term -> 'a) -> typ -> term -> term -> term -> 'a,
  casec : local_theory -> term list -> (term -> 'a) -> term -> term list -> 'a,
  letc : local_theory -> term list -> (term -> 'a) -> typ -> term -> string list -> typ list -> term -> 'a
};

(* Walks over term and calls given converter *)
fun walk_func (t1 $ t2) ts = walk_func t1 (t2::ts)
  | walk_func t ts = (t, ts)
fun build_func (f, []) = f
  | build_func (f, (t::ts)) = build_func (f$t, ts)
fun walk_abs (Abs (nm,T,t)) nms Ts = walk_abs t (nm::nms) (T::Ts)
  | walk_abs t nms Ts = (t, nms, Ts)
fun build_abs t (nm::nms) (T::Ts) = build_abs (Abs (nm,T,t)) nms Ts
  | build_abs t [] [] = t
  | build_abs _ _ _ = error "Internal error: Invalid terms to build abs"
fun walk ctxt (origin: term list) (conv as {ifc, casec, funcc, letc, ...} : 'a converter) (t as _ $ _) =
  let
    val (f, args) = walk_func t []
    val this = (walk ctxt origin conv)
    val _ = (case f of Abs _ => error "Lambdas not supported" | _ => ())
  in
    (if is_if f then
      (case f of (Const (_,T)) =>
        (case args of [cond, t, f] => ifc ctxt origin this T cond t f
                   | _ => error "Partial applications not supported (if)")
               | _ => error "Internal error: invalid if term")
      else if is_case f then casec ctxt origin this f args
      else if is_let f then
      (case f of (Const (_,lT)) =>
         (case args of [exp, t] => 
            let val (t,nms,Ts) = walk_abs t [] [] in letc ctxt origin this lT exp nms Ts t end
                     | _ => error "Partial applications not allowed (let)")
               | _ => error "Internal error: invalid let term")
      else funcc ctxt origin this f args)
  end
  | walk ctxt origin (conv as {constc, ...}) c = 
      constc ctxt origin (walk ctxt origin conv) c

(* 1. Fix all terms *)
(* Exchange Var in types and terms to Free *)
fun fixTerms (Var(ixn,T)) = Free (fst ixn, T)
  | fixTerms t = t
fun fixTypes (TVar ((t, _), T)) = TFree (t, T)
  | fixTypes t = t

fun noFun (Type ("fun", _)) = error "Functions in datatypes are not allowed in case constructions"
  | noFun T = T
fun casecBuildBounds n t = if n > 0 then casecBuildBounds (n-1) (t $ (Bound (n-1))) else t
fun casecAbs ctxt f n (Type ("fun",[T,Tr])) (Abs (v,Ta,t)) = ( map_atyps noFun T; Abs (v,Ta,casecAbs ctxt f n Tr t))
  | casecAbs ctxt f n (Type ("fun",[T,Tr])) t =
    (map_atyps noFun T; case Variable.variant_fixes ["x"] ctxt of ([v],ctxt) =>
    (Abs (v,T,casecAbs ctxt f (n + 1) Tr t))
    | _ => error "Internal error: could not fix variable")
  | casecAbs _ f n _ t = f (casecBuildBounds n (Term.incr_bv n 0 t))
fun fixCasecCases _ _ _ [t] = [t]
  | fixCasecCases ctxt f (Type (_,[T,Tr])) (t::ts) = casecAbs ctxt f 0 T t :: fixCasecCases ctxt f Tr ts
  | fixCasecCases _ _ _ _ = error "Internal error: invalid case types/terms"
fun fixCasec ctxt _ f (t as Const (_,T)) args =
      (check_args "cases" (t,args); build_func (t,fixCasecCases ctxt f T args))
  | fixCasec _ _ _ _ _ = error "Internal error: invalid case term"

fun fixPartTerms ctxt (term: term list) t =
  let
    val _ = check_args "args" (walk_func (get_l t) [])
  in
    map_r (walk ctxt term {
          funcc = (fn _ => fn _ => fn f => fn t => fn args =>
              (check_args "func" (t,args); build_func (t, map f args))),
          constc = (fn _ => fn _ => fn _ => fn c => (case c of Abs _ => error "Lambdas not supported" | _ => c)),
          ifc = (fn _ => fn _ => fn f => fn T => fn cond => fn tt => fn tf =>
            ((Const (If_name, T)) $ f cond $ (f tt) $ (f tf))),
          casec = fixCasec,
          letc = (fn _ => fn _ => fn f => fn expT => fn exp => fn nms => fn Ts => fn t =>
              let
                val f' = if length nms = 0 then
                (case f (t$exp) of t$_ => t | _ => error "Internal error: case could not be fixed (let)")
                else f t
              in (Const (Let_name,expT) $ (f exp) $ build_abs f' nms Ts) end)
      }) t
  end

(* 2. Check for properties about the function *)
(* 2.1 Check if function is recursive *)
fun or f (a,b) = f a orelse b
fun find_rec ctxt term = (walk ctxt term {
          funcc = (fn _ => fn _ => fn f => fn t => fn args => List.exists (fn term => Const_name t = Const_name term) term orelse List.foldr (or f) false args),
          constc = (K o K o K o K) false,
          ifc = (fn _ => fn _ => fn f => fn _ => fn cond => fn tt => fn tf => f cond orelse f tt orelse f tf),
          casec = (fn _ => fn _ => fn f => fn t => fn cs => f t orelse List.foldr (or (rem_abs f)) false cs),
          letc = (fn _ => fn _ => fn f => fn _ => fn exp => fn _ => fn _ => fn t => f exp orelse f t)
      }) o get_r
fun is_rec ctxt (term: term list) = List.foldr (or (find_rec ctxt term)) false

(* 2.2 Check for higher-order function if original function is used *)
fun find_used' ctxt term t T_t =
let
  val (ident, _) = walk_func (get_l t) []
  val (T_ident, T_args) = walk_func (get_l T_t) []

  fun filter_passed [] = []
    | filter_passed ((f as Free (_, Type ("Product_Type.prod",[Type ("fun",_), Type ("fun", _)])))::args) = 
        f :: filter_passed args
    | filter_passed (_::args) = filter_passed args
  val frees' = (walk ctxt term {
          funcc = (fn _ => fn _ => fn f => fn t => fn args =>
              (case t of (Const ("Product_Type.prod.snd", _)) => []
                  | _ => (if t = T_ident then [] else filter_passed args)
                    @ List.foldr (fn (l,r) => f l @ r) [] args)),
          constc = (K o K o K o K) [],
          ifc = (fn _ => fn _ => fn f => fn _ => fn cond => fn tt => fn tf => f cond @ f tt @ f tf),
          casec = (fn _ => fn _ => fn f => fn _ => fn cs => List.foldr (fn (l,r) => f l @ r) [] cs),
          letc = (fn _ => fn _ => fn f => fn _ => fn exp => fn _ => fn _ => fn t => f exp @ f t)
      }) (get_r T_t)
  fun build _ [] _ = false
    | build i (a::args) item =
        (if item = (ident,i) then contains frees' a else build (i+1) args item)
in
  build 0 T_args
end
fun find_used ctxt term terms T_terms =
  zip terms T_terms
  |> List.map (fn (t, T_t) => find_used' ctxt term t T_t)
  |> List.foldr (fn (f,g) => fn item => f item orelse g item) (K false)


(* 3. Convert equations *)
(* Some Helper *)
val plusTyp = @{typ "nat => nat => nat"}
fun plus (SOME a) (SOME b) = SOME (Const (@{const_name "Groups.plus"}, plusTyp) $ a $ b)
  | plus (SOME a) NONE = SOME a
  | plus NONE (SOME b) = SOME b
  | plus NONE NONE = NONE
fun opt_term NONE = HOLogic.zero
  | opt_term (SOME t) = t
fun use_origin (Free (nm, T as Type ("fun",_))) = HOLogic.mk_fst (Free (nm,HOLogic.mk_prodT (T, change_typ T)))
  | use_origin t = t

(* Converting of function term *)
fun fun_to_time ctxt orig_used _ (origin: term list) (func as Const (nm,T)) =
let
  val prefix = Config.get ctxt bprefix
  val used' = used_for_const orig_used func
in
  if contains origin func then SOME (Free (prefix ^ Term.term_name func, change_typ' used' 0 T)) else
  if Zero_Funcs.is_zero (Proof_Context.theory_of ctxt) (nm,T) then NONE else
    time_term ctxt func
end
  | fun_to_time ctxt _ used _ (f as Free (nm,T)) = SOME (
      if used f then HOLogic.mk_snd (Free (nm,HOLogic.mk_prodT (T,change_typ T)))
      else Free (Config.get ctxt bprefix ^ nm, change_typ T)
      )
  | fun_to_time _ _ _ _ _ = error "Internal error: invalid function to convert"

(* Convert arguments of left side of a term *)
fun conv_arg ctxt used _ (f as Free (nm,T as Type("fun",_))) =
    if used f then Free (nm, HOLogic.mk_prodT (T, change_typ' (K false) 0 T))
    else Free (Config.get ctxt bprefix ^ nm, change_typ' (K false) 0 T)
  | conv_arg ctxt _ origin (f as Const (_, Type("fun",_))) =
      (error "weird case i don't understand TODO"; HOLogic.mk_prod (f, fun_to_time ctxt (K false) (K false) origin f |> Option.valOf))
  | conv_arg _ _ _ x = x
fun conv_args ctxt used origin = map (conv_arg ctxt used origin)

(* Handle function calls *)
fun build_zero (Type ("fun", [T, R])) = Abs ("x", T, build_zero R)
  | build_zero _ = zero
fun funcc_use_origin _ _ used (f as Free (nm, T as Type ("fun",_))) =
    if used f then HOLogic.mk_fst (Free (nm,HOLogic.mk_prodT (T, change_typ T)))
    else error "Internal error: Error in used detection"
  | funcc_use_origin _ _ _ t = t
fun funcc_conv_arg ctxt origin used _ (t as (_ $ _)) = map_aterms (funcc_use_origin ctxt origin used) t
  | funcc_conv_arg ctxt _ used u (f as Free (nm, T as Type ("fun",_))) =
      if used f then
        if u then Free (nm, HOLogic.mk_prodT (T, change_typ T))
        else HOLogic.mk_snd (Free (nm,HOLogic.mk_prodT (T,change_typ T)))
      else Free (Config.get ctxt bprefix ^ nm, change_typ T)
  | funcc_conv_arg ctxt origin _ true (f as Const (_,T as Type ("fun",_))) =
  (Const (@{const_name "Product_Type.Pair"},
      Type ("fun", [T,Type ("fun", [change_typ T, HOLogic.mk_prodT (T,change_typ T)])]))
    $ f $ (Option.getOpt (fun_to_time ctxt (K false) (K false) origin f, build_zero T)))
  | funcc_conv_arg ctxt origin _ false (f as Const (_,T as Type ("fun",_))) =
      Option.getOpt (fun_to_time ctxt (K false) (K false) origin f, build_zero T)
  | funcc_conv_arg _ _ _ _ t = t

fun funcc_conv_args _ _ _ _ [] = []
  | funcc_conv_args ctxt origin used (Type ("fun", [t, ts])) (a::args) =
      funcc_conv_arg ctxt origin used (is_Used t) a :: funcc_conv_args ctxt origin used ts args
  | funcc_conv_args _ _ _ _ _ = error "Internal error: Non matching type"
fun funcc orig_used used ctxt (origin: term list) f func args =
let
  fun get_T (Free (_,T)) = T
    | get_T (Const (_,T)) = T
    | get_T (_ $ (Free (_,Type (_, [_, T])))) = T (* Case of snd was constructed *)
    | get_T _ = error "Internal error: Forgotten type"
in
  List.foldr (I #-> plus)
  (case fun_to_time ctxt orig_used used origin func
    of SOME t => SOME (build_func (t,funcc_conv_args ctxt origin used (get_T t) args))
    | NONE => NONE)
  (map f args)
end

(* Handle case terms *)
fun casecIsCase (Type (n1, [_,Type (n2, _)])) = (n1 = "fun" andalso n2 = "fun")
  | casecIsCase _ = false
fun casecLastTyp (Type (n, [T1,T2])) = Type (n, [T1, change_typ T2])
  | casecLastTyp _ = error "Internal error: Invalid case type"
fun casecTyp (Type (n, [T1, T2])) =
      Type (n, [change_typ T1, (if casecIsCase T2 then casecTyp else casecLastTyp) T2])
  | casecTyp _ = error "Internal error: Invalid case type"
fun casecAbs f (Abs (v,Ta,t)) = (case casecAbs f t of (nconst,t) => (nconst,Abs (v,Ta,t)))
  | casecAbs f t = (case f t of NONE => (false,HOLogic.zero) | SOME t => (true,t))
fun casecArgs _ [t] = (false, [map_aterms use_origin t])
  | casecArgs f (t::ar) =
    (case casecAbs f t of (nconst, tt) => 
      casecArgs f ar ||> (fn ar => tt :: ar) |>> (if nconst then K true else I))
  | casecArgs _ _ = error "Internal error: Invalid case term"
fun casec _ _ f (Const (t,T)) args =
  if not (casecIsCase T) then error "Internal error: Invalid case type" else
    let val (nconst, args') = casecArgs f args in
      plus
        (f (List.last args))
        (if nconst then
          SOME (build_func (Const (t,casecTyp T), args'))
         else NONE)
    end
  | casec _ _ _ _ _ = error "Internal error: Invalid case term"

(* Handle if terms -> drop the term if true and false terms are zero *)
fun ifc _ _ f _ cond tt ft =
  let
    val rcond = map_aterms use_origin cond
    val tt = f tt
    val ft = f ft
  in
    plus (f cond) (case (tt,ft) of (NONE, NONE) => NONE | _ =>
       if tt = ft then tt else
       (SOME ((Const (If_name, @{typ "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"})) $ rcond $ (opt_term tt) $ (opt_term ft))))
  end

fun letc_change_typ (Type ("fun", [T1, Type ("fun", [T2, _])])) = (Type ("fun", [T1, Type ("fun", [change_typ T2, HOLogic.natT])]))
  | letc_change_typ _ = error "Internal error: invalid let type"
fun letc _ _ f expT exp nms Ts t =
    plus (f exp)
    (if length nms = 0 (* In case of "length nms = 0" the expression got reducted
                          Here we need Bound 0 to gain non-partial application *)
    then (case f (t $ Bound 0) of SOME (t' $ Bound 0) =>
                                 (SOME (Const (Let_name, letc_change_typ expT) $ (map_aterms use_origin exp) $ t'))
                                  (* Expression is not used and can therefore let be dropped *)
                                | SOME t' => SOME t'
                                | NONE => NONE)
    else (case f t of SOME t' =>
      SOME (if Term.is_dependent t' then Const (Let_name, letc_change_typ expT) $ (map_aterms use_origin exp) $ build_abs t' nms Ts
                                    else Term.subst_bounds([exp],t'))
    | NONE => NONE))

(* The converter for timing functions given to the walker *)
fun converter orig_used used : term option converter = {
        constc = fn _ => fn _ => fn _ => fn t =>
          (case t of Const ("HOL.undefined", _) => SOME (Const ("HOL.undefined", @{typ "nat"}))
                   | _ => NONE),
        funcc = (funcc orig_used used),
        ifc = ifc,
        casec = casec,
        letc = letc
    }
fun top_converter is_rec _ _ = opt_term o (fn exp => plus exp (if is_rec then SOME one else NONE))

(* Use converter to convert right side of a term *)
fun to_time ctxt origin is_rec orig_used used term =
  top_converter is_rec ctxt origin (walk ctxt origin (converter orig_used used) term)

(* Converts a term to its running time version *)
fun convert_term ctxt (origin: term list) is_rec orig_used (pT $ (Const (eqN, _) $ l $ r)) =
let
  val (l' as (l_const, l_params)) = walk_func l []
  val used =
    l_const
    |> used_for_const orig_used
    |> (fn f => fn n => f (index l_params n))
in
      pT
      $ (Const (eqN, @{typ "nat \<Rightarrow> nat \<Rightarrow> bool"})
        $ (build_func (l' |>> (fun_to_time ctxt orig_used used origin) |>> Option.valOf ||> conv_args ctxt used origin))
        $ (to_time ctxt origin is_rec orig_used used r))
end
  | convert_term _ _ _ _ _ = error "Internal error: invalid term to convert"

(* 4. Tactic to prove "f_dom n" *)
fun time_dom_tac ctxt induct_rule domintros =
  (Induction.induction_tac ctxt true [] [[]] [] (SOME [induct_rule]) []
    THEN_ALL_NEW ((K (auto_tac ctxt)) THEN' (fn i => FIRST' (
    (if i <= length domintros then [Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt [List.nth (domintros, i-1)]] else []) @
    [Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt domintros]) i)))


fun get_terms theory (term: term) =
  Spec_Rules.retrieve_global theory term
      |> hd |> #rules
      |> map Thm.prop_of
   handle Empty => error "Function or terms of function not found"

(* Register timing function of a given function *)
fun reg_and_proove_time_func (theory: theory) (term: term list) (terms: term list) print =
  reg_time_func theory term terms false
  |> proove_termination term terms print
and reg_time_func (theory: theory) (term: term list) (terms: term list) print =
  let
    val lthy = Named_Target.theory_init theory
    val _ =
      case time_term lthy (hd term)
            handle (ERROR _) => NONE
        of SOME _ => error ("Timing function already declared: " ^ (Term.term_name (hd term)))
         | NONE => ()

    (* 1. Fix all terms *)
    (* Exchange Var in types and terms to Free and check constraints *)
    val terms = map
      (map_aterms fixTerms
        #> map_types (map_atyps fixTypes)
        #> fixPartTerms lthy term)
      terms

    (* 2. Find properties about the function *)
    (* 2.1 Check if function is recursive *)
    val is_rec = is_rec lthy term terms

    (* 3. Convert every equation
      - Change type of toplevel equation from _ \<Rightarrow> _ \<Rightarrow> bool to nat \<Rightarrow> nat \<Rightarrow> bool
      - On left side change name of function to timing function
      - Convert right side of equation with conversion schema
    *)
    fun convert used = map (convert_term lthy term is_rec used)
    fun repeat T_terms =
      let
        val orig_used = find_used lthy term terms T_terms
        val T_terms' = convert orig_used terms
      in
        if T_terms' <> T_terms then repeat T_terms' else T_terms'
      end
    val T_terms = repeat (convert (K true) terms)
    val orig_used = find_used lthy term terms T_terms

    (* 4. Register function and prove termination *)
    val names = map Term.term_name term
    val timing_names = map (fun_name_to_time lthy) names
    val bindings = map (fn nm => (Binding.name nm, NONE, NoSyn)) timing_names
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt
    val specs = map (fn eq => (((Binding.empty, []), eq), [], [])) T_terms

    (* For partial functions sequential=true is needed in order to support them
       We need sequential=false to support the automatic proof of termination over dom
    *)
    fun register seq =
      let
        val _ = (if seq then warning "Falling back on sequential function..." else ())
        val fun_config = Function_Common.FunctionConfig
          {sequential=seq, default=NONE, domintros=true, partials=false}
      in
        Function.add_function bindings specs fun_config pat_completeness_auto lthy
      end

    (* Context for printing without showing question marks *)
    val print_ctxt = lthy
      |> Config.put show_question_marks false
      |> Config.put show_sorts false (* Change it for debugging *)
    val print_ctxt =  List.foldl (fn (term, ctxt) => Variable.add_fixes_implicit term ctxt) print_ctxt (term @ T_terms)
    (* Print result if print *)
    val _ = if not print then () else
        let
          val nms = map (fst o dest_Const) term
          val used = map (used_for_const orig_used) term
          val typs = map (snd o dest_Const) term
        in
          print_timing' print_ctxt { names=nms, terms=terms, typs=typs } { names=timing_names, terms=T_terms, typs=map (fn (used, typ) => change_typ' used 0 typ) (zip used typs) }
        end

    (* Register function *)
    val (_, lthy) =
      register false
      handle (ERROR _) =>
        register true
           | Match =>
        register true
  in
    Local_Theory.exit_global lthy
  end
and proove_termination (term: term list) terms print (theory: theory) =
  let
    val lthy = Named_Target.theory_init theory

    (* Start proving the termination *)  
    val infos = SOME (map (Function.get_info lthy) term) handle Empty => NONE
    val timing_names = map (fun_name_to_time lthy o Term.term_name) term

    (* Proof by lexicographic_order_tac *)
    val (time_info, lthy') =
      (Function.prove_termination NONE
        (Lexicographic_Order.lexicographic_order_tac false lthy) lthy)
        handle (ERROR _) =>
        let
          val _ = warning "Falling back on proof over dom..."
          val _ = (if length term > 1 then error "Proof over dom not supported for mutual recursive functions" else ())

          fun args (a$(Var ((nm,_),T))) = args a |> (fn ar => (nm,T)::ar)
            | args (a$(Const (_,T))) = args a |> (fn ar => ("x",T)::ar)
            | args _ = []
          val dom_args =
            terms |> hd |> get_l |> args
            |> Variable.variant_frees lthy []
            |> map fst

          val {inducts, ...} = case infos of SOME [i] => i | _ => error "Proof over dom failed as no induct rule was found"
          val induct = (Option.valOf inducts |> hd)

          val domintros = Proof_Context.get_fact lthy (Facts.named (hd timing_names ^ ".domintros"))
          val prop = (hd timing_names ^ "_dom (" ^ (String.concatWith "," dom_args) ^ ")")
                      |> Syntax.read_prop lthy

          (* Prove a helper lemma *)
          val dom_lemma = Goal.prove lthy dom_args [] prop
            (fn {context, ...} => HEADGOAL (time_dom_tac context induct domintros))
          (* Add dom_lemma to simplification set *)
          val simp_lthy = Simplifier.add_simp dom_lemma lthy
        in
          (* Use lemma to prove termination *)
          Function.prove_termination NONE
            (auto_tac simp_lthy) lthy
        end
    
    (* Context for printing without showing question marks *)
    val print_ctxt = lthy'
      |> Config.put show_question_marks false
      |> Config.put show_sorts false (* Change it for debugging *)
    (* Print result if print *)
    val _ = if not print then () else
        let
          val nms = map (fst o dest_Const) term
          val typs = map (snd o dest_Const) term
        in
          print_timing' print_ctxt { names=nms, terms=terms, typs=typs } (info_pfunc time_info)
        end
  in
    (time_info, Local_Theory.exit_global lthy')
  end

fun fix_definition (Const ("Pure.eq", _) $ l $ r) = Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"})
      $ (Const ("HOL.eq", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"}) $ l $ r)
  | fix_definition t = t
fun check_definition [t] = [t]
  | check_definition _ = error "Only a single defnition is allowed"

(* Convert function into its timing function (called by command) *)
fun reg_time_fun_cmd (funcs, thms) (theory: theory) =
let
  val ctxt = Proof_Context.init_global theory
  val fterms = map (Syntax.read_term ctxt) funcs
  val (_, lthy') = reg_and_proove_time_func theory fterms
    (case thms of NONE => get_terms theory (hd fterms)
                | SOME thms => thms |> Attrib.eval_thms ctxt |> List.map Thm.prop_of)
    true
in lthy'
end

(* Convert function into its timing function (called by command) with termination proof provided by user*)
fun reg_time_function_cmd (funcs, thms) (theory: theory) =
let
  val ctxt = Proof_Context.init_global theory
  val fterms = map (Syntax.read_term ctxt) funcs
  val theory = reg_time_func theory fterms
    (case thms of NONE => get_terms theory (hd fterms)
                | SOME thms => thms |> Attrib.eval_thms ctxt |> List.map Thm.prop_of)
    true
in theory
end

(* Convert function into its timing function (called by command) *)
fun reg_time_definition_cmd (funcs, thms) (theory: theory) =
let
  val ctxt = Proof_Context.init_global theory
  val fterms = map (Syntax.read_term ctxt) funcs
  val (_, lthy') = reg_and_proove_time_func theory fterms
    (case thms of NONE => get_terms theory (hd fterms) |> check_definition |> map fix_definition
                | SOME thms => thms |> Attrib.eval_thms ctxt |> List.map Thm.prop_of)
    true
in lthy'
end

val parser = (Scan.repeat1 Parse.prop) -- (Scan.option (Parse.keyword_improper "equations" -- Parse.thms1 >> snd))

val _ = Outer_Syntax.command @{command_keyword "time_fun"}
  "Defines runtime function of a function"
  (parser >> (fn p => Toplevel.theory (reg_time_fun_cmd p)))

val _ = Outer_Syntax.command @{command_keyword "time_function"}
  "Defines runtime function of a function"
  (parser >> (fn p => Toplevel.theory (reg_time_function_cmd p)))

val _ = Outer_Syntax.command @{command_keyword "time_definition"}
  "Defines runtime function of a definition"
  (parser >> (fn p => Toplevel.theory (reg_time_definition_cmd p)))

end
