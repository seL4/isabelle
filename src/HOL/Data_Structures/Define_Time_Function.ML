
signature TIMING_FUNCTIONS =
sig
type 'a wctxt = {
  ctxt: local_theory,
  origins: term list,
  f: term -> 'a
}
type 'a converter = {
  constc : 'a wctxt -> term -> 'a,
  funcc : 'a wctxt -> term -> term list -> 'a,
  ifc : 'a wctxt -> typ -> term -> term -> term -> 'a,
  casec : 'a wctxt -> term -> term list -> 'a,
  letc : 'a wctxt -> typ -> term -> string list -> typ list -> term -> 'a
}
val walk : local_theory -> term list -> 'a converter -> term -> 'a

type pfunc = { names : string list, terms : term list, typs : typ list }
val fun_pretty':  Proof.context -> pfunc -> Pretty.T
val fun_pretty:  Proof.context -> Function.info -> Pretty.T
val print_timing':  Proof.context -> pfunc -> pfunc -> unit
val print_timing:  Proof.context -> Function.info -> Function.info -> unit

val reg_and_proove_time_func: local_theory -> term list -> term list
      -> bool -> Function.info * local_theory
val reg_time_func: local_theory -> term list -> term list
      -> bool -> Function.info * local_theory

val time_dom_tac: Proof.context -> thm -> thm list -> int -> tactic

end

structure Timing_Functions : TIMING_FUNCTIONS =
struct
(* Configure config variable to adjust the prefix *)
val bprefix = Attrib.setup_config_string @{binding "time_prefix"} (K "T_")
(* Configure config variable to adjust the suffix *)
val bsuffix = Attrib.setup_config_string @{binding "time_suffix"} (K "")

(* some default values to build terms easier *)
val zero = Const (@{const_name "Groups.zero"}, HOLogic.natT)
val one = Const (@{const_name "Groups.one"}, HOLogic.natT)
(* Extracts terms from function info *)
fun terms_of_info (info: Function.info) =
  map Thm.prop_of (case #simps info of SOME s => s
                                     | NONE => error "No terms of function found in info")

type pfunc = {
  names : string list,
  terms : term list,
  typs : typ list
}
fun info_pfunc (info: Function.info): pfunc =
let
  val {defname, fs, ...} = info;
  val T = case hd fs of (Const (_,T)) => T
                      | (Free (_,T)) => T
                      | _ => error "Internal error: Invalid info to print"
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

fun contains l e = exists (fn e' => e' = e) l
fun contains' comp l e = exists (comp e) l
fun index [] _ = 0
  | index (x::xs) el = (if x = el then 0 else 1 + index xs el)
fun used_for_const orig_used t i = orig_used (t,i)
(* Split name by . *)
val split_name = String.fields (fn s => s = #".")

(* returns true if it's an if term *)
fun is_if (Const (@{const_name "HOL.If"},_)) = true
  | is_if _ = false
(* returns true if it's a case term *)
fun is_case (Const (n,_)) = n |> split_name |> List.last |> String.isPrefix "case_"
  | is_case _ = false
(* returns true if it's a let term *)
fun is_let (Const (@{const_name "HOL.Let"},_)) = true
  | is_let _ = false
(* change type of original function to new type (_ \<Rightarrow> ... \<Rightarrow> _ to _ \<Rightarrow> ... \<Rightarrow> nat)
    and replace all function arguments f with (t*T_f) if used *)
fun change_typ' used (Type ("fun", [T1, T2])) = 
      Type ("fun", [check_for_fun' (used 0) T1, change_typ' (fn i => used (i+1)) T2])
  | change_typ' _ _ = HOLogic.natT
and check_for_fun' true (f as Type ("fun", [_,_])) = HOLogic.mk_prodT (f, change_typ' (K false) f)
  | check_for_fun' false (f as Type ("fun", [_,_])) = change_typ' (K false) f
  | check_for_fun' _ t = t
val change_typ = change_typ' (K false)
(* Convert string name of function to its timing equivalent *)
fun fun_name_to_time ctxt s name =
let
  val prefix = Config.get ctxt bprefix
  val suffix = (if s then Config.get ctxt bsuffix else "")
  fun replace_last_name [n] = [prefix ^ n ^ suffix]
    | replace_last_name (n::ns) = n :: (replace_last_name ns)
    | replace_last_name _ = error "Internal error: Invalid function name to convert"
  val parts = split_name name
in
  String.concatWith "." (replace_last_name parts)
end
(* Count number of arguments of a function *)
fun count_args (Type (n, [_,res])) = (if n = "fun" then 1 + count_args res else 0)
  | count_args _ = 0
(* Check if number of arguments matches function *)
val _ = dest_Const
fun check_args s (t, args) =
    (if length args = count_args (type_of t) then ()
     else error ("Partial applications/Lambdas not allowed (" ^ s ^ ")"))
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
(* Custom compare function for types ignoring variable names *)
fun typ_comp (Type (A,a)) (Type (B,b)) = (A = B) andalso List.foldl (fn ((c,i),s) => typ_comp c i andalso s) true (ListPair.zip (a, b))
  | typ_comp (Type _) _ = false
  | typ_comp _ (Type _) = false
  | typ_comp _ _ = true
fun const_comp (Const (nm,T)) (Const (nm',T')) = nm = nm' andalso typ_comp T T'
  | const_comp _ _ = false

fun time_term ctxt s (Const (nm,T)) =
let
  val T_nm = fun_name_to_time ctxt s nm
  val T_T = change_typ T
in
(SOME (Syntax.check_term ctxt (Const (T_nm,T_T))))
  handle (ERROR _) =>
    case Syntax.read_term ctxt (Long_Name.base_name T_nm)
      of (Const (T_nm,T_T)) =>
        let
          fun col_Used i (Type ("fun", [Type ("fun", _), Ts])) (Type ("fun", [T', Ts'])) =
            (if is_Used T' then [i] else []) @ col_Used (i+1) Ts Ts'
            | col_Used i (Type ("fun", [_, Ts])) (Type ("fun", [_, Ts'])) = col_Used (i+1) Ts Ts'
            | col_Used _ _ _ = []
        in
          SOME (Const (T_nm,change_typ' (contains (col_Used 0 T T_T)) T))
        end
       | _ => error ("Timing function of " ^ nm ^ " is not defined")
end
  | time_term _ _ _ = error "Internal error: No valid function given"


type 'a wctxt = {
  ctxt: local_theory,
  origins: term list,
  f: term -> 'a
}
type 'a converter = {
  constc : 'a wctxt -> term -> 'a,
  funcc : 'a wctxt -> term -> term list -> 'a,
  ifc : 'a wctxt -> typ -> term -> term -> term -> 'a,
  casec : 'a wctxt -> term -> term list -> 'a,
  letc : 'a wctxt -> typ -> term -> string list -> typ list -> term -> 'a
}

(* Walks over term and calls given converter *)
fun walk_func (t1 $ t2) ts = walk_func t1 (t2::ts)
  | walk_func t ts = (t, ts)
fun walk_func' t = walk_func t []
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
    val wctxt = {ctxt = ctxt, origins = origin, f = this}
  in
    (if is_if f then
      (case f of (Const (_,T)) =>
        (case args of [cond, t, f] => ifc wctxt T cond t f
                   | _ => error "Partial applications not supported (if)")
               | _ => error "Internal error: invalid if term")
      else if is_case f then casec wctxt f args
      else if is_let f then
      (case f of (Const (_,lT)) =>
         (case args of [exp, t] => 
            let val (t,nms,Ts) = walk_abs t [] [] in letc wctxt lT exp nms Ts t end
                     | _ => error "Partial applications not allowed (let)")
               | _ => error "Internal error: invalid let term")
      else funcc wctxt f args)
  end
  | walk ctxt origin (conv as {constc, ...}) c = 
      constc {ctxt = ctxt, origins = origin, f = walk ctxt origin conv} c

(* 1. Fix all terms *)
(* Exchange Var in types and terms to Free *)
fun fixTerms (Var(ixn,T)) = Free (fst ixn, T)
  | fixTerms t = t
fun fixTypes (TVar ((t, _), T)) = TFree (t, T)
  | fixTypes t = t

fun noFun (Type ("fun", _)) = error "Functions in datatypes are not allowed in case constructions"
  | noFun T = T
fun casecBuildBounds n t = if n > 0 then casecBuildBounds (n-1) (t $ (Bound (n-1))) else t
fun casecAbs wctxt n (Type ("fun",[T,Tr])) (Abs (v,Ta,t)) = (map_atyps noFun T; Abs (v,Ta,casecAbs wctxt n Tr t))
  | casecAbs wctxt n (Type ("fun",[T,Tr])) t =
    (map_atyps noFun T; Abs ("uu",T,casecAbs wctxt (n + 1) Tr t))
  | casecAbs wctxt n _ t = (#f wctxt) (casecBuildBounds n (Term.incr_bv n 0 t))
fun fixCasecCases _ _ [t] = [t]
  | fixCasecCases wctxt (Type (_,[T,Tr])) (t::ts) = casecAbs wctxt 0 T t :: fixCasecCases wctxt Tr ts
  | fixCasecCases _ _ _ = error "Internal error: invalid case types/terms"
fun fixCasec wctxt (t as Const (_,T)) args =
      (check_args "cases" (t,args); build_func (t,fixCasecCases wctxt T args))
  | fixCasec _ _ _ = error "Internal error: invalid case term"

fun fixPartTerms ctxt (term: term list) t =
  let
    val _ = check_args "args" (walk_func (get_l t) [])
  in
    map_r (walk ctxt term {
          funcc = (fn wctxt => fn t => fn args =>
              (check_args "func" (t,args); build_func (t, map (#f wctxt) args))),
          constc = (fn _ => fn c => (case c of Abs _ => error "Lambdas not supported" | _ => c)),
          ifc = (fn wctxt => fn T => fn cond => fn tt => fn tf =>
            ((Const (@{const_name "HOL.If"}, T)) $ (#f wctxt) cond $ ((#f wctxt) tt) $ ((#f wctxt) tf))),
          casec = fixCasec,
          letc = (fn wctxt => fn expT => fn exp => fn nms => fn Ts => fn t =>
              let
                val f' = if length nms = 0 then
                (case (#f wctxt) (t$exp) of t$_ => t | _ => error "Internal error: case could not be fixed (let)")
                else (#f wctxt) t
              in (Const (@{const_name "HOL.Let"},expT) $ ((#f wctxt) exp) $ build_abs f' nms Ts) end)
      }) t
  end

(* 2. Check for properties about the function *)
(* 2.1 Check if function is recursive *)
fun or f (a,b) = f a orelse b
fun find_rec ctxt term = (walk ctxt term {
          funcc = (fn wctxt => fn t => fn args =>
            List.exists (fn term => (Const_name t) = (Const_name term)) term
             orelse List.foldr (or (#f wctxt)) false args),
          constc = (K o K) false,
          ifc = (fn wctxt => fn _ => fn cond => fn tt => fn tf =>
            (#f wctxt) cond orelse (#f wctxt) tt orelse (#f wctxt) tf),
          casec = (fn wctxt => fn t => fn cs =>
            (#f wctxt) t orelse List.foldr (or (rem_abs (#f wctxt))) false cs),
          letc = (fn wctxt => fn _ => fn exp => fn _ => fn _ => fn t =>
            (#f wctxt) exp orelse (#f wctxt) t)
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
          funcc = (fn wctxt => fn t => fn args =>
              (case t of (Const ("Product_Type.prod.snd", _)) => []
                  | _ => (if t = T_ident then [] else filter_passed args)
                    @ List.foldr (fn (l,r) => (#f wctxt) l @ r) [] args)),
          constc = (K o K) [],
          ifc = (fn wctxt => fn _ => fn cond => fn tt => fn tf => (#f wctxt) cond @ (#f wctxt) tt @ (#f wctxt) tf),
          casec = (fn wctxt => fn _ => fn cs => List.foldr (fn (l,r) => (#f wctxt) l @ r) [] cs),
          letc = (fn wctxt => fn _ => fn exp => fn _ => fn _ => fn t => (#f wctxt) exp @ (#f wctxt) t)
      }) (get_r T_t)
  fun build _ [] _ = false
    | build i (a::args) item =
        (if item = (ident,i) then contains frees' a else build (i+1) args item)
in
  build 0 T_args
end
fun find_used ctxt term terms T_terms =
  ListPair.zip (terms, T_terms)
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

(* Conversion of function term *)
fun fun_to_time ctxt orig_used _ (origin: term list) (func as Const (nm,T)) =
let
  val used' = used_for_const orig_used func
in
  if contains' const_comp origin func then SOME (Free (func |> Term.term_name |> fun_name_to_time ctxt true, change_typ' used' T)) else
  if Zero_Funcs.is_zero (Proof_Context.theory_of ctxt) (nm,T) then NONE else
    time_term ctxt false func
end
  | fun_to_time ctxt _ used _ (f as Free (nm,T)) = SOME (
      if used f then HOLogic.mk_snd (Free (nm,HOLogic.mk_prodT (T,change_typ T)))
      else Free (fun_name_to_time ctxt false nm, change_typ T)
      )
  | fun_to_time _ _ _ _ _ = error "Internal error: invalid function to convert"

(* Convert arguments of left side of a term *)
fun conv_arg ctxt used _ (f as Free (nm,T as Type("fun",_))) =
    if used f then Free (nm, HOLogic.mk_prodT (T, change_typ' (K false) T))
    else Free (fun_name_to_time ctxt false nm, change_typ' (K false) T)
  | conv_arg _ _ _ x = x
fun conv_args ctxt used origin = map (conv_arg ctxt used origin)

(* Handle function calls *)
fun build_zero (Type ("fun", [T, R])) = Abs ("uu", T, build_zero R)
  | build_zero _ = zero
fun funcc_use_origin used (f as Free (nm, T as Type ("fun",_))) =
    if used f then HOLogic.mk_fst (Free (nm,HOLogic.mk_prodT (T, change_typ T)))
    else error "Internal error: Error in used detection"
  | funcc_use_origin _ t = t
fun funcc_conv_arg _ used _ (t as (_ $ _)) = map_aterms (funcc_use_origin used) t
  | funcc_conv_arg wctxt used u (f as Free (nm, T as Type ("fun",_))) =
      if used f then
        if u then Free (nm, HOLogic.mk_prodT (T, change_typ T))
        else HOLogic.mk_snd (Free (nm,HOLogic.mk_prodT (T,change_typ T)))
      else Free (fun_name_to_time (#ctxt wctxt) false nm, change_typ T)
  | funcc_conv_arg wctxt _ true (f as Const (_,T as Type ("fun",_))) =
  (Const (@{const_name "Product_Type.Pair"},
      Type ("fun", [T,Type ("fun", [change_typ T, HOLogic.mk_prodT (T,change_typ T)])]))
    $ f $ (Option.getOpt (fun_to_time (#ctxt wctxt) (K false) (K false) (#origins wctxt) f, build_zero T)))
  | funcc_conv_arg wctxt _ false (f as Const (_,T as Type ("fun",_))) =
      Option.getOpt (fun_to_time (#ctxt wctxt) (K false) (K false) (#origins wctxt) f, build_zero T)
  | funcc_conv_arg _ _ _ t = t

fun funcc_conv_args _ _ _ [] = []
  | funcc_conv_args wctxt used (Type ("fun", [t, ts])) (a::args) =
      funcc_conv_arg wctxt used (is_Used t) a :: funcc_conv_args wctxt used ts args
  | funcc_conv_args _ _ _ _ = error "Internal error: Non matching type"
fun funcc orig_used used wctxt func args =
let
  fun get_T (Free (_,T)) = T
    | get_T (Const (_,T)) = T
    | get_T (_ $ (Free (_,Type (_, [_, T])))) = T (* Case of snd was constructed *)
    | get_T _ = error "Internal error: Forgotten type"
in
  List.foldr (I #-> plus)
  (case fun_to_time (#ctxt wctxt) orig_used used (#origins wctxt) func
    of SOME t => SOME (build_func (t,funcc_conv_args wctxt used (get_T t) args))
    | NONE => NONE)
  (map (#f wctxt) args)
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
fun casec wctxt (Const (t,T)) args =
  if not (casecIsCase T) then error "Internal error: Invalid case type" else
    let val (nconst, args') = casecArgs (#f wctxt) args in
      plus
        ((#f wctxt) (List.last args))
        (if nconst then
          SOME (build_func (Const (t,casecTyp T), args'))
         else NONE)
    end
  | casec _ _ _ = error "Internal error: Invalid case term"

(* Handle if terms -> drop the term if true and false terms are zero *)
fun ifc wctxt _ cond tt ft =
  let
    val f = #f wctxt
    val rcond = map_aterms use_origin cond
    val tt = f tt
    val ft = f ft
  in
    plus (f cond) (case (tt,ft) of (NONE, NONE) => NONE | _ =>
       if tt = ft then tt else
       (SOME ((Const (@{const_name "HOL.If"}, @{typ "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"})) $ rcond $ (opt_term tt) $ (opt_term ft))))
  end

fun letc_change_typ (Type ("fun", [T1, Type ("fun", [T2, _])])) = (Type ("fun", [T1, Type ("fun", [change_typ T2, HOLogic.natT])]))
  | letc_change_typ _ = error "Internal error: invalid let type"
fun letc wctxt expT exp nms Ts t =
    plus (#f wctxt exp)
    (if length nms = 0 (* In case of "length nms = 0" the expression got reducted
                          Here we need Bound 0 to gain non-partial application *)
    then (case #f wctxt (t $ Bound 0) of SOME (t' $ Bound 0) =>
                                 (SOME (Const (@{const_name "HOL.Let"}, letc_change_typ expT) $ (map_aterms use_origin exp) $ t'))
                                  (* Expression is not used and can therefore let be dropped *)
                                | SOME t' => SOME t'
                                | NONE => NONE)
    else (case #f wctxt t of SOME t' =>
      SOME (if Term.is_dependent t' then Const (@{const_name "HOL.Let"}, letc_change_typ expT) $ (map_aterms use_origin exp) $ build_abs t' nms Ts
                                    else Term.subst_bounds([exp],t'))
    | NONE => NONE))

(* The converter for timing functions given to the walker *)
fun converter orig_used used : term option converter = {
        constc = fn _ => fn t =>
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
let
  val equations = Spec_Rules.retrieve theory term
      |> map #rules
      |> map (map Thm.prop_of)
   handle Empty => error "Function or terms of function not found"
in
  equations
    |> filter (fn ts => typ_comp (ts |> hd |> get_l |> walk_func' |> fst |> dest_Const |> snd) (term |> dest_Const |> snd))
    |> hd
end

(* Register timing function of a given function *)
fun reg_time_func (lthy: local_theory) (term: term list) (terms: term list) print =
  let
    val _ =
      case time_term lthy true (hd term)
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
    val timing_names = map (fun_name_to_time lthy true) names
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
    val print_ctxt = List.foldl (fn (term, ctxt) => Variable.add_fixes_implicit term ctxt) print_ctxt (term @ T_terms)
    (* Print result if print *)
    val _ = if not print then () else
        let
          val nms = map (fst o dest_Const) term
          val used = map (used_for_const orig_used) term
          val typs = map (snd o dest_Const) term
        in
          print_timing' print_ctxt { names=nms, terms=terms, typs=typs }
            { names=timing_names, terms=T_terms, typs=map (fn (used, typ) => change_typ' used typ) (ListPair.zip (used, typs)) }
        end

  in
    register false
      handle (ERROR _) =>
        register true
           | Match =>
        register true
  end
fun proove_termination (term: term list) terms print (T_info: Function.info, lthy: local_theory) =
  let
    (* Start proving the termination *)  
    val infos = SOME (map (Function.get_info lthy) term) handle Empty => NONE
    val timing_names = map (fun_name_to_time lthy true o Term.term_name) term

    (* Proof by lexicographic_order_tac *)
    val (time_info, lthy') =
      (Function.prove_termination NONE
        (Lexicographic_Order.lexicographic_order_tac false lthy) lthy)
        handle (ERROR _) =>
        let
          val _ = warning "Falling back on proof over dom..."
          val _ = (if length term > 1 then error "Proof over dom not supported for mutual recursive functions" else ())

          fun args (a$(Var ((nm,_),T))) = args a |> (fn ar => (nm,T)::ar)
            | args (a$(Const (_,T))) = args a |> (fn ar => ("uu",T)::ar)
            | args _ = []
          val dom_vars =
            terms |> hd |> get_l |> map_types (map_atyps fixTypes)
            |> args |> Variable.variant_frees lthy []
          val dom_args = 
            List.foldl (fn (t,p) => HOLogic.mk_prod ((Free t),p)) (Free (hd dom_vars)) (tl dom_vars)

          val {inducts, ...} = case infos of SOME [i] => i | _ => error "Proof over dom failed as no induct rule was found"
          val induct = (Option.valOf inducts |> hd)

          val domintros = Proof_Context.get_fact lthy (Facts.named (hd timing_names ^ ".domintros"))
          val prop = HOLogic.mk_Trueprop (#dom T_info $ dom_args)

          (* Prove a helper lemma *)
          val dom_lemma = Goal.prove lthy (map fst dom_vars) [] prop
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
    (time_info, lthy')
  end
fun reg_and_proove_time_func (lthy: local_theory) (term: term list) (terms: term list) print =
  reg_time_func lthy term terms false
  |> proove_termination term terms print

fun fix_definition (Const ("Pure.eq", _) $ l $ r) = Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"})
      $ (Const ("HOL.eq", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"}) $ l $ r)
  | fix_definition t = t
fun check_definition [t] = [t]
  | check_definition _ = error "Only a single definition is allowed"

fun isTypeClass' (Const (nm,_)) =
  (case split_name nm |> rev
    of (_::nm::_) => String.isSuffix "_class" nm
     | _ => false)
  | isTypeClass' _ = false
val isTypeClass =
  (List.foldr (fn (a,b) => a orelse b) false) o (map isTypeClass')

fun detect_typ (ctxt: local_theory) (term: term) =
let
  val class_term =  (case term of Const (nm,_) => Syntax.read_term ctxt nm
      | _ => error "Could not find term of class")
  fun find_free (Type (_,class)) (Type (_,inst)) =
        List.foldl (fn ((c,i),s) => (case s of NONE => find_free c i | t => t)) (NONE) (ListPair.zip (class, inst))
    | find_free (TFree _) (TFree _) = NONE
    | find_free (TFree _) (Type (nm,_)) = SOME nm
    | find_free  _ _ = error "Unhandled case in detecting type"
in
  find_free (type_of class_term) (type_of term)
    |> Option.map (hd o rev o split_name)
end

fun set_suffix (fterms: term list) ctxt =
let
  val isTypeClass = isTypeClass fterms
  val _ = (if length fterms > 1 andalso isTypeClass then error "No mutual recursion inside instantiation allowed" else ())
  val suffix = (if isTypeClass then detect_typ ctxt (hd fterms) else NONE)
in
  (case suffix of NONE => I | SOME s => Config.put bsuffix ("_" ^ s)) ctxt
end

(* Convert function into its timing function (called by command) *)
fun reg_time_fun_cmd (funcs, thms) (ctxt: local_theory) =
let
  val fterms = map (Syntax.read_term ctxt) funcs
  val ctxt = set_suffix fterms ctxt
  val (_, ctxt') = reg_and_proove_time_func ctxt fterms
    (case thms of NONE => get_terms ctxt (hd fterms)
                | SOME thms => thms |> Attrib.eval_thms ctxt |> List.map Thm.prop_of)
    true
in ctxt'
end

(* Convert function into its timing function (called by command) with termination proof provided by user*)
fun reg_time_function_cmd (funcs, thms) (ctxt: local_theory) =
let
  val fterms = map (Syntax.read_term ctxt) funcs
  val ctxt = set_suffix fterms ctxt
  val ctxt' = reg_time_func ctxt fterms
    (case thms of NONE => get_terms ctxt (hd fterms)
                | SOME thms => thms |> Attrib.eval_thms ctxt |> List.map Thm.prop_of)
    true
    |> snd
in ctxt'
end

(* Convert function into its timing function (called by command) *)
fun reg_time_definition_cmd (funcs, thms) (ctxt: local_theory) =
let
  val fterms = map (Syntax.read_term ctxt) funcs
  val ctxt = set_suffix fterms ctxt
  val (_, ctxt') = reg_and_proove_time_func ctxt fterms
    (case thms of NONE => get_terms ctxt (hd fterms) |> check_definition |> map fix_definition
                | SOME thms => thms |> Attrib.eval_thms ctxt |> List.map Thm.prop_of)
    true
in ctxt'
end

val parser = (Scan.repeat1 Parse.prop) -- (Scan.option (Parse.keyword_improper "equations" -- Parse.thms1 >> snd))

val _ = Outer_Syntax.local_theory @{command_keyword "time_fun"}
  "Defines runtime function of a function"
  (parser >> reg_time_fun_cmd)

val _ = Outer_Syntax.local_theory @{command_keyword "time_function"}
  "Defines runtime function of a function"
  (parser >> reg_time_function_cmd)

val _ = Outer_Syntax.local_theory @{command_keyword "time_definition"}
  "Defines runtime function of a definition"
  (parser >> reg_time_definition_cmd)

end
