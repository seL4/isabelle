
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
  letc : 'a wctxt -> typ -> term -> (string * typ) list -> term -> 'a
}
val walk : local_theory -> term list -> 'a converter -> term -> 'a
val Iconst : term wctxt -> term -> term
val Ifunc : term wctxt -> term -> term list -> term
val Iif : term wctxt -> typ -> term -> term -> term -> term
val Icase : term wctxt -> term -> term list -> term
val Ilet : term wctxt -> typ -> term -> (string * typ) list -> term -> term

type pfunc = { names : string list, terms : term list, typs : typ list }
val fun_pretty':  Proof.context -> pfunc -> Pretty.T
val fun_pretty:  Proof.context -> Function.info -> Pretty.T
val print_timing':  Proof.context -> pfunc -> pfunc -> unit
val print_timing:  Proof.context -> Function.info -> Function.info -> unit

type time_config = {
  print: bool,
  simp: bool,
  partial: bool
}
datatype result = Function of Function.info | PartialFunction of thm
val reg_and_proove_time_func: local_theory -> term list -> term list
      -> time_config -> result * local_theory
val reg_time_func: local_theory -> term list -> term list
      -> time_config -> result * local_theory


val time_dom_tac: Proof.context -> thm -> thm list -> int -> tactic


end

structure Timing_Functions : TIMING_FUNCTIONS =
struct
(* Configure config variable to adjust the prefix *)
val bprefix = Attrib.setup_config_string @{binding "time_prefix"} (K "T_")
val bprefix_snd = Attrib.setup_config_string @{binding "time_prefix_snd"} (K "T2_")
(* Configure config variable to adjust the suffix *)
val bsuffix = Attrib.setup_config_string @{binding "time_suffix"} (K "")

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
  Pretty.writeln (Pretty.text_fold [
      Pretty.str ("Converting " ^ (hd names) ^ (String.concat (map (fn nm => ", " ^ nm) (tl names))) ^ "\n"),
      poriginal, Pretty.str "\n", ptiming])
end
fun print_timing ctxt (oinfo: Function.info) (tinfo: Function.info) =
  print_timing' ctxt (info_pfunc oinfo) (info_pfunc tinfo)

fun print_lemma ctxt defs (T_terms: term list) =
let
  val names =
    defs
    |> map snd
    |> map (fn s => "_" ^ s)
    |> List.foldr (op ^) ""
  val begin = "lemma T" ^ names ^ "_simps [simp,code]:\n"
  fun convLine T_term =
    "  \"" ^ Syntax.string_of_term ctxt T_term ^ "\"\n"
  val lines = map convLine T_terms
  fun convDefs def = " " ^ (fst def)
  val proof = "  by (simp_all add:" :: (map convDefs defs) @ [")"]
  val _ = Pretty.writeln (Pretty.str "Characteristic recursion equations can be derived:")
in
  (begin :: lines @ proof)
  |> String.concat
  |> Active.sendback_markup_properties [Markup.padding_command]
  |> Pretty.str
  |> Pretty.writeln
end

fun contains l e = exists (fn e' => e' = e) l
fun contains' comp l e = exists (comp e) l
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
(* Convert string name of function to its timing equivalent *)
fun fun_name_to_time' ctxt s second name =
let
  val prefix = Config.get ctxt (if second then bprefix_snd else bprefix)
  val suffix = (if s then Config.get ctxt bsuffix else "")
  fun replace_last_name [n] = [prefix ^ n ^ suffix]
    | replace_last_name (n::ns) = n :: (replace_last_name ns)
    | replace_last_name _ = error "Internal error: Invalid function name to convert"
  val parts = split_name name
in
  String.concatWith "." (replace_last_name parts)
end
fun fun_name_to_time ctxt s name = fun_name_to_time' ctxt s false name
(* Count number of arguments of a function *)
fun count_args (Type (n, [_,res])) = (if n = "fun" then 1 + count_args res else 0)
  | count_args _ = 0
(* Check if number of arguments matches function *)
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
  letc : 'a wctxt -> typ -> term -> (string * typ) list -> term -> 'a
}

(* Walks over term and calls given converter *)
fun list_abs ([], t) = t
  | list_abs (a::abs,t) = list_abs (abs,t) |> absfree a
fun walk ctxt (origin: term list) (conv as {ifc, casec, funcc, letc, ...} : 'a converter) (t as _ $ _) =
  let
    val (f, args) = strip_comb t
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
            let val (abs,t) = Term.strip_abs_eta 1 t in letc wctxt lT exp abs t end
                     | _ => error "Partial applications not allowed (let)")
               | _ => error "Internal error: invalid let term")
      else funcc wctxt f args)
  end
  | walk ctxt origin (conv as {constc, ...}) c = 
      constc {ctxt = ctxt, origins = origin, f = walk ctxt origin conv} c
fun Ifunc (wctxt: term wctxt) t args = list_comb (#f wctxt t,map (#f wctxt) args)
val Iconst = K I
fun Iif (wctxt: term wctxt) T cond tt tf =
  Const (@{const_name "HOL.If"}, T) $ (#f wctxt cond) $ (#f wctxt tt) $ (#f wctxt tf)
fun Icase (wctxt: term wctxt) t cs = list_comb
  (#f wctxt t,map (fn c => c |> Term.strip_abs_eta (c |> fastype_of |> strip_type |> fst |> length) ||> #f wctxt |> list_abs) cs)
fun Ilet (wctxt: term wctxt) lT exp abs t =
  Const (@{const_name "HOL.Let"}, lT) $ (#f wctxt exp) $ list_abs (abs, #f wctxt t)

(* 1. Fix all terms *)
(* Exchange Var in types and terms to Free *)
fun freeTerms (Var(ixn,T)) = Free (fst ixn, T)
  | freeTerms t = t
fun freeTypes (TVar ((t, _), T)) = TFree (t, T)
  | freeTypes t = t
fun fix_definition (Const ("Pure.eq", _) $ l $ r) = HOLogic.mk_Trueprop (HOLogic.mk_eq (l,r))
  | fix_definition t = t
fun check_definition [t] = [t]
  | check_definition _ = error "Only a single definition is allowed"
fun get_terms theory (term: term) =
let
  val equations = Spec_Rules.retrieve theory term
      |> map #rules
      |> map (map Thm.prop_of)
   handle Empty => error "Function or terms of function not found"
  val _ = if equations = [] then error "No terms found" else ()
in
  equations
    |> map (map fix_definition)
    |> filter (List.exists
        (fn t => typ_comp (t |> get_l |> strip_comb |> fst |> dest_Const |> snd) (term |> strip_comb |> fst |> dest_Const |> snd)))
    |> hd
end

fun fixCasecCases _ [t] = [t]
  | fixCasecCases wctxt (t::ts) =
    let
      val num = fastype_of t |> strip_type |> fst |> length
      val c' = Term.strip_abs_eta num t ||> #f wctxt |> list_abs
    in
      c' :: fixCasecCases wctxt ts
    end
  | fixCasecCases _ _ = error "Internal error: invalid case types/terms"
fun fixCasec wctxt t args =
      (check_args "cases" (t,args); list_comb ((#f wctxt) t,fixCasecCases wctxt args))

fun shortFunc fixedNum (Const (nm,T)) = 
    Const (nm,T |> strip_type |>> drop fixedNum |> (op --->))
  | shortFunc _ _ = error "Internal error: Invalid term"
fun shortApp fixedNum (c, args) =
  (shortFunc fixedNum c, drop fixedNum args)
fun shortOriginFunc (term: term list) fixedNum (f as (c as Const (_,_), _))  =
  if contains' const_comp term c then shortApp fixedNum f else f
  | shortOriginFunc _ _ t = t
fun map_abs f (t as Abs _) = t |> strip_abs ||> f |> list_abs
  | map_abs _ t = t
fun fixTerms ctxt (term: term list) (fixedNum: int) (t as pT $ (eq $ l $ r)) =
  let
    val _ = check_args "args" (strip_comb (get_l t))
    val l' = shortApp fixedNum (strip_comb l) |> list_comb
    val shortOriginFunc' = shortOriginFunc (term |> map (fst o strip_comb)) fixedNum
    val r' = walk ctxt term {
          funcc = (fn wctxt => fn t => fn args =>
            (check_args "func" (t,args);
               (#f wctxt t, map (#f wctxt) args) |> shortOriginFunc' |> list_comb)),
          constc = fn wctxt => map_abs (#f wctxt),
          ifc = Iif,
          casec = fixCasec,
          letc = (fn wctxt => fn expT => fn exp => fn abs => fn t =>
              (Const (@{const_name "HOL.Let"},expT) $ (#f wctxt exp) $ list_abs (abs, #f wctxt t)))
      } r
  in
    pT $ (eq $ l' $ r')
  end
  | fixTerms _ _ _ _ = error "Internal error: invalid term"
fun postFixTerms ctxt (term: term list) (pT $ (eq $ l $ r)) =
  let
    val r' = walk ctxt term {
          funcc = (fn wctxt => fn t => fn args =>
            case List.find (fn el => Term.is_Const t
              andalso (Term.dest_Const_name (strip_comb el |> fst)) = (Term.dest_Const_name t)) term of
              SOME t => list_comb (t, map (#f wctxt) args)
            | NONE => list_comb (#f wctxt t, map (#f wctxt) args)),
          constc = Iconst,
          ifc = Iif,
          casec = Icase,
          letc = Ilet
      } r
  in
    pT $ (eq $ l $ r')
  end
  | postFixTerms _ _ _ = error "Internal error: invalid term"

(* 2. Check for properties about the function *)
(* 2.1 Check if function is recursive *)
fun or f (a,b) = f a orelse b
fun find_rec ctxt term = (walk ctxt term {
          funcc = (fn wctxt => fn t => fn args =>
            List.exists (fn term => (Const_name t) = (Const_name term)) term
             orelse List.foldr (or (#f wctxt)) false args),
          constc = fn wctxt => fn t => case t of
                Abs _ => t |> strip_abs |> snd |> (#f wctxt)
              | _ => false,
          ifc = (fn wctxt => fn _ => fn cond => fn tt => fn tf =>
            (#f wctxt) cond orelse (#f wctxt) tt orelse (#f wctxt) tf),
          casec = (fn wctxt => fn t => fn cs =>
            (#f wctxt) t orelse List.foldr (or (rem_abs (#f wctxt))) false cs),
          letc = (fn wctxt => fn _ => fn exp => fn _ => fn t =>
            (#f wctxt) exp orelse (#f wctxt) t)
      }) o get_r
fun is_rec ctxt (term: term list) = List.foldr (or (find_rec ctxt term)) false

(* 4. Tactic to prove "f_dom n" *)
fun time_dom_tac ctxt induct_rule domintros =
  (Induction.induction_tac ctxt true [] [[]] [] (SOME [induct_rule]) []
    THEN_ALL_NEW ((K (auto_tac ctxt)) THEN' (fn i => FIRST' (
    (if i <= length domintros then [Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt [List.nth (domintros, i-1)]] else []) @
    [Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt domintros]) i)))

(* Register timing function of a given function *)
type time_config = {
  print: bool,
  simp: bool,
  partial: bool
}
datatype result = Function of Function.info | PartialFunction of thm
fun reg_time_func (lthy: local_theory) (term: term list) (terms: term list) (config: time_config) =
  let
    (* some default values to build terms easier *)
    (* Const (@{const_name "Groups.zero"}, HOLogic.natT) *)
    val zero = if #partial config then @{term "Some (0::nat)"} else HOLogic.zero
    val one = Const (@{const_name "Groups.one"}, HOLogic.natT)
    val natOptT = @{typ "nat option"}
    val finT = if #partial config then natOptT else HOLogic.natT
    val some = @{term "Some::nat \<Rightarrow> nat option"}

    (* Convert implicit capturing functions in locales to their basic version *)
    val consts = Proof_Context.consts_of lthy
    val full_term = term
    val net = Consts.revert_abbrevs consts ["internal"] |> hd |> Item_Net.content
                (* filter out consts *)
              |> filter (is_Const o fst o strip_comb o fst)
                (* filter out abbreviations for locales *)
              |> filter (fn n => "local"
                  = (n |> snd |> strip_comb |> fst |> dest_Const_name |> split_name |> hd))
              |> filter (fn n => (n |> fst |> strip_comb |> fst |> dest_Const_name |> split_name |> List.last) =
                (n |> snd |> strip_comb |> fst |> dest_Const_name |> split_name |> List.last))
              |> map (fst #> strip_comb #>> dest_Const_name ##> length)
    fun n_abbrev (Const (nm,_)) =
    let
      val f = filter (fn n => fst n = nm) net
    in
      if length f >= 1 then f |> hd |> snd else 0
    end
      | n_abbrev _ = 0
    fun simpLocFunc (t: term) (args: term list) =
      let
        val n_abb = n_abbrev t
        val simp_t = case t of Const (nm,T) => Const (nm, T |> strip_type |>> drop n_abb |> (op --->))
                        | t => t
        val simp_args = drop n_abb args 
      in
        if Term.is_Const t andalso contains (term |> map (Term.dest_Const_name o fst o strip_comb)) (t |> Term.dest_Const_name)
        then (t, args) else (simp_t, simp_args)
      end

    (* change type of original function to new type (_ \<Rightarrow> ... \<Rightarrow> _ to _ \<Rightarrow> ... \<Rightarrow> nat)
        and replace all function arguments f with (t*T_f) if used *)
    fun change_typ' used (Type ("fun", [T1, T2])) = 
          Type ("fun", [check_for_fun' (used 0) T1, change_typ' (fn i => used (i+1)) T2])
      | change_typ' _ _ = finT
    and check_for_fun' true (f as Type ("fun", [_,_])) = HOLogic.mk_prodT (f, change_typ' (K false) f)
      | check_for_fun' false (f as Type ("fun", [_,_])) = change_typ' (K true) f
      | check_for_fun' _ t = t
    val change_typ = change_typ' (K true)
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
              val binderT = change_typ' (contains (col_Used 0 T T_T)) T |> Term.binder_types
              val finT = Term.body_type T_T
            in
              SOME (Const (T_nm, binderT ---> finT))
            end
           (* Case for inside of locale, would need type *)
           | f as (_$_) =>
            let
              val ((T_nm,T_T), fixes) = Term.strip_comb f |>> Term.dest_Const
              val (T_Ts, finT) = Term.strip_type T_T
              fun col_Used i (Type ("fun", [Type ("fun", _), Ts])) (Type ("fun", [T', Ts'])) =
                (if is_Used T' then [i] else []) @ col_Used (i+1) Ts Ts'
                | col_Used i (Type ("fun", [_, Ts])) (Type ("fun", [_, Ts'])) = col_Used (i+1) Ts Ts'
                | col_Used _ _ _ = []
              val binderT = change_typ' (contains (col_Used 0 T (drop (length fixes) T_Ts ---> finT))) T |> Term.binder_types
            in
              SOME (Term.list_comb (Const (T_nm, (take (length fixes) T_Ts) ---> binderT ---> finT), fixes))
            end
           | _ => error ("Timing function of " ^ nm ^ " is not defined")
    end
      | time_term _ _ _ = error "Internal error: No valid function given"

    fun opt_term NONE = zero
      | opt_term (SOME t) = t
    fun use_origin (Free (nm, T as Type ("fun",_))) = HOLogic.mk_fst (Free (nm,HOLogic.mk_prodT (T, change_typ T)))
      | use_origin t = t
    
    (* Conversion of function term *)
    fun fun_to_time' ctxt (origin: term list) second (func as Const (nm,T)) =
    let
      val origin' = map (Term.dest_Const_name o fst o strip_comb) origin
    in
      if contains origin' nm then SOME (Free (func |> Term.term_name |> fun_name_to_time' ctxt true second, change_typ T)) else
      if Zero_Funcs.is_zero (Proof_Context.theory_of ctxt) (nm,T) then NONE else
        time_term ctxt false func
    end
      | fun_to_time' _ _ _ (Free (nm,T)) =
          SOME (HOLogic.mk_snd (Free (nm,HOLogic.mk_prodT (T,change_typ' (K true) T))))
      | fun_to_time' _ _ _ _ = error "Internal error: invalid function to convert"
    fun fun_to_time context origin func = fun_to_time' context origin false func
    
    (* Convert arguments of left side of a term *)
    fun conv_arg _ (Free (nm,T as Type("fun",_))) =
        Free (nm, HOLogic.mk_prodT (T, change_typ' (K false) T))
      | conv_arg _ x = x
    fun conv_args ctxt = map (conv_arg ctxt)
    
    (* 3. Convert equations *)
    (* Some Helper *)
    val plusTyp = @{typ "nat => nat => nat"}
    fun plus (SOME a) (SOME b) = SOME ((if #partial config then @{term part_add} else Const (@{const_name "Groups.plus"}, plusTyp)) $ a $ b)
      | plus (SOME a) NONE = SOME a
      | plus NONE (SOME b) = SOME b
      | plus NONE NONE = NONE
    (* Partial helper *)
    val OPTION_BIND = @{term "Option.bind::nat option \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> nat option"}
    fun OPTION_ABS_SUC args = Term.absfree ("_uu", @{typ nat})
      (List.foldr (uncurry plus)
        (SOME (some $ HOLogic.mk_Suc (Free ("_uu", @{typ nat})))) args |> Option.valOf)
    fun build_option_bind term args =
      OPTION_BIND $ term $ OPTION_ABS_SUC args
    fun WRAP_FUNCTION t =
      if (Term.head_of t |> Term.fastype_of |> Term.body_type) = finT
      then t
      else if #partial config
            then some $ t
            else @{term "the::nat option \<Rightarrow> nat"} $ t

    (* Handle function calls *)
    fun build_zero (Type ("fun", [T, R])) = Abs ("uu", T, build_zero R)
      | build_zero _ = zero
    fun funcc_use_origin (Free (nm, T as Type ("fun",_))) =
        HOLogic.mk_fst (Free (nm,HOLogic.mk_prodT (T, change_typ T)))
      | funcc_use_origin t = t
    fun funcc_conv_arg _ _ (t as (_ $ _)) = map_aterms funcc_use_origin t
      | funcc_conv_arg _ u (Free (nm, T as Type ("fun",_))) =
          if u then Free (nm, HOLogic.mk_prodT (T, change_typ T))
          else HOLogic.mk_snd (Free (nm,HOLogic.mk_prodT (T,change_typ T)))
      | funcc_conv_arg wctxt true (f as Const (_,Type ("fun",_))) =
          HOLogic.mk_prod (f, funcc_conv_arg wctxt false f)
      | funcc_conv_arg wctxt false (f as Const (_,T as Type ("fun",_))) =
          Option.getOpt (fun_to_time (#ctxt wctxt) (#origins wctxt) f, build_zero T)
      | funcc_conv_arg wctxt false (f as Abs _) =
           f
           |> Term.strip_abs_eta ((length o fst o strip_type o type_of) f)
           ||> #f wctxt ||> opt_term
           |> list_abs
      | funcc_conv_arg wctxt true (f as Abs _) =
        let
          val f' = f
           |> Term.strip_abs_eta ((length o fst o strip_type o type_of) f)
           ||> map_aterms funcc_use_origin
           |> list_abs
        in
          HOLogic.mk_prod (f', funcc_conv_arg wctxt false f)
        end
      | funcc_conv_arg _ _ t = t
    
    fun funcc_conv_args _ _ [] = []
      | funcc_conv_args wctxt (Type ("fun", [t, ts])) (a::args) =
          funcc_conv_arg wctxt (is_Used t) a :: funcc_conv_args wctxt ts args
      | funcc_conv_args _ _ _ = error "Internal error: Non matching type"
    fun funcc wctxt func args =
    let
      val (func, args) = simpLocFunc func args
      fun get_T (Free (_,T)) = T
        | get_T (Const (_,T)) = T
        | get_T (Const ("Product_Type.prod.snd",_) $ (Free (_,Type (_, [_, T])))) = T (* Case of snd was constructed *)
        | get_T (h $ _) = (case get_T h of Type ("fun", [_,T]) => T | _ => error "Internal error: Not a locale func")
        | get_T _ = error "Internal error: Forgotten type"
      val func = (case fun_to_time (#ctxt wctxt) (#origins wctxt) func
        of SOME t => SOME (WRAP_FUNCTION (list_comb (t, funcc_conv_args wctxt (get_T t) args)))
         | NONE => NONE)
      val args = (map (#f wctxt) args)
    in
      (if not (#partial config) orelse func = NONE
      then List.foldr (uncurry plus) func args
      else build_option_bind (Option.valOf func) args |> SOME)
    end
    
    (* Handle case terms *)
    fun casecIsCase (Type (n1, [_,Type (n2, _)])) = (n1 = "fun" andalso n2 = "fun")
      | casecIsCase _ = false
    fun casecLastTyp (Type (n, [T1,T2])) = Type (n, [T1, change_typ T2])
      | casecLastTyp _ = error "Internal error: Invalid case type"
    fun casecTyp (Type (n, [T1, T2])) =
          Type (n, [change_typ T1, (if casecIsCase T2 then casecTyp else casecLastTyp) T2])
      | casecTyp _ = error "Internal error: Invalid case type"
    fun casecAbs f (Abs (v,Ta,t)) = (case casecAbs f (subst_bound (Free (v,Ta), t))
                                      of (nconst,t) => (nconst,absfree (v,Ta) t))
      | casecAbs f t = (case f t of NONE => (false, opt_term NONE) | SOME t => (true,t))
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
              SOME (list_comb (Const (t,casecTyp T), args'))
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
           (SOME ((Const (@{const_name "HOL.If"}, @{typ "bool"} --> finT --> finT --> finT)) $ rcond
              $ (opt_term tt) $ (opt_term ft))))
      end
    
    fun letc_lambda wctxt T (t as Abs _) =
          HOLogic.mk_prod (map_aterms use_origin t, 
           Term.strip_abs_eta (strip_type T |> fst |> length) t ||> #f wctxt ||> opt_term ||> map_types change_typ |> list_abs)
      | letc_lambda _ _ t = map_aterms use_origin t
    fun letc wctxt expT exp ([(nm,_)]) t =
          plus (#f wctxt exp)
          (case #f wctxt t of SOME t' =>
            (if Term.used_free nm t'
             then
              let
                val exp' = letc_lambda wctxt expT exp
                val t' = list_abs ([(nm,fastype_of exp')], t')
              in
                Const (@{const_name "HOL.Let"}, [fastype_of exp', fastype_of t'] ---> finT) $ exp' $ t'
              end
             else t') |> SOME
          | NONE => NONE)
      | letc _ _ _ _ _ = error "Unknown let state"
    
    fun constc _ (Const ("HOL.undefined", _)) = SOME (Const ("HOL.undefined", finT))
      | constc _ _ = NONE
    
    (* The converter for timing functions given to the walker *)
    val converter : term option converter = {
            constc = constc,
            funcc = funcc,
            ifc = ifc,
            casec = casec,
            letc = letc
        }
    fun top_converter is_rec _ _ =
      if #partial config
      then (fn t => Option.getOpt (t, zero))
      else (opt_term o (fn exp => plus exp (if is_rec then SOME one else NONE)))
    
    (* Use converter to convert right side of a term *)
    fun to_time ctxt origin is_rec term =
      top_converter is_rec ctxt origin (walk ctxt origin converter term)
    
    (* Converts a term to its running time version *)
    fun convert_term ctxt (origin: term list) is_rec (pT $ (Const (eqN, _) $ l $ r)) =
    let
      val (l_const, l_params) = strip_comb l
    in
        pT
        $ (Const (eqN, finT --> finT --> @{typ "bool"})
          $ (list_comb (l_const |> fun_to_time ctxt origin |> Option.valOf, l_params |> conv_args ctxt))
          $ (to_time ctxt origin is_rec r))
    end
      | convert_term _ _ _ _ = error "Internal error: invalid term to convert"
    
    (* 3.5 Support for locales *)
    fun replaceFstSndFree ctxt (origin: term list) (rfst: term -> term) (rsnd: term -> term) =
      (walk ctxt origin {
              funcc = fn wctxt => fn t => fn args =>
                case args of
                     (f as Free _)::args =>
                       (case t of
                           Const ("Product_Type.prod.fst", _) =>
                            list_comb (rfst (t $ f), map (#f wctxt) args)
                         | Const ("Product_Type.prod.snd", _) =>
                            list_comb (rsnd (t $ f), map (#f wctxt) args)
                         | t => list_comb (t, map (#f wctxt) (f :: args)))
                   | args => list_comb (t, map (#f wctxt) args),
              constc = Iconst,
              ifc = Iif,
              casec = Icase,
              letc = Ilet
          })
    
    (* 5. Check for higher-order function if original function is used \<rightarrow> find simplifications *)
    fun find_used' T_t =
    let
      val (T_ident, T_args) = strip_comb (get_l T_t)
    
      fun filter_passed [] = []
        | filter_passed ((f as Free (_, Type ("Product_Type.prod",[Type ("fun",_), Type ("fun", _)])))::args) = 
            f :: filter_passed args
        | filter_passed (_::args) = filter_passed args
      val frees = (walk lthy [] {
              funcc = (fn wctxt => fn t => fn args =>
                  (case t of (Const ("Product_Type.prod.snd", _)) => []
                      | _ => (if t = T_ident then [] else filter_passed args)
                        @ List.foldr (fn (l,r) => (#f wctxt) l @ r) [] args)),
              constc = (K o K) [],
              ifc = (fn wctxt => fn _ => fn cond => fn tt => fn tf => (#f wctxt) cond @ (#f wctxt) tt @ (#f wctxt) tf),
              casec = (fn wctxt => fn _ => fn cs => List.foldr (fn (l,r) => (#f wctxt) l @ r) [] cs),
              letc = (fn wctxt => fn _ => fn exp => fn _ => fn t => (#f wctxt) exp @ (#f wctxt) t)
          }) (get_r T_t)
      fun build _ [] = []
        | build i (a::args) =
            (if contains frees a then [(T_ident,i)] else []) @ build (i+1) args
    in
      build 0 T_args
    end
    fun find_simplifyble ctxt term terms =
    let
      val used =
        terms
        |> List.map find_used'
        |> List.foldr (op @) []
      val change =
        Option.valOf o fun_to_time ctxt term
      fun detect t i (Type ("fun",_)::args) = 
        (if contains used (change t,i) then [] else [i]) @ detect t (i+1) args
        | detect t i (_::args) = detect t (i+1) args
        | detect _ _ [] = []
    in
      map (fn t => t |> type_of |> strip_type |> fst |> detect t 0) term
    end
    
    fun define_simp' term simplifyable ctxt =
    let
      val base_name = case Named_Target.locale_of ctxt of
              NONE => ctxt |> Proof_Context.theory_of |> Context.theory_base_name
            | SOME nm => nm
      
      val orig_name = term |> dest_Const_name |> split_name |> List.last
      val red_name = fun_name_to_time ctxt false orig_name
      val name = fun_name_to_time' ctxt true true orig_name
      val full_name = base_name ^ "." ^ name
      val def_name = red_name ^ "_def"
      val def = Binding.name def_name
    
      val canon = Syntax.read_term (Local_Theory.exit ctxt) name |> strip_comb
      val canonFrees = canon |> snd
      val canonType = canon |> fst |> dest_Const_type |> strip_type |> fst |> take (length canonFrees)
    
      val types = term |> dest_Const_type |> strip_type |> fst
      val vars = Variable.variant_fixes (map (K "") types) ctxt |> fst
      fun l_typs' i ((T as (Type ("fun",_)))::types) =
        (if contains simplifyable i
         then change_typ T
         else HOLogic.mk_prodT (T,change_typ T))
        :: l_typs' (i+1) types
        | l_typs' i (T::types) = T :: l_typs' (i+1) types
        | l_typs' _ [] = []
      val l_typs = l_typs' 0 types
      val lhs =
        List.foldl (fn ((v,T),t) => t $ Free (v,T)) (Free (red_name,l_typs ---> HOLogic.natT)) (ListPair.zip (vars,l_typs))
      fun fixType (TFree _) = HOLogic.unitT
        | fixType (Type (n,ts)) = Type (n, map fixType ts)
        | fixType T = T
      fun fixUnspecified T = T |> strip_type ||> fixType |> (op --->)
      fun r_terms' i (v::vars) ((T as (Type ("fun",_)))::types) =
        (if contains simplifyable i
        then HOLogic.mk_prod (Const ("HOL.undefined", fixUnspecified T), Free (v,change_typ T))
        else Free (v,HOLogic.mk_prodT (T,change_typ T)))
        :: r_terms' (i+1) vars types
        | r_terms' i (v::vars) (T::types) = Free (v,T) :: r_terms' (i+1) vars types
        | r_terms' _ _ _ = []
      val r_terms = r_terms' 0 vars types
      val full_type = (r_terms |> map (type_of) ---> HOLogic.natT)
      val full = list_comb (Const (full_name,canonType ---> full_type), canonFrees)
      val rhs = list_comb (full, r_terms)
      val eq = (lhs, rhs) |> HOLogic.mk_eq |> HOLogic.mk_Trueprop
      val _ = Pretty.writeln (Pretty.block [Pretty.str "Defining simplified version:\n",
                                            Syntax.pretty_term ctxt eq])
    
      val (_, ctxt') = Specification.definition NONE [] [] ((def, []), eq) ctxt
    
    in
      ((def_name, orig_name), ctxt')
    end
    fun define_simp simpables ctxt =
    let
      fun cond ((term,simplifyable),(defs,ctxt)) =
        define_simp' term simplifyable ctxt |>> (fn def => def :: defs)
    in
      List.foldr cond ([], ctxt) simpables
    end
    
    
    fun replace from to =
      map (map_aterms (fn t => if t = from then to else t))
    fun replaceAll [] = I
      | replaceAll ((from,to)::xs) = replaceAll xs o replace from to
    fun calculateSimplifications ctxt T_terms term simpables =
    let
      (* Show where a simplification can take place *)
        fun reportReductions (t,(i::is)) =
        (Pretty.writeln (Pretty.str
          ((Term.term_name t |> fun_name_to_time' ctxt false true)
            ^ " can be simplified because only the time-function component of parameter "
            ^ (Int.toString (i + 1)) ^ " is used. "));
            reportReductions (t,is))
          | reportReductions (_,[]) = ()
        val _ = simpables
          |> map reportReductions
    
        (* Register definitions for simplified function *)
        val (reds, ctxt) = define_simp simpables ctxt
    
        fun genRetype (Const (nm,T),is) =
        let
          val T_name = fun_name_to_time ctxt true nm |> split_name |> List.last
          val from = Free (T_name,change_typ T)
          val to = Free (T_name,change_typ' (not o contains is) T)
        in
          (from,to)
        end
          | genRetype _ = error "Internal error: invalid term"
        val retyping = map genRetype simpables
    
        fun replaceArgs (pT $ (eq $ l $ r)) =
        let
          val (t,params) = strip_comb l
          fun match (Const (f_nm,_),_) = 
                (fun_name_to_time ctxt true f_nm |> Long_Name.base_name) = (dest_Free t |> fst)
            | match _ = false
          val simps = List.find match simpables |> Option.valOf |> snd
    
          fun dest_Prod_snd (Free (nm, Type (_, [_, T2]))) =
                Free (fun_name_to_time ctxt false nm, T2)
            | dest_Prod_snd _ = error "Internal error: Argument is not a pair"
          fun rep _ [] = ([],[])
            | rep i (x::xs) =
          let 
            val (rs,args) = rep (i+1) xs
          in
            if contains simps i
              then (x::rs,dest_Prod_snd x::args)
              else (rs,x::args)
          end
          val (rs,params) = rep 0 params
          fun fFst _ = error "Internal error: Invalid term to simplify"
          fun fSnd (t as (Const _ $ f)) =
            (if contains rs f
              then dest_Prod_snd f
              else t)
            | fSnd t = t
        in
          (pT $ (eq
              $ (list_comb (t,params))
              $ (replaceFstSndFree ctxt term fFst fSnd r
                  |> (fn t => replaceAll (map (fn t => (t,dest_Prod_snd t)) rs) [t])
                  |> hd
                )
          ))
        end
        | replaceArgs _ = error "Internal error: Invalid term"
    
        (* Calculate reduced terms *)
        val T_terms_red = T_terms
          |> replaceAll retyping
          |> map replaceArgs
    
        val _ = print_lemma ctxt reds T_terms_red
        val _ = 
            Pretty.writeln (Pretty.str "If you do not want the simplified T function, use \"time_fun [no_simp]\"")
    in
      ctxt
    end

    val _ =
      case time_term lthy true (hd term)
            handle (ERROR _) => NONE
        of SOME _ => error ("Timing function already declared: " ^ (Term.term_name (hd term)))
         | NONE => ()

    (* Number of terms fixed by locale *)
    val fixedNum = term |> hd
      |> strip_comb |> snd
      |> length

    (********************* BEGIN OF CONVERSION *********************)
    (* 1. Fix all terms *)
    (* Exchange Var in types and terms to Free and check constraints *)
    val terms = map
      (map_aterms freeTerms
        #> map_types (map_atyps freeTypes)
        #> fixTerms lthy term fixedNum)
      terms
    val fixedFrees = (hd term) |> strip_comb |> snd |> take fixedNum 
    val fixedFreesNames = map (fst o dest_Free) fixedFrees
    val term = map (shortFunc fixedNum o fst o strip_comb) term
    fun correctTerm term =
    let
      val get_f = fst o strip_comb o get_l
    in
      List.find (fn t => (dest_Const_name o get_f) t = dest_Const_name term) terms
        |> Option.valOf |> get_f
    end
    val term = map correctTerm term

    (* 2. Find properties about the function *)
    (* 2.1 Check if function is recursive *)
    val is_rec = is_rec lthy term terms

    (* 3. Convert every equation
      - Change type of toplevel equation from _ \<Rightarrow> _ \<Rightarrow> bool to nat \<Rightarrow> nat \<Rightarrow> bool
      - On left side change name of function to timing function
      - Convert right side of equation with conversion schema
    *)
    fun fFst (t as (Const (_,T) $ Free (nm,_))) =
      (if contains fixedFreesNames nm
        then Free (nm,strip_type T |>> tl |> (op --->))
        else t)
      | fFst t = t
    fun fSnd (t as (Const (_,T) $ Free (nm,_))) =
      (if contains fixedFreesNames nm
        then Free (fun_name_to_time lthy false nm,strip_type T |>> tl |> (op --->))
        else t)
      | fSnd t = t
    val T_terms = map (convert_term lthy term is_rec) terms
      |> map (map_r (replaceFstSndFree lthy term fFst fSnd))
      |> map (postFixTerms lthy full_term)

    val simpables = (if #simp config
      then find_simplifyble lthy term T_terms
      else map (K []) term)
      |> (fn s => ListPair.zip (term,s))
    (* Determine if something is simpable, if so rename everything *)
    val simpable = simpables |> map snd |> exists (not o null)
    (* Rename to secondary if simpable *)
    fun genRename (t,_) =
      let
        val old = fun_to_time' lthy term false t |> Option.valOf
        val new = fun_to_time' lthy term true t |> Option.valOf
      in
        (old,new)
      end
    val can_T_terms = if simpable 
      then replaceAll (map genRename simpables) T_terms
      else T_terms

    (* 4. Register function and prove completeness *)
    val names = map Term.term_name term
    val timing_names = map (fun_name_to_time' lthy true simpable) names
    val bindings = map (fn nm => (Binding.name nm, NONE, NoSyn)) timing_names
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt
    val specs = map (fn eq => (((Binding.empty, []), eq), [], [])) can_T_terms
    val part_specs = (Binding.empty_atts, hd can_T_terms)

    (* Context for printing without showing question marks *)
    val print_ctxt = lthy
      |> Config.put show_question_marks false
      |> Config.put show_sorts false (* Change it for debugging *)
    val print_ctxt = List.foldl (fn (term, ctxt) => Variable.add_fixes_implicit term ctxt) print_ctxt (term @ T_terms)
    (* Print result if print *)
    val _ = if not (#print config) then () else
        let
          val nms = map (dest_Const_name) term
          val typs = map (dest_Const_type) term
        in
          print_timing' print_ctxt { names=nms, terms=terms, typs=typs }
            { names=timing_names, terms=can_T_terms, typs=map change_typ typs  }
        end
    
    (* For partial functions sequential=true is needed in order to support them
       We need sequential=false to support the automatic proof of termination over dom
    *)
    fun register seq =
      let
        val _ = (if seq then warning "Falling back on sequential function..." else ())
        val fun_config = Function_Common.FunctionConfig
          {sequential=seq, default=NONE, domintros=true, partials=false}
      in
        if #partial config
        then Partial_Function.add_partial_function "option" bindings part_specs lthy |>> PartialFunction o snd
        else Function.add_function bindings specs fun_config pat_completeness_auto lthy |>> Function
      end

    val (info,ctxt) = 
      register false
        handle (ERROR _) =>
          register true
             | Match =>
          register true

    val ctxt = if simpable then calculateSimplifications ctxt T_terms term simpables else ctxt
  in
    (info, ctxt)
  end
fun proove_termination (term: term list) terms (T_info: Function.info, lthy: local_theory) =
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
            terms |> hd |> get_l |> map_types (map_atyps freeTypes)
            |> args |> Variable.variant_names lthy
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
  in
    (Function time_info, lthy')
  end
fun reg_and_proove_time_func (lthy: local_theory) (term: term list) (terms: term list) (config: time_config) =
  case reg_time_func lthy term terms config
    of (Function info, lthy') => proove_termination term terms (info, lthy')
     | r => r

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

fun check_opts [] = false
  | check_opts ["no_simp"] = true
  | check_opts (a::_) = error ("Option " ^ a ^ " is not defined")

(* Converts a function into its timing function using fun *)
fun reg_time_fun_cmd ((opts, funcs), thms) (ctxt: local_theory) =
let
  val no_simp = check_opts opts
  val fterms = map (Syntax.read_term ctxt) funcs
  val ctxt = set_suffix fterms ctxt
  val config = { print = true, simp = not no_simp, partial = false }
  val (_, ctxt') = reg_and_proove_time_func ctxt fterms
    (case thms of NONE => get_terms ctxt (hd fterms)
                | SOME thms => thms |> Attrib.eval_thms ctxt |> List.map Thm.prop_of)
    config
in ctxt'
end

(* Converts a function into its timing function using function with termination proof provided by user*)
fun reg_time_function_cmd ((opts, funcs), thms) (ctxt: local_theory) =
let
  val no_simp = check_opts opts
  val fterms = map (Syntax.read_term ctxt) funcs
  val ctxt = set_suffix fterms ctxt
  val config = { print = true, simp = not no_simp, partial = false }
  val ctxt' = reg_time_func ctxt fterms
    (case thms of NONE => get_terms ctxt (hd fterms)
                | SOME thms => thms |> Attrib.eval_thms ctxt |> List.map Thm.prop_of)
    config
    |> snd
in ctxt'
end

(* Converts a function definition into its timing function using definition *)
fun reg_time_definition_cmd ((opts, funcs), thms) (ctxt: local_theory) =
let
  val no_simp = check_opts opts
  val fterms = map (Syntax.read_term ctxt) funcs
  val ctxt = set_suffix fterms ctxt
  val config = { print = true, simp = not no_simp, partial = false }
  val (_, ctxt') = reg_and_proove_time_func ctxt fterms
    (case thms of NONE => get_terms ctxt (hd fterms) |> check_definition
                | SOME thms => thms |> Attrib.eval_thms ctxt |> List.map Thm.prop_of)
    config
in ctxt'
end

(* Converts a a partial function into its timing function using partial_function *)
fun reg_time_partial_function_cmd ((opts, funcs), thms) (ctxt: local_theory) =
let
  val no_simp = check_opts opts
  val fterms = map (Syntax.read_term ctxt) funcs
  val ctxt = set_suffix fterms ctxt
  val config = { print = true, simp = not no_simp, partial = true }
  val (_, ctxt') = reg_and_proove_time_func ctxt fterms
    (case thms of NONE => get_terms ctxt (hd fterms) |> check_definition
                | SOME thms => thms |> Attrib.eval_thms ctxt |> List.map Thm.prop_of)
    config
in ctxt'
end

val parser = (Parse.opt_attribs >> map (fst o Token.name_of_src))
             -- Scan.repeat1 Parse.prop
             -- Scan.option (Parse.keyword_improper "equations" -- Parse.thms1 >> snd)
val _ = Toplevel.local_theory
val _ = Outer_Syntax.local_theory @{command_keyword "time_fun"}
  "Defines runtime function of a function"
  (parser >> reg_time_fun_cmd)

val _ = Outer_Syntax.local_theory @{command_keyword "time_function"}
  "Defines runtime function of a function"
  (parser >> reg_time_function_cmd)

val _ = Outer_Syntax.local_theory @{command_keyword "time_definition"}
  "Defines runtime function of a definition"
  (parser >> reg_time_definition_cmd)

val _ = Outer_Syntax.local_theory @{command_keyword "time_partial_function"}
  "Defines runtime function of a definition"
  (parser >> reg_time_partial_function_cmd)

end
