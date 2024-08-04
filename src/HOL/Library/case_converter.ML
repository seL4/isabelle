(* Author: Pascal Stoop, ETH Zurich
   Author: Andreas Lochbihler, Digital Asset *)

signature CASE_CONVERTER =
sig
  type elimination_strategy
  val to_case: Proof.context -> elimination_strategy -> (string * typ -> int) ->
    thm list -> thm list option
  val replace_by_type: (Proof.context -> string * string -> bool) -> elimination_strategy
  val keep_constructor_context: elimination_strategy
end;

structure Case_Converter : CASE_CONVERTER =
struct

fun lookup_remove _ _ [] = (NONE, [])
  | lookup_remove eq k ((k', v) :: kvs) =
    if eq (k, k') then (SOME (k', v), kvs)
    else apsnd (cons (k', v)) (lookup_remove eq k kvs)

fun mk_abort msg t =
  let 
    val T = fastype_of t
    val abort = Const (\<^const_name>\<open>missing_pattern_match\<close>, HOLogic.literalT --> (HOLogic.unitT --> T) --> T)
  in
    abort $ HOLogic.mk_literal msg $ absdummy HOLogic.unitT t
  end

(* fold_term : (string * typ -> 'a) ->
               (string * typ -> 'a) ->
               (indexname * typ -> 'a) ->
               (int -> 'a) ->
               (string * typ * 'a -> 'a) ->
               ('a * 'a -> 'a) ->
               term ->
               'a *)
fun fold_term const_fun free_fun var_fun bound_fun abs_fun dollar_fun term =
  let
    fun go x = case x of
      Const (s, T) => const_fun (s, T)
      | Free (s, T) => free_fun (s, T)
      | Var (i, T) => var_fun (i, T)
      | Bound n => bound_fun n
      | Abs (s, T, term) => abs_fun (s, T, go term)
      | term1 $ term2 => dollar_fun (go term1, go term2)
  in
    go term
  end;

datatype term_coordinate = End of typ
  | Coordinate of (string * (int * term_coordinate)) list;

fun term_coordinate_merge (End T) _ = End T
  | term_coordinate_merge _ (End T) = End T
  | term_coordinate_merge (Coordinate xs) (Coordinate ys) =
  let
    fun merge_consts xs [] = xs
      | merge_consts xs ((s1, (n, y)) :: ys) = 
        case List.partition (fn (s2, (m, _)) => s1 = s2 andalso n = m) xs of
            ([], xs') => (s1, (n, y)) :: (merge_consts xs' ys)
          | ((_, (_, x)) :: _, xs') => (s1, (n, term_coordinate_merge x y)) :: (merge_consts xs' ys)
  in
    Coordinate (merge_consts xs ys)
  end;

fun coordinates_to_list (End x) = [(x, [])]
  | coordinates_to_list (Coordinate xs) = 
  let
    fun f (s, (n, xss)) = map (fn (T, xs) => (T, (s, n) :: xs)) (coordinates_to_list xss)
  in flat (map f xs) end;

type elimination_strategy = Proof.context -> term list -> term_coordinate list

fun replace_by_type replace_ctr ctxt pats =
  let
    fun term_to_coordinates P term = 
      let
        val (ctr, args) = strip_comb term
      in
        case ctr of Const (s, T) =>
          if P (dest_Type_name (body_type T), s)
          then SOME (End (body_type T))
          else
            let
              fun f (i, t) = term_to_coordinates P t |> Option.map (pair i)
              val tcos = map_filter I (map_index f args)
            in
              if null tcos then NONE
              else SOME (Coordinate (map (pair s) tcos))
            end
        | _ => NONE
      end
    in
      map_filter (term_to_coordinates (replace_ctr ctxt)) pats
    end

fun keep_constructor_context ctxt pats =
  let
    fun to_coordinates [] = NONE
      | to_coordinates pats =
        let
          val (fs, argss) = map strip_comb pats |> split_list
          val f = hd fs
          fun is_single_ctr (Const (name, T)) = 
              let
                val tyco = dest_Type_name (body_type T)
                val _ = Ctr_Sugar.ctr_sugar_of ctxt tyco |> the |> #ctrs
              in
                case Ctr_Sugar.ctr_sugar_of ctxt tyco of
                  NONE => error ("Not a free constructor " ^ name ^ " in pattern")
                | SOME info =>
                  case #ctrs info of [Const (name', _)] => name = name'
                    | _ => false
              end
            | is_single_ctr _ = false
        in 
          if not (is_single_ctr f) andalso forall (fn x => f = x) fs then
            let
              val patss = Ctr_Sugar_Util.transpose argss
              fun recurse (i, pats) = to_coordinates pats |> Option.map (pair i)
              val coords = map_filter I (map_index recurse patss)
            in
              if null coords then NONE
              else SOME (Coordinate (map (pair (dest_Const_name f)) coords))
            end
          else SOME (End (body_type (fastype_of f)))
          end
    in
      the_list (to_coordinates pats)
    end


(* AL: TODO: change from term to const_name *)
fun find_ctr ctr1 xs =
  let
    fun const_equal (ctr1, ctr2) = dest_Const_name ctr1 = dest_Const_name ctr2
  in
    lookup_remove const_equal ctr1 xs
  end;

datatype pattern 
  = Wildcard
  | Value
  | Split of int * (term * pattern) list * pattern;

fun pattern_merge Wildcard pat' = pat'
  | pattern_merge Value _ = Value
  | pattern_merge (Split (n, xs, pat)) Wildcard =
    Split (n, map (apsnd (fn pat'' => pattern_merge pat'' Wildcard)) xs, pattern_merge pat Wildcard)
  | pattern_merge (Split _) Value = Value
  | pattern_merge (Split (n, xs, pat)) (Split (m, ys, pat'')) =
    let 
      fun merge_consts xs [] = map (apsnd (fn pat => pattern_merge pat Wildcard)) xs
        | merge_consts xs ((ctr, y) :: ys) =
          (case find_ctr ctr xs of
              (SOME (ctr, x), xs) => (ctr, pattern_merge x y) :: merge_consts xs ys
            | (NONE, xs) => (ctr, y) :: merge_consts xs ys
          )
     in
       Split (if n <= 0 then m else n, merge_consts xs ys, pattern_merge pat pat'')
     end
     
fun pattern_intersect Wildcard _ = Wildcard
  | pattern_intersect Value pat2 = pat2
  | pattern_intersect (Split _) Wildcard = Wildcard
  | pattern_intersect (Split (n, xs', pat1)) Value =
    Split (n,
      map (apsnd (fn pat1 => pattern_intersect pat1 Value)) xs',
      pattern_intersect pat1 Value)
  | pattern_intersect (Split (n, xs', pat1)) (Split (m, ys, pat2)) =
    Split (if n <= 0 then m else n, 
      intersect_consts xs' ys pat1 pat2,
      pattern_intersect pat1 pat2)
and
    intersect_consts xs [] _ default2 = map (apsnd (fn pat => pattern_intersect pat default2)) xs
  | intersect_consts xs ((ctr, pat2) :: ys) default1 default2 = case find_ctr ctr xs of
    (SOME (ctr, pat1), xs') => 
      (ctr, pattern_merge (pattern_merge (pattern_intersect pat1 pat2) (pattern_intersect default1 pat2))
              (pattern_intersect pat1 default2)) ::
      intersect_consts xs' ys default1 default2
    | (NONE, xs') => (ctr, pattern_intersect default1 pat2) :: (intersect_consts xs' ys default1 default2)
        
fun pattern_lookup _ Wildcard = Wildcard
  | pattern_lookup _ Value = Value
  | pattern_lookup [] (Split (n, xs, pat)) = 
    Split (n, map (apsnd (pattern_lookup [])) xs, pattern_lookup [] pat)
  | pattern_lookup (term :: terms) (Split (n, xs, pat)) =
  let
    val (ctr, args) = strip_comb term
    fun map_ctr (term, pat) =
      let
        val args = term |> dest_Const_type |> binder_types |> map (fn T => Free ("x", T))
      in
        pattern_lookup args pat
      end
  in
    if is_Const ctr then
       case find_ctr ctr xs of (SOME (_, pat'), _) => 
           pattern_lookup terms (pattern_merge (pattern_lookup args pat') (pattern_lookup [] pat))
         | (NONE, _) => pattern_lookup terms pat
    else if length xs < n orelse n <= 0 then
      pattern_lookup terms pat
    else pattern_lookup terms
      (pattern_merge
        (fold pattern_intersect (map map_ctr (tl xs)) (map_ctr (hd xs)))
        (pattern_lookup [] pat))
  end;

fun pattern_contains terms pat = case pattern_lookup terms pat of
    Wildcard => false
  | Value => true
  | Split _ => raise Match;

fun pattern_create _ [] = Wildcard
  | pattern_create ctr_count (term :: terms) = 
    let
      val (ctr, args) = strip_comb term
    in
      if is_Const ctr then
        Split (ctr_count ctr, [(ctr, pattern_create ctr_count (args @ terms))], Wildcard)
      else Split (0, [], pattern_create ctr_count terms)
    end;

fun pattern_insert ctr_count terms pat =
  let
    fun new_pattern terms = pattern_insert ctr_count terms (pattern_create ctr_count terms)
    fun aux _ false Wildcard = Wildcard
      | aux terms true Wildcard = if null terms then Value else new_pattern terms
      | aux _ _ Value = Value
      | aux terms modify (Split (n, xs', pat)) =
      let
        val unmodified = (n, map (apsnd (aux [] false)) xs', aux [] false pat)
      in case terms of [] => Split unmodified
        | term :: terms =>
        let
          val (ctr, args) = strip_comb term
          val (m, ys, pat') = unmodified
        in
          if is_Const ctr
            then case find_ctr ctr xs' of
              (SOME (ctr, pat''), xs) =>
                Split (m, (ctr, aux (args @ terms) modify pat'') :: map (apsnd (aux [] false)) xs, pat')
              | (NONE, _) => if modify
                then if m <= 0
                  then Split (ctr_count ctr, (ctr, new_pattern (args @ terms)) :: ys, pat')
                  else Split (m, (ctr, new_pattern (args @ terms)) :: ys, pat')
                else Split unmodified
            else Split (m, ys, aux terms modify pat)
        end
      end
  in
    aux terms true pat
  end;

val pattern_empty = Wildcard;

fun replace_frees lhss rhss typ_list ctxt =
  let
    fun replace_frees_once (lhs, rhs) ctxt =
      let
        val add_frees_list = fold_rev Term.add_frees
        val frees = add_frees_list lhs []
        val (new_frees, ctxt1) = (Ctr_Sugar_Util.mk_Frees "x" (map snd frees) ctxt)
        val (new_frees1, ctxt2) =
          let
            val (dest_frees, types) = split_list (map dest_Free new_frees)
            val (new_frees, ctxt2) = Variable.variant_fixes dest_frees ctxt1
          in
            (map Free (new_frees ~~ types), ctxt2)
          end
        val dict = frees ~~ new_frees1
        fun free_map_fun (s, T) =
          case AList.lookup (op =) dict (s, T) of
              NONE => Free (s, T)
            | SOME x => x
        val map_fun = fold_term Const free_map_fun Var Bound Abs (op $)
      in
        ((map map_fun lhs, map_fun rhs), ctxt2)
      end

    fun variant_fixes (def_frees, ctxt) =
      let
        val (dest_frees, types) = split_list (map dest_Free def_frees)
        val (def_frees, ctxt1) = Variable.variant_fixes dest_frees ctxt
      in
        (map Free (def_frees ~~ types), ctxt1)
      end
    val (def_frees, ctxt1) = variant_fixes (Ctr_Sugar_Util.mk_Frees "x" typ_list ctxt)
    val (rhs_frees, ctxt2) = variant_fixes (Ctr_Sugar_Util.mk_Frees "x" typ_list ctxt1)
    val (case_args, ctxt3) = variant_fixes (Ctr_Sugar_Util.mk_Frees "x"
      (map fastype_of (hd lhss)) ctxt2)
    val (new_terms1, ctxt4) = fold_map replace_frees_once (lhss ~~ rhss) ctxt3
    val (lhss1, rhss1) = split_list new_terms1
  in
    (lhss1, rhss1, def_frees ~~ rhs_frees, case_args, ctxt4)
  end;

fun add_names_in_type (Type (name, Ts)) = 
    List.foldr (op o) (Symtab.update (name, ())) (map add_names_in_type Ts)
  | add_names_in_type (TFree _) = I
  | add_names_in_type (TVar _) = I

fun add_names_in_term (Const (_, T)) = add_names_in_type T
  | add_names_in_term (Free (_, T)) = add_names_in_type T
  | add_names_in_term (Var (_, T)) = add_names_in_type T
  | add_names_in_term (Bound _) = I
  | add_names_in_term (Abs (_, T, body)) =
    add_names_in_type T o add_names_in_term body
  | add_names_in_term (t1 $ t2) = add_names_in_term t1 o add_names_in_term t2

fun add_type_names terms =
  fold (fn term => fn f => add_names_in_term term o f) terms I

fun get_split_theorems ctxt =
  Symtab.keys
  #> map_filter (Ctr_Sugar.ctr_sugar_of ctxt)
  #> map #split;

fun match (Const (s1, _)) (Const (s2, _)) = if s1 = s2 then SOME I else NONE
  | match (Free y) x = SOME (fn z => if z = Free y then x else z)
  | match (pat1 $ pattern2) (t1 $ t2) =
    (case (match pat1 t1, match pattern2 t2) of
       (SOME f, SOME g) => SOME (f o g)
       | _ => NONE
     )
  | match _ _ = NONE;

fun match_all patterns terms =
  let
    fun combine _ NONE = NONE
      | combine (f_opt, f_opt') (SOME g) = 
        case match f_opt f_opt' of SOME f => SOME (f o g) | _ => NONE
  in
    fold_rev combine (patterns ~~ terms) (SOME I)
  end

fun matches (Const (s1, _)) (Const (s2, _)) = s1 = s2
  | matches (Free _) _ = true 
  | matches (pat1 $ pat2) (t1 $ t2) = matches pat1 t1 andalso matches pat2 t2
  | matches _ _ = false;
fun matches_all patterns terms = forall (uncurry matches) (patterns ~~ terms)

fun terms_to_case_at ctr_count ctxt (fun_t : term) (default_lhs : term list)
    (pos, (lazy_case_arg, rhs_free))
    ((lhss : term list list), (rhss : term list), type_name_fun) =
  let
    fun abort t =
      let
        val fun_name = dest_Const_name (head_of t)
        val msg = "Missing pattern in " ^ fun_name ^ "."
      in
        mk_abort msg t
      end;

    (* Step 1 : Eliminate lazy pattern *)
    fun replace_pat_at (n, tcos) pat pats =
      let
        fun map_at _ _ [] = raise Empty
          | map_at n f (x :: xs) = if n > 0
            then apfst (cons x) (map_at (n - 1) f xs)
            else apfst (fn x => x :: xs) (f x)
        fun replace [] pat term = (pat, term)
          | replace ((s1, n) :: tcos) pat term =
            let
              val (ctr, args) = strip_comb term
            in
              case ctr of Const (s2, _) =>
                  if s1 = s2
                  then apfst (pair ctr #> list_comb) (map_at n (replace tcos pat) args)
                  else (term, rhs_free)
                | _ => (term, rhs_free)
            end
        val (part1, (old_pat, part2)) = chop n pats ||> (fn xs => (hd xs, tl xs))
        val (new_pat, old_pat1) = replace tcos pat old_pat
      in
        (part1 @ [new_pat] @ part2, old_pat1)
      end                               
    val (lhss1, lazy_pats) = map (replace_pat_at pos lazy_case_arg) lhss
      |> split_list

    (* Step 2 : Split patterns *)
    fun split equs =
      let
        fun merge_pattern (Const (s1, T1), Const (s2, _)) =
            if s1 = s2 then SOME (Const (s1, T1)) else NONE
          | merge_pattern (t, Free _) = SOME t
          | merge_pattern (Free _, t) = SOME t
          | merge_pattern (t1l $ t1r, t2l $ t2r) =
            (case (merge_pattern (t1l, t2l), merge_pattern (t1r, t2r)) of
              (SOME t1, SOME t2) => SOME (t1 $ t2)
              | _ => NONE)
          | merge_pattern _ = NONE
        fun merge_patterns pats1 pats2 = case (pats1, pats2) of
          ([], []) => SOME []
          | (x :: xs, y :: ys) =>
            (case (merge_pattern (x, y), merge_patterns xs ys) of
              (SOME x, SOME xs) => SOME (x :: xs)
              | _ => NONE
            )
          | _ => raise Match
        fun merge_insert ((lhs1, case_pat), _) [] =
            [(lhs1, pattern_empty |> pattern_insert ctr_count [case_pat])]
          | merge_insert ((lhs1, case_pat), rhs) ((lhs2, pat) :: pats) =
            let
              val pats = merge_insert ((lhs1, case_pat), rhs) pats
              val (first_equ_needed, new_lhs) = case merge_patterns lhs1 lhs2 of
                SOME new_lhs => (not (pattern_contains [case_pat] pat), new_lhs)
                | NONE => (false, lhs2)
              val second_equ_needed = not (matches_all lhs1 lhs2)
                orelse not first_equ_needed
              val first_equ = if first_equ_needed
                then [(new_lhs, pattern_insert ctr_count [case_pat] pat)]
                else []
              val second_equ = if second_equ_needed
                then [(lhs2, pat)]
                else []
            in
              first_equ @ second_equ @ pats
            end
        in
          (fold merge_insert equs []
            |> split_list
            |> fst) @ [default_lhs]
        end
    val lhss2 = split ((lhss1 ~~ lazy_pats) ~~ rhss)

    (* Step 3 : Remove redundant patterns *)
    fun remove_redundant_lhs lhss =
      let
        fun f lhs pat = if pattern_contains lhs pat
          then ((lhs, false), pat)
          else ((lhs, true), pattern_insert ctr_count lhs pat)
      in
        fold_map f lhss pattern_empty
        |> fst
        |> filter snd
        |> map fst
      end
    fun remove_redundant_rhs rhss =
      let
        fun f (lhs, rhs) pat = if pattern_contains [lhs] pat
          then (((lhs, rhs), false), pat)
          else (((lhs, rhs), true), pattern_insert ctr_count [lhs] pat)
      in
        map fst (filter snd (fold_map f rhss pattern_empty |> fst))
      end
    val lhss3 = remove_redundant_lhs lhss2

    (* Step 4 : Compute right hand side *)
    fun subs_fun f = fold_term
      Const
      (f o Free)
      Var
      Bound
      Abs
      (fn (x, y) => f x $ f y)
    fun find_rhss lhs =
      let
        fun f (lhs1, (pat, rhs)) = 
          case match_all lhs1 lhs of NONE => NONE
          | SOME f => SOME (pat, subs_fun f rhs)
      in
        remove_redundant_rhs
          (map_filter f (lhss1 ~~ (lazy_pats ~~ rhss)) @
            [(lazy_case_arg, list_comb (fun_t, lhs) |> abort)]
          )
      end

    (* Step 5 : make_case of right hand side *)
    fun make_case ctxt case_arg cases = case cases of
      [(Free x, rhs)] => subs_fun (fn y => if y = Free x then case_arg else y) rhs
      | _ => Case_Translation.make_case
        ctxt
        Case_Translation.Warning
        Name.context
        case_arg
        cases
    val type_name_fun = add_type_names lazy_pats o type_name_fun
    val rhss3 = map ((make_case ctxt lazy_case_arg) o find_rhss) lhss3
  in
    (lhss3, rhss3, type_name_fun)
  end;

fun terms_to_case ctxt ctr_count (head : term) (lhss : term list list)
    (rhss : term list) (typ_list : typ list) (poss : (int * (string * int) list) list) =
  let
    val (lhss1, rhss1, def_frees, case_args, ctxt1) = replace_frees lhss rhss typ_list ctxt
    val exec_list = poss ~~ def_frees
    val (lhss2, rhss2, type_name_fun) = fold_rev
      (terms_to_case_at ctr_count ctxt1 head case_args) exec_list (lhss1, rhss1, I)
    fun make_eq_term (lhss, rhs) = (list_comb (head, lhss), rhs)
      |> HOLogic.mk_eq
      |> HOLogic.mk_Trueprop
  in
    (map make_eq_term (lhss2 ~~ rhss2),
      get_split_theorems ctxt1 (type_name_fun Symtab.empty),
      ctxt1)
  end;


fun build_case_t elimination_strategy ctr_count head lhss rhss ctxt =
  let
    val num_eqs = length lhss
    val _ = if length rhss = num_eqs andalso num_eqs > 0 then ()
      else raise Fail
        ("expected same number of left-hand sides as right-hand sides\n"
          ^ "and at least one equation")
    val n = length (hd lhss)
    val _ = if forall (fn m => length m = n) lhss then ()
      else raise Fail "expected equal number of arguments"

    fun to_coordinates (n, ts) = 
      case elimination_strategy ctxt ts of
          [] => NONE
        | (tco :: tcos) => SOME (n, fold term_coordinate_merge tcos tco |> coordinates_to_list)
    fun add_T (n, xss) = map (fn (T, xs) => (T, (n, xs))) xss
    val (typ_list, poss) = lhss
      |> Ctr_Sugar_Util.transpose
      |> map_index to_coordinates
      |> map_filter (Option.map add_T)
      |> flat
      |> split_list
  in
    if null poss then ([], [], ctxt)
    else terms_to_case ctxt (dest_Const #> ctr_count) head lhss rhss typ_list poss
  end;

fun tac ctxt {splits, intros, defs} =
  let
    val split_and_subst = 
      split_tac ctxt splits 
      THEN' REPEAT_ALL_NEW (
        resolve_tac ctxt [@{thm conjI}, @{thm allI}]
        ORELSE'
        (resolve_tac ctxt [@{thm impI}] THEN' hyp_subst_tac_thin true ctxt))
  in
    (REPEAT_ALL_NEW split_and_subst ORELSE' K all_tac)
    THEN' (K (Local_Defs.unfold_tac ctxt [@{thm missing_pattern_match_def}]))
    THEN' (K (Local_Defs.unfold_tac ctxt defs))
    THEN_ALL_NEW (SOLVED' (resolve_tac ctxt (@{thm refl} :: intros)))
  end;

fun to_case _ _ _ [] = NONE
  | to_case ctxt replace_ctr ctr_count ths =
    let
      val strip_eq = Thm.prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq
      fun import [] ctxt = ([], ctxt)
        | import (thm :: thms) ctxt =
          let
            val fun_ct = strip_eq #> fst #> head_of #> Logic.mk_term #> Thm.cterm_of ctxt
            val ct = fun_ct thm
            val cts = map fun_ct thms
            val pairs = map (fn s => (s,ct)) cts
            val thms' = map (fn (th,p) => Thm.instantiate (Thm.match p) th) (thms ~~ pairs)
          in
            Variable.import true (thm :: thms') ctxt |> apfst snd
          end

      val (iths, ctxt') = import ths ctxt
      val head = hd iths |> strip_eq |> fst |> head_of
      val eqs = map (strip_eq #> apfst (snd o strip_comb)) iths

      fun hide_rhs ((pat, rhs), name) lthy =
        let
          val frees = fold Term.add_frees pat []
          val abs_rhs = fold absfree frees rhs
          val (f, def, lthy') = case lthy
            |> Local_Defs.define [((Binding.name name, NoSyn), (Binding.empty_atts, abs_rhs))] of
              ([(f, (_, def))], lthy') => (f, def, lthy')
              | _ => raise Match
        in
          ((list_comb (f, map Free (rev frees)), def), lthy')
        end

      val rhs_names = Name.invent (Variable.names_of ctxt') "rhs" (length eqs)
      val ((def_ts, def_thms), ctxt2) =
        fold_map hide_rhs (eqs ~~ rhs_names) ctxt' |> apfst split_list
      val (ts, split_thms, ctxt3) = build_case_t replace_ctr ctr_count head
        (map fst eqs) def_ts ctxt2
      fun mk_thm t = Goal.prove ctxt3 [] [] t
          (fn {context=ctxt, ...} => tac ctxt {splits=split_thms, intros=ths, defs=def_thms} 1)
    in
      if null ts then NONE
      else
        ts
        |> map mk_thm
        |> Proof_Context.export ctxt3 ctxt
        |> map (Goal.norm_result ctxt)
        |> SOME
    end;

end
