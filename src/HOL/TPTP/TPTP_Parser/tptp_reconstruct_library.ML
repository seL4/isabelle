(*  Title:      HOL/TPTP/TPTP_Parser/tptp_reconstruct_library.ML
    Author:     Nik Sultana, Cambridge University Computer Laboratory
Collection of general functions used in the reconstruction module.
*)

signature TPTP_RECONSTRUCT_LIBRARY =
sig
  exception BREAK_LIST
  val break_list : 'a list -> 'a * 'a list
  val break_seq : 'a Seq.seq -> 'a * 'a Seq.seq
  exception MULTI_ELEMENT_LIST
  val cascaded_filter_single : bool -> ('a list -> 'a list) list -> 'a list -> 'a option
  val concat_between : 'a list list -> ('a option * 'a option) -> 'a list
  exception DIFF_TYPE of typ * typ
  exception DIFF of term * term
  val diff :
     theory ->
     term * term -> (term * term) list * (typ * typ) list
  exception DISPLACE_KV
  val displace_kv : ''a -> (''a * 'b) list -> (''a * 'b) list
  val enumerate : int -> 'a list -> (int * 'a) list
  val fold_options : 'a option list -> 'a list
  val find_and_remove : ('a -> bool) -> 'a list -> 'a * 'a list
  val lift_option : ('a -> 'b) -> 'a option -> 'b option
  val list_diff : ''a list -> ''a list -> ''a list
  val list_prod : 'a list list -> 'a list -> 'a list -> 'a list list
  val permute : ''a list -> ''a list list
  val prefix_intersection_list :
     ''a list -> ''a list -> ''a list
  val repeat_until_fixpoint : (''a -> ''a) -> ''a -> ''a
  val switch : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val zip_amap :
       'a list ->
       'b list ->
       ('a * 'b) list -> ('a * 'b) list * ('a list * 'b list)

  val consts_in : term -> term list
  val head_quantified_variable : Proof.context -> int -> thm -> (string * typ) option
  val push_allvar_in : string -> term -> term
  val strip_top_All_var : term -> (string * typ) * term
  val strip_top_All_vars : term -> (string * typ) list * term
  val strip_top_all_vars :
     (string * typ) list -> term -> (string * typ) list * term
  val trace_tac' : Proof.context -> string ->
     ('a -> thm -> 'b Seq.seq) -> 'a -> thm -> 'b Seq.seq
  val try_dest_Trueprop : term -> term

  val type_devar : typ Term_Subst.TVars.table -> term -> term
  val diff_and_instantiate : Proof.context -> thm -> term -> term -> thm

  val batter_tac : Proof.context -> int -> tactic
  val break_hypotheses_tac : Proof.context -> int -> tactic
  val clause_breaker_tac : Proof.context -> int -> tactic
  (* val dist_all_and_tac : Proof.context -> int -> tactic *)(*FIXME unused*)
  val reassociate_conjs_tac : Proof.context -> int -> tactic

  val ASAP : (int -> tactic) -> (int -> tactic) -> int -> tactic
  val COND' :
     ('a -> thm -> bool) ->
     ('a -> tactic) -> ('a -> tactic) -> 'a -> tactic

  val TERMFUN :
     (term list * term -> 'a) -> int option -> thm -> 'a list
  val TERMPRED :
     (term -> bool) ->
     (term -> bool) -> int option -> thm -> bool

  val guided_abstract :
     bool -> term -> term -> ((string * typ) * term) * term list
  val abstract :
     term list -> term -> ((string * typ) * term) list * term
end

structure TPTP_Reconstruct_Library : TPTP_RECONSTRUCT_LIBRARY =
struct

(*zip as much as possible*)
fun zip_amap [] ys acc = (acc, ([], ys))
  | zip_amap xs [] acc = (acc, (xs, []))
  | zip_amap (x :: xs) (y :: ys) acc =
      zip_amap xs ys ((x, y) :: acc);

(*Pair a list up with the position number of each element,
  starting from n*)
fun enumerate n ls =
  let
    fun enumerate' [] _ acc = acc
      | enumerate' (x :: xs) n acc = enumerate' xs (n + 1) ((n, x) :: acc)
  in
    enumerate' ls n []
    |> rev
  end

(*
enumerate 0 [];
enumerate 0 ["a", "b", "c"];
*)

(*List subtraction*)
fun list_diff l1 l2 =
  filter (fn x => forall (fn y => x <> y) l2) l1

val _ = \<^assert>
  (list_diff [1,2,3] [2,4] = [1, 3])

(* [a,b] times_list [c,d] gives [[a,c,d], [b,c,d]] *)
fun list_prod acc [] _ = rev acc
  | list_prod acc (x :: xs) ys = list_prod ((x :: ys) :: acc) xs ys

fun repeat_until_fixpoint f x =
  let
    val x' = f x
  in
    if x = x' then x else repeat_until_fixpoint f x'
  end

(*compute all permutations of a list*)
fun permute l =
  let
    fun permute' (l, []) = [(l, [])]
      | permute' (l, xs) =
          map (fn x => (x :: l, filter (fn y => y <> x) xs)) xs
          |> maps permute'
  in
    permute' ([], l)
    |> map fst
  end
(*
permute [1,2,3];
permute ["A", "B"]
*)

(*this exception is raised when the pair we wish to displace
  isn't found in the association list*)
exception DISPLACE_KV;
(*move a key-value pair, determined by the k, to the beginning of
  an association list. it moves the first occurrence of a pair
  keyed by "k"*)
local
  fun fold_fun k (kv as (k', v)) (l, buff) =
    if is_some buff then (kv :: l, buff)
    else
      if k = k' then
        (l, SOME kv)
      else
        (kv :: l, buff)
in
  (*"k" is the key value of the pair we wish to displace*)
  fun displace_kv k alist =
    let
      val (pre_alist, kv) = fold (fold_fun k) alist ([], NONE)
    in
      if is_some kv then
        the kv :: rev pre_alist
      else raise DISPLACE_KV
    end
end

(*Given two lists, it generates a new list where
  the intersection of the lists forms the prefix
  of the new list.*)
local
  fun prefix_intersection_list' (acc_pre, acc_pro) l1 l2 =
    if null l1 then
      List.rev acc_pre @ List.rev acc_pro
    else if null l2 then
      List.rev acc_pre @ l1 @ List.rev acc_pro
    else
      let val l1_hd = hd l1
      in
        prefix_intersection_list'
         (if member (op =) l2 l1_hd then
            (l1_hd :: acc_pre, acc_pro)
          else
           (acc_pre, l1_hd :: acc_pro))
         (tl l1) l2
      end
in
  fun prefix_intersection_list l1 l2 = prefix_intersection_list' ([], []) l1 l2
end;

val _ = \<^assert>
  (prefix_intersection_list [1,2,3,4,5] [1,3,5] = [1, 3, 5, 2, 4]);

val _ = \<^assert>
  (prefix_intersection_list [1,2,3,4,5] [] = [1,2,3,4,5]);

val _ = \<^assert>
  (prefix_intersection_list [] [1,3,5] = [])

fun switch f y x = f x y

(*Given a value of type "'a option list", produce
  a value of type "'a list" by dropping the NONE elements
  and projecting the SOME elements.*)
fun fold_options opt_list =
  fold
   (fn x => fn l => if is_some x then the x :: l else l)
   opt_list
   [];

val _ = \<^assert>
  ([2,0,1] =
   fold_options [NONE, SOME 1, NONE, SOME 0, NONE, NONE, SOME 2]);

fun lift_option (f : 'a -> 'b) (x_opt : 'a option) : 'b option =
  case x_opt of
      NONE => NONE
    | SOME x => SOME (f x)

fun break_seq x = (Seq.hd x, Seq.tl x)

exception BREAK_LIST
fun break_list (x :: xs) = (x, xs)
  | break_list _ = raise BREAK_LIST

exception MULTI_ELEMENT_LIST
(*Try a number of predicates, in order, to find a single element.
  Predicates are expected to either return an empty list or a
  singleton list. If strict=true and list has more than one element,
  then raise an exception. Otherwise try a new predicate.*)
fun cascaded_filter_single strict preds l =
  case preds of
      [] => NONE
    | (p :: ps) =>
      case p l of
          [] => cascaded_filter_single strict ps l
        | [x] => SOME x
        | l =>
            if strict then raise MULTI_ELEMENT_LIST
            else cascaded_filter_single strict ps l

(*concat but with optional before-and-after delimiters*)
fun concat_between [] _ = []
  | concat_between [l] _ = l
  | concat_between (l :: ls) (seps as (bef, aft)) =
    let
      val pre = if is_some bef then the bef :: l else l
      val mid = if is_some aft then [the aft] else []
      val post = concat_between ls seps
    in
      pre @ mid @ post
    end

(*Given a list, find an element satisfying pred, and return
  a pair consisting of that element and the list minus the element.*)
fun find_and_remove pred l =
  find_index pred l
  |> switch chop l
  |> apsnd break_list
  |> (fn (xs, (y, ys)) => (y, xs @ ys))

val _ = \<^assert> (find_and_remove (curry (op =) 3) [0,1,2,3,4,5] = (3, [0,1,2,4,5]))


(** Functions on terms **)

(*Extract the forall-prefix of a term, and return a pair consisting of the prefix
  and the body*)
local
  (*Strip off HOL's All combinator if it's at the toplevel*)
  fun try_dest_All (Const (\<^const_name>\<open>HOL.All\<close>, _) $ t) = t
    | try_dest_All (Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ t) = try_dest_All t
    | try_dest_All t = t

  val _ = \<^assert>
    ((\<^term>\<open>\<forall>x. (\<forall>y. P) = True\<close>
      |> try_dest_All
      |> Term.strip_abs_vars)
     = [("x", \<^typ>\<open>'a\<close>)])

  val _ = \<^assert>
    ((\<^prop>\<open>\<forall>x. (\<forall>y. P) = True\<close>
      |> try_dest_All
      |> Term.strip_abs_vars)
     = [("x", \<^typ>\<open>'a\<close>)])

  fun strip_top_All_vars' once acc t =
    let
      val t' = try_dest_All t
      val var =
        try (Term.strip_abs_vars #> hd) t'

      fun strip v t =
        (v, subst_bounds ([Free v], Term.strip_abs_body t))
    in
      if t' = t orelse is_none var then (acc, t)
      else
        let
          val (v, t) = strip (the var) t'
          val acc' = v :: acc
        in
          if once then (acc', t)
          else strip_top_All_vars' once acc' t
        end
    end
in
  fun strip_top_All_vars t = strip_top_All_vars' false [] t

val _ =
  let
    val answer =
      ([("x", \<^typ>\<open>'a\<close>)],
       HOLogic.all_const \<^typ>\<open>'a\<close> $
        (HOLogic.eq_const \<^typ>\<open>'a\<close> $
         Free ("x", \<^typ>\<open>'a\<close>)))
  in
    \<^assert>
      ((\<^term>\<open>\<forall>x. All ((=) x)\<close>
        |> strip_top_All_vars)
       = answer)
  end

  (*like strip_top_All_vars, but peels a single variable off, instead of all of them*)
  fun strip_top_All_var t =
    strip_top_All_vars' true [] t
    |> apfst the_single
end

(*like strip_top_All_vars but for "Pure.all" instead of "HOL.All"*)
fun strip_top_all_vars acc t =
  if Logic.is_all t then
    let
      val (v, t') = Logic.dest_all t
      (*bound instances in t' are replaced with free vars*)
    in
      strip_top_all_vars (v :: acc) t'
    end
  else (acc, (*variables are returned in FILO order*)
        t)

(*given a term "t"
    ! X Y Z. t'
  then then "push_allvar_in "X" t" will give
    ! Y Z X. t'
*)
fun push_allvar_in v t =
  let
    val (vs, t') = strip_top_All_vars t
    val vs' = displace_kv v vs
  in
    fold (fn (v, ty) => fn t =>
      HOLogic.mk_all (v, ty, t)) vs' t'
  end

(*Lists all consts in a term, uniquely*)
fun consts_in (Const c) = [Const c]
  | consts_in (Free _) = []
  | consts_in (Var _) = []
  | consts_in (Bound _) = []
  | consts_in (Abs (_, _, t)) = consts_in t
  | consts_in (t1 $ t2) = union (op =) (consts_in t1) (consts_in t2);

exception DIFF of term * term
exception DIFF_TYPE of typ * typ
(*This carries out naive form of matching.  It "diffs" two formulas,
  to create a function which maps (schematic or non-schematic)
  variables to terms.  The first argument is the more "general" term.
  The second argument is used to find the "image" for the variables in
  the first argument which don't appear in the second argument.

  Note that the list that is returned might have duplicate entries.
  It's not checked to see if the same variable maps to different
  values -- that should be regarded as an error.*)
fun diff thy (initial as (t_gen, t)) =
  let
    fun diff_ty acc [] = acc
      | diff_ty acc ((pair as (ty_gen, ty)) :: ts) =
          case pair of
              (Type (s1, ty_gens1), Type (s2, ty_gens2)) =>
                if s1 <> s2 orelse
                 length ty_gens1 <> length ty_gens2 then
                  raise (DIFF (t_gen, t))
                else
                  diff_ty acc
                   (ts @ ListPair.zip (ty_gens1, ty_gens2))
            | (TFree (s1, so1), TFree (s2, so2)) =>
                if s1 <> s2 orelse
                 not (Sign.subsort thy (so2, so1)) then
                  raise (DIFF (t_gen, t))
                else
                  diff_ty acc ts
            | (TVar (idx1, so1), TVar (idx2, so2)) =>
                if idx1 <> idx2 orelse
                 not (Sign.subsort thy (so2, so1)) then
                  raise (DIFF (t_gen, t))
                else
                  diff_ty acc ts
            | (TFree _, _) => diff_ty (pair :: acc) ts
            | (TVar _, _) => diff_ty (pair :: acc) ts
            | _ => raise (DIFF_TYPE pair)

    fun diff' (acc as (acc_t, acc_ty)) (pair as (t_gen, t)) ts =
      case pair of
          (Const (s1, ty1), Const (s2, ty2)) =>
            if s1 <> s2 orelse
             not (Sign.typ_instance thy (ty2, ty1)) then
              raise (DIFF (t_gen, t))
            else
              diff_probs acc ts
        | (Free (s1, ty1), Free (s2, ty2)) =>
            if s1 <> s2 orelse
             not (Sign.typ_instance thy (ty2, ty1)) then
              raise (DIFF (t_gen, t))
            else
              diff_probs acc ts
        | (Var (idx1, ty1), Var (idx2, ty2)) =>
            if idx1 <> idx2 orelse
             not (Sign.typ_instance thy (ty2, ty1)) then
              raise (DIFF (t_gen, t))
            else
              diff_probs acc ts
        | (Bound i1, Bound i2) =>
            if i1 <> i2 then
              raise (DIFF (t_gen, t))
            else
              diff_probs acc ts
        | (Abs (s1, ty1, t1), Abs (s2, ty2, t2)) =>
            if s1 <> s2 orelse
             not (Sign.typ_instance thy (ty2, ty1)) then
              raise (DIFF (t_gen, t))
            else
              diff' acc (t1, t2) ts
        | (ta1 $ ta2, tb1 $ tb2) =>
            diff_probs acc ((ta1, tb1) :: (ta2, tb2) :: ts)

        (*the particularly important bit*)
        | (Free (_, ty), _) =>
            diff_probs
             (pair :: acc_t,
              diff_ty acc_ty [(ty, Term.fastype_of t)])
             ts
        | (Var (_, ty), _) =>
            diff_probs
             (pair :: acc_t,
              diff_ty acc_ty [(ty, Term.fastype_of t)])
             ts

        (*everything else is problematic*)
        | _ => raise (DIFF (t_gen, t))

    and diff_probs acc ts =
      case ts of
          [] => acc
        | (pair :: ts') => diff' acc pair ts'
  in
    diff_probs ([], []) [initial]
  end

(*Abstracts occurrences of "t_sub" in "t", returning a list of
  abstractions of "t" with a Var at each occurrence of "t_sub".
  If "strong=true" then it uses strong abstraction (i.e., replaces
   all occurrnces of "t_sub"), otherwise it uses weak abstraction
   (i.e., replaces the occurrences one at a time).
  NOTE there are many more possibilities between strong and week.
    These can be enumerated by abstracting based on the powerset
    of occurrences (minus the null element, which would correspond
    to "t").
*)
fun guided_abstract strong t_sub t =
  let
    val varnames = Term.add_frees t [] |> map #1
    val prefixK = "v"
    val freshvar =
      let
        fun find_fresh i =
          let
            val varname = prefixK ^ Int.toString i
          in
            if member (op =) varnames varname then
              find_fresh (i + 1)
            else
              (varname, fastype_of t_sub)
          end
      in
        find_fresh 0
      end

    fun guided_abstract' t =
      case t of
          Abs (s, ty, t') =>
            if t = t_sub then [Free freshvar]
            else
              (map (fn t' => Abs (s, ty, t'))
               (guided_abstract' t'))
        | t1 $ t2 =>
            if t = t_sub then [Free freshvar]
            else
                (map (fn t' => t' $ t2)
                  (guided_abstract' t1)) @
                (map (fn t' => t1 $ t')
                  (guided_abstract' t2))
        | _ =>
            if t = t_sub then [Free freshvar]
            else [t]

    fun guided_abstract_strong' t =
      let
        fun continue t = guided_abstract_strong' t
          |> (fn x => if null x then t
                else the_single x)
      in
        case t of
            Abs (s, ty, t') =>
              if t = t_sub then [Free freshvar]
              else
                [Abs (s, ty, continue t')]
          | t1 $ t2 =>
              if t = t_sub then [Free freshvar]
              else
                [continue t1 $ continue t2]
          | _ =>
              if t = t_sub then [Free freshvar]
              else [t]
      end

  in
    ((freshvar, t_sub),
     if strong then guided_abstract_strong' t
     else guided_abstract' t)
  end

(*Carries out strong abstraction of a term guided by a list of
  other terms.
  In case some of the latter terms happen to be the same, it
  only abstracts them once.
  It returns the abstracted term, together with a map from
   the fresh names to the terms.*)
fun abstract ts t =
  fold_map (apsnd the_single oo (guided_abstract true)) ts t
  |> (fn (v_and_ts, t') =>
       let
         val (vs, ts) = ListPair.unzip v_and_ts
         val vs' =
           (* list_diff vs (list_diff (Term.add_frees t' []) vs) *)
           Term.add_frees t' []
           |> list_diff vs
           |> list_diff vs
         val v'_and_ts =
           map (fn v =>
             (v, AList.lookup (op =) v_and_ts v |> the))
            vs'
       in
         (v'_and_ts, t')
       end)

(*Instantiate type variables in a term, based on a type environment*)
fun type_devar tyenv (t : term) : term =
  case t of
      Const (s, ty) => Const (s, Term_Subst.instantiateT tyenv ty)
    | Free (s, ty) => Free (s, Term_Subst.instantiateT tyenv ty)
    | Var (idx, ty) => Var (idx, Term_Subst.instantiateT tyenv ty)
    | Bound _ => t
    | Abs (s, ty, t') =>
        Abs (s, Term_Subst.instantiateT tyenv ty, type_devar tyenv t')
    | t1 $ t2 => type_devar tyenv t1 $ type_devar tyenv t2

(*Take a "diff" between an (abstract) thm's term, and another term
  (the latter is an instance of the form), then instantiate the
  abstract theorem. This is a way of turning the latter term into
  a theorem, but without exposing the proof-search functions to
  complex terms.
  In addition to the abstract thm ("scheme_thm"), this function is
  also supplied with the (sub)term of the abstract thm ("scheme_t")
  we want to use in the diff, in case only part of "scheme_t"
  might be needed (not the whole "Thm.prop_of scheme_thm")*)
fun diff_and_instantiate ctxt scheme_thm scheme_t instance_t =
  let
    val (term_pairing, type_pairing) =
      diff (Proof_Context.theory_of ctxt) (scheme_t, instance_t)

    (*valuation of type variables*)
    val typeval = map (fn (v, T) => (dest_TVar v, Thm.ctyp_of ctxt T)) type_pairing

    val typeval_env =
      Term_Subst.TVars.table (map (apfst dest_TVar) type_pairing)
    (*valuation of term variables*)
    val termval =
      map (apfst (dest_Var o type_devar typeval_env)) term_pairing
      |> map (apsnd (Thm.cterm_of ctxt))
  in
    Thm.instantiate (typeval, termval) scheme_thm
  end

(*FIXME this is bad form?*)
val try_dest_Trueprop = perhaps (try HOLogic.dest_Trueprop)


(** Some tacticals **)

(*Lift COND to be parametrised by subgoal number*)
fun COND' sat' tac'1 tac'2 i =
  COND (sat' i) (tac'1 i) (tac'2 i)

(*Apply simplification ("wittler") as few times as possible
  before being able to apply a tactic ("tac").
  This is like a lazy version of REPEAT, since it attempts
  to REPEAT a tactic the smallest number times as possible,
  to make some other tactic succeed subsequently.*)
fun ASAP wittler (tac : int -> tactic) (i : int) = fn st =>
  let
    val tac_result = tac i st
    val pulled_tac_result = Seq.pull tac_result
    val tac_failed =
      is_none pulled_tac_result orelse
       not (has_fewer_prems 1 (fst (the pulled_tac_result)))
  in
    if tac_failed then (wittler THEN' ASAP wittler tac) i st
    else tac_result
  end


(** Some tactics **)

fun break_hypotheses_tac ctxt =
  CHANGED o
   ((REPEAT_DETERM o eresolve_tac ctxt @{thms conjE}) THEN'
    (REPEAT_DETERM o eresolve_tac ctxt @{thms disjE}))

(*Prove subgoals of form A ==> B1 | ... | A | ... | Bn*)
fun clause_breaker_tac ctxt =
  (REPEAT o resolve_tac ctxt @{thms disjI1 disjI2 conjI}) THEN'
  assume_tac ctxt

(*
  Refines a subgoal have the form:
    A1 ... An ==> B1 | ... | Aj | ... | Bi | ... | Ak | ...
  into multiple subgoals of the form:
    A'1 ==> B1 | ... | Aj | ... | Bi | ... | Ak | ...
     :
    A'm ==> B1 | ... | Aj | ... | Bi | ... | Ak | ...
  where {A'1 .. A'm} is disjoint from {B1, ..., Aj, ..., Bi, ..., Ak, ...}
  (and solves the subgoal completely if the first set is empty)
*)
fun batter_tac ctxt i =
  break_hypotheses_tac ctxt i THEN
  ALLGOALS (TRY o clause_breaker_tac ctxt)

(*Same idiom as ex_expander_tac*)
fun dist_all_and_tac ctxt i =
   let
     val simpset =
       empty_simpset ctxt
       |> Simplifier.add_simp
           @{lemma "\<forall>x. P x \<and> Q x \<equiv> (\<forall>x. P x) \<and> (\<forall>x. Q x)"
              by (rule eq_reflection, auto)}
   in
     CHANGED (asm_full_simp_tac simpset i)
   end

fun reassociate_conjs_tac ctxt =
  asm_full_simp_tac
   (Simplifier.add_simp
    @{lemma "(A & B) & C == A & B & C" by auto} (*FIXME duplicates @{thm simp_meta(3)}*)
    (Raw_Simplifier.empty_simpset ctxt))
  #> CHANGED
  #> REPEAT_DETERM


(** Subgoal analysis **)

(*Given an inference
        C
      -----
        D
  This function returns "SOME X" if C = "! X. C'".
  If C has no quantification prefix, then returns NONE.*)
fun head_quantified_variable ctxt i = fn st =>
  let
    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst

    val hypos =
      if null gls then []
      else
        rpair (i - 1) gls
        |> uncurry nth
        |> strip_top_all_vars []
        |> snd
        |> Logic.strip_horn
        |> fst

    fun foralls_of_hd_hypos () =
      hd hypos
      |> try_dest_Trueprop
      |> strip_top_All_vars
      |> #1
      |> rev

    val quantified_variables = foralls_of_hd_hypos ()
  in
    if null hypos orelse null quantified_variables then NONE
    else SOME (hd quantified_variables)
  end


(** Builders for goal analysers or transformers **)

(*Lifts function over terms to apply it to subgoals.
  "fun_over_terms" has type (term list * term -> 'a), where
  (term list * term) will be the term representations of the
  hypotheses and conclusion.
  if i_opt=SOME i then applies fun_over_terms to that
   subgoal and returns singleton result.
  otherwise applies fun_over_terms to all subgoals and return
   list of results.*)
fun TERMFUN
 (fun_over_terms : term list * term -> 'a)
 (i_opt : int option) : thm -> 'a list = fn st =>
  let
    val t_raws =
        Thm.prop_of st
        |> strip_top_all_vars []
        |> snd
        |> Logic.strip_horn
        |> fst
  in
    if null t_raws then []
    else
      let
        val ts =
          let
            val stripper =
              strip_top_all_vars []
              #> snd
              #> Logic.strip_horn
              #> apsnd try_dest_Trueprop
              #> apfst (map try_dest_Trueprop)
          in
            map stripper t_raws
          end
      in
        case i_opt of
            NONE =>
              map fun_over_terms ts
          | SOME i =>
              nth ts (i - 1)
              |> fun_over_terms
              |> single
      end
  end

(*Applies a predicate to subgoal(s) conclusion(s)*)
fun TERMPRED
 (hyp_pred_over_terms : term -> bool)
 (conc_pred_over_terms : term -> bool)
 (i_opt : int option) : thm -> bool = fn st =>
    let
      val hyp_results =
        TERMFUN (fst (*discard hypotheses*)
                 #> map hyp_pred_over_terms) i_opt st
      val conc_results =
        TERMFUN (snd (*discard hypotheses*)
                 #> conc_pred_over_terms) i_opt st
      val _ = \<^assert> (length hyp_results = length conc_results)
    in
      if null hyp_results then true
      else
        let
          val hyps_conjoined =
            fold (fn a => fn b =>
              b andalso (forall (fn x => x) a)) hyp_results true
          val concs_conjoined =
            fold (fn a => fn b =>
              b andalso a) conc_results true
        in hyps_conjoined andalso concs_conjoined end
    end


(** Tracing **)
(*If "tac i st" succeeds then msg is printed to "trace" channel*)
fun trace_tac' ctxt msg tac i st =
  let
    val result = tac i st
  in
    if Config.get ctxt tptp_trace_reconstruction andalso
     not (is_none (Seq.pull result)) then
      (tracing msg; result)
    else result
  end

end
