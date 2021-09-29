(*  Title:      HOL/Nitpick_Examples/minipick.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2010

Finite model generation for HOL formulas using Kodkod, minimalistic version.
*)

signature MINIPICK =
sig
  val minipick : Proof.context -> int -> term -> string
  val minipick_expect : Proof.context -> string -> int -> term -> unit
end;

structure Minipick : MINIPICK =
struct

open Kodkod
open Nitpick_Util
open Nitpick_HOL
open Nitpick_Peephole
open Nitpick_Kodkod

datatype rep =
  S_Rep |
  R_Rep of bool

fun check_type ctxt raw_infinite \<^Type>\<open>fun T1 T2\<close> =
    List.app (check_type ctxt raw_infinite) [T1, T2]
  | check_type ctxt raw_infinite \<^Type>\<open>prod T1 T2\<close> =
    List.app (check_type ctxt raw_infinite) [T1, T2]
  | check_type _ _ \<^Type>\<open>bool\<close> = ()
  | check_type _ _ (TFree (_, \<^sort>\<open>{}\<close>)) = ()
  | check_type _ _ (TFree (_, \<^sort>\<open>HOL.type\<close>)) = ()
  | check_type ctxt raw_infinite T =
    if raw_infinite T then
      ()
    else
      error ("Not supported: Type " ^ quote (Syntax.string_of_typ ctxt T) ^ ".")

fun atom_schema_of S_Rep card \<^Type>\<open>fun T1 T2\<close> =
    replicate_list (card T1) (atom_schema_of S_Rep card T2)
  | atom_schema_of (R_Rep true) card \<^Type>\<open>fun T1 \<^Type>\<open>bool\<close>\<close> =
    atom_schema_of S_Rep card T1
  | atom_schema_of (rep as R_Rep _) card \<^Type>\<open>fun T1 T2\<close> =
    atom_schema_of S_Rep card T1 @ atom_schema_of rep card T2
  | atom_schema_of _ card \<^Type>\<open>prod T1 T2\<close> =
    maps (atom_schema_of S_Rep card) [T1, T2]
  | atom_schema_of _ card T = [card T]
val arity_of = length ooo atom_schema_of
val atom_seqs_of = map (AtomSeq o rpair 0) ooo atom_schema_of
val atom_seq_product_of = foldl1 Product ooo atom_seqs_of

fun index_for_bound_var _ [_] 0 = 0
  | index_for_bound_var card (_ :: Ts) 0 =
    index_for_bound_var card Ts 0 + arity_of S_Rep card (hd Ts)
  | index_for_bound_var card Ts n = index_for_bound_var card (tl Ts) (n - 1)
fun vars_for_bound_var card R Ts j =
  map (curry Var 1) (index_seq (index_for_bound_var card Ts j)
                               (arity_of R card (nth Ts j)))
val rel_expr_for_bound_var = foldl1 Product oooo vars_for_bound_var
fun decls_for R card Ts T =
  map2 (curry DeclOne o pair 1)
       (index_seq (index_for_bound_var card (T :: Ts) 0)
                  (arity_of R card (nth (T :: Ts) 0)))
       (atom_seqs_of R card T)

val atom_product = foldl1 Product o map Atom

val false_atom_num = 0
val true_atom_num = 1
val false_atom = Atom false_atom_num
val true_atom = Atom true_atom_num

fun kodkod_formula_from_term ctxt total card complete concrete frees =
  let
    fun F_from_S_rep (SOME false) r = Not (RelEq (r, false_atom))
      | F_from_S_rep _ r = RelEq (r, true_atom)
    fun S_rep_from_F NONE f = RelIf (f, true_atom, false_atom)
      | S_rep_from_F (SOME true) f = RelIf (f, true_atom, None)
      | S_rep_from_F (SOME false) f = RelIf (Not f, false_atom, None)
    fun R_rep_from_S_rep \<^Type>\<open>fun T1 T2\<close> r =
        if total andalso T2 = bool_T then
          let
            val jss = atom_schema_of S_Rep card T1 |> map (rpair 0)
                      |> all_combinations
          in
            map2 (fn i => fn js =>
(*
                     RelIf (F_from_S_rep NONE (Project (r, [Num i])),
                            atom_product js, empty_n_ary_rel (length js))
*)
                     Join (Project (r, [Num i]),
                           atom_product (false_atom_num :: js))
                 ) (index_seq 0 (length jss)) jss
            |> foldl1 Union
          end
        else
          let
            val jss = atom_schema_of S_Rep card T1 |> map (rpair 0)
                      |> all_combinations
            val arity2 = arity_of S_Rep card T2
          in
            map2 (fn i => fn js =>
                     Product (atom_product js,
                              Project (r, num_seq (i * arity2) arity2)
                              |> R_rep_from_S_rep T2))
                 (index_seq 0 (length jss)) jss
            |> foldl1 Union
          end
      | R_rep_from_S_rep _ r = r
    fun S_rep_from_R_rep Ts (T as \<^Type>\<open>fun _ _\<close>) r =
        Comprehension (decls_for S_Rep card Ts T,
            RelEq (R_rep_from_S_rep T
                       (rel_expr_for_bound_var card S_Rep (T :: Ts) 0), r))
      | S_rep_from_R_rep _ _ r = r
    fun partial_eq pos Ts \<^Type>\<open>fun T1 T2\<close> t1 t2 =
        HOLogic.mk_all ("x", T1,
                        HOLogic.eq_const T2 $ (incr_boundvars 1 t1 $ Bound 0)
                        $ (incr_boundvars 1 t2 $ Bound 0))
        |> to_F (SOME pos) Ts
      | partial_eq pos Ts T t1 t2 =
        if pos andalso not (concrete T) then
          False
        else
          (t1, t2) |> apply2 (to_R_rep Ts)
                   |> (if pos then Some o Intersect else Lone o Union)
    and to_F pos Ts t =
      (case t of
         \<^Const_>\<open>Not for t1\<close> => Not (to_F (Option.map not pos) Ts t1)
       | \<^Const_>\<open>False\<close> => False
       | \<^Const_>\<open>True\<close> => True
       | \<^Const_>\<open>All _ for \<open>Abs (_, T, t')\<close>\<close> =>
         if pos = SOME true andalso not (complete T) then False
         else All (decls_for S_Rep card Ts T, to_F pos (T :: Ts) t')
       | (t0 as \<^Const_>\<open>All _\<close>) $ t1 =>
         to_F pos Ts (t0 $ eta_expand Ts t1 1)
       | \<^Const_>\<open>Ex _ for \<open>Abs (_, T, t')\<close>\<close> =>
         if pos = SOME false andalso not (complete T) then True
         else Exist (decls_for S_Rep card Ts T, to_F pos (T :: Ts) t')
       | (t0 as \<^Const_>\<open>Ex _\<close>) $ t1 =>
         to_F pos Ts (t0 $ eta_expand Ts t1 1)
       | \<^Const_>\<open>HOL.eq T for t1 t2\<close> =>
         (case pos of
            NONE => RelEq (to_R_rep Ts t1, to_R_rep Ts t2)
          | SOME pos => partial_eq pos Ts T t1 t2)
       | \<^Const_>\<open>less_eq \<^Type>\<open>fun T' \<^Type>\<open>bool\<close>\<close> for t1 t2\<close> =>
         (case pos of
            NONE => Subset (to_R_rep Ts t1, to_R_rep Ts t2)
          | SOME true =>
            Subset (Difference (atom_seq_product_of S_Rep card T',
                                Join (to_R_rep Ts t1, false_atom)),
                    Join (to_R_rep Ts t2, true_atom))
          | SOME false =>
            Subset (Join (to_R_rep Ts t1, true_atom),
                    Difference (atom_seq_product_of S_Rep card T',
                                Join (to_R_rep Ts t2, false_atom))))
       | \<^Const_>\<open>conj for t1 t2\<close> => And (to_F pos Ts t1, to_F pos Ts t2)
       | \<^Const_>\<open>disj for t1 t2\<close> => Or (to_F pos Ts t1, to_F pos Ts t2)
       | \<^Const_>\<open>implies for t1 t2\<close> =>
         Implies (to_F (Option.map not pos) Ts t1, to_F pos Ts t2)
       | \<^Const_>\<open>Set.member _ for t1 t2\<close> => to_F pos Ts (t2 $ t1)
       | t1 $ t2 =>
         (case pos of
            NONE => Subset (to_S_rep Ts t2, to_R_rep Ts t1)
          | SOME pos =>
            let
              val kt1 = to_R_rep Ts t1
              val kt2 = to_S_rep Ts t2
              val kT = atom_seq_product_of S_Rep card (fastype_of1 (Ts, t2))
            in
              if pos then
                Not (Subset (kt2, Difference (kT, Join (kt1, true_atom))))
              else
                Subset (kt2, Difference (kT, Join (kt1, false_atom)))
            end)
       | _ => raise SAME ())
      handle SAME () => F_from_S_rep pos (to_R_rep Ts t)
    and to_S_rep Ts t =
      case t of
        \<^Const_>\<open>Pair _ _ for t1 t2\<close> => Product (to_S_rep Ts t1, to_S_rep Ts t2)
      | \<^Const_>\<open>Pair _ _ for _\<close> => to_S_rep Ts (eta_expand Ts t 1)
      | \<^Const_>\<open>Pair _ _\<close> => to_S_rep Ts (eta_expand Ts t 2)
      | \<^Const_>\<open>fst _ _ for t1\<close> =>
        let val fst_arity = arity_of S_Rep card (fastype_of1 (Ts, t)) in
          Project (to_S_rep Ts t1, num_seq 0 fst_arity)
        end
      | \<^Const_>\<open>fst _ _\<close> => to_S_rep Ts (eta_expand Ts t 1)
      | \<^Const_>\<open>snd _ _ for t1\<close> =>
        let
          val pair_arity = arity_of S_Rep card (fastype_of1 (Ts, t1))
          val snd_arity = arity_of S_Rep card (fastype_of1 (Ts, t))
          val fst_arity = pair_arity - snd_arity
        in Project (to_S_rep Ts t1, num_seq fst_arity snd_arity) end
      | \<^Const_>\<open>snd _ _\<close> => to_S_rep Ts (eta_expand Ts t 1)
      | Bound j => rel_expr_for_bound_var card S_Rep Ts j
      | _ => S_rep_from_R_rep Ts (fastype_of1 (Ts, t)) (to_R_rep Ts t)
    and partial_set_op swap1 swap2 op1 op2 Ts t1 t2 =
      let
        val kt1 = to_R_rep Ts t1
        val kt2 = to_R_rep Ts t2
        val (a11, a21) = (false_atom, true_atom) |> swap1 ? swap
        val (a12, a22) = (false_atom, true_atom) |> swap2 ? swap
      in
        Union (Product (op1 (Join (kt1, a11), Join (kt2, a12)), true_atom),
               Product (op2 (Join (kt1, a21), Join (kt2, a22)), false_atom))
      end
    and to_R_rep Ts t =
      (case t of
         \<^Const_>\<open>Not\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>All _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>Ex _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>HOL.eq _ for _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>HOL.eq _\<close> => to_R_rep Ts (eta_expand Ts t 2)
       | \<^Const_>\<open>less_eq \<^Type>\<open>fun _ \<^Type>\<open>bool\<close>\<close> for _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>less_eq _\<close> => to_R_rep Ts (eta_expand Ts t 2)
       | \<^Const_>\<open>conj for _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>conj\<close> => to_R_rep Ts (eta_expand Ts t 2)
       | \<^Const_>\<open>disj for _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>disj\<close> => to_R_rep Ts (eta_expand Ts t 2)
       | \<^Const_>\<open>implies for _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>implies\<close> => to_R_rep Ts (eta_expand Ts t 2)
       | \<^Const_>\<open>Set.member _ for _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>Set.member _\<close> => to_R_rep Ts (eta_expand Ts t 2)
       | \<^Const_>\<open>Collect _ for t'\<close> => to_R_rep Ts t'
       | \<^Const_>\<open>Collect _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>bot \<open>T as \<^Type>\<open>fun T' \<^Type>\<open>bool\<close>\<close>\<close>\<close> =>
         if total then empty_n_ary_rel (arity_of (R_Rep total) card T)
         else Product (atom_seq_product_of (R_Rep total) card T', false_atom)
       | \<^Const_>\<open>top \<open>T as \<^Type>\<open>fun T' \<^Type>\<open>bool\<close>\<close>\<close>\<close> =>
         if total then atom_seq_product_of (R_Rep total) card T
         else Product (atom_seq_product_of (R_Rep total) card T', true_atom)
       | \<^Const_>\<open>insert T for t1 t2\<close> =>
         if total then
           Union (to_S_rep Ts t1, to_R_rep Ts t2)
         else
           let
             val kt1 = to_S_rep Ts t1
             val kt2 = to_R_rep Ts t2
           in
             RelIf (Some kt1,
                    if arity_of S_Rep card T = 1 then
                      Override (kt2, Product (kt1, true_atom))
                    else
                      Union (Difference (kt2, Product (kt1, false_atom)),
                             Product (kt1, true_atom)),
                    Difference (kt2, Product (atom_seq_product_of S_Rep card T,
                                              false_atom)))
           end
       | \<^Const_>\<open>insert _ for _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>insert _\<close> => to_R_rep Ts (eta_expand Ts t 2)
       | Const (\<^const_name>\<open>trancl\<close>,  (* FIXME proper type!? *)
                Type (_, [Type (_, [Type (_, [T', _]), _]), _])) $ t1 =>
         if arity_of S_Rep card T' = 1 then
           if total then
             Closure (to_R_rep Ts t1)
           else
             let
               val kt1 = to_R_rep Ts t1
               val true_core_kt = Closure (Join (kt1, true_atom))
               val kTx =
                 atom_seq_product_of S_Rep card (HOLogic.mk_prodT (`I T'))
               val false_mantle_kt =
                 Difference (kTx,
                     Closure (Difference (kTx, Join (kt1, false_atom))))
             in
               Union (Product (Difference (false_mantle_kt, true_core_kt),
                               false_atom),
                      Product (true_core_kt, true_atom))
             end
         else
           error "Not supported: Transitive closure for function or pair type."
       | \<^Const_>\<open>trancl _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>inf \<^Type>\<open>fun _ \<^Type>\<open>bool\<close>\<close> for t1 t2\<close> =>
         if total then Intersect (to_R_rep Ts t1, to_R_rep Ts t2)
         else partial_set_op true true Intersect Union Ts t1 t2
       | \<^Const_>\<open>inf _ for _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>inf _\<close> => to_R_rep Ts (eta_expand Ts t 2)
       | \<^Const_>\<open>sup \<^Type>\<open>fun _ \<^Type>\<open>bool\<close>\<close> for t1 t2\<close> =>
         if total then Union (to_R_rep Ts t1, to_R_rep Ts t2)
         else partial_set_op true true Union Intersect Ts t1 t2
       | \<^Const_>\<open>sup _ for _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>sup _\<close> => to_R_rep Ts (eta_expand Ts t 2)
       | \<^Const_>\<open>minus \<^Type>\<open>fun _ \<^Type>\<open>bool\<close>\<close> for t1 t2\<close> =>
         if total then Difference (to_R_rep Ts t1, to_R_rep Ts t2)
         else partial_set_op true false Intersect Union Ts t1 t2
       | \<^Const_>\<open>minus \<^Type>\<open>fun _ \<^Type>\<open>bool\<close>\<close> for _\<close> => to_R_rep Ts (eta_expand Ts t 1)
       | \<^Const_>\<open>minus \<^Type>\<open>fun _ \<^Type>\<open>bool\<close>\<close>\<close> => to_R_rep Ts (eta_expand Ts t 2)
       | \<^Const_>\<open>Pair _ _ for _ _\<close> => to_S_rep Ts t
       | \<^Const_>\<open>Pair _ _ for _\<close> => to_S_rep Ts t
       | \<^Const_>\<open>Pair _ _\<close> => to_S_rep Ts t
       | \<^Const_>\<open>fst _ _ for _\<close> => raise SAME ()
       | \<^Const_>\<open>fst _ _\<close> => raise SAME ()
       | \<^Const_>\<open>snd _ _ for _\<close> => raise SAME ()
       | \<^Const_>\<open>snd _ _\<close> => raise SAME ()
       | \<^Const_>\<open>False\<close> => false_atom
       | \<^Const_>\<open>True\<close> => true_atom
       | Free (x as (_, T)) =>
         Rel (arity_of (R_Rep total) card T, find_index (curry (op =) x) frees)
       | Term.Var _ => error "Not supported: Schematic variables."
       | Bound _ => raise SAME ()
       | Abs (_, T, t') =>
         (case (total, fastype_of1 (T :: Ts, t')) of
            (true, \<^Type>\<open>bool\<close>) =>
            Comprehension (decls_for S_Rep card Ts T, to_F NONE (T :: Ts) t')
          | (_, T') =>
            Comprehension (decls_for S_Rep card Ts T @
                           decls_for (R_Rep total) card (T :: Ts) T',
                           Subset (rel_expr_for_bound_var card (R_Rep total)
                                                          (T' :: T :: Ts) 0,
                                   to_R_rep (T :: Ts) t')))
       | t1 $ t2 =>
         (case fastype_of1 (Ts, t) of
            \<^Type>\<open>bool\<close> =>
            if total then
              S_rep_from_F NONE (to_F NONE Ts t)
            else
              RelIf (to_F (SOME true) Ts t, true_atom,
                     RelIf (Not (to_F (SOME false) Ts t), false_atom,
                     None))
          | T =>
            let val T2 = fastype_of1 (Ts, t2) in
              case arity_of S_Rep card T2 of
                1 => Join (to_S_rep Ts t2, to_R_rep Ts t1)
              | arity2 =>
                let val res_arity = arity_of (R_Rep total) card T in
                  Project (Intersect
                      (Product (to_S_rep Ts t2,
                                atom_seq_product_of (R_Rep total) card T),
                       to_R_rep Ts t1),
                      num_seq arity2 res_arity)
                end
            end)
       | _ => error ("Not supported: Term " ^
                     quote (Syntax.string_of_term ctxt t) ^ "."))
      handle SAME () => R_rep_from_S_rep (fastype_of1 (Ts, t)) (to_S_rep Ts t)
  in to_F (if total then NONE else SOME true) [] end

fun bound_for_free total card i (s, T) =
  let val js = atom_schema_of (R_Rep total) card T in
    ([((length js, i), s)],
     [TupleSet [], atom_schema_of (R_Rep total) card T |> map (rpair 0)
                   |> tuple_set_from_atom_schema])
  end

fun declarative_axiom_for_rel_expr total card Ts \<^Type>\<open>fun T1 T2\<close> r =
    if total andalso body_type T2 = bool_T then
      True
    else
      All (decls_for S_Rep card Ts T1,
           declarative_axiom_for_rel_expr total card (T1 :: Ts) T2
               (List.foldl Join r (vars_for_bound_var card S_Rep (T1 :: Ts) 0)))
  | declarative_axiom_for_rel_expr total _ _ _ r =
    (if total then One else Lone) r
fun declarative_axiom_for_free total card i (_, T) =
  declarative_axiom_for_rel_expr total card [] T
      (Rel (arity_of (R_Rep total) card T, i))

(* Hack to make the old code work as is with sets. *)
fun unsetify_type \<^Type>\<open>set T\<close> = unsetify_type T --> bool_T
  | unsetify_type (Type (s, Ts)) = Type (s, map unsetify_type Ts)
  | unsetify_type T = T

fun kodkod_problem_from_term ctxt total raw_card raw_infinite t =
  let
    val thy = Proof_Context.theory_of ctxt
    fun card \<^Type>\<open>fun T1 T2\<close> = reasonable_power (card T2) (card T1)
      | card \<^Type>\<open>prod T1 T2\<close> = card T1 * card T2
      | card \<^Type>\<open>bool\<close> = 2
      | card T = Int.max (1, raw_card T)
    fun complete \<^Type>\<open>fun T1 T2\<close> = concrete T1 andalso complete T2
      | complete \<^Type>\<open>prod T1 T2\<close> = complete T1 andalso complete T2
      | complete T = not (raw_infinite T)
    and concrete \<^Type>\<open>fun T1 T2\<close> = complete T1 andalso concrete T2
      | concrete \<^Type>\<open>prod T1 T2\<close> = concrete T1 andalso concrete T2
      | concrete _ = true
    val neg_t =
      \<^Const>\<open>Not\<close> $ Object_Logic.atomize_term ctxt t
      |> map_types unsetify_type
    val _ = fold_types (K o check_type ctxt raw_infinite) neg_t ()
    val frees = Term.add_frees neg_t []
    val bounds =
      map2 (bound_for_free total card) (index_seq 0 (length frees)) frees
    val declarative_axioms =
      map2 (declarative_axiom_for_free total card)
           (index_seq 0 (length frees)) frees
    val formula =
      neg_t |> kodkod_formula_from_term ctxt total card complete concrete frees 
            |> fold_rev (curry And) declarative_axioms
    val univ_card = univ_card 0 0 0 bounds formula
  in
    {comment = "", settings = [], univ_card = univ_card, tuple_assigns = [],
     bounds = bounds, int_bounds = [], expr_assigns = [], formula = formula}
  end

fun solve_any_kodkod_problem thy problems =
  let
    val {debug, overlord, timeout, ...} = Nitpick_Commands.default_params thy []
    val deadline = Timeout.end_time timeout
    val max_threads = 1
    val max_solutions = 1
  in
    case solve_any_problem debug overlord deadline max_threads max_solutions
                           problems of
      Normal ([], _, _) => "none"
    | Normal _ => "genuine"
    | TimedOut _ => "unknown"
    | Error (s, _) => error ("Kodkod error: " ^ s)
  end

val default_raw_infinite = member (op =) [\<^Type>\<open>nat\<close>, \<^Type>\<open>int\<close>]

fun minipick ctxt n t =
  let
    val thy = Proof_Context.theory_of ctxt
    val {total_consts, ...} = Nitpick_Commands.default_params thy []
    val totals =
      total_consts |> Option.map single |> the_default [true, false]
    fun problem_for (total, k) =
      kodkod_problem_from_term ctxt total (K k) default_raw_infinite t
  in
    (totals, 1 upto n)
    |-> map_product pair
    |> map problem_for
    |> solve_any_kodkod_problem (Proof_Context.theory_of ctxt)
  end

fun minipick_expect ctxt expect n t =
  if getenv "KODKODI" <> "" then
    if minipick ctxt n t = expect then ()
    else error ("\"minipick_expect\" expected " ^ quote expect)
  else
    ()

end;
