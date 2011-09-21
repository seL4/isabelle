(*  Title:      HOL/Nitpick_Examples/minipick.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2010

Finite model generation for HOL formulas using Kodkod, minimalistic version.
*)

signature MINIPICK =
sig
  datatype rep = S_Rep | R_Rep
  type styp = Nitpick_Util.styp

  val vars_for_bound_var :
    (typ -> int) -> rep -> typ list -> int -> Kodkod.rel_expr list
  val rel_expr_for_bound_var :
    (typ -> int) -> rep -> typ list -> int -> Kodkod.rel_expr
  val decls_for : rep -> (typ -> int) -> typ list -> typ -> Kodkod.decl list
  val false_atom : Kodkod.rel_expr
  val true_atom : Kodkod.rel_expr
  val formula_from_atom : Kodkod.rel_expr -> Kodkod.formula
  val atom_from_formula : Kodkod.formula -> Kodkod.rel_expr
  val kodkod_problem_from_term :
    Proof.context -> (typ -> int) -> term -> Kodkod.problem
  val solve_any_kodkod_problem : theory -> Kodkod.problem list -> string
end;

structure Minipick : MINIPICK =
struct

open Kodkod
open Nitpick_Util
open Nitpick_HOL
open Nitpick_Peephole
open Nitpick_Kodkod

datatype rep = S_Rep | R_Rep

fun check_type ctxt (Type (@{type_name fun}, Ts)) =
    List.app (check_type ctxt) Ts
  | check_type ctxt (Type (@{type_name prod}, Ts)) =
    List.app (check_type ctxt) Ts
  | check_type _ @{typ bool} = ()
  | check_type _ (TFree (_, @{sort "{}"})) = ()
  | check_type _ (TFree (_, @{sort HOL.type})) = ()
  | check_type ctxt T =
    raise NOT_SUPPORTED ("type " ^ quote (Syntax.string_of_typ ctxt T))

fun atom_schema_of S_Rep card (Type (@{type_name fun}, [T1, T2])) =
    replicate_list (card T1) (atom_schema_of S_Rep card T2)
  | atom_schema_of R_Rep card (Type (@{type_name fun}, [T1, @{typ bool}])) =
    atom_schema_of S_Rep card T1
  | atom_schema_of R_Rep card (Type (@{type_name fun}, [T1, T2])) =
    atom_schema_of S_Rep card T1 @ atom_schema_of R_Rep card T2
  | atom_schema_of _ card (Type (@{type_name prod}, Ts)) =
    maps (atom_schema_of S_Rep card) Ts
  | atom_schema_of _ card T = [card T]
val arity_of = length ooo atom_schema_of

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
       (map (AtomSeq o rpair 0) (atom_schema_of R card T))

val atom_product = foldl1 Product o map Atom

val false_atom = Atom 0
val true_atom = Atom 1

fun formula_from_atom r = RelEq (r, true_atom)
fun atom_from_formula f = RelIf (f, true_atom, false_atom)

fun kodkod_formula_from_term ctxt card frees =
  let
    fun R_rep_from_S_rep (Type (@{type_name fun}, [T1, @{typ bool}])) r =
        let
          val jss = atom_schema_of S_Rep card T1 |> map (rpair 0)
                    |> all_combinations
        in
          map2 (fn i => fn js =>
                   RelIf (formula_from_atom (Project (r, [Num i])),
                          atom_product js, empty_n_ary_rel (length js)))
               (index_seq 0 (length jss)) jss
          |> foldl1 Union
        end
      | R_rep_from_S_rep (Type (@{type_name fun}, [T1, T2])) r =
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
    fun S_rep_from_R_rep Ts (T as Type (@{type_name fun}, _)) r =
        Comprehension (decls_for S_Rep card Ts T,
            RelEq (R_rep_from_S_rep T
                       (rel_expr_for_bound_var card S_Rep (T :: Ts) 0), r))
      | S_rep_from_R_rep _ _ r = r
    fun to_F Ts t =
      (case t of
         @{const Not} $ t1 => Not (to_F Ts t1)
       | @{const False} => False
       | @{const True} => True
       | Const (@{const_name All}, _) $ Abs (_, T, t') =>
         All (decls_for S_Rep card Ts T, to_F (T :: Ts) t')
       | (t0 as Const (@{const_name All}, _)) $ t1 =>
         to_F Ts (t0 $ eta_expand Ts t1 1)
       | Const (@{const_name Ex}, _) $ Abs (_, T, t') =>
         Exist (decls_for S_Rep card Ts T, to_F (T :: Ts) t')
       | (t0 as Const (@{const_name Ex}, _)) $ t1 =>
         to_F Ts (t0 $ eta_expand Ts t1 1)
       | Const (@{const_name HOL.eq}, _) $ t1 $ t2 =>
         RelEq (to_R_rep Ts t1, to_R_rep Ts t2)
       | Const (@{const_name ord_class.less_eq},
                Type (@{type_name fun},
                      [Type (@{type_name fun}, [_, @{typ bool}]), _]))
         $ t1 $ t2 =>
         Subset (to_R_rep Ts t1, to_R_rep Ts t2)
       | @{const HOL.conj} $ t1 $ t2 => And (to_F Ts t1, to_F Ts t2)
       | @{const HOL.disj} $ t1 $ t2 => Or (to_F Ts t1, to_F Ts t2)
       | @{const HOL.implies} $ t1 $ t2 => Implies (to_F Ts t1, to_F Ts t2)
       | t1 $ t2 => Subset (to_S_rep Ts t2, to_R_rep Ts t1)
       | Free _ => raise SAME ()
       | Term.Var _ => raise SAME ()
       | Bound _ => raise SAME ()
       | Const (s, _) => raise NOT_SUPPORTED ("constant " ^ quote s)
       | _ => raise TERM ("Minipick.kodkod_formula_from_term.to_F", [t]))
      handle SAME () => formula_from_atom (to_R_rep Ts t)
    and to_S_rep Ts t =
      case t of
        Const (@{const_name Pair}, _) $ t1 $ t2 =>
        Product (to_S_rep Ts t1, to_S_rep Ts t2)
      | Const (@{const_name Pair}, _) $ _ => to_S_rep Ts (eta_expand Ts t 1)
      | Const (@{const_name Pair}, _) => to_S_rep Ts (eta_expand Ts t 2)
      | Const (@{const_name fst}, _) $ t1 =>
        let val fst_arity = arity_of S_Rep card (fastype_of1 (Ts, t)) in
          Project (to_S_rep Ts t1, num_seq 0 fst_arity)
        end
      | Const (@{const_name fst}, _) => to_S_rep Ts (eta_expand Ts t 1)
      | Const (@{const_name snd}, _) $ t1 =>
        let
          val pair_arity = arity_of S_Rep card (fastype_of1 (Ts, t1))
          val snd_arity = arity_of S_Rep card (fastype_of1 (Ts, t))
          val fst_arity = pair_arity - snd_arity
        in Project (to_S_rep Ts t1, num_seq fst_arity snd_arity) end
      | Const (@{const_name snd}, _) => to_S_rep Ts (eta_expand Ts t 1)
      | Bound j => rel_expr_for_bound_var card S_Rep Ts j
      | _ => S_rep_from_R_rep Ts (fastype_of1 (Ts, t)) (to_R_rep Ts t)
    and to_R_rep Ts t =
      (case t of
         @{const Not} => to_R_rep Ts (eta_expand Ts t 1)
       | Const (@{const_name All}, _) => to_R_rep Ts (eta_expand Ts t 1)
       | Const (@{const_name Ex}, _) => to_R_rep Ts (eta_expand Ts t 1)
       | Const (@{const_name HOL.eq}, _) $ _ => to_R_rep Ts (eta_expand Ts t 1)
       | Const (@{const_name HOL.eq}, _) => to_R_rep Ts (eta_expand Ts t 2)
       | Const (@{const_name ord_class.less_eq},
                Type (@{type_name fun},
                      [Type (@{type_name fun}, [_, @{typ bool}]), _])) $ _ =>
         to_R_rep Ts (eta_expand Ts t 1)
       | Const (@{const_name ord_class.less_eq}, _) =>
         to_R_rep Ts (eta_expand Ts t 2)
       | @{const HOL.conj} $ _ => to_R_rep Ts (eta_expand Ts t 1)
       | @{const HOL.conj} => to_R_rep Ts (eta_expand Ts t 2)
       | @{const HOL.disj} $ _ => to_R_rep Ts (eta_expand Ts t 1)
       | @{const HOL.disj} => to_R_rep Ts (eta_expand Ts t 2)
       | @{const HOL.implies} $ _ => to_R_rep Ts (eta_expand Ts t 1)
       | @{const HOL.implies} => to_R_rep Ts (eta_expand Ts t 2)
       | Const (@{const_name bot_class.bot},
                T as Type (@{type_name fun}, [_, @{typ bool}])) =>
         empty_n_ary_rel (arity_of R_Rep card T)
       | Const (@{const_name insert}, _) $ t1 $ t2 =>
         Union (to_S_rep Ts t1, to_R_rep Ts t2)
       | Const (@{const_name insert}, _) $ _ => to_R_rep Ts (eta_expand Ts t 1)
       | Const (@{const_name insert}, _) => to_R_rep Ts (eta_expand Ts t 2)
       | Const (@{const_name trancl}, _) $ t1 =>
         if arity_of R_Rep card (fastype_of1 (Ts, t1)) = 2 then
           Closure (to_R_rep Ts t1)
         else
           raise NOT_SUPPORTED "transitive closure for function or pair type"
       | Const (@{const_name trancl}, _) => to_R_rep Ts (eta_expand Ts t 1)
       | Const (@{const_name inf_class.inf},
                Type (@{type_name fun},
                      [Type (@{type_name fun}, [_, @{typ bool}]), _]))
         $ t1 $ t2 =>
         Intersect (to_R_rep Ts t1, to_R_rep Ts t2)
       | Const (@{const_name inf_class.inf}, _) $ _ =>
         to_R_rep Ts (eta_expand Ts t 1)
       | Const (@{const_name inf_class.inf}, _) =>
         to_R_rep Ts (eta_expand Ts t 2)
       | Const (@{const_name sup_class.sup},
                Type (@{type_name fun},
                      [Type (@{type_name fun}, [_, @{typ bool}]), _]))
         $ t1 $ t2 =>
         Union (to_R_rep Ts t1, to_R_rep Ts t2)
       | Const (@{const_name sup_class.sup}, _) $ _ =>
         to_R_rep Ts (eta_expand Ts t 1)
       | Const (@{const_name sup_class.sup}, _) =>
         to_R_rep Ts (eta_expand Ts t 2)
       | Const (@{const_name minus_class.minus},
                Type (@{type_name fun},
                      [Type (@{type_name fun}, [_, @{typ bool}]), _]))
         $ t1 $ t2 =>
         Difference (to_R_rep Ts t1, to_R_rep Ts t2)
       | Const (@{const_name minus_class.minus},
                Type (@{type_name fun},
                      [Type (@{type_name fun}, [_, @{typ bool}]), _])) $ _ =>
         to_R_rep Ts (eta_expand Ts t 1)
       | Const (@{const_name minus_class.minus},
                Type (@{type_name fun},
                      [Type (@{type_name fun}, [_, @{typ bool}]), _])) =>
         to_R_rep Ts (eta_expand Ts t 2)
       | Const (@{const_name Pair}, _) $ _ $ _ => raise SAME ()
       | Const (@{const_name Pair}, _) $ _ => raise SAME ()
       | Const (@{const_name Pair}, _) => raise SAME ()
       | Const (@{const_name fst}, _) $ _ => raise SAME ()
       | Const (@{const_name fst}, _) => raise SAME ()
       | Const (@{const_name snd}, _) $ _ => raise SAME ()
       | Const (@{const_name snd}, _) => raise SAME ()
       | Const (_, @{typ bool}) => atom_from_formula (to_F Ts t)
       | Free (x as (_, T)) =>
         Rel (arity_of R_Rep card T, find_index (curry (op =) x) frees)
       | Term.Var _ => raise NOT_SUPPORTED "schematic variables"
       | Bound _ => raise SAME ()
       | Abs (_, T, t') =>
         (case fastype_of1 (T :: Ts, t') of
            @{typ bool} => Comprehension (decls_for S_Rep card Ts T,
                                          to_F (T :: Ts) t')
          | T' => Comprehension (decls_for S_Rep card Ts T @
                                 decls_for R_Rep card (T :: Ts) T',
                                 Subset (rel_expr_for_bound_var card R_Rep
                                                              (T' :: T :: Ts) 0,
                                         to_R_rep (T :: Ts) t')))
       | t1 $ t2 =>
         (case fastype_of1 (Ts, t) of
            @{typ bool} => atom_from_formula (to_F Ts t)
          | T =>
            let val T2 = fastype_of1 (Ts, t2) in
              case arity_of S_Rep card T2 of
                1 => Join (to_S_rep Ts t2, to_R_rep Ts t1)
              | arity2 =>
                let val res_arity = arity_of R_Rep card T in
                  Project (Intersect
                      (Product (to_S_rep Ts t2,
                                atom_schema_of R_Rep card T
                                |> map (AtomSeq o rpair 0) |> foldl1 Product),
                       to_R_rep Ts t1),
                      num_seq arity2 res_arity)
                end
            end)
       | _ => raise NOT_SUPPORTED ("term " ^
                                   quote (Syntax.string_of_term ctxt t)))
      handle SAME () => R_rep_from_S_rep (fastype_of1 (Ts, t)) (to_S_rep Ts t)
  in to_F [] end

fun bound_for_free card i (s, T) =
  let val js = atom_schema_of R_Rep card T in
    ([((length js, i), s)],
     [TupleSet [], atom_schema_of R_Rep card T |> map (rpair 0)
                   |> tuple_set_from_atom_schema])
  end

fun declarative_axiom_for_rel_expr card Ts (Type (@{type_name fun}, [T1, T2]))
                                   r =
    if body_type T2 = bool_T then
      True
    else
      All (decls_for S_Rep card Ts T1,
           declarative_axiom_for_rel_expr card (T1 :: Ts) T2
               (List.foldl Join r (vars_for_bound_var card S_Rep (T1 :: Ts) 0)))
  | declarative_axiom_for_rel_expr _ _ _ r = One r
fun declarative_axiom_for_free card i (_, T) =
  declarative_axiom_for_rel_expr card [] T (Rel (arity_of R_Rep card T, i))

fun kodkod_problem_from_term ctxt raw_card t =
  let
    val thy = ProofContext.theory_of ctxt
    fun card (Type (@{type_name fun}, [T1, T2])) =
        reasonable_power (card T2) (card T1)
      | card (Type (@{type_name prod}, [T1, T2])) = card T1 * card T2
      | card @{typ bool} = 2
      | card T = Int.max (1, raw_card T)
    val neg_t = @{const Not} $ Object_Logic.atomize_term thy t
    val _ = fold_types (K o check_type ctxt) neg_t ()
    val frees = Term.add_frees neg_t []
    val bounds = map2 (bound_for_free card) (index_seq 0 (length frees)) frees
    val declarative_axioms =
      map2 (declarative_axiom_for_free card) (index_seq 0 (length frees)) frees
    val formula = kodkod_formula_from_term ctxt card frees neg_t
                  |> fold_rev (curry And) declarative_axioms
    val univ_card = univ_card 0 0 0 bounds formula
  in
    {comment = "", settings = [], univ_card = univ_card, tuple_assigns = [],
     bounds = bounds, int_bounds = [], expr_assigns = [], formula = formula}
  end

fun solve_any_kodkod_problem thy problems =
  let
    val {debug, overlord, ...} = Nitpick_Isar.default_params thy []
    val max_threads = 1
    val max_solutions = 1
  in
    case solve_any_problem debug overlord NONE max_threads max_solutions
                           problems of
      JavaNotInstalled => "unknown"
    | JavaTooOld => "unknown"
    | KodkodiNotInstalled => "unknown"
    | Normal ([], _, _) => "none"
    | Normal _ => "genuine"
    | TimedOut _ => "unknown"
    | Error (s, _) => error ("Kodkod error: " ^ s)
  end

end;
