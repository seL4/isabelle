(*  Title:      HOL/SMT/Tools/smt_monomorph.ML
    Author:     Sascha Boehme, TU Muenchen

Monomorphization of terms, i.e., computation of all (necessary) instances.
*)

signature SMT_MONOMORPH =
sig
  val monomorph: theory -> term list -> term list
end

structure SMT_Monomorph: SMT_MONOMORPH =
struct

fun selection [] = []
  | selection (x :: xs) = (x, xs) :: map (apsnd (cons x)) (selection xs)

fun permute [] = []
  | permute [x] = [[x]]
  | permute xs = maps (fn (y, ys) => map (cons y) (permute ys)) (selection xs)

fun fold_all f = fold (fn x => maps (f x))


val typ_has_tvars = Term.exists_subtype (fn TVar _ => true | _ => false)
val term_has_tvars = Term.exists_type typ_has_tvars

val ignored = member (op =) [
  @{const_name All}, @{const_name Ex}, @{const_name Let}, @{const_name If},
  @{const_name "op ="}, @{const_name zero_class.zero},
  @{const_name one_class.one}, @{const_name number_of}]
fun consts_of ts = AList.group (op =) (fold Term.add_consts ts [])
  |> filter_out (ignored o fst)

val join_consts = curry (AList.join (op =) (K (merge (op =))))
fun diff_consts cs ds = 
  let fun diff (n, Ts) =
    (case AList.lookup (op =) cs n of
      NONE => SOME (n, Ts)
    | SOME Us =>
        let val Ts' = fold (remove (op =)) Us Ts
        in if null Ts' then NONE else SOME (n, Ts') end)
  in map_filter diff ds end

fun instances thy is (n, Ts) env =
  let
    val Us = these (AList.lookup (op =) is n)
    val Ts' = filter typ_has_tvars (map (Envir.subst_type env) Ts)
  in
    (case map_product pair Ts' Us of
      [] => [env]
    | TUs => map_filter (try (fn TU => Sign.typ_match thy TU env)) TUs)
  end

fun proper_match ps env =
  forall (forall (not o typ_has_tvars o Envir.subst_type env) o snd) ps

val eq_tab = gen_eq_set (op =) o pairself Vartab.dest

fun specialize thy cs is ((r, ps), ces) (ts, ns) =
  let
    val ps' = filter (AList.defined (op =) is o fst) ps

    val envs = permute ps'
      |> maps (fn ps => fold_all (instances thy is) ps [Vartab.empty])
      |> filter (proper_match ps')
      |> filter_out (member eq_tab ces)
      |> distinct eq_tab

    val us = map (fn env => Envir.subst_term_types env r) envs
    val ns' = join_consts (diff_consts is (diff_consts cs (consts_of us))) ns
  in (envs @ ces, (fold (insert (op aconv)) us ts, ns')) end


fun incr_tvar_indices i t =
  let
    val incrT = Logic.incr_tvar i

    fun incr t =
      (case t of
        Const (n, T) => Const (n, incrT T)
      | Free (n, T) => Free (n, incrT T)
      | Abs (n, T, t1) => Abs (n, incrT T, incr t1)
      | t1 $ t2 => incr t1 $ incr t2
      | _ => t)
  in incr t end


val monomorph_limit = 10

(* Instantiate all polymorphic constants (i.e., constants occurring both with
   ground types and type variables) with all (necessary) ground types; thereby
   create copies of terms containing those constants.
   To prevent non-termination, there is an upper limit for the number of
   recursions involved in the fixpoint construction. *)
fun monomorph thy ts =
  let
    val (ps, ms) = List.partition term_has_tvars ts

    fun with_tvar (n, Ts) =
      let val Ts' = filter typ_has_tvars Ts
      in if null Ts' then NONE else SOME (n, Ts') end
    fun incr t idx = (incr_tvar_indices idx t, idx + Term.maxidx_of_term t + 1)
    val rps = fst (fold_map incr ps 0)
      |> map (fn r => (r, map_filter with_tvar (consts_of [r])))

    fun mono count is ces cs ts =
      let
        val spec = specialize thy cs is
        val (ces', (ts', is')) = fold_map spec (rps ~~ ces) (ts, [])
        val cs' = join_consts is cs
      in
        if null is' then ts'
        else if count > monomorph_limit then
          (Output.warning "monomorphization limit reached"; ts')
        else mono (count + 1) is' ces' cs' ts'
      end
  in mono 0 (consts_of ms) (map (K []) rps) [] ms end

end
