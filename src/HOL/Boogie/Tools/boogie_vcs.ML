(*  Title:      HOL/Boogie/Tools/boogie_vcs.ML
    Author:     Sascha Boehme, TU Muenchen

Store for Boogie's verification conditions.
*)

signature BOOGIE_VCS =
sig
  datatype skel = Nil of string | Imp of skel | Con1 of skel | Con2 of skel |
    Conj of skel * skel
  val size_of: skel * 'a -> int
  val names_of: skel * 'a -> string list
  val paths_of: skel * term -> (skel * term) list
  val split_path: int -> skel * term -> (skel * term) * (skel * term)
  val extract: skel * term -> string -> (skel * term) option

  val set: (string * term) list -> theory -> theory
  val lookup: theory -> string -> (skel * term) option
  val discharge: string * (skel * thm) -> theory -> theory
  val close: theory -> theory
  val is_closed: theory -> bool

  datatype state = Proved | NotProved | PartiallyProved
  val state_of: theory -> (string * state) list
  val state_of_vc: theory -> string -> string list * string list
end

structure Boogie_VCs: BOOGIE_VCS =
struct

(* simplify VCs: drop True, fold premises into conjunctions *)

local
  val dest_eq = HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of

  val true_rules = map dest_eq @{lemma
    "(True & P) = P" 
    "(P & True) = P"
    "(P --> True) = True"
    "(True --> P) = P"
    by simp_all}

  val fold_prems =
    dest_eq @{lemma "(P1 --> P2 --> Q) = ((P1 & P2) --> Q)" by fast}
in
fun simp_vc thy = Pattern.rewrite_term thy (true_rules @ [fold_prems]) []
end


(* VC skeleton: reflect the structure of implications and conjunctions *)

datatype skel =
  Nil of string |  (* assertion with label name *)
  Imp of skel |    (* implication: only conclusion is relevant *)
  Con1 of skel |   (* only left conjunct *)
  Con2 of skel |   (* right left conjunct *)
  Conj of skel * skel   (* full conjunction *)

val skel_of =
  let
    fun skel (@{term "op -->"} $ _ $ u) = Imp (skel u)
      | skel (@{term "op &"} $ t $ u) = Conj (skel t, skel u)
      | skel (@{term assert_at} $ Free (n, _) $ _) = Nil n
      | skel t = raise TERM ("skel_of", [t])
  in skel o HOLogic.dest_Trueprop end

fun size (Nil _) = 1
  | size (Imp sk) = size sk
  | size (Con1 sk) = size sk
  | size (Con2 sk) = size sk
  | size (Conj (sk1, sk2)) = size sk1 + size sk2

fun size_of (sk, _) = size sk

fun add_names (Nil name) = cons name   (* label names are unique! *)
  | add_names (Imp sk) = add_names sk
  | add_names (Con1 sk) = add_names sk
  | add_names (Con2 sk) = add_names sk
  | add_names (Conj (sk1, sk2)) = add_names sk1 #> add_names sk2

fun names_of (sk, _) = add_names sk []


fun make_app t u = t $ u
fun dest_app (t $ u) = (t, u)
  | dest_app t = raise TERM ("dest_app", [t])

val make_prop = HOLogic.mk_Trueprop
val dest_prop = HOLogic.dest_Trueprop

val make_imp = curry HOLogic.mk_imp
val dest_imp = HOLogic.dest_imp

val make_conj = curry HOLogic.mk_conj
fun dest_conj (@{term "op &"} $ t $ u) = (t, u)
  | dest_conj t = raise TERM ("dest_conj", [t])


fun app_both f g (x, y) = (f x, g y)

fun under_imp f r (sk, t) =
  let val (t1, t2) = dest_imp t
  in f (sk, t2) |> r (app_both Imp (make_imp t1)) end

fun split_conj f r1 r2 r (sk1, sk2, t) =
  let val (t1, t2) = dest_conj t
  in
    f (sk2, t2)
    |>> r1 (app_both (Conj o pair sk1) (make_conj t1))
    ||> r2 (apfst Con2)
    |> r
  end

val paths_of =
  let
    fun chop1 xs = (hd xs, tl xs)     

    fun split (sk, t) =
      (case sk of
        Nil _ => [(sk, t)]
      | Imp sk' => under_imp split map (sk', t)
      | Con1 sk1 => splt Con1 (sk1, t)
      | Con2 sk2 => splt Con2 (sk2, t)
      | Conj (sk1 as Nil _, sk2) =>
          split_conj (chop1 o split) I map (op ::) (sk1, sk2, t)
      | Conj (sk1, sk2) =>
          let val (t1, t2) = dest_conj t
          in splt Con1 (sk1, t1) @ splt Con2 (sk2, t2) end)
    and splt c st = split st |> map (apfst c)

  in map (apsnd make_prop) o split o apsnd dest_prop end

fun split_path i =
  let
    fun split_at i (sk, t) =
      (case sk of
        Imp sk' => under_imp (split_at i) pairself (sk', t)
      | Con1 sk1 => split_at i (sk1, t) |> pairself (apfst Con1)
      | Con2 sk2 => split_at i (sk2, t) |> pairself (apfst Con2)
      | Conj (sk1, sk2) =>
          if i > 1
          then split_conj (split_at (i-1)) I I I (sk1, sk2, t)
          else app_both (pair (Con1 sk1)) (pair (Con2 sk2)) (dest_conj t)
      | _ => raise TERM ("split_path: " ^ string_of_int i, [t]))
  in pairself (apsnd make_prop) o split_at i o apsnd dest_prop end

fun extract (sk, t) name =
  let
    fun is_in (Nil n) = (n = name, false)
      | is_in (Imp sk) = is_in sk
      | is_in (Con1 sk) = is_in sk
      | is_in (Con2 sk) = is_in sk
      | is_in (Conj (sk1, sk2)) =
          if fst (is_in sk1) then (true, true) else is_in sk2 ||> K true

    fun extr (sk, t) =
      (case sk of
        Nil _ => (sk, t)
      | Imp sk' => under_imp extr I (sk', t)
      | Con1 sk1 => extr (sk1, t) |> apfst Con1
      | Con2 sk2 => extr (sk2, t) |> apfst Con2
      | Conj (sk1, sk2) =>
          (case is_in sk1 of
            (true, true) => extr (sk1, fst (dest_conj t)) |> apfst Con1
          | (true, false) => (Con1 sk1, fst (dest_conj t))
          | (false, _) => extr (sk2, snd (dest_conj t)) |> apfst Con2))
  in
    (case is_in sk of
      (true, true) => SOME ((sk, dest_prop t) |> extr |> apsnd make_prop)
    | (true, false) => SOME (sk, t)
    | (false, _) => NONE)
  end


fun cut thy =
  let
    fun opt_map_both f g = Option.map (app_both f g)

    fun cut_err (u, t) = raise TERM ("cut: not matching", [u, t])

    val matches = Pattern.matches thy

    fun sub (usk, u) (sk, t) =
      (case (usk, sk) of
        (Nil _, Nil _) => if matches (u, t) then NONE else cut_err (u, t)
      | (Imp usk', Imp sk') => sub_imp (usk', u) (sk', t)

      | (Con1 usk1, Con1 sk1) =>
          sub (usk1, u) (sk1, t) |> Option.map (apfst Con1)
      | (Con2 usk2, Con2 sk2) =>
          sub (usk2, u) (sk2, t) |> Option.map (apfst Con2)

      | (Con1 _, Con2 _) => SOME (sk, t)
      | (Con2 _, Con1 _) => SOME (sk, t)

      | (Con1 usk1, Conj (sk1, sk2)) =>
          let val (t1, t2) = dest_conj t
          in
            sub (usk1, u) (sk1, t1)
            |> opt_map_both (Conj o rpair sk2) (fn t1' => make_conj t1' t2)
            |> SOME o the_default (Con2 sk2, t2)
          end
      | (Con2 usk2, Conj (sk1, sk2)) => 
          let val (t1, t2) = dest_conj t
          in
            sub (usk2, u) (sk2, t2)
            |> opt_map_both (Conj o pair sk1) (make_conj t1)
            |> SOME o the_default (Con1 sk1, t1)
          end
      | (Conj (usk1, _), Con1 sk1) =>
          let val (u1, _) = dest_conj u
          in sub (usk1, u1) (sk1, t) |> Option.map (apfst Con1) end
      | (Conj (_, usk2), Con2 sk2) =>
          let val (_, u2) = dest_conj u
          in sub (usk2, u2) (sk2, t) |> Option.map (apfst Con2) end

      | (Conj (usk1, usk2), Conj (sk1, sk2)) =>
          sub_conj (usk1, usk2, u) (sk1, sk2, t)

      | _ => cut_err (u, t))

    and sub_imp (usk', u) (sk', t) =
      let
        val (u1, u2) = dest_imp u
        val (t1, t2) = dest_imp t
      in
        if matches (u1, t1)
        then sub (usk', u2) (sk', t2) |> opt_map_both Imp (make_imp t1)
        else cut_err (u, t)
      end

    and sub_conj (usk1, usk2, u) (sk1, sk2, t) =
      let
        val (u1, u2) = dest_conj u
        val (t1, t2) = dest_conj t
      in
        (case (sub (usk1, u1) (sk1, t1), sub (usk2, u2) (sk2, t2)) of
          (NONE, NONE) => NONE
        | (NONE, SOME (sk2', t2')) => SOME (Con2 sk2', t2')
        | (SOME (sk1', t1'), NONE) => SOME (Con1 sk1', t1')
        | (SOME (sk1', t1'), SOME (sk2', t2')) =>
            SOME (Conj (sk1', sk2'), make_conj t1' t2'))
      end
  in
    (fn su => fn st =>
    (su, st)
    |> pairself (apsnd dest_prop)
    |> uncurry sub
    |> Option.map (apsnd make_prop))
  end


local
  fun imp f (lsk, lthm) (rsk, rthm) =
    let
      val mk_prop = Thm.capply @{cterm Trueprop}
      val ct = Thm.cprop_of lthm |> Thm.dest_arg |> Thm.dest_arg1 |> mk_prop
      val th = Thm.assume ct
      fun imp_elim thm = @{thm mp} OF [thm, th]
      fun imp_intr thm = Thm.implies_intr ct thm COMP_INCR @{thm impI}
      val (sk, thm) = f (lsk, imp_elim lthm) (rsk, imp_elim rthm)
    in (Imp sk, imp_intr thm) end

  fun conj1 thm = @{thm conjunct1} OF [thm]
  fun conj2 thm = @{thm conjunct2} OF [thm]
in
fun join (lsk, lthm) (rsk, rthm) =
  (case (lsk, rsk) of
    (Nil _, Nil _) => (lsk, lthm)
  | (Imp lsk', Imp rsk') => imp join (lsk', lthm) (rsk', rthm)

  | (Con1 lsk1, Con1 rsk1) => join (lsk1, lthm) (rsk1, rthm) |>> Con1
  | (Con2 lsk2, Con2 rsk2) => join (lsk2, lthm) (rsk2, rthm) |>> Con2

  | (Con1 lsk1, Con2 rsk2) => (Conj (lsk1, rsk2), @{thm conjI} OF [lthm, rthm])
  | (Con2 lsk2, Con1 rsk1) => (Conj (rsk1, lsk2), @{thm conjI} OF [rthm, lthm])

  | (Con1 lsk1, Conj (rsk1, rsk2)) =>
      let val (sk1, thm) = join (lsk1, lthm) (rsk1, conj1 rthm)
      in (Conj (sk1, rsk2), @{thm conjI} OF [thm, conj2 rthm]) end
  | (Con2 lsk2, Conj (rsk1, rsk2)) =>
      let val (sk2, thm) = join (lsk2, lthm) (rsk2, conj2 rthm)
      in (Conj (rsk1, sk2), @{thm conjI} OF [conj1 rthm, thm]) end
  | (Conj (lsk1, lsk2), Con1 rsk1) =>
      let val (sk1, thm) = join (lsk1, conj1 lthm) (rsk1, rthm)
      in (Conj (sk1, lsk2), @{thm conjI} OF [thm, conj2 lthm]) end
  | (Conj (lsk1, lsk2), Con2 rsk2) =>
      let val (sk2, thm) = join (lsk2, conj2 lthm) (rsk2, rthm)
      in (Conj (lsk1, sk2), @{thm conjI} OF [conj1 lthm, thm]) end

  | (Conj (lsk1, lsk2), Conj (rsk1, rsk2)) =>
      let
        val (sk1, th1) = join (lsk1, conj1 lthm) (rsk1, conj1 rthm)
        val (sk2, th2) = join (lsk2, conj2 lthm) (rsk2, conj2 rthm)
      in (Conj (sk1, sk2), @{thm conjI} OF [th1, th2]) end

  | _ => raise THM ("join: different structure", 0, [lthm, rthm]))
end


(* the VC store *)

fun err_vcs () = error "undischarged Boogie verification conditions found"

datatype vc =
  VC_NotProved of skel * term |
  VC_PartiallyProved of (skel * term) * (skel * thm) |
  VC_Proved of skel * thm

fun goal_of (VC_NotProved g) = SOME g
  | goal_of (VC_PartiallyProved (g, _)) = SOME g
  | goal_of (VC_Proved _) = NONE

fun proof_of (VC_NotProved _) = NONE
  | proof_of (VC_PartiallyProved (_, p)) = SOME p
  | proof_of (VC_Proved p) = SOME p

structure VCs = Theory_Data
(
  type T = vc Symtab.table option
  val empty = NONE
  val extend = I
  fun merge (NONE, NONE) = NONE
    | merge _ = err_vcs ()
)

fun prep thy t = VC_NotProved (` skel_of (simp_vc thy (HOLogic.mk_Trueprop t)))

fun set vcs thy = VCs.map (fn
    NONE => SOME (Symtab.make (map (apsnd (prep thy)) vcs))
  | SOME _ => err_vcs ()) thy

fun lookup thy name =
  (case VCs.get thy of
    SOME vcs =>
      (case Symtab.lookup vcs name of
        SOME vc => goal_of vc
      | NONE => NONE)
  | NONE => NONE)

fun discharge (name, prf) thy = thy |> VCs.map (Option.map
  (Symtab.map_entry name (fn
      VC_NotProved goal =>
        (case cut thy (apsnd Thm.prop_of prf) goal of
          SOME goal' => VC_PartiallyProved (goal', prf)
        | NONE => VC_Proved prf)
    | VC_PartiallyProved (goal, proof) =>
        (case cut thy (apsnd Thm.prop_of prf) goal of
          SOME goal' => VC_PartiallyProved (goal', join prf proof)
        | NONE => VC_Proved (join prf proof))
    | VC_Proved proof => VC_Proved proof)))

val close = VCs.map (fn
    SOME vcs =>
      if Symtab.exists (is_some o goal_of o snd) vcs
      then err_vcs ()
      else NONE
  | NONE => NONE)

val is_closed = is_none o VCs.get


datatype state = Proved | NotProved | PartiallyProved

fun state_of thy =
  (case VCs.get thy of
    SOME vcs => Symtab.dest vcs |> map (apsnd (fn
        VC_NotProved _ => NotProved
      | VC_PartiallyProved _ => PartiallyProved
      | VC_Proved _ => Proved))
  | NONE => [])

fun names_of' skx = these (Option.map names_of skx)

fun state_of_vc thy name =
  (case VCs.get thy of
    SOME vcs =>
      (case Symtab.lookup vcs name of
        SOME vc => (names_of' (proof_of vc), names_of' (goal_of vc))
      | NONE => ([], []))
  | NONE => ([], []))

end
