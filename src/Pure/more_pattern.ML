(*  Title:      Pure/more_pattern.ML
    Author:     Tobias Nipkow, TU Muenchen
    Author:     Stefan Berghofer, TU Muenchen

Add-ons to Higher-Order Patterns, outside the inference kernel.
*)

signature PATTERN =
sig
  include PATTERN
  val matches: theory -> term * term -> bool
  val matchess: theory -> term list * term list -> bool
  val equiv: theory -> term * term -> bool
  val first_order: term -> bool
  val match_rew: theory -> term -> term * term -> (term * term) option
  val rewrite_term: theory -> (term * term) list -> (term -> term option) list -> term -> term
  val rewrite_term_top: theory -> (term * term) list -> (term -> term option) list -> term -> term
  val rewrite_term_yoyo: theory -> (term * term) list -> (term -> term option) list -> term -> term
end;

structure Pattern: PATTERN =
struct

fun matches thy po =
  (Pattern.match thy po (Vartab.empty, Vartab.empty); true) handle Pattern.MATCH => false;

fun matchess thy (ps, os) =
  length ps = length os andalso
    ((fold (Pattern.match thy) (ps ~~ os) (Vartab.empty, Vartab.empty); true)
      handle Pattern.MATCH => false);

fun equiv thy (t, u) = matches thy (t, u) andalso matches thy (u, t);

fun first_order (Abs (_, _, t)) = first_order t
  | first_order (Var _ $ _) = false
  | first_order (t $ u) = first_order t andalso first_order u
  | first_order _ = true;


(* rewriting -- simple but fast *)

fun match_rew thy tm (tm1, tm2) =
  let val rtm = perhaps (Term.rename_abs tm1 tm) tm2 in
    SOME (Envir.subst_term (Pattern.match thy (tm1, tm) (Vartab.empty, Vartab.empty)) rtm, rtm)
      handle Pattern.MATCH => NONE
  end;

local

val skel0 = Bound 0;
val skel_fun = fn skel $ _ => skel | _ => skel0;
val skel_arg = fn _ $ skel => skel | _ => skel0;
val skel_body = fn Abs (_, _, skel) => skel | _ => skel0;

datatype mode = Bottom | Top | Yoyo;

fun rewrite_term_mode mode thy rules procs term =
  let
    fun variant_absfree bounds x tm =
      let
        val ((x', T), t') =
          Term.dest_abs_fresh (Name.bound bounds) tm
            handle Term.USED_FREE _ => Term.dest_abs_global tm;  (* FIXME proper context *)
        fun abs u = Abs (x, T, abstract_over (Free (x', T), u));
      in (abs, t') end;

    fun rew (Abs (_, _, body) $ t) = SOME (subst_bound (t, body), skel0)
      | rew tm =
          (case get_first (match_rew thy tm) rules of
            NONE => Option.map (rpair skel0) (get_first (fn proc => proc tm) procs)
          | some => some);

    fun rew_sub rw bounds _ (Abs (_, _, body) $ t) =
          let val t' = subst_bound (t, body)
          in SOME (the_default t' (rew_sub rw bounds skel0 t')) end
      | rew_sub rw bounds skel (t $ u) =
          (case (rw bounds (skel_fun skel) t, rw bounds (skel_arg skel) u) of
            (SOME t', SOME u') => SOME (t' $ u')
          | (SOME t', NONE) => SOME (t' $ u)
          | (NONE, SOME u') => SOME (t $ u')
          | (NONE, NONE) => NONE)
      | rew_sub rw bounds skel (t as Abs (x, _, _)) =
          let val (abs, t') = variant_absfree bounds x t
          in Option.map abs (rw (bounds + 1) (skel_body skel) t') end
      | rew_sub _ _ _ _ = NONE;


    (* bottom-up with skeleton *)

    fun rew_bottom _ (Var _) _ = NONE
      | rew_bottom bounds skel t =
          (case rew_sub rew_bottom bounds skel t of
            SOME t1 =>
              (case rew t1 of
                SOME (t2, skel') => SOME (the_default t2 (rew_bottom bounds skel' t2))
              | NONE => SOME t1)
          | NONE =>
              (case rew t of
                SOME (t1, skel') => SOME (the_default t1 (rew_bottom bounds skel' t1))
              | NONE => NONE));


    (* top-down *)

    fun rew_top bounds _ t =
      (case rew t of
        SOME (t1, _) =>
          (case rew_sub rew_top bounds skel0 t1 of
            SOME t2 => SOME (the_default t2 (rew_top bounds skel0 t2))
          | NONE => SOME t1)
      | NONE =>
          (case rew_sub rew_top bounds skel0 t of
            SOME t1 => SOME (the_default t1 (rew_top bounds skel0 t1))
          | NONE => NONE));


    (* yoyo: see also Ast.normalize *)

    fun rew_yoyo1 t =
      rew t |> Option.map (fn (t', _) => the_default t' (rew_yoyo1 t'));

    fun rew_yoyo2 bounds _ t =
      (case rew_yoyo1 t of
        SOME t1 =>
          (case rew_sub rew_yoyo2 bounds skel0 t1 of
            SOME t2 => SOME (the_default t2 (rew_yoyo1 t2))
          | NONE => SOME t1)
      | NONE =>
          (case rew_sub rew_yoyo2 bounds skel0 t of
            SOME t1 => SOME (the_default t1 (rew_yoyo1 t1))
          | NONE => NONE));

    fun rew_yoyo bounds skel t =
      rew_yoyo2 bounds skel t |> Option.map (fn t' => the_default t' (rew_yoyo bounds skel0 t'));


    val rewrite = (case mode of Bottom => rew_bottom | Top => rew_top | Yoyo => rew_yoyo);
  in the_default term (rewrite 0 skel0 term) end;

in

val rewrite_term = rewrite_term_mode Bottom;
val rewrite_term_top = rewrite_term_mode Top;
val rewrite_term_yoyo = rewrite_term_mode Yoyo;

end;

open Pattern;

end;
