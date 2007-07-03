(*  Title:      Pure/conjunction.ML
    ID:         $Id$
    Author:     Makarius

Meta-level conjunction.
*)

signature CONJUNCTION =
sig
  val conjunction: cterm
  val mk_conjunction: cterm * cterm -> cterm
  val mk_conjunction_balanced: cterm list -> cterm
  val dest_conjunction: cterm -> cterm * cterm
  val cong: thm -> thm -> thm
  val convs: (cterm -> thm) -> cterm -> thm
  val conjunctionD1: thm
  val conjunctionD2: thm
  val conjunctionI: thm
  val intr: thm -> thm -> thm
  val intr_balanced: thm list -> thm
  val elim: thm -> thm * thm
  val elim_balanced: int -> thm -> thm list
  val curry_balanced: int -> thm -> thm
  val uncurry_balanced: int -> thm -> thm
end;

structure Conjunction: CONJUNCTION =
struct

(** abstract syntax **)

fun read s = Thm.read_cterm ProtoPure.thy (s, propT);
val cert = Thm.cterm_of ProtoPure.thy;

val true_prop = cert Logic.true_prop;
val conjunction = cert Logic.conjunction;

fun mk_conjunction (A, B) = Thm.capply (Thm.capply conjunction A) B;

fun mk_conjunction_balanced [] = true_prop
  | mk_conjunction_balanced ts = BalancedTree.make mk_conjunction ts;

fun dest_conjunction ct =
  (case Thm.term_of ct of
    (Const ("ProtoPure.conjunction", _) $ _ $ _) => Thm.dest_binop ct
  | _ => raise TERM ("dest_conjunction", [Thm.term_of ct]));



(** derived rules **)

(* conversion *)

val cong = Thm.combination o Thm.combination (Thm.reflexive conjunction);

fun convs cv ct =
  (case try dest_conjunction ct of
    NONE => cv ct
  | SOME (A, B) => cong (convs cv A) (convs cv B));


(* intro/elim *)

local

val A = read "PROP A" and vA = read "PROP ?A";
val B = read "PROP B" and vB = read "PROP ?B";
val C = read "PROP C";
val ABC = read "PROP A ==> PROP B ==> PROP C";
val A_B = read "PROP ProtoPure.conjunction(A, B)"

val conjunction_def = Drule.unvarify ProtoPure.conjunction_def;

fun conjunctionD which =
  Drule.implies_intr_list [A, B] (Thm.assume (which (A, B))) COMP
  Drule.forall_elim_vars 0 (Thm.equal_elim conjunction_def (Thm.assume A_B));

in

val conjunctionD1 = Drule.store_standard_thm "conjunctionD1" (conjunctionD #1);
val conjunctionD2 = Drule.store_standard_thm "conjunctionD2" (conjunctionD #2);

val conjunctionI = Drule.store_standard_thm "conjunctionI"
  (Drule.implies_intr_list [A, B]
    (Thm.equal_elim
      (Thm.symmetric conjunction_def)
      (Thm.forall_intr C (Thm.implies_intr ABC
        (Drule.implies_elim_list (Thm.assume ABC) [Thm.assume A, Thm.assume B])))));


fun intr tha thb =
  Thm.implies_elim
    (Thm.implies_elim
      (Thm.instantiate ([], [(vA, Thm.cprop_of tha), (vB, Thm.cprop_of thb)]) conjunctionI)
    tha)
  thb;

fun elim th =
  let
    val (A, B) = dest_conjunction (Thm.cprop_of th)
      handle TERM (msg, _) => raise THM (msg, 0, [th]);
    val inst = Thm.instantiate ([], [(vA, A), (vB, B)]);
  in
   (Thm.implies_elim (inst conjunctionD1) th,
    Thm.implies_elim (inst conjunctionD2) th)
  end;

end;


(* balanced conjuncts *)

fun intr_balanced [] = asm_rl
  | intr_balanced ths = BalancedTree.make (uncurry intr) ths;

fun elim_balanced 0 _ = []
  | elim_balanced n th = BalancedTree.dest elim n th;


(* currying *)

local

fun conjs n =
  let val As = map (fn A => cert (Free (A, propT))) (Name.invents Name.context "A" n)
  in (As, mk_conjunction_balanced As) end;

val B = cert (Free ("B", propT));

fun comp_rule th rule =
  Thm.adjust_maxidx_thm ~1 (th COMP
    (rule |> Drule.forall_intr_frees |> Drule.forall_elim_vars (Thm.maxidx_of th + 1)));

in

(*
   A1 && ... && An ==> B
  -----------------------
  A1 ==> ... ==> An ==> B
*)
fun curry_balanced n th =
  if n < 2 then th
  else
    let
      val (As, C) = conjs n;
      val D = Drule.mk_implies (C, B);
    in
      comp_rule th
        (Thm.implies_elim (Thm.assume D) (intr_balanced (map Thm.assume As))
          |> Drule.implies_intr_list (D :: As))
    end;

(*
  A1 ==> ... ==> An ==> B
  -----------------------
  A1 && ... && An ==> B
*)
fun uncurry_balanced n th =
  if n < 2 then th
  else
    let
      val (As, C) = conjs n;
      val D = Drule.list_implies (As, B);
    in
      comp_rule th
        (Drule.implies_elim_list (Thm.assume D) (elim_balanced n (Thm.assume C))
          |> Drule.implies_intr_list [D, C])
    end;

end;

end;
