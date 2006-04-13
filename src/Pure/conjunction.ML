(*  Title:      Pure/conjunction.ML
    ID:         $Id$
    Author:     Makarius

Meta-level conjunction.
*)

signature CONJUNCTION =
sig
  val conjunction: cterm
  val mk_conjunction: cterm * cterm -> cterm
  val dest_conjunction: cterm -> cterm * cterm
  val cong: thm -> thm -> thm
  val conv: int -> (int -> cterm -> thm) -> cterm -> thm
  val conjunctionD1: thm
  val conjunctionD2: thm
  val conjunctionI: thm
  val intr: thm -> thm -> thm
  val intr_list: thm list -> thm
  val elim: thm -> thm * thm
  val elim_list: thm -> thm list
  val elim_precise: int list -> thm -> thm list list
  val curry: int -> thm -> thm
  val uncurry: int -> thm -> thm
  val split_defined: int -> thm -> thm * thm list
end;

structure Conjunction: CONJUNCTION =
struct


(** abstract syntax **)

fun read s = Thm.read_cterm ProtoPure.thy (s, propT);
val cert = Thm.cterm_of ProtoPure.thy;

val conjunction = cert Logic.conjunction;
fun mk_conjunction (A, B) = Thm.capply (Thm.capply conjunction A) B;

fun dest_conjunction ct =
  (case Thm.term_of ct of
    (Const ("ProtoPure.conjunction", _) $ _ $ _) => Drule.dest_binop ct
  | _ => raise TERM ("dest_conjunction", [term_of ct]));



(** derived rules **)

(* conversion *)

(*rewrite the A's in A1 && ... && An*)

val cong = Thm.combination o Thm.combination (Thm.reflexive conjunction);

fun conv 0 _ = reflexive
  | conv n cv =
      let
        fun cnv i ct =
          if i = n then cv i ct
          else
            (case try dest_conjunction ct of
              NONE => cv i ct
            | SOME (A, B) => cong (cv i A) (cnv (i + 1) B));
      in cnv 1 end;


(* intro/elim *)

local

val A = read "PROP A";
val B = read "PROP B";
val C = read "PROP C";
val ABC = read "PROP A ==> PROP B ==> PROP C";
val A_B = read "PROP ProtoPure.conjunction(A, B)"

val conjunction_def = #1 (freeze_thaw ProtoPure.conjunction_def);

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

fun intr tha thb = thb COMP (tha COMP Drule.incr_indexes2 tha thb conjunctionI);

fun intr_list [] = asm_rl
  | intr_list ths = foldr1 (uncurry intr) ths;

fun elim th =
 (th COMP Drule.incr_indexes th conjunctionD1,
  th COMP Drule.incr_indexes th conjunctionD2);

(*((A && B) && C) && D && E -- flat*)
fun elim_list th =
  let val (th1, th2) = elim th
  in elim_list th1 @ elim_list th2 end handle THM _ => [th];

(*(A1 && B1 && C1) && (A2 && B2 && C2 && D2) && A3 && B3 -- improper*)
fun elim_precise spans =
  let
    fun elm 0 _ = []
      | elm 1 th = [th]
      | elm n th =
          let val (th1, th2) = elim th
          in th1 :: elm (n - 1) th2 end;
    fun elms (0 :: ns) ths = [] :: elms ns ths
      | elms (n :: ns) (th :: ths) = elm n th :: elms ns ths
      | elms _ _ = [];
  in elms spans o elm (length (filter_out (equal 0) spans)) end;

end;


(* currying *)

local

fun conjs m =
  let val As = map (fn i => Free ("A" ^ string_of_int i, propT)) (1 upto m)
  in (As, Logic.mk_conjunction_list As) end;

val B = Free ("B", propT);

fun comp_rule th rule =
  Thm.adjust_maxidx_thm (th COMP
    (rule |> Drule.forall_intr_frees |> Drule.forall_elim_vars (Thm.maxidx_of th + 1)));

in

(*
   A1 && ... && An ==> B
  -----------------------
  A1 ==> ... ==> An ==> B
*)
fun curry n th =
  let
    val k =
      (case try Logic.dest_implies (Thm.prop_of th) of
        NONE => 0
      | SOME (prem, _) => length (Logic.dest_conjunction_list prem));
    val m = if n = ~1 then k else Int.min (n, k);
  in
    if m < 2 then th
    else
      let
        val (As, C) = conjs m;
        val cAs = map cert As;
        val D = Logic.mk_implies (Logic.mk_conjunction_list As, B) |> cert;
      in
        comp_rule th
          (Thm.implies_elim (Thm.assume D) (intr_list (map Thm.assume cAs))
            |> Drule.implies_intr_list (D :: cAs))
      end
  end;

(*
  A1 ==> ... ==> An ==> B
  -----------------------
   A1 && ... && An ==> B
*)
fun uncurry n th =
  let
    val k = Thm.nprems_of th;
    val m = if n = ~1 then k else Int.min (n, k);
  in
    if m < 2 then th
    else
      let
        val (As, C) = conjs m ||> cert;
        val D = Logic.list_implies (As, B) |> cert;
      in
        comp_rule th
          (Drule.implies_elim_list (Thm.assume D) (elim_list (Thm.assume C))
            |> Drule.implies_intr_list [D, C])
      end
  end;

end;


(* defined conjunctions *)

fun project th 1 = (th RS conjunctionD1 handle THM _ => th)
  | project th k = project (th RS conjunctionD2) (k - 1);

fun split_defined n eq =
  let
    val intro =
      (eq RS Drule.equal_elim_rule2)
      |> curry n
      |> K (n = 0) ? Thm.eq_assumption 1;
    val dests = map (project (eq RS Drule.equal_elim_rule1)) (1 upto n);
  in (intro, dests) end;

end;
