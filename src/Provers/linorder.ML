(*
  Title:	Transitivity reasoner for linear orders
  Id:		$Id$
  Author:	Clemens Ballarin, started 8 November 2002
  Copyright:	TU Muenchen
*)

(***
This is a very simple package for transitivity reasoning over linear orders.
Simple means exponential time (and space) in the number of premises.
Should be replaced by a graph-theoretic algorithm.

The package provides a tactic trans_tac that uses all premises of the form

  t = u, t < u, t <= u, ~(t < u) and ~(t <= u)

to
1. either derive a contradiction,
   in which case the conclusion can be any term,
2. or prove the conclusion, which must be of the same form as the premises.

To get rid of ~= in the premises, it is advisable to use an elimination
rule of the form

  [| t ~= u; t < u ==> P; u < t ==> P |] ==> P.

The package is implemented as an ML functor and thus not limited to the
relation <= and friends.  It can be instantiated to any total order ---
for example, the divisibility relation "dvd".
***)

(*** Credits ***

This package is closely based on a (no longer used) transitivity reasoner for
the natural numbers, which was written by Tobias Nipkow.

****************)

signature LESS_ARITH =
sig
  val less_reflE: thm  (* x < x ==> P *)
  val le_refl: thm  (* x <= x *)
  val less_imp_le: thm (* x <= y ==> x < y *)
  val not_lessI: thm (* y <= x  ==> ~(x < y) *)
  val not_leI: thm (* y < x  ==> ~(x <= y) *)
  val not_lessD: thm (* ~(x < y) ==> y <= x *)
  val not_leD: thm (* ~(x <= y) ==> y < x *)
  val eqI: thm (* [| x <= y; y <= x |] ==> x = y *)
  val eqD1: thm (* x = y ==> x <= y *)
  val eqD2: thm (* x = y ==> y <= x *)
  val less_trans: thm  (* [| x <= y; y <= z |] ==> x <= z *)
  val less_le_trans: thm  (* [| x <= y; y < z |] ==> x < z *)
  val le_less_trans: thm  (* [| x < y; y <= z |] ==> x < z *)
  val le_trans: thm  (* [| x < y; y < z |] ==> x < z *)
  val decomp: term -> (term * string * term) option
    (* decomp (`x Rel y') should yield (x, Rel, y)
       where Rel is one of "<", "<=", "~<", "~<=", "=" and "~="
       other relation symbols are ignored *)
end;

signature TRANS_TAC =
sig
  val trans_tac: int -> tactic
end;

functor Trans_Tac_Fun (Less: LESS_ARITH): TRANS_TAC =
struct

(*** Proof objects ***)

datatype proof
  = Asm of int
  | Thm of proof list * thm;

(* Turn proof objects into theorems *)

fun prove asms =
  let fun pr (Asm i) = nth_elem (i, asms)
        | pr (Thm (prfs, thm)) = (map pr prfs) MRS thm
  in pr end;

(*** Exceptions ***)

exception Contr of proof;  (* Raised when contradiction is found *)

exception Cannot;  (* Raised when goal cannot be proved *)

(*** Internal representation of inequalities ***)

datatype less
  = Less of term * term * proof
  | Le of term * term * proof;

fun lower (Less (x, _, _)) = x
  | lower (Le (x, _, _)) = x;

fun upper (Less (_, y, _)) = y
  | upper (Le (_, y, _)) = y;

infix subsumes;

fun (Less (x, y, _)) subsumes (Le (x', y', _)) = (x = x' andalso y = y')
  | (Less (x, y, _)) subsumes (Less (x', y', _)) = (x = x' andalso y = y')
  | (Le (x, y, _)) subsumes (Le (x', y', _)) = (x = x' andalso y = y')
  | _ subsumes _ = false;

fun trivial (Le (x, x', _)) = (x = x')
  | trivial _ = false;

(*** Transitive closure ***)

fun add new =
  let fun adds([], news) = new::news
        | adds(old::olds, news) = if new subsumes old then adds(olds, news)
                                  else adds(olds, old::news)
  in adds end;

fun ctest (less as Less (x, x', p)) = 
    if x = x' then raise Contr (Thm ([p], Less.less_reflE))
    else less
  | ctest less = less;

fun mktrans (Less (x, _, p), Less (_, z, q)) =
    Less (x, z, Thm([p, q], Less.less_trans))
  | mktrans (Less (x, _, p), Le (_, z, q)) =
    Less (x, z, Thm([p, q], Less.less_le_trans))
  | mktrans (Le (x, _, p), Less (_, z, q)) =
    Less (x, z, Thm([p, q], Less.le_less_trans))
  | mktrans (Le (x, _, p), Le (_, z, q)) =
    Le (x, z, Thm([p, q], Less.le_trans));

fun trans new olds =
  let fun tr (news, old) =
            if upper old = lower new then mktrans (old, new)::news
            else if upper new = lower old then mktrans (new, old)::news
            else news
  in foldl tr ([], olds) end;

fun close1 olds new =
    if trivial new orelse exists (fn old => old subsumes new) olds then olds
    else let val news = trans new olds
         in close (add new (olds, [])) news end
and close olds [] = olds
  | close olds (new::news) = close (close1 olds (ctest new)) news;

(*** Solving and proving goals ***)

(* Recognise and solve trivial goal *)

fun triv_sol (Le (x, x',  _)) = 
    if x = x' then Some (Thm ([], Less.le_refl)) 
    else None
  | triv_sol _ = None;

(* Solve less starting from facts *)

fun solve facts less =
  case triv_sol less of
    None => (case (Library.find_first (fn fact => fact subsumes less) facts, less) of
	(None, _) => raise Cannot
      | (Some (Less (_, _, p)), Less _) => p
      | (Some (Le (_, _, p)), Less _) =>
	   error "trans_tac/solve: internal error: le cannot subsume less"
      | (Some (Less (_, _, p)), Le _) => Thm ([p], Less.less_imp_le)
      | (Some (Le (_, _, p)), Le _) => p)
  | Some prf => prf;

(* Turn term t into Less or Le; n is position of t in list of assumptions *)

fun mkasm (t, n) =
  case Less.decomp t of
    Some (x, rel, y) => (case rel of
      "<"   => [Less (x, y, Asm n)]
    | "~<"  => [Le (y, x, Thm ([Asm n], Less.not_lessD))]
    | "<="  => [Le (x, y, Asm n)]
    | "~<=" => [Less (y, x, Thm ([Asm n], Less.not_leD))]
    | "="   => [Le (x, y, Thm ([Asm n], Less.eqD1)),
                Le (x, y, Thm ([Asm n], Less.eqD1))]
    | "~="  => []
    | _     => error ("trans_tac/mkasm: unknown relation " ^ rel))
  | None => [];

(* Turn goal t into a pair (goals, proof) where goals is a list of
   Le/Less-subgoals to solve, and proof the validation that proves the concl t
   Asm ~1 is dummy (denotes a goal)
*)

fun mkconcl t =
  case Less.decomp t of
    Some (x, rel, y) => (case rel of
      "<"   => ([Less (x, y, Asm ~1)], Asm 0)
    | "~<"  => ([Le (y, x, Asm ~1)], Thm ([Asm 0], Less.not_lessI))
    | "<="  => ([Le (x, y, Asm ~1)], Asm 0)
    | "~<=" => ([Less (y, x, Asm ~1)], Thm ([Asm 0], Less.not_leI))
    | "="   => ([Le (x, y, Asm ~1), Le (y, x, Asm ~1)],
                 Thm ([Asm 0, Asm 1], Less.eqI))
    | _  => raise Cannot)
  | None => raise Cannot;

val trans_tac = SUBGOAL (fn (A, n) =>
  let val Hs = Logic.strip_assums_hyp A
    val C = Logic.strip_assums_concl A
    val lesss = flat (ListPair.map mkasm (Hs, 0 upto (length Hs - 1)))
    val clesss = close [] lesss
    val (subgoals, prf) = mkconcl C
    val prfs = map (solve clesss) subgoals
  in METAHYPS (fn asms =>
    let val thms = map (prove asms) prfs
    in rtac (prove thms prf) 1 end) n
  end
  handle Contr p => METAHYPS (fn asms => rtac (prove asms p) 1) n
       | Cannot => no_tac);

end;
