(* FIXME dead code!?!? *)

theory Mutabelle
imports Main
begin

ML_file "mutabelle.ML"

ML {*
val comms = [@{const_name HOL.eq}, @{const_name HOL.disj}, @{const_name HOL.conj}];

val forbidden =
 [(@{const_name Power.power}, "'a"),
  (@{const_name HOL.induct_equal}, "'a"),
  (@{const_name HOL.induct_implies}, "'a"),
  (@{const_name HOL.induct_conj}, "'a"),
  (@{const_name HOL.undefined}, "'a"),
  (@{const_name HOL.default}, "'a"),
  (@{const_name dummy_pattern}, "'a::{}"),
  (@{const_name Groups.uminus}, "'a"),
  (@{const_name Nat.size}, "'a"),
  (@{const_name Groups.abs}, "'a")];

val forbidden_thms =
 ["finite_intvl_succ_class",
  "nibble"];

val forbidden_consts =
 [@{const_name nibble_pair_of_char}];

fun is_forbidden s th =
 exists (fn s' => s' mem Long_Name.explode s) forbidden_thms orelse
 exists (fn s' => s' mem (Term.add_const_names (prop_of th) [])) forbidden_consts;

fun test j = List.app (fn i =>
 Mutabelle.mutqc_thystat_mix is_forbidden
   @{theory List} @{theory Main} comms forbidden 1 [] i j ("list_" ^ string_of_int i ^ ".txt"))
 (1 upto 10);

fun get_numbers xs =
 let
   val (_, xs1) = take_prefix (not o equal ":") xs;
   val (_, xs2) = take_prefix (fn ":" => true | " " => true | _ => false) xs1;
   val (xs3, xs4) = take_prefix Symbol.is_digit xs2;
   val (_, xs5) = take_prefix (equal " ") xs4;
   val (xs6, xs7) = take_prefix Symbol.is_digit xs5
 in
   case (xs3, xs6) of
     ([], _) => NONE
   | (_, []) => NONE
   | (ys, zs) => SOME (fst (read_int ys), fst (read_int zs), xs7)
 end;

fun add_numbers s =
 let
   fun strip ("\n" :: "\n" :: "\n" :: xs) = xs
     | strip (_ :: xs) = strip xs;

   fun add (i, j) xs = (case get_numbers xs of
         NONE => (i, j)
       | SOME (i', j', xs') => add (i+i', j+j') xs')
 in add (0,0) (strip (explode s)) end;
*}

(*
ML {*
Quickcheck.test_term (Proof_Context.init_global @{theory})
 false (SOME "SML") 1 1 (prop_of (hd @{thms nibble_pair_of_char_simps}))
*}

ML {*
fun is_executable thy th = can (Quickcheck.test_term
 (Proof_Context.init_global thy) false (SOME "SML") 1 1) (prop_of th);

fun is_executable_term thy t = can (Quickcheck.test_term
 (Proof_Context.init_global thy) false (SOME "SML") 1 1) t;

fun thms_of thy = filter (fn (_, th) => not (Thm.is_internal th) andalso
   Context.theory_name (theory_of_thm th) = Context.theory_name thy andalso
   is_executable thy th)
 (Global_Theory.all_thms_of thy);

fun find_thm thy = find_first (fn (_, th) => not (Thm.is_internal th) andalso
   Context.theory_name (theory_of_thm th) = Context.theory_name thy andalso
   is_executable thy th)
 (Global_Theory.all_thms_of thy);
*}

ML {*
is_executable @{theory} (hd @{thms nibble_pair_of_char_simps})
*}
*)

ML {*
Mutabelle.mutate_mix @{term "Suc x \<noteq> 0"} @{theory} comms forbidden 1
*}

ML {*
Mutabelle.mutqc_thystat_mix is_forbidden @{theory Nat} @{theory} comms forbidden 1 [] 10 5 "/tmp/muta.out"
*}

end