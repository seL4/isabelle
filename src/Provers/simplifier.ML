(*  Title:      Provers/simplifier.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  TU Munich

Generic simplifier, suitable for most logics.
 
*)

infix 4 addsimps addeqcongs addsolver delsimps
        setsolver setloop setmksimps setsubgoaler;

signature SIMPLIFIER =
sig
  type simpset
  val addeqcongs: simpset * thm list -> simpset
  val addsimps: simpset * thm list -> simpset
  val addsolver: simpset * (thm list -> int -> tactic) -> simpset
  val delsimps: simpset * thm list -> simpset
  val asm_full_simp_tac: simpset -> int -> tactic
  val     full_simp_tac: simpset -> int -> tactic
  val      asm_simp_tac: simpset -> int -> tactic
  val empty_ss: simpset
  val merge_ss: simpset * simpset -> simpset
  val prems_of_ss: simpset -> thm list
  val rep_ss: simpset -> {simps: thm list, congs: thm list}
  val setsolver: simpset * (thm list -> int -> tactic) -> simpset
  val setloop: simpset * (int -> tactic) -> simpset
  val setmksimps: simpset * (thm -> thm list) -> simpset
  val setsubgoaler: simpset * (simpset -> int -> tactic) -> simpset
  val simp_tac: simpset -> int -> tactic

  val simpset: simpset ref
  val Addsimps: thm list -> unit
  val Delsimps: thm list -> unit
  val Simp_tac: int -> tactic
  val      Asm_simp_tac: int -> tactic
  val     Full_simp_tac: int -> tactic
  val Asm_full_simp_tac: int -> tactic
end;

structure Simplifier :SIMPLIFIER =
struct

datatype simpset =
  Simpset of {mss: meta_simpset,
              simps: thm list,
              congs: thm list,
              subgoal_tac: simpset -> int -> tactic,
              finish_tac: thm list -> int -> tactic,
              loop_tac: int -> tactic};

val empty_ss =
  Simpset{mss=empty_mss,
          simps= [],
          congs= [],
          subgoal_tac= K(K no_tac),
          finish_tac= K(K no_tac),
          loop_tac= K no_tac};

val simpset = ref empty_ss;

fun (Simpset{mss,simps,congs,subgoal_tac,finish_tac,...}) setloop loop_tac =
  Simpset{mss=mss,
          simps= simps,
          congs= congs,
          subgoal_tac= subgoal_tac,
          finish_tac=finish_tac,
          loop_tac= DETERM o loop_tac};

fun (Simpset{mss,simps,congs,subgoal_tac,loop_tac,...}) setsolver finish_tac =
  Simpset{mss=mss,
          simps= simps,
          congs= congs,
          subgoal_tac= subgoal_tac,
          finish_tac=finish_tac,
          loop_tac=loop_tac};

fun (Simpset{mss,simps,congs,subgoal_tac,loop_tac,finish_tac}) addsolver tac =
  Simpset{mss=mss,
          simps= simps,
          congs= congs,
          subgoal_tac= subgoal_tac,
          finish_tac=fn hyps => finish_tac hyps ORELSE' tac hyps,
          loop_tac=loop_tac};

fun (Simpset{mss,simps,congs,finish_tac,loop_tac,...}) setsubgoaler
    subgoal_tac =
  Simpset{mss=mss,
          simps= simps,
          congs= congs,
          subgoal_tac= subgoal_tac,
          finish_tac=finish_tac,
          loop_tac=loop_tac};
     
fun (Simpset{mss,simps,congs,subgoal_tac,finish_tac,loop_tac}) setmksimps
    mk_simps =
  Simpset{mss=Thm.set_mk_rews(mss,mk_simps),
          simps= simps,
          congs= congs,
          subgoal_tac= subgoal_tac,
          finish_tac=finish_tac,
          loop_tac=loop_tac};

fun (Simpset{mss,simps,congs,subgoal_tac,finish_tac,loop_tac}) addsimps rews =
  let val rews' = flat(map (Thm.mk_rews_of_mss mss) rews) in
  Simpset{mss= Thm.add_simps(mss,rews'),
          simps= rews' @ simps,
          congs= congs,
          subgoal_tac= subgoal_tac,
          finish_tac=finish_tac,
          loop_tac=loop_tac}
  end;

fun Addsimps rews = (simpset := !simpset addsimps rews);

fun (Simpset{mss,simps,congs,subgoal_tac,finish_tac,loop_tac}) delsimps rews =
  let val rews' = flat(map (Thm.mk_rews_of_mss mss) rews) in
  Simpset{mss= Thm.del_simps(mss,rews'),
          simps= foldl (gen_rem eq_thm) (simps,rews'),
          congs= congs,
          subgoal_tac= subgoal_tac,
          finish_tac=finish_tac,
          loop_tac=loop_tac}
  end;

fun Delsimps rews = (simpset := !simpset delsimps rews);

fun (Simpset{mss,simps,congs,subgoal_tac,finish_tac,loop_tac}) addeqcongs
    newcongs =
  Simpset{mss= Thm.add_congs(mss,newcongs),
          simps= simps,
          congs= newcongs @ congs,
          subgoal_tac= subgoal_tac,
          finish_tac=finish_tac,
          loop_tac=loop_tac};
     
fun merge_ss(Simpset{mss,simps,congs,subgoal_tac,finish_tac,loop_tac},
             Simpset{simps=simps2,congs=congs2,...}) =
  let val simps' = gen_union eq_thm (simps,simps2)
      val congs' = gen_union eq_thm (congs,congs2)
      val mss' = Thm.set_mk_rews(empty_mss,Thm.mk_rews_of_mss mss)
      val mss' = Thm.add_simps(mss',simps')
      val mss' = Thm.add_congs(mss',congs')
  in Simpset{mss=         mss',
             simps=       simps',
             congs=       congs',
             subgoal_tac= subgoal_tac,
             finish_tac=  finish_tac,
             loop_tac=    loop_tac}
  end;

fun prems_of_ss(Simpset{mss,...}) = prems_of_mss mss;

fun rep_ss(Simpset{simps,congs,...}) = {simps=simps,congs=congs};

fun NEWSUBGOALS tac tacf =
  STATE(fn state0 =>
    tac THEN STATE(fn state1 => tacf(nprems_of state1 - nprems_of state0)));

fun gen_simp_tac mode =
  fn (Simpset{mss,simps,congs,subgoal_tac,finish_tac,loop_tac}) =>
  let fun solve_all_tac mss =
        let val ss = Simpset{mss=mss,simps=simps,congs=congs,
                             subgoal_tac=subgoal_tac,
                             finish_tac=finish_tac, loop_tac=loop_tac}
            val solve1_tac =
              NEWSUBGOALS (subgoal_tac ss 1)
                          (fn n => if n<0 then all_tac else no_tac)
        in DEPTH_SOLVE(solve1_tac) end

      fun simp_loop_tac i thm =
	  (asm_rewrite_goal_tac mode solve_all_tac mss i THEN
	   (finish_tac (prems_of_mss mss) i  ORELSE  looper i))  thm
      and allsimp i n = EVERY(map (fn j => simp_loop_tac (i+j)) (n downto 0))
      and looper i = TRY(NEWSUBGOALS (loop_tac i) (allsimp i))
  in simp_loop_tac end;

val asm_full_simp_tac = gen_simp_tac (true ,true );
val     full_simp_tac = gen_simp_tac (true ,false);
val      asm_simp_tac = gen_simp_tac (false,true );
val          simp_tac = gen_simp_tac (false,false);

fun Asm_full_simp_tac i = asm_full_simp_tac (!simpset) i;
fun     Full_simp_tac i =     full_simp_tac (!simpset) i;
fun      Asm_simp_tac i =      asm_simp_tac (!simpset) i;
fun          Simp_tac i =          simp_tac (!simpset) i;

end;
