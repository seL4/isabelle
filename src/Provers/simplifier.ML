(*  Title:      Provers/simplifier
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  TU Munich

Generic simplifier, suitable for most logics.
 
*)
infix addsimps addeqcongs
      setsolver setloop setmksimps setsubgoaler;

signature SIMPLIFIER =
sig
  type simpset
  val addeqcongs: simpset * thm list -> simpset
  val addsimps: simpset * thm list -> simpset
  val asm_full_simp_tac: simpset -> int -> tactic
  val asm_simp_tac: simpset -> int -> tactic
  val empty_ss: simpset
  val merge_ss: simpset * simpset -> simpset
  val prems_of_ss: simpset -> thm list
  val rep_ss: simpset -> {simps: thm list, congs: thm list}
  val setsolver: simpset * (thm list -> int -> tactic) -> simpset
  val setloop: simpset * (int -> tactic) -> simpset
  val setmksimps: simpset * (thm -> thm list) -> simpset
  val setsubgoaler: simpset * (simpset -> int -> tactic) -> simpset
  val simp_tac: simpset -> int -> tactic
end;

structure Simplifier:SIMPLIFIER =
struct

datatype simpset =
  SS of {mss: meta_simpset,
         simps: thm list,
         congs: thm list,
         subgoal_tac: simpset -> int -> tactic,
         finish_tac: thm list -> int -> tactic,
         loop_tac: int -> tactic};

val empty_ss =
  SS{mss=empty_mss,
     simps= [],
     congs= [],
     subgoal_tac= K(K no_tac),
     finish_tac= K(K no_tac),
     loop_tac= K no_tac};


fun (SS{mss,simps,congs,subgoal_tac,finish_tac,...}) setloop loop_tac =
  SS{mss=mss,
     simps= simps,
     congs= congs,
     subgoal_tac= subgoal_tac,
     finish_tac=finish_tac,
     loop_tac=loop_tac};

fun (SS{mss,simps,congs,subgoal_tac,loop_tac,...}) setsolver finish_tac =
  SS{mss=mss,
     simps= simps,
     congs= congs,
     subgoal_tac= subgoal_tac,
     finish_tac=finish_tac,
     loop_tac=loop_tac};

fun (SS{mss,simps,congs,finish_tac,loop_tac,...}) setsubgoaler subgoal_tac =
  SS{mss=mss,
     simps= simps,
     congs= congs,
     subgoal_tac= subgoal_tac,
     finish_tac=finish_tac,
     loop_tac=loop_tac};

fun (SS{mss,simps,congs,subgoal_tac,finish_tac,loop_tac}) setmksimps mk_simps =
  SS{mss=Thm.set_mk_rews(mss,mk_simps),
     simps= simps,
     congs= congs,
     subgoal_tac= subgoal_tac,
     finish_tac=finish_tac,
     loop_tac=loop_tac};

fun (SS{mss,simps,congs,subgoal_tac,finish_tac,loop_tac}) addsimps rews =
  let val rews' = flat(map (Thm.mk_rews_of_mss mss) rews)
  in
  SS{mss= Thm.add_simps(mss,rews'),
     simps= rews' @ simps,
     congs= congs,
     subgoal_tac= subgoal_tac,
     finish_tac=finish_tac,
     loop_tac=loop_tac}
  end;

fun (SS{mss,simps,congs,subgoal_tac,finish_tac,loop_tac}) addeqcongs newcongs =
  SS{mss= Thm.add_congs(mss,newcongs),
     simps= simps,
     congs= newcongs @ congs,
     subgoal_tac= subgoal_tac,
     finish_tac=finish_tac,
     loop_tac=loop_tac};

fun merge_ss(SS{mss,simps,congs,subgoal_tac,finish_tac,loop_tac},
             SS{simps=simps2,congs=congs2,...}) =
  let val simps' = gen_union eq_thm (simps,simps2)
      val congs' = gen_union eq_thm (congs,congs2)
      val mss' = Thm.set_mk_rews(empty_mss,Thm.mk_rews_of_mss mss)
      val mss' = Thm.add_simps(mss',simps')
      val mss' = Thm.add_congs(mss',congs')
  in SS{mss=         mss',
        simps=       simps,
        congs=       congs',
        subgoal_tac= subgoal_tac,
        finish_tac=  finish_tac,
        loop_tac=    loop_tac}
  end;

fun prems_of_ss(SS{mss,...}) = prems_of_mss mss;

fun rep_ss(SS{simps,congs,...}) = {simps=simps,congs=congs};

fun add_asms (SS{mss,simps,congs,subgoal_tac,finish_tac,loop_tac}) prems =
  let val rews = flat(map (mk_rews_of_mss mss) prems)
  in SS{mss= add_prems(add_simps(mss,rews),prems), simps=simps, congs=congs,
        subgoal_tac=subgoal_tac,finish_tac=finish_tac,
        loop_tac=loop_tac}
  end;

fun NEWSUBGOALS tac tacf =
  STATE(fn state0 =>
    tac THEN STATE(fn state1 => tacf(nprems_of state1 - nprems_of state0)));

fun asm_full_simp_tac(SS{mss,simps,congs,subgoal_tac,finish_tac,loop_tac}) =
  let fun solve_all_tac mss =
        let val ss = SS{mss=mss,simps=simps,congs=congs,
                        subgoal_tac=subgoal_tac,
                        finish_tac=finish_tac, loop_tac=loop_tac}
            val solve1_tac =
              NEWSUBGOALS (subgoal_tac ss 1)
                          (fn n => if n<0 then all_tac else no_tac)
        in DEPTH_SOLVE(solve1_tac) end

      fun simp_loop i thm =
        tapply(asm_rewrite_goal_tac solve_all_tac mss i THEN
               (finish_tac (prems_of_mss mss) i  ORELSE  looper i),
               thm)
      and allsimp i n = EVERY(map (fn j => simp_loop_tac (i+j)) (n downto 0))
      and looper i = TRY(NEWSUBGOALS (loop_tac i) (allsimp i))
      and simp_loop_tac i = Tactic(simp_loop i)

  in fn i => COND (has_fewer_prems 0) no_tac (simp_loop_tac i) end;

fun asm_simp_tac ss =
      METAHYPS(fn prems => asm_full_simp_tac (add_asms ss prems) 1);

fun simp_tac ss = METAHYPS(fn _ => asm_full_simp_tac ss 1);

end;
