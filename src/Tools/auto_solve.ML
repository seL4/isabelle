(*  Title:      Pure/Tools/auto_solve.ML
    Author:     Timothy Bourke and Gerwin Klein, NICTA

Check whether a newly stated theorem can be solved directly by an
existing theorem. Duplicate lemmas can be detected in this way.

The implemenation is based in part on Berghofer and Haftmann's
Pure/codegen.ML. It relies critically on the FindTheorems solves
feature.
*)

signature AUTO_SOLVE =
sig
  val auto : bool ref
  val auto_time_limit : int ref
  val limit : int ref

  val seek_solution : bool -> Proof.state -> Proof.state
end;

structure AutoSolve : AUTO_SOLVE =
struct

val auto = ref false;
val auto_time_limit = ref 2500;
val limit = ref 5;

fun seek_solution int state =
  let
    val ctxt = Proof.context_of state;

    fun conj_to_list [] = []
      | conj_to_list (t::ts) =
        (Conjunction.dest_conjunction t
         |> (fn (t1, t2) => conj_to_list (t1::t2::ts)))
        handle TERM _ => t::conj_to_list ts;

    val crits = [(true, FindTheorems.Solves)];
    fun find g = (NONE, snd (FindTheorems.find_theorems ctxt g (SOME (!limit)) false crits));
    fun find_cterm g = (SOME g, snd (FindTheorems.find_theorems ctxt
                                      (SOME (Goal.init g)) (SOME (!limit)) false crits));

    fun prt_result (goal, results) =
      let
        val msg = case goal of
                    NONE => "The current goal"
                  | SOME g => Syntax.string_of_term ctxt (term_of g);
      in
        Pretty.big_list (msg ^ " could be solved directly with:")
                        (map (FindTheorems.pretty_thm ctxt) results)
      end;

    fun seek_against_goal () =
      let
        val goal = try Proof.get_goal state
                   |> Option.map (#2 o #2);

        val goals = goal
                    |> Option.map (fn g => cprem_of g 1)
                    |> the_list
                    |> conj_to_list;

        val rs = if length goals = 1
                 then [find goal]
                 else map find_cterm goals;
        val frs = filter_out (null o snd) rs;

      in if null frs then NONE else SOME frs end;

    fun go () =
      let
        val res = TimeLimit.timeLimit
                    (Time.fromMilliseconds (! auto_time_limit))
                    (try seek_against_goal) ();
      in
        case Option.join res of
          NONE => state
        | SOME results => (Proof.goal_message
                            (fn () => Pretty.chunks [Pretty.str "",
                              Pretty.markup Markup.hilite
                              (Library.separate (Pretty.brk 0)
                                                (map prt_result results))])
                              state)
      end handle TimeLimit.TimeOut => (warning "AutoSolve: timeout."; state);
  in
    if int andalso ! auto andalso not (! Toplevel.quiet)
    then go ()
    else state
  end;

end;

val _ = Context.>> (Specification.add_theorem_hook AutoSolve.seek_solution);

val auto_solve = AutoSolve.auto;
val auto_solve_time_limit = AutoSolve.auto_time_limit;

