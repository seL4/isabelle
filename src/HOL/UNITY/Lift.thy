(*  Title:      HOL/UNITY/Lift.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Lift-Control Example
*)

Lift = SubstAx +

record state =
  floor :: int		(*current position of the lift*)
  open  :: bool		(*whether the door is open at floor*)
  stop  :: bool		(*whether the lift is stopped at floor*)
  req   :: int set	(*for each floor, whether the lift is requested*)
  up    :: bool		(*current direction of movement*)
  move  :: bool		(*whether moving takes precedence over opening*)

consts
  Min, Max :: int       (*least and greatest floors*)

rules
  Min_le_Max  "Min <= Max"
  
constdefs
  
  (** Abbreviations: the "always" part **)
  
  above :: state set
    "above == {s. EX i. floor s < i & i <= Max & i : req s}"

  below :: state set
    "below == {s. EX i. Min <= i & i < floor s & i : req s}"

  queueing :: state set
    "queueing == above Un below"

  goingup :: state set
    "goingup   == above Int  ({s. up s}  Un -below)"

  goingdown :: state set
    "goingdown == below Int ({s. ~ up s} Un -above)"

  ready :: state set
    "ready == {s. stop s & ~ open s & move s}"

 
  (** Further abbreviations **)

  moving :: state set
    "moving ==  {s. ~ stop s & ~ open s}"

  stopped :: state set
    "stopped == {s. stop s  & ~ open s & ~ move s}"

  opened :: state set
    "opened ==  {s. stop s  &  open s  &  move s}"

  closed :: state set  (*but this is the same as ready!!*)
    "closed ==  {s. stop s  & ~ open s &  move s}"

  atFloor :: int => state set
    "atFloor n ==  {s. floor s = n}"

  Req :: int => state set
    "Req n ==  {s. n : req s}"


  
  (** The program **)
  
  request_act :: "(state*state) set"
    "request_act == {(s,s'). s' = s (|stop:=True, move:=False|)
		                  & ~ stop s & floor s : req s}"

  open_act :: "(state*state) set"
    "open_act ==
         {(s,s'). s' = s (|open :=True,
			   req  := req s - {floor s},
			   move := True|)
		       & stop s & ~ open s & floor s : req s
	               & ~(move s & s: queueing)}"

  close_act :: "(state*state) set"
    "close_act == {(s,s'). s' = s (|open := False|) & open s}"

  req_up :: "(state*state) set"
    "req_up ==
         {(s,s'). s' = s (|stop  :=False,
			   floor := floor s + #1,
			   up    := True|)
		       & s : (ready Int goingup)}"

  req_down :: "(state*state) set"
    "req_down ==
         {(s,s'). s' = s (|stop  :=False,
			   floor := floor s - #1,
			   up    := False|)
		       & s : (ready Int goingdown)}"

  move_up :: "(state*state) set"
    "move_up ==
         {(s,s'). s' = s (|floor := floor s + #1|)
		       & ~ stop s & up s & floor s ~: req s}"

  move_down :: "(state*state) set"
    "move_down ==
         {(s,s'). s' = s (|floor := floor s - #1|)
		       & ~ stop s & ~ up s & floor s ~: req s}"

  button_press  :: "(state*state) set"
    "button_press ==
         {(s,s'). EX n. s' = s (|req := insert n (req s)|)
		        & Min <= n & n <= Max}"


  Lprg :: state program
    (*for the moment, we OMIT button_press*)
    "Lprg == mk_program ({s. floor s = Min & ~ up s & move s & stop s &
		          ~ open s & req s = {}},
			 {request_act, open_act, close_act,
			  req_up, req_down, move_up, move_down})"


  (** Invariants **)

  bounded :: state set
    "bounded == {s. Min <= floor s & floor s <= Max}"

  open_stop :: state set
    "open_stop == {s. open s --> stop s}"
  
  open_move :: state set
    "open_move == {s. open s --> move s}"
  
  stop_floor :: state set
    "stop_floor == {s. stop s & ~ move s --> floor s : req s}"
  
  moving_up :: state set
    "moving_up == {s. ~ stop s & up s -->
                   (EX f. floor s <= f & f <= Max & f : req s)}"
  
  moving_down :: state set
    "moving_down == {s. ~ stop s & ~ up s -->
                     (EX f. Min <= f & f <= floor s & f : req s)}"
  
  metric :: [int,state] => int
    "metric ==
       %n s. if floor s < n then (if up s then n - floor s
			          else (floor s - Min) + (n-Min))
             else
             if n < floor s then (if up s then (Max - floor s) + (Max-n)
		                  else floor s - n)
             else #0"

locale floor =
  fixes 
    n	:: int
  assumes
    Min_le_n    "Min <= n"
    n_le_Max    "n <= Max"
  defines

end
