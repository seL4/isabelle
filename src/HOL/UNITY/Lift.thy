(*  Title:      HOL/UNITY/Lift.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Lift-Control Example
*)

Lift = SubstAx +

record state =
  floor :: nat		(*current position of the lift*)
  open  :: bool		(*whether the door is open at floor*)
  stop  :: bool		(*whether the lift is stopped at floor*)
  req   :: nat set	(*for each floor, whether the lift is requested*)
  up    :: bool		(*current direction of movement*)
  move  :: bool		(*whether moving takes precedence over opening*)

consts
  min, max :: nat	(*least and greatest floors*)

rules
  min_le_max  "min <= max"
  

constdefs
  
  (** Abbreviations: the "always" part **)
  
  above :: state set
    "above == {s. EX i. floor s < i & i <= max & i : req s}"

  below :: state set
    "below == {s. EX i. min <= i & i < floor s & i : req s}"

  queueing :: state set
    "queueing == above Un below"

  goingup :: state set
    "goingup == above Int ({s. up s} Un Compl below)"

  goingdown :: state set
    "goingdown == below Int ({s. ~ up s} Un Compl above)"

  ready :: state set
    "ready == {s. stop s & ~ open s & move s}"

 
  (** Further abbreviations **)

  moving :: state set
    "moving ==  {s. ~ stop s & ~ open s}"

  stopped :: state set
    "stopped == {s. stop s  & ~ open s &  move s}"

  opened :: state set
    "opened ==  {s. stop s  &  open s  &  move s}"

  closed :: state set
    "closed ==  {s. stop s  & ~ open s &  move s}"

  atFloor :: nat => state set
    "atFloor n ==  {s. floor s = n}"


  
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

  req_up_act :: "(state*state) set"
    "req_up_act ==
         {(s,s'). s' = s (|stop  :=False,
			   floor := Suc (floor s),
			   up    := True|)
		       & s : (ready Int goingup)}"

  req_down_act :: "(state*state) set"
    "req_down_act ==
         {(s,s'). s' = s (|stop  :=False,
			   floor := floor s - 1,
			   up    := False|)
		       & s : (ready Int goingdown)}"

  move_up :: "(state*state) set"
    "move_up ==
         {(s,s'). s' = s (|floor := Suc (floor s)|)
		       & ~ stop s & up s & floor s ~: req s}"

  move_down :: "(state*state) set"
    "move_down ==
         {(s,s'). s' = s (|floor := floor s - 1|)
		       & ~ stop s & ~ up s & floor s ~: req s}"

  Lprg :: state program
    "Lprg == (|Init = {s. floor s = min & ~ up s & move s & stop s &
		          ~ open s & req s = {}},
	       Acts = {id, request_act, open_act, close_act,
		       req_up_act, req_down_act, move_up, move_down}|)"


  (** Invariants **)

  bounded :: state set
    "bounded == {s. min <= floor s & floor s <= max}"

  open_stop :: state set
    "open_stop == {s. open s --> stop s}"
  
  open_move :: state set
    "open_move == {s. open s --> move s}"
  
  stop_floor :: state set
    "stop_floor == {s. open s & ~ move s --> floor s : req s}"
  
  moving_up :: state set
    "moving_up == {s. ~ stop s & up s -->
                   (EX f. floor s <= f & f <= max & f : req s)}"
  
  moving_down :: state set
    "moving_down == {s. ~ stop s & ~ up s -->
                     (EX f. min <= f & f <= floor s & f : req s)}"
  
  (*intersection of all invariants: NECESSARY??*)
  valid :: state set
    "valid == bounded Int open_stop Int open_move"

end
