
Cockpit = MuIOAOracle +

datatype 'a action = Alarm 'a | Info 'a | Ack 'a
datatype event = NONE | PonR | Eng | Fue


(*This cockpit automaton is a deeply simplified version of the
  control component of a helicopter alarm system considered in a study
  of ESG.  Some properties will be proved by using model checker
  mucke.*)

automaton cockpit =
  signature
    actions event action
    inputs "Alarm a"
    outputs "Ack a","Info a"
  states
    APonR_incl :: bool
    info :: event
  initially "info=NONE & ~APonR_incl"
  transitions
    "Alarm a"
      post info:="if (a=NONE) then info else a",
        APonR_incl:="if (a=PonR) then True else APonR_incl"
    "Info a"
      pre "(a=info)"
    "Ack a"
      pre "(a=PonR --> APonR_incl) & (a=NONE --> ~APonR_incl)"
      post info:="NONE",APonR_incl:="if (a=PonR) then False else APonR_incl"

automaton cockpit_hide = hide_action "Info a" in cockpit


(*Subsequent automata express the properties to be proved, see also
  Cockpit.ML*)

automaton Al_before_Ack =
  signature
    actions event action
    inputs "Alarm a"
    outputs "Ack a"
  states
    APonR_incl :: bool
  initially "~APonR_incl"
  transitions
    "Alarm a"
      post APonR_incl:="if (a=PonR) then True else APonR_incl"
    "Ack a"
      pre "(a=PonR --> APonR_incl)"
      post APonR_incl:="if (a=PonR) then False else APonR_incl"

automaton Info_while_Al =
  signature
    actions event action
    inputs "Alarm a"
    outputs "Ack a", "Info i"
  states
    info_at_Pon :: bool
  initially "~info_at_Pon"
  transitions
    "Alarm a"
      post
        info_at_Pon:="if (a=PonR) then True else (if (a=NONE) then info_at_Pon else False)"
    "Info a"
      pre "(a=PonR) --> info_at_Pon"
    "Ack a"
      post info_at_Pon:="False"

automaton Info_before_Al =
  signature
    actions event action
    inputs "Alarm a"
    outputs "Ack a", "Info i"
  states
    info_at_NONE :: bool
  initially "info_at_NONE"
  transitions
    "Alarm a"
      post info_at_NONE:="if (a=NONE) then info_at_NONE else False"
    "Info a"
      pre "(a=NONE) --> info_at_NONE"
    "Ack a"
      post info_at_NONE:="True"

end
