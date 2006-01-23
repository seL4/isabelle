(*  Title:      Pure/ML-Systems/smlnj-interrupt-timeout.ML
    ID:         $Id$
    Author:     Tjark Weber, Makarius
    Copyright   2006

Bounded time execution (similar to SML/NJ's TimeLimit structure).
*)

fun interrupt_timeout time f x =
  TimeLimit.timeLimit time f x
    handle TimeLimit.TimeOut => raise SML90.Interrupt;
