(*  Title:      HOL/UNITY/Network
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Communication Network

From Misra, "A Logic for Concurrent Programming" (1994), section 5.7
*)

Network = UNITY +

(*The state assigns a number to each process variable*)

datatype pvar = Sent | Rcvd | Idle

datatype pname = Aproc | Bproc

types state = "pname * pvar => nat"

end
