(*  Title:      HOLCF/Coind.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Example for co-induction on streams
*)

Coind = Stream2 +


consts

        nats            :: "dnat stream"
        from            :: "dnat -> dnat stream"

defs
        nats_def        "nats == fix`(LAM h.scons`dzero`(smap`dsucc`h))"

        from_def        "from == fix`(LAM h n.scons`n`(h`(dsucc`n)))"

end

(*
                smap`f`UU = UU
      x~=UU --> smap`f`(scons`x`xs) = scons`(f`x)`(smap`f`xs)

                nats = scons`dzero`(smap`dsucc`nats)

                from`n = scons`n`(from`(dsucc`n))
*)


