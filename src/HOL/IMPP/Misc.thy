(*  Title:      HOL/IMPP/Misc.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 TUM

Several examples for Hoare logic
*)
Misc = Hoare +

defs
  newlocs_def "newlocs       == %x. arbitrary"
  setlocs_def "setlocs s l'  == case s of st g l => st g l'"
  getlocs_def "getlocs s     == case s of st g l => l"
   update_def "update s vn v == case vn of
                              Glb gn => (case s of st g l => st (g(gn:=v)) l)
                            | Loc ln => (case s of st g l => st g (l(ln:=v)))"

end
  