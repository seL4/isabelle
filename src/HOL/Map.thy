(*  Title:      HOL/Map.thy
    ID:         $Id$
    Author:     Tobias Nipkow, based on a theory by David von Oheimb
    Copyright   1997 TU Muenchen

The datatype of `maps' (written ~=>); strongly resembles maps in VDM.
*)

Map = List + Option +

types ('a,'b) "~=>" = 'a => 'b option (infixr 0)

consts
empty   :: "'a ~=> 'b"
update  :: "('a ~=> 'b) => 'a => 'b => ('a ~=> 'b)"
           ("_/[_/|->/_]" [900,0,0] 900)
override:: "('a ~=> 'b) => ('a ~=> 'b) => ('a ~=> 'b)" (infixl "++" 100)
dom     :: "('a ~=> 'b) => 'a set"
ran     :: "('a ~=> 'b) => 'b set"
map_of  :: "('a * 'b)list => 'a ~=> 'b"

syntax (symbols)
  "~=>"     :: [type, type] => type
               (infixr "\\<leadsto>" 0)
  update    :: "('a ~=> 'b) => 'a => 'b => ('a ~=> 'b)"
               ("_/[_/\\<mapsto>/_]" [900,0,0] 900)
  override  :: "('a ~=> 'b) => ('a ~=> 'b) => ('a ~=> 'b)"
               (infixl "\\<oplus>" 100)

defs
empty_def "empty == %x. None"

update_def "m[a|->b] == %x. if x=a then Some b else m x"

override_def "m1++m2 == %x. case m2 x of None => m1 x | Some y => Some y"

dom_def "dom(m) == {a. m a ~= None}"
ran_def "ran(m) == {b. ? a. m a = Some b}"

primrec map_of list
"map_of [] = empty"
"map_of (p#ps) = (map_of ps)[fst p |-> snd p]"

end
