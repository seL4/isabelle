(*  Title:      HOL/Map.thy
    ID:         $Id$
    Author:     Tobias Nipkow, based on a theory by David von Oheimb
    Copyright   1997 TU Muenchen

The datatype of `maps' (written ~=>); strongly resembles maps in VDM.
*)

Map = List + Option +

types ('a,'b) "~=>" = 'a => 'b option (infixr 0)

consts
empty	::  "'a ~=> 'b"
chg_map	:: "('b => 'b) => 'a => ('a ~=> 'b) => ('a ~=> 'b)"
override:: "('a ~=> 'b) => ('a ~=> 'b) => ('a ~=> 'b)" (infixl "++" 100)
dom	:: "('a ~=> 'b) => 'a set"
ran	:: "('a ~=> 'b) => 'b set"
map_of	:: "('a * 'b)list => 'a ~=> 'b"
map_upds:: "('a ~=> 'b) => 'a list => 'b list => 
	    ('a ~=> 'b)"			 ("_/'(_[|->]_/')" [900,0,0]900)
syntax
map_upd	:: "('a ~=> 'b) => 'a => 'b => ('a ~=> 'b)"
					         ("_/'(_/|->_')"   [900,0,0]900)

syntax (xsymbols)
  "~=>"     :: [type, type] => type      (infixr "\\<leadsto>" 0)
  map_upd   :: "('a ~=> 'b) => 'a      => 'b      => ('a ~=> 'b)"
					  ("_/'(_/\\<mapsto>/_')"  [900,0,0]900)
  map_upds  :: "('a ~=> 'b) => 'a list => 'b list => ('a ~=> 'b)"
				         ("_/'(_/[\\<mapsto>]/_')" [900,0,0]900)

translations

  "m(a|->b)" == "m(a:=Some b)"

defs

empty_def    "empty == %x. None"

chg_map_def  "chg_map f a m == case m a of None => m | Some b => m(a|->f b)"

override_def "m1++m2 == %x. case m2 x of None => m1 x | Some y => Some y"

dom_def "dom(m) == {a. m a ~= None}"
ran_def "ran(m) == {b. ? a. m a = Some b}"

primrec
  "map_of [] = empty"
  "map_of (p#ps) = (map_of ps)(fst p |-> snd p)"

primrec "t([]  [|->]bs) = t"
        "t(a#as[|->]bs) = t(a|->hd bs)(as[|->]tl bs)"

end
