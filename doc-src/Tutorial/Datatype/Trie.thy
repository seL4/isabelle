Trie = Main +
consts   assoc :: "('key * 'val)list => 'key => 'val option"
primrec "assoc [] x = None"
        "assoc (p#ps) x =
           (let (a,b) = p in if a=x then Some b else assoc ps x)"
datatype ('a,'v)trie = Trie ('v option) "('a * ('a,'v)trie)list"
consts value :: ('a,'v)trie => 'v option
       alist :: "('a,'v)trie => ('a * ('a,'v)trie)list"
primrec "value(Trie ov al) = ov"
primrec "alist(Trie ov al) = al"
consts   lookup :: ('a,'v)trie => 'a list => 'v option
primrec "lookup t [] = value t"
        "lookup t (a#as) = (case assoc (alist t) a of
                              None => None
                            | Some at => lookup at as)"
consts update :: ('a,'v)trie => 'a list => 'v => ('a,'v)trie

primrec
  "update t []     v = Trie (Some v) (alist t)"
  "update t (a#as) v = (let tt = (case assoc (alist t) a of
                                    None => Trie None [] | Some at => at)
                        in Trie (value t) ((a,update tt as v)#alist t))"
end
