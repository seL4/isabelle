(*  Title:      HOL/ex/AVL.thy
    ID:         $Id$
    Author:     Cornelia Pusch and Tobias Nipkow
    Copyright   1998  TUM

AVL trees: at the moment only insertion.
This version works exclusively with nat.
Balance check could be simplified by working with int:
"isbal (MKT n l r) = (abs(int(height l) - int(height r)) <= #1 &
                      isbal l & isbal r)"
*)

AVL = Main +

datatype tree = ET | MKT nat tree tree

consts
 height :: "tree => nat"
 isin   :: "nat => tree => bool"
 isord  :: "tree => bool"
 isbal  :: "tree => bool"

primrec
"height ET = 0"
"height (MKT n l r) = Suc(max (height l) (height r))"

primrec
"isin k ET = False"
"isin k (MKT n l r) = (k=n | isin k l | isin k r)"

primrec
"isord ET = True"
"isord (MKT n l r) = ((! n'. isin n' l --> n' < n) &
                      (! n'. isin n' r --> n < n') &
                      isord l & isord r)"

primrec
"isbal ET = True"
"isbal (MKT n l r) = ((height l = height r | 
                       height l = Suc(height r) | 
                       height r = Suc(height l)) & 
                      isbal l & isbal r)"


datatype bal = Just | Left | Right

constdefs
 bal :: "tree => bal"
"bal t == case t of ET => Just
 | (MKT n l r) => if height l = height r then Just
                  else if height l < height r then Right else Left"

consts
 r_rot,l_rot,lr_rot,rl_rot :: "nat * tree * tree => tree"

recdef r_rot "{}"
"r_rot (n, MKT ln ll lr, r) = MKT ln ll (MKT n lr r)"

recdef l_rot "{}"
"l_rot(n, l, MKT rn rl rr) = MKT rn (MKT n l rl) rr"

recdef lr_rot "{}"
"lr_rot(n, MKT ln ll (MKT lrn lrl lrr), r) = MKT lrn (MKT ln ll lrl) (MKT n lrr r)"

recdef rl_rot "{}"
"rl_rot(n, l, MKT rn (MKT rln rll rlr) rr) = MKT rln (MKT n l rll) (MKT rn rlr rr)"


constdefs 
 l_bal :: "nat => tree => tree => tree"
"l_bal n l r == if bal l = Right 
                then lr_rot (n, l, r)
                else r_rot (n, l, r)"

 r_bal :: "nat => tree => tree => tree"
"r_bal n l r == if bal r = Left
                then rl_rot (n, l, r)
                else l_rot (n, l, r)"

consts
 insert :: "nat => tree => tree"
primrec
"insert x ET = MKT x ET ET"
"insert x (MKT n l r) = 
   (if x=n
    then MKT n l r
    else if x<n
         then let l' = insert x l
              in if height l' = Suc(Suc(height r))
                 then l_bal n l' r
                 else MKT n l' r
         else let r' = insert x r
              in if height r' = Suc(Suc(height l))
                 then r_bal n l r'
                 else MKT n l r')"

end
