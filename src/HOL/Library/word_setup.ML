(*  Title:      HOL/Library/word_setup.ML
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)

comments containing lcp are the removal of fast_bv_of_nat.
*)

local
    fun is_const_bool (Const("True",_)) = true
      | is_const_bool (Const("False",_)) = true
      | is_const_bool _ = false
    fun is_const_bit (Const("Word.bit.Zero",_)) = true
      | is_const_bit (Const("Word.bit.One",_)) = true
      | is_const_bit _ = false
    fun num_is_usable (Const("Numeral.Pls",_)) = true
      | num_is_usable (Const("Numeral.Min",_)) = false
      | num_is_usable (Const("Numeral.Bit",_) $ w $ b) =
	num_is_usable w andalso is_const_bool b
      | num_is_usable _ = false
    fun vec_is_usable (Const("List.list.Nil",_)) = true
      | vec_is_usable (Const("List.list.Cons",_) $ b $ bs) =
	vec_is_usable bs andalso is_const_bit b
      | vec_is_usable _ = false
    fun add_word thy =
	let
 (*lcp**	    val fast1_th = PureThy.get_thm thy "Word.fast_nat_to_bv_def"**)
	    val fast2_th = PureThy.get_thm thy (Name "Word.fast_bv_to_nat_def")
 (*lcp**	    fun f sg thms (Const("Word.nat_to_bv",_) $ (Const("Numeral.number_of",_) $ t)) =
		if num_is_usable t
		then SOME (Drule.cterm_instantiate [(cterm_of sg (Var(("w",0),Type("Numeral.bin",[]))),cterm_of sg t)] fast1_th)
		else NONE
	      | f _ _ _ = NONE **)
	    fun g sg thms (Const("Word.bv_to_nat",_) $ (t as (Const("List.list.Cons",_) $ _ $ _))) =
		if vec_is_usable t
		then SOME (Drule.cterm_instantiate [(cterm_of sg (Var(("bs",0),Type("List.list",[Type("Word.bit",[])]))),cterm_of sg t)] fast2_th)
		else NONE
	      | g _ _ _ = NONE
  (*lcp**	    val simproc1 = Simplifier.simproc (sign_of thy) "nat_to_bv" ["Word.nat_to_bv (number_of ?w)"] f ***)
	    val simproc2 = Simplifier.simproc (sign_of thy) "bv_to_nat" ["Word.bv_to_nat (?x # ?xs)"] g
	in
	  Simplifier.change_simpset_of thy (fn ss => ss addsimprocs [(*lcp*simproc1,**)simproc2]);
          thy
	end
in
val setup_word = [add_word]
end
