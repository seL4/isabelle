(*  Title:      HOL/Library/word_setup.ML
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)
*)

local
    fun is_const_bool (Const("True",_)) = true
      | is_const_bool (Const("False",_)) = true
      | is_const_bool _ = false
    fun is_const_bit (Const("Word.bit.Zero",_)) = true
      | is_const_bit (Const("Word.bit.One",_)) = true
      | is_const_bit _ = false
    fun num_is_usable (Const("Numeral.bin.Pls",_)) = true
      | num_is_usable (Const("Numeral.bin.Min",_)) = false
      | num_is_usable (Const("Numeral.bin.Bit",_) $ w $ b) =
	num_is_usable w andalso is_const_bool b
      | num_is_usable _ = false
    fun vec_is_usable (Const("List.list.Nil",_)) = true
      | vec_is_usable (Const("List.list.Cons",_) $ b $ bs) =
	vec_is_usable bs andalso is_const_bit b
      | vec_is_usable _ = false
    fun add_word thy =
	let
	    val fast1_th = PureThy.get_thm thy "Word.fast_nat_to_bv_def"
	    val fast2_th = PureThy.get_thm thy "Word.fast_bv_to_nat_def"
	    fun f sg thms (Const("Word.nat_to_bv",_) $ (Const("Numeral.number_of",_) $ t)) =
		if num_is_usable t
		then Some (Drule.cterm_instantiate [(cterm_of sg (Var(("w",0),Type("Numeral.bin",[]))),cterm_of sg t)] fast1_th)
		else None
	      | f _ _ _ = None
	    fun g sg thms (Const("Word.bv_to_nat",_) $ (t as (Const("List.list.Cons",_) $ _ $ _))) =
		if vec_is_usable t
		then Some (Drule.cterm_instantiate [(cterm_of sg (Var(("bs",0),Type("List.list",[Type("Word.bit",[])]))),cterm_of sg t)] fast2_th)
		else None
	      | g _ _ _ = None
	    val simproc1 = Simplifier.simproc (sign_of thy) "nat_to_bv" ["Word.nat_to_bv (number_of ?w)"] f
	    val simproc2 = Simplifier.simproc (sign_of thy) "bv_to_nat" ["Word.bv_to_nat (?x # ?xs)"] g
	in
	    Simplifier.change_simpset_of (op addsimprocs) [simproc1,simproc2] thy
	end
in
val setup_word = [add_word]
end
