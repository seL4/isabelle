(* $Id$ *)


Dagstuhl  =  Stream2 +

consts
	y  :: "'a"
       YS  :: "'a stream"
       YYS :: "'a stream"

defs

YS_def    "YS  == fix`(LAM x. scons`y`x)"
YYS_def   "YYS == fix`(LAM z. scons`y`(scons`y`z))"
  
end

