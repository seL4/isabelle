(* $Id$ *)


Dagstuhl  =  Stream +

consts
        y  :: "'a"
       YS  :: "'a stream"
       YYS :: "'a stream"

defs

YS_def    "YS  == fix`(LAM x. y && x)"
YYS_def   "YYS == fix`(LAM z. y && y && z)"
  
end

