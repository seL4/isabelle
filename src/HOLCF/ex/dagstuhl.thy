(*
    ID:         $ $
*)

Dagstuhl  =  Stream2 +

consts
       YS  :: "'a stream"
       YYS :: "'a stream"

rules

YS_def    "YS  = fix[LAM x. scons[y][x]]"
YYS_def   "YYS = fix[LAM z. scons[y][scons[y][z]]]"
  
end

