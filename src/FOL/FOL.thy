
FOL = IFOL +

rules
  classical "(~P ==> P) ==> P"

setup ClasetThyData.setup
setup attrib_setup              (* FIXME move to IFOL.thy *)

end
