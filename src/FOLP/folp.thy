FOLP = IFOLP +
consts
  cla :: "[p=>p]=>p"
rules
  classical "(!!x.x:~P ==> f(x):P) ==> cla(f):P"
end
