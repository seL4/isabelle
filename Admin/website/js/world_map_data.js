var world_data = [];
var i = 0;

world_data[i++] = ['Xiaoqi Ma', CAPTION, 'University of Reading', STICKY, NOCLOSE];
world_data[i++] = ['<a href=\'http://www.cl.cam.ac.uk/users/lcp/\'>Larry Paulson</a>, <a href=\'http://www.cl.cam.ac.uk/~tjr22\'>Tom Ridge</a> et al.', CAPTION, 'University of Cambridge', STICKY, NOCLOSE];
world_data[i++] = ['Sara Kalvala', CAPTION, 'University of Warwick', STICKY, NOCLOSE];
world_data[i++] = ['Paqui Lucio', CAPTION, 'Basque Country University', STICKY, NOCLOSE];
world_data[i++] = ['Pierre Cast&eacute;ran', CAPTION, 'Universit&eacute; Bordeaux', STICKY, NOCLOSE];
world_data[i++] = ['Achim D. Brucker, Burkhart Wolff: <b><a href=\'http://www.brucker.ch/projects/hol-ocl/index.en.html\'>HOL-OCL</a></b>, <b><a href=\'http://www.brucker.ch/projects/hol-testgen/index.en.html\'>HOL-TestGen</a></b>, <b><a href=\'http://abacus.informatik.uni-freiburg.de/holz/index.html\'>HOL-Z</a></b>, <b><a href=\'http://www.brucker.ch/projects/isamorph/\'>IsaMorph</a></b><br>J&uuml;rgen Doser: <b><a href=\'http://www.infsec.ethz.ch/people/doserj/mds\'>Model-Driven Security with Secure UML</a></b><br>Christoph Sprenger: <b><a href=\'http://www.zisc.ethz.ch/research/securityprotocolproofs\'>Cryptographically Faithful Proofs of Security Protocols</a></b>', CAPTION, 'ETH Z&uuml;rich', STICKY, NOCLOSE];
world_data[i++] = ['Walther Neuper: <b>ISAC</b>', CAPTION, 'Graz University of Technology', STICKY, NOCLOSE];
world_data[i++] = ['<a href=\'http://www4.informatik.tu-muenchen.de/~nipkow/\'>Tobias Nipkow</a> et al.', CAPTION, 'Technische Universit&auml;t M&uuml;nchen', STICKY, NOCLOSE];
world_data[i++] = ['Harald Hiss', CAPTION, 'Albert-Ludwigs-Universit&auml;t Freiburg', STICKY, NOCLOSE];
world_data[i++] = ['<a href=\'http://www.loria.fr/~merz/\'>Stephan Merz</a> et al.', CAPTION, 'LORIA', STICKY, NOCLOSE];
world_data[i++] = ['Peter Lammich', CAPTION, 'Institut f&uuml;r Informatik, Universit&auml;t M&uuml;nster', STICKY, NOCLOSE];
world_data[i++] = ['Till Mossakowski: <b>Heterogeneous Tool Set</b>', CAPTION, 'University of Bremen, DFKI Lab Bremen', STICKY, NOCLOSE];
world_data[i++] = ['J&oslash;rgen Villadsen', CAPTION, 'Technical University of Denmark', STICKY, NOCLOSE];
world_data[i++] = ['See the zoomed in section of the map for details.', CAPTION, 'Europe', STICKY, NOCLOSE];
world_data[i++] = ['<a href=\'http://users.rsise.anu.edu.au/~jeremy/\'>Jeremy Dawson</a>, <a href="http://users.rsise.anu.edu.au/~jiameng/">Jia Meng</a>, <a href=\'http://users.rsise.anu.edu.au/~michaeln/\'>Michael Norrish</a>', CAPTION, 'ANU, NICTA', STICKY, NOCLOSE];
world_data[i++] = ['<a href=\'http://www.cse.unsw.edu.au/~kleing/\'>Gerwin Klein</a> et al.: <b>L4.verified</b>', CAPTION, 'NICTA, UNSW', STICKY, NOCLOSE];
world_data[i++] = ['Kamal Kant Gupta', CAPTION, 'IIT Guwahati', STICKY, NOCLOSE];
world_data[i++] = ['Yasuhiko Minamide', CAPTION, 'University of Tsukuba', STICKY, NOCLOSE];
world_data[i++] = ['Gang Yu: <b>Formalizing Lambda-Calculus and Virtual Machine with Non-Local Control Operators</b>', CAPTION, 'Institute of Software, Beijing', STICKY, NOCLOSE];
world_data[i++] = ['John Matthews', CAPTION, 'Galois Connections', STICKY, NOCLOSE];
world_data[i++] = ['Slawomir Kolodynski: <b>IsarMathLib</b>', CAPTION, 'Newark, CA', STICKY, NOCLOSE];
world_data[i++] = ['Robert Lamar', CAPTION, 'Stetson University', STICKY, NOCLOSE];
world_data[i++] = ['<a href=\'http://www.andrew.cmu.edu/~avigad/isabelle/\'>Jeremy Avigad</a>, <a href=\'http://www.cs.cmu.edu/~seanmcl/research\'>Sean McLaughlin</a>', CAPTION, 'Carnegie Mellon University', STICKY, NOCLOSE];

function world_click(i) {
    var entry = world_data[i];
    return overlib(entry[0], entry[1], entry[2], entry[3], entry[4]);
}
