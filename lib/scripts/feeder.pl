#
# $Id$
#
# feeder.pl - feed isabelle session
#

# args

($head, $noint, $emitpid, $quit, $symbols, $tail) = @ARGV;


# symbols translation table

%tab = (
#GENERATED TEXT FOLLOWS - Do not edit!
  "\xa0", "\\<space2>",
  "\xa1", "\\<Gamma>",
  "\xa2", "\\<Delta>",
  "\xa3", "\\<Theta>",
  "\xa4", "\\<Lambda>",
  "\xa5", "\\<Pi>",
  "\xa6", "\\<Sigma>",
  "\xa7", "\\<Phi>",
  "\xa8", "\\<Psi>",
  "\xa9", "\\<Omega>",
  "\xaa", "\\<alpha>",
  "\xab", "\\<beta>",
  "\xac", "\\<gamma>",
  "\xad", "\\<delta>",
  "\xae", "\\<epsilon>",
  "\xaf", "\\<zeta>",
  "\xb0", "\\<eta>",
  "\xb1", "\\<theta>",
  "\xb2", "\\<kappa>",
  "\xb3", "\\<lambda>",
  "\xb4", "\\<mu>",
  "\xb5", "\\<nu>",
  "\xb6", "\\<xi>",
  "\xb7", "\\<pi>",
  "\xb8", "\\<rho>",
  "\xb9", "\\<sigma>",
  "\xba", "\\<tau>",
  "\xbb", "\\<phi>",
  "\xbc", "\\<chi>",
  "\xbd", "\\<psi>",
  "\xbe", "\\<omega>",
  "\xbf", "\\<not>",
  "\xc0", "\\<and>",
  "\xc1", "\\<or>",
  "\xc2", "\\<forall>",
  "\xc3", "\\<exists>",
  "\xc4", "\\<And>",
  "\xc5", "\\<lceil>",
  "\xc6", "\\<rceil>",
  "\xc7", "\\<lfloor>",
  "\xc8", "\\<rfloor>",
  "\xc9", "\\<turnstile>",
  "\xca", "\\<Turnstile>",
  "\xcb", "\\<lbrakk>",
  "\xcc", "\\<rbrakk>",
  "\xcd", "\\<cdot>",
  "\xce", "\\<in>",
  "\xcf", "\\<subseteq>",
  "\xd0", "\\<inter>",
  "\xd1", "\\<union>",
  "\xd2", "\\<Inter>",
  "\xd3", "\\<Union>",
  "\xd4", "\\<sqinter>",
  "\xd5", "\\<squnion>",
  "\xd6", "\\<Sqinter>",
  "\xd7", "\\<Squnion>",
  "\xd8", "\\<bottom>",
  "\xd9", "\\<doteq>",
  "\xda", "\\<equiv>",
  "\xdb", "\\<noteq>",
  "\xdc", "\\<sqsubset>",
  "\xdd", "\\<sqsubseteq>",
  "\xde", "\\<prec>",
  "\xdf", "\\<preceq>",
  "\xe0", "\\<succ>",
  "\xe1", "\\<approx>",
  "\xe2", "\\<sim>",
  "\xe3", "\\<simeq>",
  "\xe4", "\\<le>",
  "\xe5", "\\<Colon>",
  "\xe6", "\\<leftarrow>",
  "\xe7", "\\<midarrow>",
  "\xe8", "\\<rightarrow>",
  "\xe9", "\\<Leftarrow>",
  "\xea", "\\<Midarrow>",
  "\xeb", "\\<Rightarrow>",
  "\xec", "\\<bow>",
  "\xed", "\\<mapsto>",
  "\xee", "\\<leadsto>",
  "\xef", "\\<up>",
  "\xf0", "\\<down>",
  "\xf1", "\\<notin>",
  "\xf2", "\\<times>",
  "\xf3", "\\<oplus>",
  "\xf4", "\\<ominus>",
  "\xf5", "\\<otimes>",
  "\xf6", "\\<oslash>",
  "\xf7", "\\<subset>",
  "\xf8", "\\<infinity>",
  "\xf9", "\\<box>",
  "\xfa", "\\<diamond>",
  "\xfb", "\\<circ>",
  "\xfc", "\\<bullet>",
  "\xfd", "\\<parallel>",
  "\xfe", "\\<surd>",
  "\xff", "\\<copyright>"
#END OF GENERATED TEXT
);


# setup hangup handler

sub hangup {
    exit(0);
}

$SIG{'HUP'} = "hangup";


# main

#bulletproof session
$noint && ($SIG{INT} = "IGNORE");

#buffer lines
$| = 1;


$emitpid && (print $$, "\n");

$head && (print "$head", "\n");

if (!$quit) {
    while (<STDIN>) {
	$symbols && (s/([\xa1-\xff])/\\$tab{$1}/g);
	print;
    }
}

$tail && (print "$tail", "\n");


# wait forever, expecting to be terminated by HUP

close STDOUT;
sleep;
