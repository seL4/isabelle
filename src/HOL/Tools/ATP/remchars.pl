#!/usr/bin/perl
#
# isa2tex.pl - Converts isabelle formulae into LaTeX
# A complete hack - needs more work.
#
# by Michael Dales (michael@dcs.gla.ac.uk)

# Begin math mode
#printf "\$";
#ALL íxaè::ê'aè::étypeè.   (~ (ìPè::ê'aè::étypeè => bool) (ìxè::ê'aè::étypeè) | ìPè íxaè) & (~ ìPè íxaè# | ìPè ìxè)((ìPè::ê'aè::étypeè => bool) (ìxaè::ê'aè::étypeè) | (ALL íxè::ê'aè::étypeè. ìPè íxè)) &((AL#L íxè::ê'aè::étypeè. ~ ìPè íxè) | ~ ìPè (ìxbè::ê'aè::étypeè))
#perhaps change to all chars not in alphanumeric or a few symbols?

while (<STDIN>)
{

    #chop();
    s%\n$%%;
    s%í%%g;
    s%ì%%g;
    s%è%%g;
    s%î%%g;
    s%ê%%g;
    s%é%%g;
    
    #printf "$_\\newline\n";
    printf "$_";
}

# End math mode
#printf "\$\n";
#printf "\\end{tabbing}\n";
