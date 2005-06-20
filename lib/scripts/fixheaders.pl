#!/usr/bin/env perl -w
#
# $Id$
# Author: Florian Haftmann, TUM
#
# DESCRIPTION: migrates theory header (of new-style theories) to non-deprecated syntax

use strict;
use File::Find;
use File::Basename;
use File::Copy;

# configuration
my @suffices = ('\.thy');
my $backupsuffix = '~~';

# migrator function
sub fixheaders {

    my ($file) = @_;

    open(ISTREAM, $file) or die $!;
    my @content = <ISTREAM>;
    close ISTREAM or die $!;
    my $content = join("", @content);
    $_ = $content;
    if (m!^theory!cgoms) {
        my $prelude = $`;
        my $thyheader = "theory";
        $thyheader .= skip_wscomment();
        if (m!\G(\S+)!cgoms) {
            $thyheader .= $1;
            $thyheader .= skip_wscomment();
            if (m!\G(?:imports|=)!cgoms) {
                $thyheader .= "imports";
                $thyheader .= skip_wscomment() || " ";
                while (m/\G(?!uses|files|begin|:)/cgoms && m!\G(?:[\w_]+|"[^"]+")!cgoms) {
                    $thyheader .= $&;
                    $thyheader .= skip_wscomment();
                    if (m!\G\+!cgoms) {
                        m!\G ?!cgoms;
                    }
                    $thyheader .= skip_wscomment();
                }
            }
            if (m!\G(?:files|uses)!cgoms) {
                $thyheader .= "uses";
                $thyheader .= skip_wscomment();
                while (m/\G(?!begin|:)/cgoms && m!\G(\("[^"]+"\)|"[^"]+"|[^"\s]+)!cgoms) {
                    $thyheader .= $&;
                    $thyheader .= skip_wscomment();
                }
            }

            if (m!\G(?:begin|:)!cgoms) {
                my $postlude = $';
                if ($& eq ":") {
                    $thyheader .= " ";
                }
                $thyheader .=  "begin";
                my $newcontent = "$prelude$thyheader$postlude";
                if ($content ne $newcontent) {
                    print STDERR "fixing $file\n";
                    my $backupfile = "$file$backupsuffix";
                    if (! -f $backupfile) {
                        rename $file, $backupfile or die $!;
                    }
                    open(OSTREAM, ">$file") or die $!;
                    print OSTREAM $newcontent;
                    close(OSTREAM) or die $!;
                }
            }
        }
    }

}

# utility functions
sub skip_wscomment {
    my $commentlevel = 0;
    my @skipped = ();
    while () {
        if (m!\G\(\*!cgoms) {
            push(@skipped, $&);
            $commentlevel++;
        } elsif ($commentlevel > 0) {
            if (m!\G\*\)!cgoms) {
                push(@skipped, $&);
                $commentlevel--;
            } elsif (m/\G(?:
                        \*(?!\))|\((?!\*)|[^(*]
                       )*/cgomsx) {
                push(@skipped, $&);
            } else {
                die "probably incorrectly nested comment";
            }
        } elsif (m!\G\s+!cgoms) {
            push(@skipped, $&);
        } else {
            return join('', @skipped);
        }
    }
}

# main
foreach my $file (@ARGV) {
    eval {
        fixheaders($file);
    };
    if ($@) {
        print STDERR "*** fixheaders $file: ", $@, "\n";
    }
}
