#!/usr/local/bin/perl
#
#   Checklinks 1.0.1
#
#     Starting at one or more seed HTML files, recursively check the
#     validity of all links on the site.  Major features:
#
#       * Local URLs are read from the filesystem when possible (much
#           faster than going through HTTP server).
#       * Basic server-side includes (aka SSI or SHTML) are checked.
#       * Latest standards are supported-- HTML 4.0, HTTP 1.1, URIs
#           according to RFC 2396.
#       * Links are traversed breadth-first.
#
#   To list command-line options, run "cl -?" or see &usage() below.
#
#   TO CONFIGURE: 
#
#   1) Set $LOCAL_HOST and $DOCUMENT_ROOT, just below.  If you don't, the
#      program will try to guess them in set_needed_globals(), but it's more
#      reliable if you enter them here.
#
#   2) If needed, set any further server configuration below-- things like
#      path aliases and so forth.  If you have the srm.conf file, you can 
#      feed it into this script with "-c srm.conf"; otherwise, the default 
#      settings will probably work OK.
#
#   You can set a few parameters with the undocumented "-D <name=value>"
#   command-line option, e.g. "-D LOCAL_HOST=www.myhost.com".
#
#   Further comments, including an overview of script internals, are at
#   the end of this file.
#
#   Copyright (C) 1998, 2000 by James Marshall, james@jmarshall.com
#   see http://www.jmarshall.com/tools/cl/ for more info
#
#
#   CHANGES IN 1.0.1:
#
#     This is just a bug fix release.  Fixes include:
#       . Aliases are handled correctly now.  Sorry 'bout that.
#       . A redirect + relative URL no longer results in infinitely
#           recursing URLs.
#       . More HTML tags are searched for links.
#       . Non-HTML files are no longer searched for links.
#       . There were other minor bug fixes.
#
#----------------------------------------------------------------------

#use strict ;

my( $LOCAL_HOST, $DOCUMENT_ROOT, $USER_DIR, @DIRECTORY_INDEX,
    %ALIAS, %ALIAS_MATCH, %SCRIPT_ALIAS, %SCRIPT_ALIAS_MATCH, %UN_ALIAS,
    @SHTML_EXTENSIONS, @CGI_EXTENSIONS, @INCLUDE_PATTERNS, @EXCLUDE_PATTERNS,
          @INCLUDE_STATUS, @EXCLUDE_STATUS,
    $verbose_report, $max_depth, $file_check, $full_http_check,
    $MAX_REDIRECTS, $MAX_ATTEMPTS, $HTML_BY_NAME, $SUPPORT_NCSA_BUG,
    @NO_PROXY, $DOC_ROOT_DEV, $DOC_ROOT_INODE, $DOC_ROOT_EXISTS, $CWD,
    %html_urls, %non_html_urls, %e_to_ch,

    %home_dir, %dir_to_user, %inode_to_user,

    %url, @urlstoget, 

    $debug, $CL_VERSION,
  ) ;


#----- User Configuration ---------------------------------------------

# This should be 'localhost', or a hostname of the Web server.  URLs at
#   this host will be assumed to be local; URLs not at this host will not be
#   traversed into. If this names a remote host, the program will not work.
# Note that 'localhost' doesn't necessarily point to your local Web server.

# $LOCAL_HOST= 'localhost' ;
# $LOCAL_HOST= 'www.example.com' ;
$LOCAL_HOST='isabelle.in.tum.de';

# This is your root Web directory, i.e. the directory that the Web server
#   sends the user if the URL "http://$LOCAL_HOST" is requested.  It's in
#   the configuration file srm.conf (and is read by -c option).
# If you don't know the document root of your server, but you don't need
#   it because you're only checking URLs whose path starts with ~, put a
#   non-existent path here rather than leave it blank (a hack).

# $DOCUMENT_ROOT= '/home/www/htdocs' ;
$DOCUMENT_ROOT='/home/proj/isabelle';

#----- variables equivalent to srm.conf entries 

# These globals are from the equivalent entries in srm.conf, etc.
# See the command-line option -c <config-file>, to read values directly 
#   from srm.conf instead.

# $USER_DIR= 'public_html' ;
$USER_DIR='.html-data';
@DIRECTORY_INDEX= qw( index.html index.cgi index.shtml ) ;

# Used in &url_to_filename(), and possibly elsewhere
# Note that ALIAS_MATCH and SCRIPT_ALIAS_MATCH use Perl (not standard) regexps.
# If order of multiple e.g. "Alias" directives is important, this may not work.
%ALIAS= () ;
%ALIAS_MATCH= () ;
%SCRIPT_ALIAS= () ;
%SCRIPT_ALIAS_MATCH= () ;

# The list of file extensions to interpret as CGI scripts or
#   server-parsed HTML files.
# These are not specific settings in srm.conf, but are combinations of
#   AddHandler directives and possibly AddType directives.
@CGI_EXTENSIONS=   qw( .cgi ) ;
@SHTML_EXTENSIONS= qw( .shtml ) ;

#----- end of variables equivalent to srm.conf entries 

# Specify patterns here to only include URLs that match at least one
#   pattern.  As a special case, an empty list includes all URLs, i.e.
#   does not restrict URLs by name (except perhaps by @EXCLUDE_PATTERNS).
# This can be added to or cleared with the -I command-line option.
@INCLUDE_PATTERNS= () ;

# Specify patterns here to cause matching URLs to be excluded,
#   e.g. '\?' means ignore all URLs that query.
# This can be added to or cleared with the -X command-line option.
# @EXCLUDE_PATTERNS=  qw( \? ) ;

# Only report URLs whose status codes start with one of these patterns.
#   As a special case, an empty list reports all URLs, i.e. does not 
#   restrict URLs by status code (except perhaps by @EXCLUDE_STATUS).
# This can be added to or cleared with the -i command-line option.
@INCLUDE_STATUS= () ;

# Don't report URLs whose status codes start with these patterns.  Default
#   is qw( 200 ).
# This can be added to or cleared with the -x command-line option.
@EXCLUDE_STATUS= qw( 200 ) ;

# For 302 or 303 HTTP redirection, redirect no more than this many times.
$MAX_REDIRECTS= 5 ;

# If a connection times out, etc., attempt no more than this many times.
$MAX_ATTEMPTS= 5 ;

# The old version determined whether a file was HTML by the -T test (text
#   file), and so traversed all HTML-like links in any text file that wasn't
#   a CGI script.  It's probably more appropriate to check the file
#   extension, to exclude source code, .txt files, etc.  Leave $HTML_BY_NAME
#   set to use the filename, or unset it to traverse all HTML-like links in
#   any text files, as the old version did.
$HTML_BY_NAME= 1 ;

# Some old NCSA servers, including 1.5.2, don't report the HTTP version
#   correctly in the status line; they return e.g. "HTTP 200 OK".  To allow
#   this, leave the variable here set.
$SUPPORT_NCSA_BUG= 1 ;


#----- DO NOT CHANGE ANYTHING BELOW THIS LINE, unless you want to... ---

#----- Further Global Variable Initialization --------------------------

$CL_VERSION= '1.0.1' ;

$ENV{'http_proxy'}||= $ENV{'HTTP_PROXY'} ;
@NO_PROXY= split(/[\s,]+/, $ENV{'no_proxy'} || $ENV{'NO_PROXY'} ) ;


# If output's not going directly to terminal, this ensures autoflushing.
$|= 1 ;

#----- End of Configuration --------------------------------------------

use strict 'vars' ;
use IO::Socket ;

&usage unless @ARGV ;

# Process command-line options
&getopts ;

# Make any final needed adjustments to globals, after the hard-coded
#   values above and any options have been processed.
&adjust_all_globals ;

# Default to "." if no starting filenames given.
# 3-6-98: Anh, decided against it.
#@ARGV= ('.') unless @ARGV ;

# &add_url() sets $url{$_} and pushes to @urlstoget, only if not already
#   added, plus any other initialization.
# Only add a file if it can be accessed with a URL.
foreach my $arg (@ARGV) {
    if ($arg=~ m#^http://#i) {
        &add_url($arg, '-', 0) ;
    } else {
        my($URL)= &filename_to_url($arg, $CWD) ;
        if (defined($URL)) {
            &add_url($URL, '-', 0) ;
        } else {
	    die "ERROR: $arg is not accessible through the Web server.\n" ;
        }
    }
}


# Check the URLs, in order.  @urlstoget may grow and rearrange.
while (@urlstoget) {
    my($url)= shift(@urlstoget) ;
    if ( !$url->{'ishtml'} or !$url->{'islocal'} or $url->{'dontfollow'}
         or (length($max_depth) and $url->{'depth'} > $max_depth ) ) {
        &verify_url($url) ;    # may set ishtml=true
    }
    if ( $url->{'ishtml'} and $url->{'islocal'} and !$url->{'dontfollow'}
         and (!length($max_depth) or $url->{'depth'} <= $max_depth ) ) {
        my($HTML)= &load_url($url) ;  # may set ishtml=false
        # 11-30-99 JSM: fixed to handle rel URLs in redirected pages correctly
        my($base_url)= $url->{'location'} || $url->{'URL'} ;
        &extract_urls($HTML, $base_url, $url->{'URL'}, $url->{'depth'}+1) 
            if $url->{'ishtml'} ;      # big, calls &add_url()
    }

    # If we get an error response that may be corrected with another
    #   attempt, put it back in the queue.  Such errors include 408,
    #   503, 504, and the homegrown codes 600, 601, 602, and 603.
    if ($url->{'status'}=~ /^(408|503|504|600|601|602|603)\b/ ) {
        push(@urlstoget, $url) if ( $url->{'numtries'} < $MAX_ATTEMPTS ) ;
    }

}

&make_report() ;

exit ;



#----- Process command-line options -----------------------------------

# Process any command-line options.
sub getopts {
    my($opt, $param) ;
    while ($ARGV[0]=~ /^-/) {
        $opt= shift(@ARGV) ;
        ($opt, $param)= $opt=~ /^-(.)(.*)/ ;

        # Turn on verbose reporting
        if ($opt eq 'v') {
            $verbose_report= ($param ne '-') ;

        # User-specified patterns to exclude ('' to clear list)
        } elsif ($opt eq 'I') {
            $param= shift(@ARGV) unless length($param) ;
            if (length($param)) { push(@INCLUDE_PATTERNS, $param) }
            else { @INCLUDE_PATTERNS= () }

        # User-specified patterns to exclude ('' to clear list)
        } elsif ($opt eq 'X') {
            $param= shift(@ARGV) unless length($param) ;
            if (length($param)) { push(@EXCLUDE_PATTERNS, $param) }
            else { @EXCLUDE_PATTERNS= () }

        # User-specified response codes to ignore ('' to clear list)
        } elsif ($opt eq 'i') {
            $param= shift(@ARGV) unless length($param) ;
            if (length($param)) { push(@INCLUDE_STATUS, $param) }
            else { @INCLUDE_STATUS= () }

        # User-specified response codes to ignore ('' to clear list)
        } elsif ($opt eq 'x') {
            $param= shift(@ARGV) unless length($param) ;
            if (length($param)) { push(@EXCLUDE_STATUS, $param) }
            else { @EXCLUDE_STATUS= () }

        # Maximum traversal depth
        } elsif ($opt eq 'd') {
            $param= shift(@ARGV) unless length($param) ;
            $max_depth= $param ;

        # Make it a "file check"-- only read local files, do not use HTTP
        } elsif ($opt eq 'f') {
            $file_check= ($param ne '-') ;

        # Use HTTP for all URL's, even local files
        } elsif ($opt eq 'h') {
            $full_http_check= ($param ne '-') ;

        # Read configuration parameters from srm.conf-like file
        } elsif ($opt eq 'c') {
            $param= shift(@ARGV) unless length($param) ;
            &read_srm_conf($param) ;
            
        # Print current configuration parameters
        } elsif ($opt eq 'q') {
            &print_config ;
            exit ;   # jsm-- should we exit?

        # Allow certain parameters to be defined via the command line
        } elsif ($opt eq 'D') {
            $param= shift(@ARGV) unless length($param) ;
            $debug=1, unshift(@ARGV,$param), next if $param=~ /^-/ ;
            my($name,$value)= split(/=/, $param, 2) ;
            $value= 1 unless length($value) ;
            if ($name=~ /^(LOCAL_HOST|DOCUMENT_ROOT|USER_DIR|DEBUG|debug)$/) {
                eval "\$$name= \$value" ;
                #$$name= $value ;  # this doesn't work, because of initial my()
            }

        } elsif ($opt eq '?') {
            &usage ;

        # End command-line option processing on "--"
        } elsif ($opt eq '-') {
            return ;

        } else {
            print STDERR 
                "Illegal option-- '$opt'.  Enter \"$0 -?\" for help.\n" ;
            exit ;
        }

    }

    if ($file_check and $full_http_check) {
        print STDERR "You cannot use both the -f and the -h options.\n" ;
        exit ;
    }

}


# Read appropriate values from the given file, typically srm.conf.  If a
#   directory is named, default to filename "srm.conf".
# Note that opening "-" will open STDIN.
sub read_srm_conf {
    my($fname)= @_ ;
    local(*SRM) ;

    # default to srm.conf if only a directory is named
    if (-d $fname) {
        $fname=~ s#/$## ;
        $fname.= "/srm.conf" ;
    }

    # Clear old values
    $DOCUMENT_ROOT= $USER_DIR= '' ;
    @DIRECTORY_INDEX= @CGI_EXTENSIONS= @SHTML_EXTENSIONS= () ;
    %ALIAS= %ALIAS_MATCH= %SCRIPT_ALIAS= %SCRIPT_ALIAS_MATCH= () ;

    open(SRM, "<$fname") || die "Can't open $fname: $!" ;
    while (<SRM>) {
        s/#.*// ;
        next unless /\S/ ;
        my($name, @param)= /(\S+)/g ;

        if ($name eq 'DocumentRoot') {
            $DOCUMENT_ROOT= $param[0] ;

        } elsif ($name eq 'UserDir') {
            $USER_DIR= $param[0] ;

        } elsif ($name eq 'DirectoryIndex') {
            @DIRECTORY_INDEX= @param ;

        } elsif ($name eq 'Alias') {
            $ALIAS{$param[0]}= $param[1] ;

        } elsif ($name eq 'AliasMatch') {
            $ALIAS_MATCH{$param[0]}= $param[1] ;

        } elsif ($name eq 'ScriptAlias') {
            $SCRIPT_ALIAS{$param[0]}= $param[1] ;

        } elsif ($name eq 'ScriptAliasMatch') {
            $SCRIPT_ALIAS_MATCH{$param[0]}= $param[1] ;

        } elsif ($name eq 'AddHandler') {
            if ($param[0] eq 'cgi-script') {
                push(@CGI_EXTENSIONS, $param[1]) ;
            } elsif ($param[0] eq 'server-parsed') {
                push(@SHTML_EXTENSIONS, $param[1]) ;
            }
        }

    }
    close(SRM) ;
}


# Make any final settings to global variables, after the hard-coded values
#   and command-line options have been processed.
# Most non-user-configurable globals are also set here.
sub adjust_all_globals {

    # Standardize $USER_DIR to never have trailing slash
    $USER_DIR=~ s#/$## ;

    # If no $LOCAL_HOST set, try to read it from first URL in list, or
    #   use the string 'localhost' if that URL contains no hostname.
    unless (length($LOCAL_HOST)) {
        $LOCAL_HOST= (&parse_url($ARGV[0]))[1] || 'localhost' ;
        print STDERR "LOCAL_HOST set to \"\L$LOCAL_HOST\E\"\n" ;
    }
    $LOCAL_HOST= lc($LOCAL_HOST) ;

    # If no $DOCUMENT_ROOT, try to guess it from $HOME, username, $USER_DIR.
    unless (length($DOCUMENT_ROOT)) {
        my($home) ;
        unless ($home= $ENV{'HOME'}) {
            my($uname)= getpwuid($<) || $ENV{'USER'} || `whoami` || `id -un` ;
            chomp($uname) ;
            &read_home_dirs unless %home_dir ;   # only read when needed
            $home= $home_dir{$uname} ;
        }
        $DOCUMENT_ROOT= "$home/$USER_DIR" ;

        die "Could not determine DOCUMENT_ROOT; edit the $0 script to set it.\n"
            unless (-d $DOCUMENT_ROOT) ;

        print STDERR "DOCUMENT_ROOT set to \"$DOCUMENT_ROOT\"\n" ;
    }
    $DOCUMENT_ROOT=~ s#/$## ;

    # Allows &filename_to_url() to unalias as best as possible.  Note that 
    #   use of &filename_to_url() can be avoided by the user; see note in 
    #   that routine.
    %UN_ALIAS= (reverse (%ALIAS, %SCRIPT_ALIAS) ) ;

    # These are to compare equivalency to later, in &filename_to_url().
    ($DOC_ROOT_DEV, $DOC_ROOT_INODE)= stat("$DOCUMENT_ROOT/.") ;
    
    $DOC_ROOT_EXISTS= -e _ ;
    
    # Set CWD from shell variable, else from `pwd`.
    $CWD= $ENV{'PWD'} || `pwd` || die "couldn't run pwd: $!" ;
    chomp($CWD) ;


    # These are used by &extract_urls().
    # This is a complete list of URL-type attributes defined in HTML 4.0,
    #   plus any others I found, like nonstandard ones or from an earlier HTML.
    # Only a few of these are commonly used, as of early 1998.
    # The set in %html_urls could possibly link to HTML resources, while the
    #   set in %non_html_urls could not.  The %special(.*) sets, here for 
    #   reference only, include URL attributes that require special handling.

    %html_urls= ( 'a'          => [ 'href' ],
                  'area'       => [ 'href' ],
                  'frame'      => [ 'src', 'longdesc' ],
                  'link'       => [ 'href', 'urn' ],
                  'img'        => [ 'longdesc', 'usemap' ],
                  'q'          => [ 'cite' ],
                  'blockquote' => [ 'cite' ],
                  'ins'        => [ 'cite' ],
                  'del'        => [ 'cite' ],
                  'object'     => [ 'usemap' ],
                  'input'      => [ 'usemap' ],
                  'iframe'     => [ 'src', 'longdesc' ],
		  'ilayer'     => [ 'src' ],
		  'layer'      => [ 'src' ],
		  'fig'        => [ 'imagemap' ],
		  'overlay'    => [ 'imagemap' ],
		  'meta'       => [ 'url' ],
		  'note'       => [ 'src' ],
                ) ;

    %non_html_urls= ( 'body'    => [ 'background' ], 
                      'img'     => [ 'src', 'lowsrc', 'dynsrc' ],
                      'input'   => [ 'src' ],
                      'script'  => [ 'src', 'for' ],

		      'fig'     => [ 'src' ],
		      'overlay' => [ 'src' ],
		      'select'  => [ 'src' ],
		      'ul'      => [ 'src' ],
		      'h1'      => [ 'src' ],
		      'h2'      => [ 'src' ],
		      'h3'      => [ 'src' ],
		      'h4'      => [ 'src' ],
		      'h5'      => [ 'src' ],
		      'h6'      => [ 'src' ],
		      'hr'      => [ 'src' ],
		      'table'   => [ 'src' ],
		      'td'      => [ 'src' ],
		      'th'      => [ 'src' ],
		      'tr'      => [ 'src' ],

		      'bgsound' => [ 'src' ],
		      'embed'   => [ 'src' ],
                  ) ;

    # %special_urls= ( 'base' => [ 'href' ] ) ;
    #
    # %special_html_urls= ( 'object' => [ 'codebase', 'data' ] ) ;
    #
    # %special_non_html_urls=
    #      ( 'head'   => [ 'profile' ],
    #        'object' => [ 'codebase', 'archive', 'classid' ],
    #        'applet' => [ 'codebase', 'code', 'object', 'archive' ],
    #        'form'   => [ 'action', 'script' ]
    #      ) ;


    # This is a translation from entity character references to characters, 
    #   used in &HTMLunescape().
    # This simplified version only supports &quot; &lt; &gt; &amp;, but that
    #   should be enough for URL-type attributes.
    # See http://www.w3.org/TR/REC-html40/sgml/entities.html for full entity 
    #   list.

    %e_to_ch= (quot => '"', 
               'lt' => '<', 
               'gt' => '>', 
               amp  => '&') ;

}


#----------------------------------------------------------------------

# Add the URL to our data structures; specifically, to %url and @urlstoget.
# Returns a pointer to the structure in %url, or undef if already defined
#   or on error.
# Currently, this always receives the URL with the host name lowercase,
#   either from &absolute_url() or from using $LOCAL_HOST.
sub add_url {
    my($URL, $referer, $depth, $ishtml, $iscgi, $dontfollow)= @_ ;

    # Allow the user to restrict URL patterns:  URLs must be in 
    #   @INCLUDE_PATTERNS but not in @EXCLUDE_PATTERNS (but only restrict 
    #   by @INCLUDE_PATTERNS if it's not empty).
    return undef if @INCLUDE_PATTERNS &&
                    !grep( $URL=~ /$_/, @INCLUDE_PATTERNS ) ;
    return undef if grep( $URL=~ /$_/, @EXCLUDE_PATTERNS ) ;

    # Canonicalize URL, so we don't get a page multiple times
    $URL= &canonicalize($URL) ;
    
    # for obscure case involving a <form action=___.cgi>-extracted URL being
    #   overwritten by <a href=___.cgi> extraction (don't fret over this)
    $url{$URL}{'dontfollow'}&&= $dontfollow if $url{$URL} ;

    # Don't add the record a second time!  Or will infinitely traverse.
    return undef if $url{$URL} ;  # or add to @referers, for 301 correction...?

    # Only HTTP URLs are currently supported
    return undef unless $URL=~ /^http:/i ;

    # Any self-referral here indicates a bug in the program.  It's happened.
    die "PROGRAM ERROR: $URL shows its first referer as itself.\n"
        if $referer eq $URL ;

    my(%u) ;
    @u{qw(URL referer depth ishtml iscgi dontfollow)}= 
        ($URL, $referer, $depth, $ishtml, $iscgi, $dontfollow) ;
    $u{'islocal'}= ($URL=~ m#^http://\Q$LOCAL_HOST\E/#io) + 0 ; # make length>0
    if ($u{'islocal'}) {
#        $u{'filename'}= &url_to_filename($URL) ;
        @u{'filename', 'location'}= &url_to_filename($URL) ;
        $u{'iscgi'}= &is_cgi($u{'filename'}, $URL)  if $u{'iscgi'} eq '' ;

	# 2-27-00 JSM:  Detect ishtml by filename, not -T test.
	if ( $u{'ishtml'} eq '' ) {
	    $u{'ishtml'}=  $HTML_BY_NAME
		?  ( !$u{'iscgi'} && -e $u{'filename'} && 
		     $u{'filename'}=~ /\.html?$/i ) + 0
		:  (!$u{'iscgi'} && -e $u{'filename'} && -T _) + 0 ;
	}
#        $u{'ishtml'}= (!$u{'iscgi'} && -e $u{'filename'} && -T _) + 0
#            unless length($u{'ishtml'}) ;

    }

    #  If we're only doing a file check, don't add URLs that require HTTP
    return undef if ($file_check and (!$u{'islocal'} or $u{'iscgi'}) ) ;

    push(@urlstoget, \%u) ;
    $url{$URL}= \%u ;

    # return \%u ;   # unneeded because of previous statement
}


# Guess if a file is a CGI script or not.  Returns true if the (regular) file
#   is executable, has one of @CGI_EXTENSIONS, or if the URL is in a 
#   ScriptAlias'ed directory.
# $fname must be absolute path, but $URL is optional (saves time if available).
# Note that URLs like "/path/script.cgi?a=b" are handled correctly-- the
#   previously extracted filename is tested for CGI-ness, while the URL is
#   checked for ScriptAlias matching (which is unaffected by final query
#   strings or PATH_INFO).
sub is_cgi {
    my($fname, $URL)= @_ ;
    return 1 if (-x $fname && ! -d _ ) ;   # should we really do this?
    foreach (@CGI_EXTENSIONS) { return 1 if $fname=~ /\Q$_\E$/i }

    $URL= &filename_to_url($fname) unless length($URL) ;  # currently unused
    my($URLpath)= $URL=~ m#^http://[^/]*(.*)#i ;
    foreach (keys %SCRIPT_ALIAS)        { return 1 if $URLpath=~ /^\Q$_\E/ }
    foreach (keys %SCRIPT_ALIAS_MATCH)  { return 1 if $URLpath=~ /^$_/ }

    return 0 ;
}
   

# Put the URL in such a form that two URLs that point to the same resource
#   have the same URL, to avoid superfluous retrievals.
# Host name is lowercased elsewhere-- this routine is only called from
#   &add_url; see note there.  To lowercase the host name here would be
#   inefficient.
sub canonicalize {
    my($URL)= @_ ;

    $URL=~ s/#.*// ;    # remove any "#" fragment from end of URL

    return $URL ;
}


#----- File reading/downloading routines (includes networking) --------

# Verify that a URL exists, and set $url->{'status'} accordingly.  Do
#   this either by checking the local filesystem or by using the HTTP HEAD 
#   method for remote sites or CGI scripts.
# Set $url->{'ishtml'} accordingly if discovered from Content-Type:.
# This does not support various Redirect directives in srm.conf.
sub verify_url {
    my($url)= @_ ;

    print STDERR "verifying $url->{'URL'}\n" if $debug ;


    # Depending on the state of $url->{islocal, iscgi, dontfollow} and
    #   $full_http_check, take appropriate actions to check/set the
    #   status code for this URL.
    
    # NOTE: In some situations, specifically when checking a CGI script
    #   named in a <form action> (thus implying that dontfollow is set),
    #   and using HTTP to check the URL (because the script is remote or
    #   $full_http_check is set), the HTTP response code may not be
    #   accurate.  This is because there is no form data sent with the
    #   request, as there normally would be.  In these cases, a cautionary
    #   note is appended to $url->{'status'}.  Additionally, an empty 
    #   $url->{'status'} is changed to an explanatory note (maybe we should
    #   do that in load_url() too?).

    # Use HEAD if file is remote, or if $full_http_check is set.
    if (!$url->{'islocal'} or $full_http_check) {
        &load_url_using_HTTP($url, 'HEAD') ;
        $url->{'status'}= '[no status returned]'
            unless length($url->{'status'}) ;
        $url->{'status'}.= ' (NOTE: Form was not submitted normally)'
            if $url->{'dontfollow'} ;

    # URL is local:  If it's not CGI, do a normal local file check
    } elsif (!$url->{'iscgi'}) {
        $url->{'status'}= (-e $url->{'filename'})  
            ? "200 Local File Exists"  : "404 File Not Found" ;

    # URL is local CGI:  Use HEAD unless dontfollow is set
    } elsif (!$url->{'dontfollow'}) {
        &load_url_using_HTTP($url, 'HEAD') ;

    # Else it's a local CGI with dontfollow set:  Check for executable file
    } else {
        $url->{'status'}= 
             (! -e $url->{'filename'})  ? "404 File Not Found"
           : (! -x $url->{'filename'})  ? "403 Local File Is Not Executable"
           :                              "200 Local Executable File Exists"

    }
        

# Old verify routine below:
#
#    # If is a local non-CGI file, check it directly from the filesystem
#    if ($url->{'islocal'} and !$url->{'iscgi'} and !$full_http_check) {
#        $url->{'status'}= (-e $url->{'filename'})  
#            ? "200 Local File Exists"  : "404 File Not Found" ;
#
#    # Otherwise, download its HEAD from its HTTP server
#    } else {
#        &load_url_using_HTTP($url, 'HEAD') ;
#    }


}



# Load entire file/resource and return its contents, setting $url->{'status'}
#    accordingly.  Do this either by checking the local filesystem or by 
#    using the HTTP GET method for remote sites or CGI scripts.
# Set $url->{'ishtml'} accordingly if discovered from Content-Type:.
# This does not support various Redirect directives in srm.conf.
sub load_url {
    my($url)= @_ ;
    my($HTML) ;

    print STDERR "loading $url->{'URL'}\n" if $debug ;

    # If is a local non-CGI file, read it directly from the filesystem
    if ($url->{'islocal'} and !$url->{'iscgi'} and !$full_http_check) {
        my($iscgi) ;
        ($HTML, $url->{'ssierrs'}, $iscgi)= 
            &read_expanded_file($url->{'filename'}, $url->{'URL'}) ;
        $url->{'status'}= 
            !defined($HTML)
                  ? sprintf("450 Can't read file: %s (%s)", $!, $!+0)
            : @{$url->{'ssierrs'}}
                  ? sprintf("451 SSI Error(s) (%s total)",
                            scalar @{$url->{'ssierrs'}})

            :       "200 Local File Read OK" ;

        # $url->{'iscgi'} may be set if an SHTML file included CGI calls.
        # Don't set it if we're doing a file check, in which case we'll
        #   keep whatever $HTML we could get.
        $url->{'iscgi'}= $iscgi unless $file_check ;
    }

    # Otherwise (or if rereckoned), download the resource from its HTTP server
    if (!$url->{'islocal'} or $url->{'iscgi'} or $full_http_check) {
        (undef, undef, $HTML)= &load_url_using_HTTP($url, 'GET') ;
    }

    # Note that this will be set even when URL is to be reloaded, like
    #   for a 601 (timeout) response.
    $url->{'hasbeenloaded'}= 1 ;
    return $HTML ;
}


# Read a local file and return its contents.  If a file is SSI (aka SHTML),
#   expand any SSI <!--#include--> directives as needed, recursively 
#   including nested files.
# This is used for all local reads, SHTML or not, but the vast bulk of this
#   routine is for SHTML files.
#
# If file is SHTML, this routine also returns a structure of error data,
#   and a boolean saying if this file needs to be downloaded via HTTP
#   for a complete check (e.g. includes CGI calls).
#
# $fname must be canonicalized absolute path, but $URL parameter is optional.
# %$parents contains all "include"-ancestors of the file, to prevent loops.
#   If omitted, assumes no ancestors (and a fresh hash is started).
#
# This routine seems much bigger and more complex than it needs to be.
#   It could be one third the size and much simpler if we didn't have to
#   worry about full error reporting on nested includes.
#
# Note: This routine was made to mimic what Apache would return to a client.
#   However, the result differs from Apache's in two slight ways, both
#   involving nested SSI within <!--#include file="..." -->, and both
#   apparent bugs in Apache 1.1 (may be fixed in later versions):
#
#   1) If a <file="..."> value contains no "/" (i.e. in current directory),
#      then Apache always parses the included file as SHTML, regardless of
#      extension.  This routine checks @SHTML_EXTENSIONS for all included
#      files.
#   2) If a <file="..."> value containing a "/" loads an SHTML file  
#      containing a <virtual="..."> tag with a relative path, the directive
#      fails in Apache.  This routine tries to guess the correct path/URL.
#
#
# Notes on this routine, and SHTML files in general:
#
# At first thought, it seems like we could load each included file
# only once, instead of once for every file that includes it.
# However, because of the fact that relative URLs are resolved
# relative to the top-level including file, the top-level file will
# need to be expanded every time.  (It's legal (though of questionable
# wisdom) to include a file from e.g. both /a/index.shtml and
# /b/index.shtml, so links from the included file point to different
# URLs.)
#
# Note that while URLs in included files (e.g. <a href="...">) are
# resolved relative to the top-level including file, nested include tags
# are resolved relative to the direct includer.
#
# We could possibly be more efficient in time (but costly in memory)
# by storing the expanded contents and $errlist of each included file,
# since those will be constant (except $errlist's include-loop
# reporting might vary somewhat).  There are probably other ways to
# eek out savings of time and memory, at the cost of complexity.
#
# The main loop here is inside of an s/// statement.  Unusual, but it's an
# appropriate way to handle the recursion. Recursion is needed, since each
# included file may or may not be SHTML.
#
# $iscgi is set if a file includes "<!--#exec", or if it contains an
#   <!--#include virtual="..." --> tag that points to a CGI file, or if 
#   any of its include-children sets $iscgi.
#
#
# Notes to help clarify data structures, if (God forbid) you have to modify 
# this routine:
#
# Each error is a list of files in an "include chain", and $errlist is a
# list of errors.  $errlist is associated with the current $HTML.  Each
# error in $errlist is associated with some tag in $HTML, as iterated in
# the s/// loop.  When this routine returns ($HTML, $errlist), the
# errors in $errlist should all have as their first element tags that
# were found in $HTML.
#
# Each error's final element (the "leaf") is associated with a tag that
# tried to load an invalid file.  Each leaf will always be the complete 
# set of errors for that tag (i.e. it has no children, since it couldn't
# load the file).
#
# If the file can be validly loaded, then we may have 0 or multiple errors
# associated with this file/tag (and returned from this routine).  Each
# file's $errlist is an accumulation of all of its children's $errlist's.
#
# Errors that come from loading a child are associated with the child's
# $HTML and tags.  Before adding them to the parent's (current) $errlist,
# they must have the CHILD's path/tag unshifted onto the front of the 
# include chain; all errors are then added to the current $errlist.
# This ensures that:
#   a) The errors are now all associated with the tag that loaded the child.
#   b) The errors in the current $errlist are always associated with tags
#      from the current $HTML.
#

sub read_expanded_file {
    my($fname, $URL, $parents)= @_ ;
    my($HTML, $errlist, $iscgi) ;
    my($isshtml) ;

    $parents->{$fname}= 1 ;

    $HTML= &read_file($fname) ;
    return(undef) unless defined($HTML) ;

    foreach (@SHTML_EXTENSIONS) {
        $isshtml= 1, last if ($fname=~ /\Q$_\E$/i) ;
    }

    if ($isshtml) {
        $errlist= [] ;
        $iscgi= ($HTML=~ /<!--#exec\b/i) ;

        $HTML=~ s{(<!--#include\b.*?>)} {
            do {
                my($childfname, $childURL) ;
                my($childHTML, $childerrlist, $childiscgi) ;
                my($tagst) = $1 ;
                my($tag)= &parse_tag($tagst) ;
              GET_CHILD: {
                  if (length($tag->{'attrib'}{'virtual'})) {
                      $URL= &filename_to_url($fname) unless length($URL) ;
                      $childURL= 
                          &absolute_url($tag->{'attrib'}{'virtual'}, $URL) ;
                      ($childfname)= &url_to_filename($childURL) ;

                      # If it's a CGI, don't follow it, but no error either
                      if (&is_cgi($childfname, $childURL)) {
                          $iscgi= 1 ;
                          last GET_CHILD ;
                      }

                  } elsif (length($tag->{'attrib'}{'file'})) {
                      $childfname= $tag->{'attrib'}{'file'} ;
                      if ($childfname=~ m#^(/|~)#) {
                          push(@$errlist, [ {'path' => $childfname, 
                                             'tag' => $tagst, 'errmsg' =>
                                  'Absolute paths are not allowed in '
                                . '<!--#include file="..." -->.'}]);
                          last GET_CHILD ;
                      }
                      if ($childfname=~ m#\.\.(/|$)#) {
                          push(@$errlist, [ {'path' => $childfname, 
                                             'tag' => $tagst, 'errmsg' =>
                                  'Paths can not contain "../" in '
                                . '<!--#include file="..." -->.'}]);
                          last GET_CHILD ;
                      }
                      $childfname= ($fname=~ m#(.*/)#)[0] . $childfname ;

                  } else {
                      push(@$errlist, [ {'path' => '',
                                         'tag' => $tagst, 'errmsg' =>
                              'Tag must contain either the "file" or '
                            . '"virtual" attribute.'}]);
                      last GET_CHILD ;

                  }

                  # canonicalize filename for %$parents
                  1 while $childfname=~ s#/\.(/|$)#/# ;
                  1 while $childfname=~ s#/(?!\.\./)[^/]+/\.\.(/|$)#/# ;

                  # Guarantee that file exists, is regular, and is readable
                  unless (-e $childfname) {
                      push(@$errlist, [{'path' => $childfname, 'tag' => $tagst,
                                        'errmsg' => 'File not found'} ] ) ;
                      last GET_CHILD ;
                  }
                  unless (-f $childfname) {
                      push(@$errlist, [{'path' => $childfname, 'tag' => $tagst,
                                        'errmsg' => 'File is not a regular'
                                            . ' file.' } ] ) ;
                      last GET_CHILD ;
                  }
                  unless (-r $childfname) {
                      push(@$errlist, [{'path' => $childfname, 'tag' => $tagst,
                                        'errmsg' => 'File is not readable by'
                                            . ' current user.' } ] ) ;
                      last GET_CHILD ;
                  }

                  # Guard against include loops
                  if ($parents->{$childfname}) {
                      push(@$errlist, [{'path' => $childfname, 'tag' => $tagst,
                                        'errmsg' => 'An "include" loop exists'
                                            . ' involving this file.' } ] ) ;
                      last GET_CHILD ;
                  }


                  # Get the included file, with any error data
                  ($childHTML, $childerrlist, $childiscgi)= 
                      &read_expanded_file($childfname, $childURL, $parents) ;

                  # Log if there was any error reading the file
                  push(@$errlist, [{'path' => $childfname, 'tag' => $tagst,
                                    'errmsg' => "Can't read file: $!." } ] )
                      unless defined($childHTML) ;

                  # Add any errors to the current (parent) error list
                  foreach my $error (@$childerrlist) {
                      unshift(@$error, 
                              { 'path' => $childfname, 'tag' => $tagst } ) ;
                  }
                  push(@$errlist, @$childerrlist) ;

                  # Parent is a CGI if any of its children is a CGI
                  $iscgi||= $childiscgi ;
            
              }   # GET_CHILD


              $childHTML ;   # final value to replace in main s/// construct

          }   # do {}

        }gie ;   # $HTML=~ s{} {}

    } # if ($isshtml)

    delete $parents->{$fname} ;

    return($HTML, $errlist, $iscgi) ;
}



# Returns the contents of the named file, or undef on error.
sub read_file {
    my($fname)= @_ ;
    local(*F, $/) ;
 
    undef $/ ;
    open(F, "<$fname") || return undef ;
    my($ret)= <F> ;
    close(F) ;
    
    return $ret ;
}


# Try to get the given URL with the given HTTP method, and return the
#   status line, headers, and body.
# Set $url->{'status'} accordingly, and set $url->{'ishtml'} accordingly
#   if Content-Type: header is returned.
# This is specific to this program, and calls the more general &get_url().
# This could be slightly more efficient if 302 or 303 was handled in the
#   calling routine, where it could take advantage of a new URL being local.
sub load_url_using_HTTP {
    my($url, $method)= @_ ;
    my($status_line, $headers, $body) ;

    # We should not get here if $file_check is set
    die "mistakenly called load_url_using_HTTP($url->{'URL'})" if $file_check ;

    GETFILE: {
        ($status_line, $headers, $body)=
            &get_url( ($url->{'location'} || $url->{'URL'}), $method) ;

        # If HEAD failed (as on some servers), sigh and use GET
        ($status_line, $headers, $body)=
            &get_url( ($url->{'location'} || $url->{'URL'}), 'GET')
                unless length($status_line) ;

        ($url->{'status'})=  $status_line=~ m#^HTTP/[\d.]+\s+(.*)# ;

	# 2-27-00 JSM:  Allow old NCSA servers to not include the HTTP version.
	if ($SUPPORT_NCSA_BUG and $url->{'status'} eq '') {
	    ($url->{'status'})=  $status_line=~ m#^HTTP(?:/[\d.]+)?\s+(.*)# ;
	}

        # Redirect to new location if status is 302 or 303
        if ($url->{'status'}=~ /^(301|302|303)\b/) {
            ($url->{'location'})= $headers=~ m#^Location:[ \t]+(\S+)#im ;
            last GETFILE unless length($url->{'location'}) ;
            $url->{'location'}= 
                &absolute_url($url->{'location'}, $url->{'URL'}) ;
            redo GETFILE
                if    ($url->{'status'}=~ /^(302|303)\b/)
                   && (++$url->{'numredirects'} <= $MAX_REDIRECTS) ;
        }
    }

    $url->{'numtries'}++ ;
    $url->{'lasttried'}= time ;

    # If successful response included Content-Type:, set ishtml accordingly
    $url->{'ishtml'}= (lc($1) eq 'text/html') + 0
        if $url->{'status'}=~ /^2/
           and $headers=~ m#^content-type:[ \t]*(\S+)#im ;

    print STDERR "status: $status_line\n" if $debug ;

    return($status_line, $headers, $body) ;
}


# Request the HTTP resource at the given absolute URL using the given method,
#   and return the response status line, headers, and body.
# jsm-- in the future, this should support downloading to a file, in case
#   the download is too large to fit in memory.
sub get_url {
    my($URL, $method)= @_ ;
    my($host, $uri, $endhost) ;
    my($S, $rin) ;
    my($response, $status_line, $headers, $body, $status_code) ;
    my($content_length) ;
    $method= uc($method) ;
    $method= 'GET' unless length($method) ;

    ($host, $uri)= $URL=~ m#^http://([^/]*)(.*)$#i ;
    $uri= '/' unless length($uri) ;
    $endhost= $host ;

    # use an HTTP proxy if $ENV{'http_proxy'} is set
    USEPROXY: {
        last USEPROXY unless $host=~ /\./ ;
        if (length($ENV{'http_proxy'})) {
            foreach (@NO_PROXY) {
                last USEPROXY if $host=~ /$_$/i ;
            }
            ($host)= $ENV{'http_proxy'}=~ m#^(?:http://)?([^/]*)#i ;
            $uri= $URL ;
        }
    }

    # Open socket
    $S= IO::Socket::INET->new(PeerAddr => $host,  # may contain :port
                              PeerPort => 80,     # default if none in PeerAddr
                              Proto => 'tcp') ;
    return("HTTP/1.1 600 Can't create socket: $@") unless defined($S) ;
    $S->autoflush() ;   # very important!!

    # Send HTTP 1.1 request
    print $S "$method $uri HTTP/1.1\015\012",
             "Host: $endhost\015\012",
             "Connection: close\015\012",
             "User-agent: CheckLinks/$CL_VERSION\015\012",
             "\015\012" ;

    # Wait for socket response with select()
    vec($rin= '', fileno($S), 1)= 1 ;
    select($rin, undef, undef, 60) 
        || return("HTTP/1.1 601 Connection timed out") ;

    local($/)= "\012" ;

    # Handle "100 Continue" responses for HTTP 1.1: loop until non-1xx.
    do {
        $status_line= <$S> ;
        $status_line=~ s/\015?\012$// ;
        ($status_code)= $status_line=~ m#^HTTP/\d+\.\d+\s+(\d+)# ;

        $headers= '' ;
        while (<$S>) {
            last if /^\015?\012/ ;
            $headers.= $_ ;
        }
        $headers=~ s/\015?\012[ \t]+/ /g ;
    } until $status_code!~ /^1/ ;

    # Body length is determined by HTTP 1.1 spec, section 4.4:  these
    #   certain conditions implying no body, then chunked encoding,
    #   then Content-length: header, then server closing connection.
    if ($method eq 'HEAD' or $status_code=~ /^(1|204\b|304\b)/) {
        $body= undef ;

    # else chunked encoding
    } elsif ($headers=~ /^transfer-encoding:[ \t]*chunked\b/im) {
        # 7-16-99:  Old code was only saving last chunk.  Fix using
        #   $this_chunk contributed by Mark Trotter.
        my($this_chunk, $chunk_size, $readsofar, $thisread) ;
        while ($chunk_size= hex(<$S>)) {
            $readsofar= 0 ;
            while ($readsofar!=$chunk_size) {
                last unless $thisread=
                    read($S, $this_chunk, $chunk_size-$readsofar, $readsofar) ;
                $readsofar+= $thisread ;
            }
            return("HTTP/1.1 603 Incomplete chunked response", $headers, $body)
                if $readsofar!=$chunk_size ;
            $_= <$S> ;    # clear CRLF after chunk
            $body.= $this_chunk ;
        }

        # Read footers if they exist
        while (<$S>) {
            last if /^\015?\012/ ;
            $headers.= $_ ;
        }
        $headers=~ s/\015?\012[ \t]+/ /g ;


    # else body length given in Content-length:
    } elsif (($content_length)= $headers=~ /^content-length:[ \t]*(\d+)/im) {
        my($readsofar, $thisread) ;
        while ($readsofar!=$content_length) {
            last unless $thisread=
                read($S, $body, $content_length-$readsofar, $readsofar) ;
            $readsofar+= $thisread ;
        }
        return(sprintf("HTTP/1.1 602 Incomplete response (%s of %s bytes)",
                       $readsofar+0, $content_length),
               $headers, $body)
            if $readsofar!=$content_length ;


    # else body is entire socket output
    } else {
        local($/)= undef ;
        $body= <$S> ;
    }

    close($S) ;

    return($status_line, $headers, $body) ;
}


#----- URL-parsing routines -------------------------------------------

# The routines parse_url(), unparse_url(), and absolute_url() are based on
#   different sections in the Internet Draft "Uniform Resource Identifiers
#   (URI): Generic Syntax and Semantics", 11-18-97, by Berners-Lee,
#   Fielding, and Masinter, filename draft-fielding-uri-syntax-01.

# Parse a URL into its components, according to URI draft, sections 4.3, 4.4.
# This regular expression is straight from Appendix B, modified to use Perl 5.
# Returns scheme, site, path, query, and fragment.  All but path may have
#   the undefined value.
sub parse_url {
    my($URL)= @_ ;
    my($scheme, $site, $path, $query, $fragment)=
        ($URL=~ m{^(?:    ([^:/?\#]+):)?
                   (?: // ([^/?\#]*))?
                          ([^?\#]*)
                   (?: \? ([^\#]*))?
                   (?: \# (.*))?
                 }x
        ) ;
        
        
    # Un-URL-encode the path, to equivalate things like %7E --> ~
    # Note that in some situations, this may cause problems with URLs that
    #   contain the % character: if the unescaped URL is then used in 
    #   relative URL calculation, it may be unescaped again (rare).
    $path=~ s/\+/ /g ;
    $path=~ s/%([0-9A-Fa-f]{2})/chr(hex($1))/ge ;

    # Note that in HTTP, the presence of a host implies a path beginning with
    #   '/', so $path should be '/' for URLs like "http://www.somehost.com"
    $path= '/' if !length($path) && length($site) && lc($scheme) eq 'http' ;

    return($scheme, $site, $path, $query, $fragment) ;

}


# Returns a full URL string, given its components
# The full procedure is described in the URI draft, section 5.2, step 7.
sub unparse_url {
    my($scheme, $site, $path, $query, $fragment)= @_ ;
    my($URL) ;

    $URL= "$scheme:"    if defined($scheme) ;
    $URL.= "//$site"    if defined($site) ;
    $URL.= $path ;
    $URL.= "?$query"    if defined($query) ;
    $URL.= "#$fragment" if defined($fragment) ;

    return $URL ;
}


# Returns a canonicalized absolute URL, given a relative URL and a base URL.
# The full procedure is described in the URI draft, section 5.2.
# Note that a relative URI of "#fragment" should be resolved to "the current
#   document", not to an absolute URL.  This presents a quandary for this
#   routine:  should it always return an absolute URL, thus violating the
#   spec, or should it not always return an absolute URL, thus requiring any
#   caller to check for this special case?  This routine leaves that up to
#   the caller, with $return_rel_fragment-- if set, stick to the spec;
#   otherwise, always return an absolute URL.  See section G.4 of the draft.
# Note that the pathname reduction in steps 6.c-f messes up any PATH_INFO
#   that has ./ or ../ in it, which may be a bug in the spec.
sub absolute_url {
    my($relurl, $baseurl, $return_rel_fragment)= @_ ;
    my(@relurl, @baseurl) ;

    # parse_url() returns scheme, site, path, query, fragment
    @relurl= &parse_url($relurl) ;      # Step 1
    @baseurl= &parse_url($baseurl) ;

    COMBINE: {

        # Step 2
        # See note above about $return_rel_fragment
        if (  $relurl[2] eq '' && 
              !defined($relurl[0]) &&
              !defined($relurl[1]) &&
              !defined($relurl[3]) ) {
            @relurl[0..3]= @baseurl[0..3] ;
            return $relurl if $return_rel_fragment ;   # see note above
            last COMBINE ;
        }

        last COMBINE if defined($relurl[0]) ;    # Step 3
        $relurl[0]= $baseurl[0] ;

        last COMBINE if defined($relurl[1]) ;    # Step 4
        $relurl[1]= $baseurl[1] ;

        last COMBINE if $relurl[2]=~ m#^/# ;     # Step 5

        # Step 6-- resolve relative path
        my($path)= $baseurl[2]=~ m#^(.*/)# ;     # Step 6.a
        $relurl[2]= $path . $relurl[2] ;         # Step 6.b
        
    } # COMBINE

    # Put the remaining steps outside of the block to canonicalize the path.
    # Arguably, this is not allowed.  To avoid such arguments at the expense of
    #   path canonicalization, put steps 6.c-f back in the COMBINE block.

    1 while $relurl[2]=~ s#(^|/)\./#$1# ;    # Step 6.c
    $relurl[2]=~ s#(^|/)\.$#$1# ;            # Step 6.d

    # Step 6.e
    my($oldpath) ;
    while ($relurl[2]=~ s#(([^/]+)/\.\./)# ($2 eq '..')  ? $1  : '' #ge) {
        last if ($relurl[2] eq $oldpath) ;
        $oldpath= $relurl[2] ;
    }

    # Step 6.f
    $relurl[2]=~ s#(([^/]+)/\.\.$)# ($2 eq '..')  ? $1  : '' #ge ;

    # Step 6.g: allow leading ".." segments to remain in path
    # Step 6.h: relurl[2] is already the buffer string

    # To canonicalize further, lowercase the hostname (is this valid for all
    #   schemes?)
    $relurl[1]= lc($relurl[1]) if defined($relurl[1]) ;

    return &unparse_url(@relurl) ;                  # Step 7
}



# Convert a local URL into a canonicalized absolute path, or undef if
#   not on this host or other error.
# Result should only be used as filename.
# Supports UserDir (e.g. public_html) for "/~username/path/file" URLs.
# Supports Alias, AliasMatch, ScriptAlias, and ScriptAliasMatch from srm.conf
#   (but note use of Perl regex's instead of standard regex's).
# Inserts index.html, etc. (from @DIRECTORY_INDEX) if result is a directory,
#   but just return directory name (ending in '/') if none of those exists.
# Removes PATH_INFO, if any, from filename.
# Directory names are always returned with trailing slash (which would not
#   be appropriate if PATH_INFO was to be retained).
# While this routines makes some tests (e.g. if the file is a directory),
#   it does not verify that file at the resulting $filename exists.
# Note that not all URLs point to files, so this routine is not always
#   appropriate.  In this program, the result from this routine is only
#   used when we know the URL is not a CGI script (and is therefore a file),
#   except in &is_cgi() itself, which tests if a file is a CGI script.
#   If it weren't for &is_cgi(), we could ignore cases when the URL isn't
#   a file.
# 12-1-99 JSM:  Changed to also return "redirected" location, in case URL
#   is a directory but not ending in a slash, so relative URLs will resolve
#   correctly against the redirected URL.
sub url_to_filename {
    my($URL)= @_ ;
    my($URLpath, $path, $location, $docroot, $user) ;
    return undef unless $URL=~ m#^http://\Q$LOCAL_HOST\E/#io ;
    $URLpath= (&parse_url($URL))[2] ;
    die "couldn't get path from [$URL]" unless length($URLpath) ;

    # Note minor security hole:  if this script is run setuid, then any 
    #   file on the system could be read by using an ALIAS to point to the 
    #   file.  Note also that if a $URLpath such as "/alias/dir/../.." is
    #   passed to this routine, the alias will be substituted BEFORE the
    #   ".." path segments are traversed.  A case like this probably a
    #   mistake in the URL anyway.

    # Make no more than one alias substitution-- is there a precedence order?
    # Note that %(.*)_MATCH use Perl regex's, not standard regex's.
    # 3-29-99 JSM:  These all alias to actual directory, not to a resulting
    #   URL, so no further conversion should be done if one of these matches.
    # 3-29-99 JSM:  Changed ALIAS_MATCH and SCRIPT_ALIAS_MATCH blocks to
    #   allow $1-type substitution in targets; MUST TEST!
    ALIAS: {
        foreach (keys %ALIAS) 
            { $path= $URLpath, last ALIAS 
                  if $URLpath=~ s/^\Q$_\E/$ALIAS{$_}/ }
        foreach (keys %ALIAS_MATCH) 
            { $path= $URLpath, last ALIAS 
                  if eval "\$URLpath=~ s/^\$_/$ALIAS_MATCH{$_}/" }
        foreach (keys %SCRIPT_ALIAS) 
            { $path= $URLpath, last ALIAS 
                  if $URLpath=~ s/^\Q$_\E/$SCRIPT_ALIAS{$_}/ }
        foreach (keys %SCRIPT_ALIAS_MATCH) 
            { $path= $URLpath, last ALIAS 
                  if eval "\$URLpath=~ s/^\$_/$SCRIPT_ALIAS_MATCH{$_}/" }
    }


    # If $path has been set in above ALIAS block, no further conversion is
    #   needed.  
    if ($path eq '') {

        # Must check for ^/.. before PATH_INFO check, in case $URL's path
        #   is e.g. '/../conf/access.conf'
        return undef if $URLpath=~ m#^/\.\.(/|$)# ;   # ^/.. is not allowed

        # Set $docroot and $path for this file, based on the URL (contains '~' ?)
        if (length($USER_DIR) and ($user,$path)= $URLpath=~ m#^/~([^/]+)(.*)# ) {
            &read_home_dirs unless %home_dir ;   # only read when needed
            return undef unless length($home_dir{$user}) ;
            $docroot= "$home_dir{$user}/$USER_DIR" ;
            $path= '/' unless length($path) ;
        } else {
            # If we have no $DOCUMENT_ROOT, we can't handle URLs without ~.
            return undef unless $DOC_ROOT_EXISTS ;
            $docroot= $DOCUMENT_ROOT ;
            $path= $URLpath ;
        }

        # Handle PATH_INFO: remove path segments until an existing file is named.
        # Note that directories cannot have PATH_INFO after them.
        unless (-e "$docroot$path") {
            for (my($path2)= $path ; $path2=~ m#/# ; $path2=~ s#/[^/]*$##) {
                 last if -d "$docroot$path2" ;
                 $path= $path2, last if -e "$docroot$path2" ;
             }
        }

        # canonicalize path, and recheck for ^/.. (handles an obscure error,
        #   when $URL's path is e.g. '/a/b/../../..'; but must canonicalize
        #   after PATH_INFO check, in case path is e.g. '/a/b.cgi/../../..').
        1 while $path=~ s#/\.(/|$)#/# ;
        1 while $path=~ s#/(?!\.\./)[^/]+/\.\.(/|$)#/# ;
        return undef if $path=~ m#^/\.\.(/|$)# ;   # ^/.. is not allowed

        $path= "$docroot$path" ;

    }


    # Add "index.html", etc. if appropriate
    if (-d $path) {
        $path.= '/' unless $path=~ m#/$# ;
        # 12-1-99 JSM: set "redirected" location also
        $location= "$URL/" unless $URL=~ m#/$# ;
        foreach (@DIRECTORY_INDEX) {
            $path.= $_, last if -f "$path$_" ;
        }
    }
    return ($path, $location) ;
}


# Convert a local (possibly relative) pathname into a canonicalized URL.
# If filename is relative and no $basepath is given, assume it's in the 
#   current directory.
# Supports UserDir (e.g. public_html) for "/~username/path/file" URLs.
# Each path segment is checked to see if it's the same as $DOCUMENT_ROOT,
#   by comparing inodes.  When a match is found, it's cut off the front,
#   and an absolute URL is constructed.  If $DOCUMENT_ROOT is never matched,
#   then $USER_DIR is scanned for.  If that doesn't match (i.e. the file 
#   is not served to the Web), undef is returned.
# Note that $DOC_ROOT_DEV and $DOC_ROOT_INODE are set at the start of the
#   program for efficiency, but are an integral part of this routine.
# %ALIAS is supported using %UN_ALIAS, as best as possible.  See next note
#   on avoiding use of this routine.
# This is currently only used when parsing command-line filenames, and when
#   an <!--#include file="..." --> includes an <!--#include virtual="..." -->
#   (which may be an error anyway).  Thus, it can be avoided if needed, such
#   as when complex aliasing makes results ambiguous.
# jsm-- should this add/remove @DIRECTORY_INDEX, to avoid some duplication?
# 3-29-99 JSM:  Changed UNALIAS handling-- if it's unaliased, then no other
#   conversion is necessary.
sub filename_to_url {
    my($path, $basepath)= @_ ;
    my($URLpath) ;
    unless ($path=~ m#^/#) {
        $basepath= $CWD unless length($basepath) ;
        $basepath.= '/' if -d $basepath && $basepath!~ m#/$# ;
        $basepath=~ s#/[^/]*$#/# ;
        $path= "$basepath$path"  ;
    }

    # canonicalize filename by removing ./ and ../ where appropriate
    1 while $path=~ s#/\.(/|$)#/# ;
    1 while $path=~ s#/(?!\.\./)[^/]+/\.\.(/|$)#/# ;

    # canonicalize directory to include final /
    $path.= '/' if -d $path && $path!~ m#/$# ;

    # First, if path can be unaliased, return that.
    # (Added 3-29-99 by JSM.)
    foreach (keys %UN_ALIAS) 
        { $URLpath= $path, last if $path=~ s/^\Q$_\E/$UN_ALIAS{$_}/ }
    return "http://\L$LOCAL_HOST\E$URLpath" if $URLpath ne '' ;

    # Then, check if file is under $DOCUMENT_ROOT tree, and convert if so.
    if ($DOC_ROOT_EXISTS) {
        my($doc_root)= $path ;
        while ($doc_root=~ s#/[^/]*$##) {
            my($dev,$inode)= stat("$doc_root/.") ;
            if ( ($dev==$DOC_ROOT_DEV) && ($inode==$DOC_ROOT_INODE) ) {
                $path=~ s/^$doc_root// ;
#                foreach (keys %UN_ALIAS) 
#                    { last if $path=~ s/^\Q$_\E/$UN_ALIAS{$_}/ }
                return "http://\L$LOCAL_HOST\E$path" ;
            }
        }
    }

    # Handle possible case of "~username/$USER_DIR/$path"
    # I don't think %ALIAS applies here, does it?
    # This misses some when $HOME/$USER_DIR points through a symbolic link,
    #   and $CWD isn't set to match %dir_to_user.  Work around by avoiding
    #   this routine, e.g. using only URLs on command line.
    if (length($USER_DIR)) {
        if ($path=~ m#^(.*?)/$USER_DIR(/.*)# ) {
            # First, see if path is in %dir_to_user
            &read_home_dirs unless %dir_to_user ;   # only read when needed
            return "http://\L$LOCAL_HOST\E/~$dir_to_user{$1}$2"
                if length($dir_to_user{$1}) ;

            # If not, then we must check inodes to equivalate directories
            &read_inode_to_user unless %inode_to_user ; # only read when needed
            my($dev,$inode)= stat("$1/.") ;
            return "http://\L$LOCAL_HOST\E/~$inode_to_user{$dev}{$inode}$2"
                if length($inode_to_user{$dev}{$inode}) ;
        }
    }

    return undef ;
}



# Reads all users' home directory into %home_dir, from /etc/passwd.
# Also creates %dir_to_user, which is faster than %inode_to_user (below).
# Only used when $USER_DIR is used, for "/~username/path/file" URLs.
# 2-27-00 JSM:  Changed to use getpwent, instead of reading /etc/passwd.
sub read_home_dirs {
    my($user, $homedir) ;

    setpwent ;   # to rewind, in case getpwent has already been used
    while ( ($user, $homedir)= (getpwent)[0,7] ) {
        $home_dir{$user}= $homedir ;
        $dir_to_user{$homedir}= $user
            unless $dir_to_user{$homedir} ne '' ;
    }
    endpwent ;   # clean way to end getpwent processing
}


# Reads home directory inode information into %inode_to_user, from /etc/passwd.
# Because this is time-consuming, it is only called if needed, and only once.
# Only used when $USER_DIR is used, for "/~username/path/file" URLs.
# On SPARCstation-10 with 3000 /etc/passwd records, this takes ~2 seconds.
# 2-27-00 JSM:  Changed to use already-existing %home_dir, instead of reading
#   /etc/passwd again.
sub read_inode_to_user {
    my($user, $homedir) ;
    my($dev, $inode) ;
    &read_home_dirs unless %home_dir ;   # only read when needed

    while ( ($user, $homedir)= each %home_dir ) {
        ($dev,$inode)= stat("$homedir/.") ;
        $inode_to_user{$dev}{$inode}= $user 
            unless $inode_to_user{$dev}{$inode} ne '' ;
    }
}



#----- Extracting URLs from HTML ------------------------------------


# Parse an SGML tag, and return a hash structure with a "name" scalar and
#   an "attrib" hash.
# Parses first tag in string, ignoring all surrounding text.
# Results are canonicalized to lower case wherever case-insensitive.
sub parse_tag {
    my($tag)= @_ ;       # will be mangled
    my($tagname,%attrib) ;

    # only parse first tag in string
    ($tag)= split(/>/, $tag) ;  # remove all after >
    $tag=~ s/^([^<]*<)?\s*// ;  # remove pre-<, <, and leading blanks
    ($tagname,$tag)= split(/\s+/, $tag, 2) ;        # split out tag name

    # Extract name/value (possibly quoted), lowercase name, set $attrib{}.
    # If quoted, is delimited by quotes; if not, delimited by whitespace.
    $attrib{lc($1)}= &HTMLunescape($+)
        while ($tag=~ s/\s*(\w+)\s*=\s*(([^"']\S*)|"([^"]*)"?|'([^']*)'?)//) ;

    # now, get remaining non-valued (boolean) attributes
    $tag=~ s/^\s*|\s*$//g ;             # skip leading/trailing blanks
    foreach (split(/\s+/, $tag)) {
        $_= lc($_) ;
        $attrib{$_}= $_ ;   # booleans have values equal to their name
    }

    return { 'name'   => lc($tagname), 
             'attrib' => \%attrib       } ;
}


# Unescape any HTML character references and return resulting string.
# Support entity character references in %e_to_ch (which is incomplete),
#   plus "$#ddd;" and "&#xdd;" forms for values<256.
# Note that not decoding a valid character is erroneous, in that a
#   subsequent re-escaping will not return the original string, because
#   of the ampersand.  Nonetheless, that's preferable to losing the data.
#   Q:  Is there an appropriate general way to represent an unescaped string?
sub HTMLunescape {
    my($s)= @_ ;

    # Try alpha, decimal, and hex representations, only substituting if valid
    $s=~ s/&(([a-zA-Z][a-zA-Z0-9.-]*);?|#([0-9]+);?|#[Xx]([0-9a-fA-F]+);?)/
              length($2)   ? ( defined($e_to_ch{$2}) ? $e_to_ch{$2}  : "&$1" )
            : length($3)   ? ( $3 < 256              ? chr($3)       : "&$1" )
            : length($4)   ? ( hex($4) < 256         ? chr(hex($4))  : "&$1" )
                           :   "&$1"
          /ge ;

    return $s ;
}


# Given a block of HTML, extracts all URLs referenced in it, and adds them
#   to our data structures to be downloaded or checked (i.e. calls 
#   &add_url()).
# Note that %html_urls and %non_html_urls are set at the start of the
#   program for efficiency, but are an integral part of this routine.
# Currently, this extracts all <.*?> patterns, which may not be valid if
#   "<" or ">" characters are e.g. inside a <script> element.
sub extract_urls {
    my($HTML, $baseurl, $referer, $depth)= @_ ;
    my(@tags) ;

    # Remove comments before extracting links, as pointed out by Tim Hunter.
    $HTML=~ s/<!--.*?--.*?>//gs ;

    # We must look for <base> tag before all the work, so we must parse
    #   all tags first.  :(  Therefore, we save this large array of
    #   structures for efficiency, hoping we don't run out of memory.
    my($i)= -1 ;  # to start at array element 0

    foreach ($HTML=~ /(<.*?>)/gs) {
        $tags[++$i]= &parse_tag($_) ;
        $baseurl= $tags[$i]{'attrib'}{'href'}
            if ($tags[$i]{'name'} eq 'base') 
                and (length($tags[$i]{'attrib'}{'href'})) ;
    }

    # For each tag, call &add_url() for each URL in the tag
    foreach my $tag (@tags) {
        next if $tag->{'name'}=~ m#^/# ;

        # Handle the "regular" tag-attributes, in %html_urls and %non_html_urls

        foreach (@{$html_urls{$tag->{'name'}}}) {
            &add_url(&absolute_url($tag->{'attrib'}{$_}, $baseurl), 
                     $referer, $depth) 
                if length($tag->{'attrib'}{$_}) ;
        }

        foreach (@{$non_html_urls{$tag->{'name'}}}) {
            &add_url(&absolute_url($tag->{'attrib'}{$_}, $baseurl), 
                     $referer, $depth, 0) 
                if length($tag->{'attrib'}{$_}) ;
        }

        # Now handle each tag-attribute that needs special attention

        if ($tag->{'name'} eq 'object') {
            my($codebase)=
                &absolute_url($tag->{'attrib'}{'codebase'}, $baseurl) ;

            &add_url(&absolute_url($tag->{'attrib'}{'data'}, $codebase),
                     $referer, $depth)
                if length($tag->{'attrib'}{'data'}) ;

            # There seems to be a contradiction between the HTML 4.0 spec
            #   section 13.3.3 and RFC 1808 section 4 step 2b regarding
            #   the URL resolution of e.g. classid="java:program.start".
            #   For now, we'll stick with the RFC 1808 method.
            &add_url(&absolute_url($tag->{'attrib'}{'classid'}, $codebase),
                     $referer, $depth, 0)
                if length($tag->{'attrib'}{'classid'}) ;

            # <object> tag's "archive" attribute is a space-separated list
            foreach (split(/\s+/, $tag->{'attrib'}{'archive'})) {
                &add_url(&absolute_url($_, $codebase), $referer, $depth, 0) ;
            }

        } elsif ($tag->{'name'} eq 'head') {
            # "profile" attribute is a space-separated list
            foreach (split(/\s+/, $tag->{'attrib'}{'profile'})) {
                &add_url(&absolute_url($_, $baseurl), $referer, $depth, 0) ;
            }

        } elsif ($tag->{'name'} eq 'applet') {
            my($codebase)=
                &absolute_url($tag->{'attrib'}{'codebase'}, $baseurl) ;

            &add_url(&absolute_url($tag->{'attrib'}{'code'}, $codebase),
                     $referer, $depth, 0)
                if length($tag->{'attrib'}{'code'}) ;

            &add_url(&absolute_url($tag->{'attrib'}{'object'}, $codebase),
                     $referer, $depth, 0)
                if length($tag->{'attrib'}{'object'}) ;

            # <applet> tag's "archive" attribute is a comma-separated list
            foreach (split(/\s*,\s*/, $tag->{'attrib'}{'archive'})) {
                &add_url(&absolute_url($_, $codebase), $referer, $depth, 0) ;
            }

        # Check form script for existence only, but don't follow hyperlinks.
        # Handles the unlikely case when a CGI is referred to by both a
        #   <form action=___.cgi> tag and an <a href=___.cgi> tag: If a CGI
        #   is only pointed to by <form action>, then don't follow the link
        #   (i.e. set $url->{'dontfollow'} to verify, not load).  If a CGI
        #   is called by at least one <a href> tag, then do follow the link.
        } elsif ($tag->{'name'} eq 'form') {
            &add_url(&absolute_url($tag->{'attrib'}{'action'}, $baseurl),
                     $referer, $depth, undef, 1, 1)
                if length($tag->{'attrib'}{'action'}) ;

        }   # if ($tag->{'name'} eq '...')


    }   # foreach $tag (@tags)

}   # &extract_urls()



#----- output routines ------------------------------------------------

# Generate final report
sub make_report {
    if ($verbose_report) { &make_verbose_report }
    else                 { &make_short_report }
}



# Generate a verbose report of all URLs that have been checked
sub make_verbose_report {
    my($rootlist)= join("\n    ", @ARGV) ;
    my($numurls)= scalar keys %url ;

    print <<EOH ;
======================================================================
Report of invalid links on $LOCAL_HOST, 
recursively followed starting with the files/URLs:

    $rootlist

EOH

    if (@INCLUDE_PATTERNS) {
        my($includelist)= join("\n    ", @INCLUDE_PATTERNS) ;
        print <<EOH ;
Only including URLs matching at least one of the following patterns:
    $includelist

EOH
    }

    if (@EXCLUDE_PATTERNS) {
        my($excludelist)= join("\n    ", @EXCLUDE_PATTERNS) ;
        print <<EOH ;
Excluding URLs matching any of the following patterns:
    $excludelist

EOH
    }

    print "Total URLs checked: $numurls\n\n" ;

    print( "Only reporting response codes beginning with: ", 
           join(", ", @INCLUDE_STATUS), "\n" )
        if @INCLUDE_STATUS ;

    print( "Excluding response codes beginning with: ",
           join(", ", @EXCLUDE_STATUS), "\n" )
        if @EXCLUDE_STATUS ;

    print "Maximum traversal depth: $max_depth\n" if length($max_depth) ;
    print "Only local files were checked; no CGI scripts were invoked.\n"
        if $file_check ;
    print "Local URLs were read from the filesystem where possible.\n"
        unless $full_http_check ;

    print "\n" ;

    # Only report status errors if there are any.
    # Using grep()s is slightly inefficient, but a *lot* cleaner.
    my($has_statuserrs) ;
    foreach my $URL (sort keys %url) {
        next if @INCLUDE_STATUS &&
                !grep($url{$URL}{'status'}=~ /^$_/, @INCLUDE_STATUS) ;
        next if grep($url{$URL}{'status'}=~ /^$_/, @EXCLUDE_STATUS) ;

        $has_statuserrs=1, last ;
    }


    if ($has_statuserrs) {
        print <<EOH ;
======================================================================

RESULTS FROM ALL URLS WITH SELECTED RESPONSE STATUS CODES
------------------------------------------------------------

EOH

        foreach (sort keys %url) {
            my($u)= $url{$_} ;

            next if @INCLUDE_STATUS &&
                    !grep($u->{'status'}=~ /^$_/, @INCLUDE_STATUS) ;
            next if grep($u->{'status'}=~ /^$_/, @EXCLUDE_STATUS) ;

            print "$u->{'URL'}\n", '-' x 50, "\n" ;
            print "Status:   $u->{'status'}\n" ;
            print "Moved to: $u->{'location'}\n" if $u->{'location'} ;
            print "Depth:    $u->{'depth'}\n" ;

            for (my($URL)= $u->{'referer'}, my($tab)= '  ' ;
                 length($url{$URL}) ;
                 $URL= $url{$URL}{'referer'}, $tab.= '  ' )
            {
                print "${tab}referred by $url{$URL}{'URL'}\n" ;
                die "PROGRAM ERROR: apparent infinite referer loop.\n"
                    if length($tab)>200 ;      # simple-minded sanity check
            }

            print "\n\n" ;
        }  # URL

    }



    # Only report SSI errors if there are any
    my($has_ssierrs) ;
    foreach (sort keys %url) { 
        $has_ssierrs=1, last if @{$url{$_}{'ssierrs'}} ;
    }


    if ($has_ssierrs) {
        print <<EOH ;
======================================================================

PROBLEMS WITH SERVER-SIDE INCLUDE (AKA SHTML) DIRECTIVES
------------------------------------------------------------

EOH
        foreach (sort keys %url) {
            my($u)= $url{$_} ;
            if (@{$u->{'ssierrs'}}) {
                print "$u->{'URL'}\n", '-' x 50, "\n" ;
                printf "Total %s SSI Errors:\n",  $#{$u->{'ssierrs'}}+1 ;
                foreach my $i (0..$#{$u->{'ssierrs'}}) {
                    printf "  %s) ", $i+1 ;
                    my($tab)= ' ' x (4+length($i+1)) ;
                    my($tab2) ;
                    foreach my $level (@{$u->{'ssierrs'}[$i]}) {
                        print "${tab2}file:   $level->{'path'}\n" ;
                        print "${tab}in tag: $level->{'tag'}\n" ;
                        print "${tab}error:  $level->{'errmsg'}\n" 
                            if $level->{'errmsg'} ;
                        $tab.= '  ' ;
                        $tab2= $tab ;
                    }
                }
                print "\n\n" ;
            }
        }
    }


    unless ($has_statuserrs or $has_ssierrs) {
        print <<EOH ;
======================================================================

                    <<     NO ERRORS FOUND     >>

EOH
    }

    print '=' x 70, "\n" ;

} # &make_verbose_report()


# Generate a one-line-per-URL report
sub make_short_report {
    my($numurls)= scalar keys %url ;

    print "Total $numurls URLs checked\n" ;
    URL: foreach my $URL (sort keys %url) {
        next if @INCLUDE_STATUS &&
                !grep($url{$URL}{'status'}=~ /^$_/, @INCLUDE_STATUS) ;
        next if grep($url{$URL}{'status'}=~ /^$_/, @EXCLUDE_STATUS) ;

        print "$url{$URL}{'URL'}\t$url{$URL}{'status'}\n" ;
    }  # URL
}



# Print a summary of usage and exit
sub usage {
    print <<EOF ;

Checklinks $CL_VERSION

To recursively check all HTML links on the local site, enter:
    $0  <options>  [ start-file | start-URL ] ...

Options include:
  -v                    Generate full (verbose) report, including full
                          referral information and detailed SSI error
                          reporting.
  -I <include-pattern>  Only check URLs matching <include-pattern>.
  -X <exclude-pattern>  Don't check URLs matching <exclude-pattern>.
  -i <include-status>   Only report URLs whose response code starts with
                          the pattern <include-status>.
  -x <exclude-status>   Don't report URLs whose response code starts with
                          the pattern <exclude-status>.  Default is to
                          exclude "200" responses only (i.e. "-x 200").
  -d <max-depth>        Traverse links no deeper than <max-depth>.
  -f                    "File mode"-- only read files from the filesystem;
                          do not go through the HTTP server at all.  This
                          will skip all URLs that point to CGI scripts.
  -h                    "HTTP mode"-- use HTTP to check ALL URLs, even
                          if they could be read from the filesystem.
                          Incompatible with "-f" option.
  -c <config-file>      Read appropriate configuration parameters from
                          <config-file>, typically srm.conf.  Use '-' to
                          read from STDIN.  If a directory is named, use
                          "srm.conf" in that directory.
  -q                    Print current configuration parameters.
  -?                    Print this help message.
  --                    End command-line option processing.

Don't stack options like "-vf"; use "-v -f" instead.

For -I, -X, -i, and -x:
  Values are interpreted as Perl 5 regular expressions.
  Use multiple options to build a list (e.g. "-I include1 -I include2").
  Use a value of '' to clear a list (e.g. -x '' means "report all responses",
    "-x '' -x 401" means "report all but 401 responses").
  As a special case, an empty -I or -i list implies no include-restrictions.
  If an item is in both the include and exclude list, it is excluded.
  Note that -I and -X restrict which URLs are traversed into, so they may
    prune large areas of your Web structure.

EOF
    exit ;
}


#----- debugging routines below ---------------------------------------

# Print current configuration settings
sub print_config {
    print "\n----- OPTIONS SPECIFIC TO THIS EXECUTION -----------------------------\n\n" ;
    
    print "Include only URLs containing one of the following patterns:\n",
          ( map { "    $_\n" } @INCLUDE_PATTERNS ),
          "\n"
        if @INCLUDE_PATTERNS ;

    print "Exclude URLs containing one of the following patterns:\n",
          (map { "    $_\n" } @EXCLUDE_PATTERNS ),
          "\n"
        if @EXCLUDE_PATTERNS ;

    print "Only report response codes beginning with:  ",
          join(", ", @INCLUDE_STATUS), "\n"
        if @INCLUDE_STATUS ;

    print "Don't report response codes beginning with: ",
          join(", ", @EXCLUDE_STATUS), "\n"
        if @EXCLUDE_STATUS ;

    print "\nMaximum search depth:  $max_depth\n" if length($max_depth) ;

    print <<EOS ;

----- INSTALLATION PARAMETERS ----------------------------------------
    
Local Host:           $LOCAL_HOST
Document Root:        $DOCUMENT_ROOT
User Web Directory:   $USER_DIR
Default Filename(s):  @DIRECTORY_INDEX

File extensions indicating a CGI program:       @CGI_EXTENSIONS
File extensions indicating server-parsed HTML:  @SHTML_EXTENSIONS

EOS

    print "Directory Aliases:\n",
          map { sprintf("    %15s ==> %s\n", $_, $ALIAS{$_}) }
              sort keys %ALIAS, 
          "\n"
        if keys %ALIAS ;

    print "Directory Regular Expression Aliases:\n", 
          map { sprintf("    %15s ==> %s\n", $_, $ALIAS_MATCH{$_}) }
              sort keys %ALIAS_MATCH,
          "\n"
        if keys %ALIAS_MATCH ;

    print "Script Directory Aliases:\n", 
          map { sprintf("    %15s ==> %s\n", $_, $SCRIPT_ALIAS{$_}) }
              sort keys %SCRIPT_ALIAS,
          "\n"
        if keys %SCRIPT_ALIAS ;

    print "Script Directory Regular Expression Aliases:\n", 
          map { sprintf("    %15s ==> %s\n", $_, $SCRIPT_ALIAS_MATCH{$_}) }
              sort keys %SCRIPT_ALIAS_MATCH,
          "\n"
        if keys %SCRIPT_ALIAS_MATCH ;

    if ($ENV{'http_proxy'}) {
        print "HTTP Proxy:  $ENV{'http_proxy'}\n" ;
        print "Except to hosts ending in:  $ENV{'no_proxy'}\n" 
            if $ENV{'no_proxy'} ;
        print "\n" ;
    } else {
        print "Not using any HTTP Proxy.\n" ;
    }

    print "Maximum HTTP redirections allowed for a URL:  $MAX_REDIRECTS\n",
          "Maximum number of tries to get a single URL:  $MAX_ATTEMPTS\n\n";
          
    print '-' x 70, "\n\n" ;

}



# print configuration, in a style more for debugging (mostly from srm.conf)
sub print_debug_config {
    print <<EOF ;
DOCUMENT_ROOT=    [$DOCUMENT_ROOT]
USER_DIR=         [$USER_DIR]
DIRECTORY_INDEX=  [@DIRECTORY_INDEX]

CGI_EXTENSIONS=   [@CGI_EXTENSIONS]
SHTML_EXTENSIONS= [@SHTML_EXTENSIONS]

EOF

    foreach (sort keys %ALIAS) 
        { print "ALIAS{$_}= [$ALIAS{$_}]\n" }
    foreach (sort keys %ALIAS_MATCH) 
        { print "ALIAS_MATCH{$_}= [$ALIAS_MATCH{$_}]\n" }
    foreach (sort keys %SCRIPT_ALIAS) 
        { print "SCRIPT_ALIAS{$_}= [$SCRIPT_ALIAS{$_}]\n" }
    foreach (sort keys %SCRIPT_ALIAS_MATCH) 
        { print "SCRIPT_ALIAS_MATCH{$_}= [$SCRIPT_ALIAS_MATCH{$_}]\n" }

}


#----------------------------------------------------------------------
#
#   SPARSE DOCUMENTATION ON PROGRAM INTERNALS:
#
#----------------------------------------------------------------------
#
#   URLs are read directly from the local filesystem if possible, or
#   downloaded or checked with HTTP GET and HEAD methods if not.  CGI
#   scripts are called through the HTTP server, even if local (since the
#   resource their URLs refer to are not files).
#
#
#   Global variables:
#
#     %url holds all data regarding all URLs, using the text URL as the key:
#
#     %url{$URL}{qw( URL filename referer depth
#                    ishtml iscgi islocal dontfollow
#                    status location numredirects numtries lasttried
#                    ssierrs
#                    hasbeenloaded)}  <== only for testing
#         URL is same as hash key
#         ishtml means is type text/html; links MAY be extracted.  (Used in
#           main loop.)
#         iscgi means is a CGI script; MUST NOT be read directly from 
#           filesystem. (Used in verify_url() and load_url().)
#         islocal means served by local server:
#             a) MAY be read directly from filesystem
#             b) links MAY be extracted
#         dontfollow means links MUST NOT be extracted.
#         status begins with a number, but may have text afterward.
#
#         islocal= (URL=~ m#^http://$LOCAL_HOST/#i) , i.e. redundant.
#         ishtml and iscgi are guesses, may be 0, 1, or '' for unset.
#         iscgi only matters for local URLs, but may safely be set for 
#           remote URLs.
#         dontfollow is a hack to handle an obscure CGI-related situation.
#
#     In addition to the standard HTTP status codes, 'status' may take one
#     of the following values:
#         450 Can't read file: $!
#         451 SSI Error(s) (__ total)
#         600 Can't create socket: $@
#         601 Connection timed out
#         602 Incomplete response (%s of %s bytes)
#         603 Incomplete chunked response
#
#     Handling of 602 and 603 is somewhat hackish-- overwrites real status
#       line with artificial one.
#
#     $url->{'ssierrs'} is a list of errors relating to SSI includes.
#       Each error has a list of filenames representing the include
#       chain.  Each element in the chain stores the absolute
#       pathname, the <!--#include--> tag which called it, and
#       possibly an error message (usually only on the last file in
#       the include-chain).  Thus, the entire structure is
#
#         $url->{'ssierrs'}[$errid][$levelsdeep]{qw( path tag errmsg )}
#
#       This is only a memory hog with many errors of deeply nested files.
#
#
#     @urlstoget: canonicalized list of URLs left to get, in order
#         of appearance.  List elements are pointers to %url elements.
#         This array may grow from &extract_urls(), or be rearranged when
#         a URL needs to be retried.
#
#   Note that $url is normally a pointer, and $URL is normally a string.
#
#   Files/paths are canonicalized by removing unneeded "./" and "../"
#     segments.
#   Directories are canonicalized to always end in "/", including in URLs;
#     note that some system variables and local directory variables aren't so.
#   URLs that point to "/" end in "/", e.g. "http://www.foo.com/".
#
#
#   This program has a lot of unused functionality for possible extension,
#   so don't get confused by routines that do more than they are used for.
#
#----------------------------------------------------------------------
#
# To do:
#
#   * If you want a different output format (like in HTML), it should 
#       be easy enough to add.
#   * This could be extended to check remote sites without much trouble.
#   * Should probably support directories that don't have index.html.
#   * Check that pointed-to fragments exist in target files
#   * keep track of servers and don't hit them too often
#   * support robots.txt
#   * add option to read list of URLs from file
#   * support HTTP Basic Authentication somehow.  Note that currently, this
#       reads local files even when they should be protected by .htaccess
#       (unless using -h option).
#   * Read list of local host names from gethostbyname() ?
#   * check read permissions on files?
#   * In the event multiple URLs redirect to the same URL, this could be a
#       little more efficient if it saved the redirected loads/downloads.
#
#----------------------------------------------------------------------
