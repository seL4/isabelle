// Little utility to convert result() -> qed ... in Isabelle's files
// Written in 1995 by Carsten Clasohm (clasohm@informatik.tu-muenchen.de)

#define LIN_LEN   1000		// maximal length of lines in sourcefile

#include <iostream.h>
#include <fstream.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>
#include <unistd.h>
#include <ctype.h>

// Null terminated list of theorem names that must not be included in the
// theorem database
char * excludeName[] = {"temp", "tmp", 0};

int ExcludeThm(char *name)
{
    for (int i = 0; excludeName[i]; i++)
	if (strcmp(name, excludeName[i]) == 0)
	    return 1;
    return 0;
}

main(int argc, char *argv[])
{
    char l[LIN_LEN];
    int lines = 0;

    // Open input and output files
    ifstream in(argv[1]);
    ofstream out(argv[2]);

    if (in.bad() || out.bad())
    {
        cerr << "qed version 1.00, Written in 1994 by Carsten Clasohm"
                "(clasohm@informatik.tu-muenchen.de)\n\n";
	cerr << "Usage: qed <infile> <outfile>\n";
	exit(1);
    }

#ifdef DEBUG
    cerr << "Processing file " << argv[1] << '\n';
#endif

    // Process each line separatly
    in.getline(l, LIN_LEN);
    while (!in.eof())
    {
	char *rPos;
	char *valPos;
	char *eqPos;
	char *tmp;

	if ((rPos = strstr(l, "result()")) && (!isalnum(*(rPos-1)))
	    && (valPos = strstr(l, "val ")) && (eqPos = strstr(l, "=")))
	{                            // does line contain "result()" and "val"?
	    char name[LIN_LEN];

	    assert(eqPos-(valPos+4) > 0);
	    strncpy(name, valPos+4, eqPos-(valPos+4));
	    name[eqPos-(valPos+4)] = 0;
	    if (!isalnum(name[eqPos-(valPos+4)-1]))
	        name[eqPos-(valPos+4)-1] = 0;
#ifdef DEBUG
	    cerr << "Found result: \"" << name << "\"\n";
#endif
	    char prefix[LIN_LEN];
	    char arg[LIN_LEN];

	    if (ExcludeThm(name))
		out << l << '\n';
	    else if ((rPos - eqPos < 5) && (rPos == strstr(l, "result();")))
	    {                                              // replace by "qed"?
		strncpy(prefix, l, valPos-l);
		prefix[valPos-l] = 0;
		out << prefix << "qed \"" << name << "\";" << '\n';
	    }
	    else				         // replace by bind_thm
	    {                                           
		int d = (*(eqPos+1) == ' ') ? 2 : 1;
		strcpy(arg, eqPos+d);
		arg[strlen(arg)-1] = 0;
		strcpy(prefix, l);
		prefix[valPos-l] = 0;
		out << prefix << "bind_thm(\"" << name << "\", "
		    << arg << ");\n";
	    }
	}
	else if ((rPos = strstr(l, "prove_goal")) 
		 && (!isalnum(*(rPos-1))) 
		 && (!isalnum(*(rPos+10)) || (*(rPos+10) == 'w'))
		 && (valPos = strstr(l, "val ")) 
		 && (eqPos = strstr(l, "="))
                 && (rPos - eqPos < 5))
	{                                    // replace prove_goal by qed_goal?
	    char name[LIN_LEN];

	    assert(eqPos-(valPos+4) > 0);
	    strncpy(name, valPos+4, eqPos-(valPos+4));
	    name[eqPos-(valPos+4)] = 0;
	    if (!isalnum(name[eqPos-(valPos+4)-1]))
	        name[eqPos-(valPos+4)-1] = 0;
#ifdef DEBUG
	    cerr << "Found prove_goal: \"" << name << "\"\n";
#endif
	    if (ExcludeThm(name))
		out << l << '\n';
	    else
	    {
	        char prefix[LIN_LEN];
	        char arg[LIN_LEN];

	        strncpy(prefix, l, valPos-l);
	        prefix[valPos-l] = 0;
	        out << prefix << "qed_goal"
                    << ((*(rPos+10) == 'w') ? "w " : " ")
		    << '\"' << name << '\"' << strchr(rPos, ' ') << '\n';
	    }
	}
	else if ((rPos = strstr(l, "standard"))
		 && (!isalnum(*(rPos-1))) 
		 && (!isalnum(*(rPos+8))) 
		 && (valPos = strstr(l, "val ")) 
		 && (eqPos = strstr(l, "="))
                 && (rPos - eqPos < 5)
                 && (l[strlen(l)-1] == ';'))
	{                                                   // insert bind_thm?
	    char name[LIN_LEN];

	    assert(eqPos-(valPos+4) > 0);
	    strncpy(name, valPos+4, eqPos-(valPos+4));
	    name[eqPos-(valPos+4)] = 0;
	    if (!isalnum(name[eqPos-(valPos+4)-1]))
	        name[eqPos-(valPos+4)-1] = 0;
#ifdef DEBUG
	    cerr << "Found standard: \"" << name << "\"\n";
#endif
	    if (ExcludeThm(name))
		out << l << '\n';
	    else
	    {
	        char prefix[LIN_LEN];
	        char arg[LIN_LEN];

	        strncpy(prefix, l, valPos-l);
	        prefix[valPos-l] = 0;
	        strcpy(l+strlen(l)-1, ");");    // insert ")" before line's ';'
	        out << prefix << "bind_thm (\"" << name << "\","
	            << strchr(rPos, ' ') << '\n';
            }
	}
	else                                           // output line unchanged
	    out << l << '\n';
	in.getline(l, LIN_LEN);
    }
    in.close();
    out.close();
#ifdef DEBUG
    cerr << "Done\n";
#endif
}
