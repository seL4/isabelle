# $Id$
# This Makefile allows the common theory for security logics to be
#	built separately.
#
BIN = $(ISABELLEBIN)
COMP = $(ISABELLECOMP)
NAMES = Message Shared NS_Shared OtwayRees OtwayRees_AN Yahalom

FILES = DB-ROOT.ML $(NAMES:%=%.thy) $(NAMES:%=%.ML)

$(BIN)/Auth:   $(BIN)/HOL  $(FILES) 
	if [ -d $${ISABELLEBIN:?}/Pure ];\
           	then echo Bad value for ISABELLEBIN: \
                	$(BIN) is the Isabelle source directory; \
                	exit 1; \
           	fi;\
	case "$(COMP)" in \
	poly*)	echo 'make_database"$(BIN)/Auth"; quit();'  \
		  | $(COMP) $(BIN)/HOL;\
                if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'open PolyML; init_html(); exit_use"DB-ROOT.ML";' \
                       | $(COMP) $(BIN)/Auth;\
		elif [ "$${MAKE_HTML-undefined}" != "undefined" ]; \
                then echo 'open PolyML; init_html(); exit_use"DB-ROOT.ML";                               make_html := false;' | $(COMP) $(BIN)/Auth;\
                else echo 'open PolyML; exit_use"DB-ROOT.ML";' \
                       | $(COMP) $(BIN)/Auth;\
                fi;\
		discgarb -c $(BIN)/Auth;;\
	sml*)	if [ "$${MAKE_HTML}" = "true" ]; \
                then echo 'init_html(); exit_use"DB-ROOT.ML";                                            xML"$(BIN)/Auth" banner;' | $(BIN)/HOL;\
                elif [ "$${MAKE_HTML-undefined}" != "undefined" ];\
                then echo 'init_html(); exit_use"DB-ROOT.ML";                                            make_html := false; xML"$(BIN)/Auth" banner;' \
                       | $(BIN)/HOL;\
                else echo 'exit_use"DB-ROOT.ML"; xML"$(BIN)/Auth" banner;' \
                       | $(BIN)/HOL;\
                fi;;\
	*)	echo Bad value for ISABELLECOMP: \
                	$(COMP) is not poly or sml; exit 1;;\
	esac

$(BIN)/HOL:
	cd ..;  $(MAKE)

.PRECIOUS:  $(BIN)/HOL $(BIN)/Auth 
