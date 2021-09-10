# $Header: /cvsroot/gpvn/prolog/Makefile,v 1.1 2002/01/23 14:00:27 oommoo Exp $

CC        = gcc
CFLAGS    = -c 
CINCLUDES = -I/usr/local/gprolog-1.2.1/include/ 
CLIBS     = 
DFLAGS    = -g -DADWDEBUG
GP        = gplc
GPFLAGS   = --no-del-temp --temp-dir ./tmp

TARGETS   = gpvn

all: $(TARGETS)
	@echo Make all done.

gpvn: gpvn.pl
	$(GP) $(GPFLAGS) gpvn.pl

clean:
	rm -f *.o *~ gpvn
	rm -f ./tmp/*


# 
# $Log: Makefile,v $
# Revision 1.1  2002/01/23 14:00:27  oommoo
# incremental
# 
# 