# AMR code make file

MAKEFILENAME=Makefile

#include $(ASTTOPDIR)/Makefile.rules
include ../../Makefile.rules

# Use MODE=DEBUG for debuggable library (default target builds both)
#
# default mode = NORM ==> no debug, no wmops
#

# Use VAD=VAD1 for VAD option 1, or VAD=VAD2 for VAD option 2
#
# default mode = VAD1
#
VAD=VAD1

#
# compiler flags (for normal, DEBUG compilation)
#

CFLAGS = -Wall  -I. -O4 -D$(VAD)
CFLAGSDEPEND = -MM $(CFLAGS)                    # for make depend



#
# source/object files
#

OBJS=sp_enc.o sp_dec.o interf_enc.o interf_dec.o


LIB=libamr.a
#
# default target: build standalone speech encoder and decoder
#
all: $(LIB)

$(LIB): $(OBJS)
	$(ECHO_PREFIX) echo "   [AR] $^ -> $@"
	$(CMD_PREFIX) $(AR) cr $@ $^
	$(CMD_PREFIX) $(RANLIB) $@

#
# make / clean dependency list
#
depend:
	$(MAKE) -f $(MAKEFILENAME) $(MFLAGS) $(MAKEDEFS) clean_depend
	$(CC) $(CFLAGSDEPEND) $(ALL_SRCS) >> $(MAKEFILENAME)

clean_depend:
	chmod u+w $(MAKEFILENAME)
	(awk 'BEGIN{f=1}{if (f) print $0}/^\# DO NOT DELETE THIS LINE -- make depend depends on it./{f=0}'\
	    < $(MAKEFILENAME) > .depend && \
	mv .depend $(MAKEFILENAME)) || exit 1;

#
# remove object/executable files
#
clean:
	rm -f $(LIB) *.o core

# DO NOT DELETE THIS LINE -- make depend depends on it.
sp_enc.o: sp_enc.c sp_enc.h typedef.h rom_enc.h
interf_enc.o: interf_enc.c sp_enc.h typedef.h interf_rom.h rom_dec.h
sp_dec.o: sp_dec.c sp_dec.h rom_dec.h typedef.h
interf_dec.o: interf_dec.c typedef.h sp_dec.h interf_rom.h rom_dec.h