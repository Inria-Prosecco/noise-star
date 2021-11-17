## Flags and includes
HACL_INCLUDES = \
	-I$(HACL_HOME)/dist/kremlin/include -I$(HACL_HOME)/dist/gcc-compatible \
	-I$(HACL_HOME)/dist/kremlin/kremlib/dist/minimal
HACL_LIBS = \
	-L$(HACL_HOME)/dist/gcc-compatible -levercrypt \
	-Wl,-rpath=$(HACL_HOME)/dist/gcc-compatible


NOISE_STAR_IMPLEMENTATION = ../noise-all/api-IKpsk2/IKpsk2_25519_ChaChaPoly_SHA256
NOISE_STAR_LIBS = \
	-L$(NOISE_STAR_IMPLEMENTATION) \
	-lnoiseapi

INCLUDES = \
	$(HACL_INCLUDES) \
	-I$(NOISE_STAR_IMPLEMENTATION)
LIBS = $(NOISE_STAR_LIBS) $(HACL_LIBS)

## Targets
.PHONY: all
all: ikpsk2-ex.test

.PHONY: %.test
%.test: %.exe
	./$<

lnoiseapi.a:
	cd $(NOISE_STAR_IMPLEMENTATION) && make -j

ikpsk2-ex.exe: lnoiseapi.a
	gcc $(INCLUDES) ikpsk2-ex.c -o $@ $(LIBS)

.PHONY: clean
clean:
	rm -f *.o *.exe
