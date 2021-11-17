## Flags and includes

HACL_INCLUDES = \
	-I$(HACL_HOME)/dist/kremlin/include \
	-I$(HACL_HOME)/dist/kremlin/kremlib/dist/minimal

HACL_LIBS = \
	-L$(HACL_HOME)/dist/gcc-compatible -levercrypt


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
	DYLD_LIBRARY_PATH=$(HACL_HOME)/dist/gcc-compatible LD_LIBRARY_PATH=$(HACL_HOME)/dist/gcc-compatible ./$<

.PHONY: $(NOISE_STAR_IMPLEMENTATION)/libnoise.a
$(NOISE_STAR_IMPLEMENTATION)/libnoise.a:
	cd $(NOISE_STAR_IMPLEMENTATION) && $(MAKE)

ikpsk2-ex.exe: $(NOISE_STAR_IMPLEMENTATION)/libnoise.a
	$(CC) $(INCLUDES) ikpsk2-ex.c -o $@ $(LIBS)

.PHONY: clean
clean:
	rm -f *.o *.exe
