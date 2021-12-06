## Flags and includes

HACL_INCLUDES = \
	-I$(HACL_HOME)/dist/kremlin/include \
	-I$(HACL_HOME)/dist/kremlin/kremlib/dist/minimal

HACL_LIBS = \
	-L$(HACL_HOME)/dist/gcc-compatible -levercrypt

NOISE_STAR_LIBS = -L$(NOISE_STAR_IMPLEMENTATION) -lnoiseapi
INCLUDES = $(HACL_INCLUDES) -I$(NOISE_STAR_IMPLEMENTATION)
LIBS = $(NOISE_STAR_LIBS) $(HACL_LIBS)

## Targets
.PHONY: all
all: ikpsk2-ex.test kk-ex.test

.PHONY: %.test
%.test: %.exe
	DYLD_LIBRARY_PATH=$(HACL_HOME)/dist/gcc-compatible LD_LIBRARY_PATH=$(HACL_HOME)/dist/gcc-compatible ./$<


ikpsk2-ex.test: NOISE_STAR_IMPLEMENTATION := ../noise-all/api-IKpsk2/IKpsk2_25519_ChaChaPoly_SHA256
# I don't understand why it doesn't work without this
ikpsk2-ex.test: ../noise-all/api-IKpsk2/IKpsk2_25519_ChaChaPoly_SHA256/libnoise.a

kk-ex.test: NOISE_STAR_IMPLEMENTATION := ../noise-all/api-KK/KK_25519_ChaChaPoly_SHA256
# I don't understand why it doesn't work without this
kk-ex.test: ../noise-all/api-KK/KK_25519_ChaChaPoly_SHA256/libnoise.a

nk-ex.test: NOISE_STAR_IMPLEMENTATION := ../noise-all/api-NK/NK_25519_ChaChaPoly_SHA256
# I don't understand why it doesn't work without this
nk-ex.test: ../noise-all/api-NK/NK_25519_ChaChaPoly_SHA256/libnoise.a

%.exe: $(NOISE_STAR_IMPLEMENTATION)/libnoise.a %.c
%.exe:
	$(CC) -Wall -Wextra $(INCLUDES) $*.c -o $@ $(LIBS)

.PHONY: %/libnoise.a
%/libnoise.a:
	cd $* && $(MAKE)

.PHONY: clean
clean:
	rm -f *.o *.exe
