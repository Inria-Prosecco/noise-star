Build Instructions
==================

Clone and build HACL\*.

```bash
git checkout https://github.com/project-everest/hacl-star
cd hacl-star
export HACL_HOME=$(pwd)
cd dist/gcc-compatible
make -j
```

Then, navigate to one of the directories you are interested in:

```bash
cd api-IKpsk2/IKpsk2_25519_ChaChaPoly_SHA256
make -j
```

In order to link a final executable, remember to pass
`-L$HACL-HOME/dist/gcc-compatible -levercrypt` to the linker (after
`-lnoiseapi`).

Example
=======

See `examples` for an example of usuage of the API.
Building and running the example simply requires executing `make` in the subdirectory,
after HACL* and Noise\* have been properly built.

The example uses IKpsk2, with Curve25519, ChaChaPoly and SHA256 (non-optimized
implementations).

Verified Implementation
=======================

The formally verified, generic implementation is in `src/`.

Specific Choices of Cryptographic Implementations
=================================================

There are a lot of cipher suites, and most of the cryptographic primitives have
several (optimized) implementations. Because there are too many of them, we only
generate implementations for specific choices of cryptographic primitive
implementations. If you desire a specific choice of implementations made available
by the [Hacl\*](https://github.com/project-everest/hacl-star) library, feel free
to contact the authors.
