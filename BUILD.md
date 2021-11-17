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
