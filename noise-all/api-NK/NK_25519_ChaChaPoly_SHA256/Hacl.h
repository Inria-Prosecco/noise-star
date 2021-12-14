/** This file was automatically generated */


#ifndef __Hacl_H
#define __Hacl_H
#include <stdint.h>
#include "kremlin/internal/target.h"
#include "kremlin/internal/types.h"




extern void Lib_Memzero0_memzero(void *x0, uint64_t x1);

extern void Hacl_Hash_Core_SHA2_init_256(uint32_t *s);

extern void Hacl_Hash_SHA2_hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst);

extern void
Hacl_HMAC_compute_sha2_256(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);

typedef struct Hacl_Streaming_SHA2_state_sha2_224_s
{
  uint32_t *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_SHA2_state_sha2_224;

extern void
Hacl_Streaming_SHA2_update_256(
  Hacl_Streaming_SHA2_state_sha2_224 *p,
  uint8_t *data,
  uint32_t len
);

extern void
Hacl_Streaming_SHA2_finish_256(Hacl_Streaming_SHA2_state_sha2_224 *p, uint8_t *dst);

extern void
Hacl_Chacha20Poly1305_32_aead_encrypt(
  uint8_t *k,
  uint8_t *n,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t mlen,
  uint8_t *m,
  uint8_t *cipher,
  uint8_t *mac
);

extern uint32_t
Hacl_Chacha20Poly1305_32_aead_decrypt(
  uint8_t *k,
  uint8_t *n,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t mlen,
  uint8_t *m,
  uint8_t *cipher,
  uint8_t *mac
);

extern void Hacl_Curve25519_51_secret_to_public(uint8_t *pub, uint8_t *priv);

extern bool Hacl_Curve25519_51_ecdh(uint8_t *out, uint8_t *priv, uint8_t *pub);

extern void Lib_RandomBuffer_System_crypto_random(uint8_t *buf, uint32_t len);


#define __Hacl_H_DEFINED
#endif
