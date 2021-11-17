/** This file was automatically generated */


#ifndef __Hacl_H
#define __Hacl_H
#include <stdint.h>
#include "kremlin/internal/target.h"
#include "kremlin/internal/types.h"




extern void Lib_Memzero0_memzero(void *x0, uint64_t x1);

extern void Hacl_Hash_Core_SHA2_init_512(uint64_t *s);

extern void Hacl_Hash_SHA2_hash_512(uint8_t *input, uint32_t input_len, uint8_t *dst);

extern void
Hacl_HMAC_compute_sha2_512(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);

typedef struct Hacl_Streaming_SHA2_state_sha2_384_s
{
  uint64_t *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_SHA2_state_sha2_384;

extern void
Hacl_Streaming_SHA2_update_512(
  Hacl_Streaming_SHA2_state_sha2_384 *p,
  uint8_t *data,
  uint32_t len
);

extern void
Hacl_Streaming_SHA2_finish_512(Hacl_Streaming_SHA2_state_sha2_384 *p, uint8_t *dst);

extern void Hacl_Curve25519_64_secret_to_public(uint8_t *pub, uint8_t *priv);

extern bool Hacl_Curve25519_64_ecdh(uint8_t *out, uint8_t *priv, uint8_t *pub);

extern void Lib_RandomBuffer_System_crypto_random(uint8_t *buf, uint32_t len);


#define __Hacl_H_DEFINED
#endif
