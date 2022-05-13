/** This file was automatically generated */


#ifndef __Hacl_H
#define __Hacl_H
#include <stdint.h>
#include "krml/internal/target.h"
#include "krml/internal/types.h"




#define Spec_Blake2_Blake2S 0
#define Spec_Blake2_Blake2B 1

typedef uint8_t Spec_Blake2_alg;

extern void Lib_Memzero0_memzero(void *x0, uint64_t x1);

#define Hacl_Impl_Blake2_Core_M32 0
#define Hacl_Impl_Blake2_Core_M128 1
#define Hacl_Impl_Blake2_Core_M256 2

typedef uint8_t Hacl_Impl_Blake2_Core_m_spec;

extern void
Hacl_Blake2s_32_blake2s_init(
  uint32_t *wv,
  uint32_t *hash,
  uint32_t kk,
  uint8_t *k,
  uint32_t nn
);

extern void
Hacl_Blake2s_32_blake2s(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *k
);

extern void
Hacl_HMAC_compute_blake2s_32(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);

extern uint32_t
Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_alg a, Hacl_Impl_Blake2_Core_m_spec m);

typedef struct Hacl_Streaming_Blake2_blake2s_32_block_state_s
{
  uint32_t *fst;
  uint32_t *snd;
}
Hacl_Streaming_Blake2_blake2s_32_block_state;

typedef struct Hacl_Streaming_Blake2_blake2s_32_state_s
{
  Hacl_Streaming_Blake2_blake2s_32_block_state block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_Blake2_blake2s_32_state;

/*
  Update function when there is no key
*/
extern void
Hacl_Streaming_Blake2_blake2s_32_no_key_update(
  Hacl_Streaming_Blake2_blake2s_32_state *p,
  uint8_t *data,
  uint32_t len
);

/*
  Finish function when there is no key
*/
extern void
Hacl_Streaming_Blake2_blake2s_32_no_key_finish(
  Hacl_Streaming_Blake2_blake2s_32_state *p,
  uint8_t *dst
);

extern void Hacl_Curve25519_64_secret_to_public(uint8_t *pub, uint8_t *priv);

extern bool Hacl_Curve25519_64_ecdh(uint8_t *out, uint8_t *priv, uint8_t *pub);

extern void Lib_RandomBuffer_System_crypto_random(uint8_t *buf, uint32_t len);


#define __Hacl_H_DEFINED
#endif
