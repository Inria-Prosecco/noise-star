/** This file was automatically generated */


#ifndef __Noise_NN_H
#define __Noise_NN_H
#include <stdint.h>
#include "krml/internal/target.h"
#include "krml/internal/types.h"


#include "Hacl.h"

#define Noise_NN_CSuccess 0
#define Noise_NN_CIncorrect_transition 1
#define Noise_NN_CPremessage 2
#define Noise_NN_CNo_key 3
#define Noise_NN_CAlready_key 4
#define Noise_NN_CRs_rejected_by_policy 5
#define Noise_NN_CRs_not_certified 6
#define Noise_NN_CAlready_peer 7
#define Noise_NN_CPeer_conflict 8
#define Noise_NN_CUnknown_peer_id 9
#define Noise_NN_CInput_size 10
#define Noise_NN_CDH_error 11
#define Noise_NN_CDecrypt_error 12
#define Noise_NN_CSaturated_nonce 13
#define Noise_NN_CEphemeral_generation 14
#define Noise_NN_CSecurity_level 15

typedef uint8_t Noise_NN_error_code;

typedef struct Noise_NN_sized_buffer_s
{
  uint32_t size;
  uint8_t *buffer;
}
Noise_NN_sized_buffer;

#define Noise_NN_Handshake_read 0
#define Noise_NN_Handshake_write 1
#define Noise_NN_Transport 2

typedef uint8_t Noise_NN_status;

typedef uint8_t *Noise_NN_noise_string;

typedef Noise_NN_noise_string *Noise_NN_hstring;

Noise_NN_error_code Noise_NN_dh_secret_to_public(uint8_t *dest, uint8_t *priv);

Noise_NN_error_code Noise_NN_dh(uint8_t *dest, uint8_t *priv, uint8_t *pub);

void
Noise_NN_aead_encrypt(
  uint8_t *key,
  uint64_t nonce,
  uint32_t aad_len,
  uint8_t *aad,
  uint32_t plen,
  uint8_t *plain,
  uint8_t *cipher
);

Noise_NN_error_code
Noise_NN_aead_decrypt(
  uint8_t *key,
  uint64_t nonce,
  uint32_t aad_len,
  uint8_t *aad,
  uint32_t plen,
  uint8_t *plain,
  uint8_t *cipher
);

void Noise_NN_hash(uint8_t *output, uint32_t inlen, uint8_t *input);

void Noise_NN_mix_hash(uint8_t *hash1, uint32_t inlen, uint8_t *input);

void
Noise_NN_hmac(uint8_t *output, uint32_t keylen, uint8_t *key, uint32_t datalen, uint8_t *data);

void
Noise_NN_kdf(
  uint8_t *hash1,
  uint32_t keylen,
  uint8_t *key,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3
);

void Noise_NN_mix_psk(uint8_t *psk, uint8_t *st_cs_k, uint8_t *st_ck, uint8_t *st_h);

void
Noise_NN_encrypt_and_hash(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *cipher,
  uint8_t *st_cs_k,
  uint8_t *st_h,
  uint64_t nonce
);

Noise_NN_error_code
Noise_NN_decrypt_and_hash(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *cipher,
  uint8_t *st_cs_k,
  uint8_t *st_h,
  uint64_t nonce
);

Noise_NN_error_code
Noise_NN_mix_dh(uint8_t *sec, uint8_t *pub, uint8_t *cipher_key, uint8_t *ck, uint8_t *hash1);


#define __Noise_NN_H_DEFINED
#endif
