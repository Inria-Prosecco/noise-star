/** This file was automatically generated */


#ifndef __Noise_KKpsk2_H
#define __Noise_KKpsk2_H
#include <stdint.h>
#include "krml/internal/target.h"
#include "krml/internal/types.h"


#include "EverCrypt.h"
#include "Hacl.h"

#define Noise_KKpsk2_CSuccess 0
#define Noise_KKpsk2_CIncorrect_transition 1
#define Noise_KKpsk2_CPremessage 2
#define Noise_KKpsk2_CNo_key 3
#define Noise_KKpsk2_CAlready_key 4
#define Noise_KKpsk2_CRs_rejected_by_policy 5
#define Noise_KKpsk2_CRs_not_certified 6
#define Noise_KKpsk2_CAlready_peer 7
#define Noise_KKpsk2_CPeer_conflict 8
#define Noise_KKpsk2_CUnknown_peer_id 9
#define Noise_KKpsk2_CInput_size 10
#define Noise_KKpsk2_CDH_error 11
#define Noise_KKpsk2_CDecrypt_error 12
#define Noise_KKpsk2_CSaturated_nonce 13
#define Noise_KKpsk2_CEphemeral_generation 14
#define Noise_KKpsk2_CSecurity_level 15

typedef uint8_t Noise_KKpsk2_error_code;

bool Noise_KKpsk2_lbytes_eq(uint32_t len, uint8_t *b1, uint8_t *b2);

typedef struct Noise_KKpsk2_sized_buffer_s
{
  uint32_t size;
  uint8_t *buffer;
}
Noise_KKpsk2_sized_buffer;

uint64_t Noise_KKpsk2_bytes_to_nonce(uint8_t *n8);

#define Noise_KKpsk2_Handshake_read 0
#define Noise_KKpsk2_Handshake_write 1
#define Noise_KKpsk2_Transport 2

typedef uint8_t Noise_KKpsk2_status;

typedef uint8_t *Noise_KKpsk2_noise_string;

typedef Noise_KKpsk2_noise_string *Noise_KKpsk2_hstring;

Noise_KKpsk2_error_code Noise_KKpsk2_dh_secret_to_public(uint8_t *dest, uint8_t *priv);

Noise_KKpsk2_error_code Noise_KKpsk2_dh(uint8_t *dest, uint8_t *priv, uint8_t *pub);

void
Noise_KKpsk2_aead_encrypt(
  uint8_t *key,
  uint64_t nonce,
  uint32_t aad_len,
  uint8_t *aad,
  uint32_t plen,
  uint8_t *plain,
  uint8_t *cipher
);

Noise_KKpsk2_error_code
Noise_KKpsk2_aead_decrypt(
  uint8_t *key,
  uint64_t nonce,
  uint32_t aad_len,
  uint8_t *aad,
  uint32_t plen,
  uint8_t *plain,
  uint8_t *cipher
);

void Noise_KKpsk2_hash(uint8_t *output, uint32_t inlen, uint8_t *input);

void Noise_KKpsk2_mix_hash(uint8_t *hash1, uint32_t inlen, uint8_t *input);

void
Noise_KKpsk2_hmac(
  uint8_t *output,
  uint32_t keylen,
  uint8_t *key,
  uint32_t datalen,
  uint8_t *data
);

void
Noise_KKpsk2_kdf(
  uint8_t *hash1,
  uint32_t keylen,
  uint8_t *key,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3
);

void Noise_KKpsk2_mix_psk(uint8_t *psk, uint8_t *st_cs_k, uint8_t *st_ck, uint8_t *st_h);

void
Noise_KKpsk2_encrypt_and_hash(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *cipher,
  uint8_t *st_cs_k,
  uint8_t *st_h,
  uint64_t nonce
);

Noise_KKpsk2_error_code
Noise_KKpsk2_decrypt_and_hash(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *cipher,
  uint8_t *st_cs_k,
  uint8_t *st_h,
  uint64_t nonce
);

Noise_KKpsk2_error_code
Noise_KKpsk2_mix_dh(
  uint8_t *sec,
  uint8_t *pub,
  uint8_t *cipher_key,
  uint8_t *ck,
  uint8_t *hash1
);


#define __Noise_KKpsk2_H_DEFINED
#endif
