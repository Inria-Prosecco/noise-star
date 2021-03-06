/** This file was automatically generated */


#include "Noise_NNpsk2.h"

uint64_t Noise_NNpsk2_bytes_to_nonce(uint8_t *n8)
{
  uint64_t u = load64_le(n8);
  uint64_t nonce = u;
  return nonce;
}

Noise_NNpsk2_error_code Noise_NNpsk2_dh_secret_to_public(uint8_t *dest, uint8_t *priv)
{
  Hacl_Curve25519_64_secret_to_public(dest, priv);
  return Noise_NNpsk2_CSuccess;
}

Noise_NNpsk2_error_code Noise_NNpsk2_dh(uint8_t *dest, uint8_t *priv, uint8_t *pub)
{
  bool b = Hacl_Curve25519_64_ecdh(dest, priv, pub);
  if (b)
    return Noise_NNpsk2_CSuccess;
  else
    return Noise_NNpsk2_CDH_error;
}

void
Noise_NNpsk2_aead_encrypt(
  uint8_t *key,
  uint64_t nonce,
  uint32_t aad_len,
  uint8_t *aad,
  uint32_t plen,
  uint8_t *plain,
  uint8_t *cipher
)
{
  uint8_t n12[12U] = { 0U };
  uint8_t *nonce12_end = n12 + (uint32_t)4U;
  store64_le(nonce12_end, nonce);
  uint8_t *output = cipher;
  uint8_t *tag = cipher + plen;
  Hacl_Chacha20Poly1305_32_aead_encrypt(key, n12, aad_len, aad, plen, plain, output, tag);
  Lib_Memzero0_memzero(n12, (uint32_t)12U * sizeof (n12[0U]));
}

Noise_NNpsk2_error_code
Noise_NNpsk2_aead_decrypt(
  uint8_t *key,
  uint64_t nonce,
  uint32_t aad_len,
  uint8_t *aad,
  uint32_t plen,
  uint8_t *plain,
  uint8_t *cipher
)
{
  uint8_t n12[12U] = { 0U };
  uint8_t *nonce12_end = n12 + (uint32_t)4U;
  store64_le(nonce12_end, nonce);
  uint8_t *output = cipher;
  uint8_t *tag = cipher + plen;
  uint32_t
  r = Hacl_Chacha20Poly1305_32_aead_decrypt(key, n12, aad_len, aad, plen, plain, output, tag);
  Lib_Memzero0_memzero(n12, (uint32_t)12U * sizeof (n12[0U]));
  if (r == (uint32_t)0U)
    return Noise_NNpsk2_CSuccess;
  else
    return Noise_NNpsk2_CDecrypt_error;
}

void Noise_NNpsk2_hash(uint8_t *output, uint32_t inlen, uint8_t *input)
{
  Hacl_Hash_SHA2_hash_256(input, inlen, output);
}

void Noise_NNpsk2_mix_hash(uint8_t *hash1, uint32_t inlen, uint8_t *input)
{
  uint8_t buf[64U] = { 0U };
  uint32_t block_state[8U] = { 0U };
  Hacl_Streaming_SHA2_state_sha2_224
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  Hacl_Streaming_SHA2_state_sha2_224 p = s;
  Hacl_Hash_Core_SHA2_init_256(block_state);
  Hacl_Streaming_SHA2_state_sha2_224 *s0 = &p;
  Hacl_Streaming_SHA2_update_256(s0, hash1, (uint32_t)32U);
  Hacl_Streaming_SHA2_update_256(s0, input, inlen);
  Hacl_Streaming_SHA2_finish_256(s0, hash1);
}

void
Noise_NNpsk2_hmac(
  uint8_t *output,
  uint32_t keylen,
  uint8_t *key,
  uint32_t datalen,
  uint8_t *data
)
{
  Hacl_HMAC_compute_sha2_256(output, key, keylen, data, datalen);
}

void
Noise_NNpsk2_kdf(
  uint8_t *hash1,
  uint32_t keylen,
  uint8_t *key,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3
)
{
  uint8_t output[33U] = { 0U };
  uint8_t secret[32U] = { 0U };
  uint8_t *output_hash = output;
  uint8_t *output1 = output;
  Noise_NNpsk2_hmac(secret, (uint32_t)32U, hash1, keylen, key);
  if (!(dst1 == NULL))
  {
    output[0U] = (uint8_t)1U;
    Noise_NNpsk2_hmac(output_hash, (uint32_t)32U, secret, (uint32_t)1U, output1);
    memcpy(dst1, output_hash, (uint32_t)32U * sizeof (uint8_t));
    if (!(dst2 == NULL))
    {
      output[32U] = (uint8_t)2U;
      Noise_NNpsk2_hmac(output_hash, (uint32_t)32U, secret, (uint32_t)33U, output);
      memcpy(dst2, output_hash, (uint32_t)32U * sizeof (uint8_t));
      if (!(dst3 == NULL))
      {
        output[32U] = (uint8_t)3U;
        Noise_NNpsk2_hmac(output_hash, (uint32_t)32U, secret, (uint32_t)33U, output);
        memcpy(dst3, output_hash, (uint32_t)32U * sizeof (uint8_t));
      }
    }
  }
  Lib_Memzero0_memzero(output, (uint32_t)33U * sizeof (output[0U]));
  Lib_Memzero0_memzero(secret, (uint32_t)32U * sizeof (secret[0U]));
}

void Noise_NNpsk2_mix_psk(uint8_t *psk, uint8_t *st_cs_k, uint8_t *st_ck, uint8_t *st_h)
{
  uint8_t temp_hash[32U] = { 0U };
  Noise_NNpsk2_kdf(st_ck, (uint32_t)32U, psk, st_ck, temp_hash, st_cs_k);
  Noise_NNpsk2_mix_hash(st_h, (uint32_t)32U, temp_hash);
  Lib_Memzero0_memzero(temp_hash, (uint32_t)32U * sizeof (temp_hash[0U]));
}

void
Noise_NNpsk2_encrypt_and_hash(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *cipher,
  uint8_t *st_cs_k,
  uint8_t *st_h,
  uint64_t nonce
)
{
  Noise_NNpsk2_aead_encrypt(st_cs_k, nonce, (uint32_t)32U, st_h, msg_len, msg, cipher);
  uint32_t cipher_len = msg_len + (uint32_t)16U;
  Noise_NNpsk2_mix_hash(st_h, cipher_len, cipher);
}

Noise_NNpsk2_error_code
Noise_NNpsk2_decrypt_and_hash(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *cipher,
  uint8_t *st_cs_k,
  uint8_t *st_h,
  uint64_t nonce
)
{
  Noise_NNpsk2_error_code
  r1 = Noise_NNpsk2_aead_decrypt(st_cs_k, nonce, (uint32_t)32U, st_h, msg_len, msg, cipher);
  if (r1 == Noise_NNpsk2_CSuccess)
  {
    Noise_NNpsk2_mix_hash(st_h, msg_len + (uint32_t)16U, cipher);
    return Noise_NNpsk2_CSuccess;
  }
  else
    return r1;
}

Noise_NNpsk2_error_code
Noise_NNpsk2_mix_dh(
  uint8_t *sec,
  uint8_t *pub,
  uint8_t *cipher_key,
  uint8_t *ck,
  uint8_t *hash1
)
{
  uint8_t dh_key[32U] = { 0U };
  Noise_NNpsk2_error_code r1 = Noise_NNpsk2_dh(dh_key, sec, pub);
  Noise_NNpsk2_error_code r2;
  if (r1 == Noise_NNpsk2_CSuccess)
  {
    Noise_NNpsk2_kdf(ck, (uint32_t)32U, dh_key, ck, cipher_key, NULL);
    r2 = Noise_NNpsk2_CSuccess;
  }
  else
    r2 = r1;
  Noise_NNpsk2_error_code r = r2;
  Lib_Memzero0_memzero(dh_key, (uint32_t)32U * sizeof (dh_key[0U]));
  return r;
}

