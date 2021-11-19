/** This file was automatically generated */


#include "Noise_NKpsk2.h"

inline bool Noise_NKpsk2_lbytes_eq(uint32_t len, uint8_t *b1, uint8_t *b2)
{
  uint8_t accp = (uint8_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint8_t x1 = b1[i];
    uint8_t x2 = b2[i];
    uint8_t diff = x1 ^ x2;
    uint8_t acc = accp;
    uint8_t acc_ = diff | acc;
    accp = acc_;
  }
  uint8_t r = accp;
  return r == (uint8_t)0U;
}

uint64_t Noise_NKpsk2_bytes_to_nonce(uint8_t *n8)
{
  uint64_t u = load64_le(n8);
  uint64_t nonce = u;
  return nonce;
}

Noise_NKpsk2_error_code Noise_NKpsk2_dh_secret_to_public(uint8_t *dest, uint8_t *priv)
{
  Hacl_Curve25519_64_secret_to_public(dest, priv);
  return Noise_NKpsk2_CSuccess;
}

Noise_NKpsk2_error_code Noise_NKpsk2_dh(uint8_t *dest, uint8_t *priv, uint8_t *pub)
{
  bool b = Hacl_Curve25519_64_ecdh(dest, priv, pub);
  if (b)
    return Noise_NKpsk2_CSuccess;
  else
    return Noise_NKpsk2_CDH_error;
}

void
Noise_NKpsk2_aead_encrypt(
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

Noise_NKpsk2_error_code
Noise_NKpsk2_aead_decrypt(
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
    return Noise_NKpsk2_CSuccess;
  else
    return Noise_NKpsk2_CDecrypt_error;
}

void Noise_NKpsk2_hash(uint8_t *output, uint32_t inlen, uint8_t *input)
{
  Hacl_Blake2s_32_blake2s((uint32_t)32U, output, inlen, input, (uint32_t)0U, NULL);
}

void Noise_NKpsk2_mix_hash(uint8_t *hash1, uint32_t inlen, uint8_t *input)
{
  KRML_CHECK_SIZE(sizeof (uint8_t),
    Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2S, Hacl_Impl_Blake2_Core_M32));
  uint8_t
  buf[Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2S, Hacl_Impl_Blake2_Core_M32)];
  memset(buf,
    0U,
    Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2S,
      Hacl_Impl_Blake2_Core_M32)
    * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
  uint32_t wv[(uint32_t)4U * (uint32_t)4U];
  memset(wv, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
  uint32_t b[(uint32_t)4U * (uint32_t)4U];
  memset(b, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
  Hacl_Streaming_Blake2_blake2s_32_block_state block_state = { .fst = wv, .snd = b };
  Hacl_Streaming_Blake2_blake2s_32_state
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  Hacl_Streaming_Blake2_blake2s_32_state p = s;
  Hacl_Blake2s_32_blake2s_init(block_state.fst,
    block_state.snd,
    (uint32_t)0U,
    NULL,
    (uint32_t)32U);
  Hacl_Streaming_Blake2_blake2s_32_state *s0 = &p;
  Hacl_Streaming_Blake2_blake2s_32_no_key_update(s0, hash1, (uint32_t)32U);
  Hacl_Streaming_Blake2_blake2s_32_no_key_update(s0, input, inlen);
  Hacl_Streaming_Blake2_blake2s_32_no_key_finish(s0, hash1);
}

void
Noise_NKpsk2_hmac(
  uint8_t *output,
  uint32_t keylen,
  uint8_t *key,
  uint32_t datalen,
  uint8_t *data
)
{
  Hacl_HMAC_compute_blake2s_32(output, key, keylen, data, datalen);
}

void
Noise_NKpsk2_kdf(
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
  Noise_NKpsk2_hmac(secret, (uint32_t)32U, hash1, keylen, key);
  if (!(dst1 == NULL))
  {
    output[0U] = (uint8_t)1U;
    Noise_NKpsk2_hmac(output_hash, (uint32_t)32U, secret, (uint32_t)1U, output1);
    memcpy(dst1, output_hash, (uint32_t)32U * sizeof (uint8_t));
    if (!(dst2 == NULL))
    {
      output[32U] = (uint8_t)2U;
      Noise_NKpsk2_hmac(output_hash, (uint32_t)32U, secret, (uint32_t)33U, output);
      memcpy(dst2, output_hash, (uint32_t)32U * sizeof (uint8_t));
      if (!(dst3 == NULL))
      {
        output[32U] = (uint8_t)3U;
        Noise_NKpsk2_hmac(output_hash, (uint32_t)32U, secret, (uint32_t)33U, output);
        memcpy(dst3, output_hash, (uint32_t)32U * sizeof (uint8_t));
      }
    }
  }
  Lib_Memzero0_memzero(output, (uint32_t)33U * sizeof (output[0U]));
  Lib_Memzero0_memzero(secret, (uint32_t)32U * sizeof (secret[0U]));
}

void Noise_NKpsk2_mix_psk(uint8_t *psk, uint8_t *st_cs_k, uint8_t *st_ck, uint8_t *st_h)
{
  uint8_t temp_hash[32U] = { 0U };
  Noise_NKpsk2_kdf(st_ck, (uint32_t)32U, psk, st_ck, temp_hash, st_cs_k);
  Noise_NKpsk2_mix_hash(st_h, (uint32_t)32U, temp_hash);
  Lib_Memzero0_memzero(temp_hash, (uint32_t)32U * sizeof (temp_hash[0U]));
}

void
Noise_NKpsk2_encrypt_and_hash(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *cipher,
  uint8_t *st_cs_k,
  uint8_t *st_h,
  uint64_t nonce
)
{
  Noise_NKpsk2_aead_encrypt(st_cs_k, nonce, (uint32_t)32U, st_h, msg_len, msg, cipher);
  uint32_t cipher_len = msg_len + (uint32_t)16U;
  Noise_NKpsk2_mix_hash(st_h, cipher_len, cipher);
}

Noise_NKpsk2_error_code
Noise_NKpsk2_decrypt_and_hash(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *cipher,
  uint8_t *st_cs_k,
  uint8_t *st_h,
  uint64_t nonce
)
{
  Noise_NKpsk2_error_code
  r1 = Noise_NKpsk2_aead_decrypt(st_cs_k, nonce, (uint32_t)32U, st_h, msg_len, msg, cipher);
  if (r1 == Noise_NKpsk2_CSuccess)
  {
    Noise_NKpsk2_mix_hash(st_h, msg_len + (uint32_t)16U, cipher);
    return Noise_NKpsk2_CSuccess;
  }
  else
    return r1;
}

Noise_NKpsk2_error_code
Noise_NKpsk2_mix_dh(
  uint8_t *sec,
  uint8_t *pub,
  uint8_t *cipher_key,
  uint8_t *ck,
  uint8_t *hash1
)
{
  uint8_t dh_key[32U] = { 0U };
  Noise_NKpsk2_error_code r1 = Noise_NKpsk2_dh(dh_key, sec, pub);
  Noise_NKpsk2_error_code r2;
  if (r1 == Noise_NKpsk2_CSuccess)
  {
    Noise_NKpsk2_kdf(ck, (uint32_t)32U, dh_key, ck, cipher_key, NULL);
    r2 = Noise_NKpsk2_CSuccess;
  }
  else
    r2 = r1;
  Noise_NKpsk2_error_code r = r2;
  Lib_Memzero0_memzero(dh_key, (uint32_t)32U * sizeof (dh_key[0U]));
  return r;
}

