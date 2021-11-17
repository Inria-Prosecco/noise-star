/** This file was automatically generated */


#ifndef __NN_H
#define __NN_H
#include <stdint.h>
#include "kremlin/internal/target.h"
#include "kremlin/internal/types.h"


#include "Hacl.h"
#include "Noise.h"

#define Noise_Success 0
#define Noise_Error 1
#define Noise_Stuck 2

typedef uint8_t Noise_rcode_tags;

typedef struct Noise_rcode_s
{
  Noise_rcode_tags tag;
  union {
    Noise_error_code case_Error;
    Noise_error_code case_Stuck;
  }
  val;
}
Noise_rcode;

bool Noise_uu___is_Success(Noise_rcode projectee);

bool Noise_uu___is_Error(Noise_rcode projectee);

Noise_error_code Noise___proj__Error__item___0(Noise_rcode projectee);

bool Noise_uu___is_Stuck(Noise_rcode projectee);

Noise_error_code Noise___proj__Stuck__item___0(Noise_rcode projectee);

typedef uint8_t Noise_conf_level_t;

typedef uint8_t Noise_auth_level_t;

#define NOISE_AUTH_ZERO ((uint8_t)0U)

#define NOISE_AUTH_KNOWN_SENDER ((uint8_t)1U)

#define NOISE_AUTH_KNOWN_SENDER_NO_KCI ((uint8_t)2U)

#define NOISE_MAX_AUTH_LEVEL ((uint8_t)2U)

#define NOISE_CONF_ZERO ((uint8_t)0U)

#define NOISE_CONF_KNOWN_RECEIVER ((uint8_t)2U)

#define NOISE_CONF_KNOWN_RECEIVER_NON_REPLAYABLE ((uint8_t)3U)

#define NOISE_CONF_STRONG_FORWARD_SECRECY ((uint8_t)5U)

#define NOISE_MAX_CONF_LEVEL ((uint8_t)5U)

#define Noise_Auth_level 0
#define Noise_Conf_level 1
#define Noise_No_level 2

typedef uint8_t Noise_ac_level_t_tags;

typedef struct Noise_ac_level_t_s
{
  Noise_ac_level_t_tags tag;
  union {
    uint8_t case_Auth_level;
    uint8_t case_Conf_level;
  }
  val;
}
Noise_ac_level_t;

bool Noise_uu___is_Auth_level(Noise_ac_level_t projectee);

uint8_t Noise___proj__Auth_level__item__l(Noise_ac_level_t projectee);

bool Noise_uu___is_Conf_level(Noise_ac_level_t projectee);

uint8_t Noise___proj__Conf_level__item__l(Noise_ac_level_t projectee);

bool Noise_uu___is_No_level(Noise_ac_level_t projectee);

typedef struct Noise_encap_message_t_s Noise_encap_message_t;

typedef Noise_encap_message_t *Noise_encap_message_p_or_null;

Noise_encap_message_t
*Noise___proj__Mkencap_message_p_or_null__item__emp(Noise_encap_message_t *projectee);

bool Noise_encap_message_p_is_null(Noise_encap_message_t *emp);

typedef Noise_encap_message_t *Noise_encap_message_p;

void Noise_encap_message_p_free(Noise_encap_message_t *emp);

Noise_encap_message_t
*Noise_pack_message_with_conf_level(
  uint8_t requested_conf_level,
  uint32_t msg_len,
  uint8_t *msg
);

Noise_encap_message_t *Noise_pack_message(uint32_t msg_len, uint8_t *msg);

bool
Noise_unpack_message_with_auth_level(
  uint32_t *out_msg_len,
  uint8_t **out_msg,
  uint8_t requested_auth_level,
  Noise_encap_message_t *emp
);

bool
Noise_unpack_message(uint32_t *out_msg_len, uint8_t **out_msg, Noise_encap_message_t *emp);

void
Noise_unsafe_unpack_message(
  Noise_ac_level_t *out_ac_level,
  uint32_t *out_msg_len,
  uint8_t **out_msg,
  Noise_encap_message_t *emp
);

extern Prims_int Noise_num_pattern_messages;

bool Noise_rcode_is_success(Noise_rcode c);

bool Noise_rcode_is_error(Noise_rcode c);

bool Noise_rcode_is_stuck(Noise_rcode c);

/*******************************************************************************

An instanciation of the NoiseAPI for the NN pattern.

This instanciation uses the following features:
* uint32 for the sessions and peers counters/unique identifiers
* we don't accept unknown remote static keys: all remote keys should have been
  registered in the device by adding the proper peers.
* device/session/peer names are null-terminated strings of ANSI char

*******************************************************************************/


typedef Noise_status Noise_status0;

#define Noise_IMS_Handshake 0
#define Noise_IMS_Transport 1

typedef uint8_t Noise_init_state_t_tags;

typedef struct Noise_init_state_t_s Noise_init_state_t;

typedef struct Noise_peer_t_s Noise_peer_t;

typedef struct Noise_cell_s Noise_cell;

typedef struct Noise_cell_s
{
  Noise_cell *next;
  Noise_peer_t *data;
}
Noise_cell;

typedef struct Noise_device_t_s Noise_device_t;

typedef struct Noise_resp_state_t_s Noise_resp_state_t;

#define Noise_DS_Initiator 0
#define Noise_DS_Responder 1

typedef uint8_t Noise_session_t_tags;

typedef struct Noise_session_t_s Noise_session_t;

typedef Noise_session_t Noise_session_t0;

typedef Noise_session_t *Noise_session_p;

typedef Noise_device_t Noise_device_t0;

typedef Noise_device_t *Noise_device_p;

typedef Noise_peer_t Noise_peer_t0;

typedef Noise_peer_t *Noise_peer_p;

/*
  Create a device.
 
  Parameters:
  * `prlg`: Prologue for session initialization
  * `info`: Device name
  * `sk`: (if present) symmetric key used to serialize/deserialize private data
  * `spriv`: (if present) static private key
 
  May fail and return NULL if provided unvalid keys.
*/
Noise_device_t
*Noise_device_create(uint32_t prlg_len, uint8_t *prlg, uint8_t *info, uint8_t *sk);

/*
  Create a device.

  Takes as arguments a symmetric key `sk` for secret data serialization/
  deserialization, and an encrypted static private key `spriv`. The device
  name `info` is used as authentication data to encrypt/decrypt the device
  private key.

  May fail and return NULL if provided unvalid keys.
*/
Noise_device_t
*Noise_device_create_from_secret(uint32_t prlg_len, uint8_t *prlg, uint8_t *info, uint8_t *sk);

/*
  Free a device.

  Take care to free the device **AFTER** having freed all the sessions created
  from this device.
*/
void Noise_device_free(Noise_device_t *dvp);

/*
  Add a peer to the device and return a pointer to the newly created peer.

  May fail and return NULL if the device already contains a peer with the same
  public static key.

  Note that the peer is owned by the device: we don't provide any way of freeing it
  on the user side, and it might be invalidated after a removal operation.
  For this reason, we advise to immediately use the returned pointer (to retrieve
  the peer id for instance), then forget it.
*/
Noise_peer_t *Noise_device_add_peer(Noise_device_t *dvp, uint8_t *pinfo);

/*
  Remove a peer designated by its unique identifier.
*/
void Noise_device_remove_peer(Noise_device_t *dvp, uint32_t pid);

/*
  Lookup a peer by using its unique identifier.

  Return NULL is no peer was found.

  Note that the peer is owned by the device: we don't provide any way of freeing it
  on the user side, and it might be invalidated after a removal operation.
  For this reason, we advise to immediately use the returned pointer (to retrieve
  the peer name, etc.), then forget it.
*/
Noise_peer_t *Noise_device_lookup_peer_by_id(Noise_device_t *dvp, uint32_t id);

/*
  Copy the peer information to the user provided pointer.
*/
void Noise_device_get_info(Noise_noise_string *out, Noise_device_t *dvp);

/*
  Return the current value of the sessions counter.

  The device keeps track of the number of sessions created so far, in order
  to give them unique identifiers.
*/
uint32_t Noise_device_get_sessions_counter(Noise_device_t *dvp);

/*
  Return true if the sessions counter is saturated.

  It is not possible to create any more sessions if the counter is saturated.
*/
bool Noise_device_sessions_counter_is_saturated(Noise_device_t *dvp);

/*
  Return the current value of the peers counter.

  The device keeps track of the number of peers created so far, in order
  to give them unique identifiers.
*/
uint32_t Noise_device_get_peers_counter(Noise_device_t *dvp);

/*
  Return true if the peers counter is saturated.

  It is not possible to add any more peers to the device if the counter is saturated.
*/
bool Noise_device_peers_counter_is_saturated(Noise_device_t *dvp);

/*
  Return the unique peer identifier.
*/
uint32_t Noise_peer_get_id(Noise_peer_t *pp);

/*
  Copy the peer information to the user provided pointer.
*/
void Noise_peer_get_info(Noise_noise_string *out, Noise_peer_t *pp);

/*
  Create an initiator session.

  May fail and return NULL in case of invalid keys, unknown peer, etc.
*/
Noise_session_t *Noise_session_create_initiator(Noise_device_t *dvp);

/*
  Create a responder session.

  May fail and return NULL in case of invalid keys, unknown peer, etc.
*/
Noise_session_t *Noise_session_create_responder(Noise_device_t *dvp);

/*
  Free a session.

  Be sure to free all sessions before freeing the device used to create
  those sessions.
*/
void Noise_session_free(Noise_session_t *sn);

/*
  Write a message with the current session.

  If successful, this function will allocate a buffer of the proper length
  in `*out` and will write the length of this buffer in `*out_len`. Note that
  using `out` and `out_len` is always safe: if the function fails, it will set
  `*outlen` to 0 and `*out` to NULL.
*/
Noise_rcode
Noise_session_write(
  Noise_encap_message_t *payload,
  Noise_session_t *sn_p,
  uint32_t *out_len,
  uint8_t **out
);

/*
  Read a message with the current session.

  If successful, this function will allocate a an encapsulated message
  in `*payload_out`. Note that using `payload_out` is always safe: if the
  function fails, it will set `*payload_out` to NULL.
*/
Noise_rcode
Noise_session_read(
  Noise_encap_message_t **payload_out,
  Noise_session_t *sn_p,
  uint32_t inlen,
  uint8_t *input
);

/*
  Compute the length of the next message, given a payload length.

  Note that the function may fail, if the length of the message is too long
  for example (though very unlikely). You thus need to check the returned value.

  Also note that the length of the next message is always equal to:
  payload length + a value depending only on the current step.
*/
bool
Noise_session_compute_next_message_len(
  uint32_t *out,
  Noise_session_t *sn,
  uint32_t payload_len
);

/*
  Return the current status.
*/
Noise_status Noise_session_get_status(Noise_session_t *sn);

/*
  Copy the session hash to the user provided buffer.

  Note that the session hash is always public.

  Using the session hash might be pertinent once the session has reached the
  transport phase.
*/
void Noise_session_get_hash(uint8_t *out, Noise_session_t *sn);

/*
  Return the session unique identifier.
*/
uint32_t Noise_session_get_id(Noise_session_t *sn);

/*
  Copy the session information to the user provided pointer.
*/
void Noise_session_get_info(Noise_noise_string *out, Noise_session_t *sn);

/*
  Return the session's peer unique identifier.

  The remote may be unknown, in which case the returned id will be 0.
  Note that you can safely use the returned peer id without testing
  it, because all the functions taking peer ids as parameters were
  written to correctly manipulate 0. In particular, looking up id 0 will return
  NULL, and trying to create a session with peer id 0 will cleanly fail
  by also returning NULL.
*/
uint32_t Noise_session_get_peer_id(Noise_session_t *sn);

/*
  Copy the session peer information, if known, to the user provided pointer.

  The remote may be unknown yet, in which case there is no peer information
  in the device and the function will return false.
*/
bool Noise_session_get_peer_info(Noise_noise_string *out, Noise_session_t *sn);

/*
  Return true if this session has reached the maximum security level for this
  pattern.

  Once the maximum security level is reached, it is not possible to have better
  confidentiality/authentication guarantees for the payloads sent/received
  with this session. Note that the guarantees provided by the maximum reachable
  level vary with the pattern, which must thus be carefully chosen.

  In order to reach the maximum level, the session must have finished the
  handshake. Moreover, in case the session sends the last handshake message,
  it must wait for the first transport message from the remote: otherwise,
  we have no way to know whether the remote was itself able to finish the
  handshake.
*/
bool Noise_session_reached_max_security(Noise_session_t *snp);

/*
  DO NOT use this: for tests and benchmarks only
*/
Noise_session_t
*Noise__session_create_initiator_with_ephemeral(
  Noise_device_t *dvp,
  uint8_t *epriv,
  uint8_t *epub
);

/*
  DO NOT use this: for tests and benchmarks only
*/
Noise_session_t
*Noise__session_create_responder_with_ephemeral(
  Noise_device_t *dvp,
  uint8_t *epriv,
  uint8_t *epub
);


#define __NN_H_DEFINED
#endif
