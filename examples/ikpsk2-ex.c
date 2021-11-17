#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>

#include <IKpsk2.h>

typedef Noise_device_t        device;
typedef Noise_session_t       session;
typedef Noise_peer_t          peer;
typedef Noise_encap_message_t encap_message;
typedef Noise_rcode           rcode;
typedef uint32_t              peer_id;

// Using IKpsk2 with:
// - DH: Curve25519
// - AEAD: ChaChaPoly
// - Hash: SHA256
#define AEAD_KEY_SIZE 32
#define DH_KEY_SIZE   32
#define HASH_SIZE     32
#define PSK_SIZE      32

#define RETURN_IF_ERROR(e, msg) if (!(e)) { printf("Error: %s\n", msg); return 1; }

// Symmetric key used by Alice for serialization/deserialization
uint8_t alice_srlz_key[AEAD_KEY_SIZE] = {
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
};

// Alice's DH keys
uint8_t alice_spriv[DH_KEY_SIZE] = {
    0xc3, 0xda, 0x55, 0x37, 0x9d, 0xe9, 0xc6, 0x90,
    0x8e, 0x94, 0xea, 0x4d, 0xf2, 0x8d, 0x08, 0x4f,
    0x32, 0xec, 0xcf, 0x03, 0x49, 0x1c, 0x71, 0xf7,
    0x54, 0xb4, 0x07, 0x55, 0x77, 0xa2, 0x85, 0x52
};

/*uint8_t alice_spub[DH_KEY_SIZE] = {
    0xe6, 0xdb, 0x68, 0x67, 0x58, 0x30, 0x30, 0xdb,
    0x35, 0x94, 0xc1, 0xa4, 0x24, 0xb1, 0x5f, 0x7c,
    0x72, 0x66, 0x24, 0xec, 0x26, 0xb3, 0x35, 0x3b,
    0x10, 0xa9, 0x03, 0xa6, 0xd0, 0xab, 0x1c, 0x4c
    };*/
uint8_t alice_spub[DH_KEY_SIZE]  = { 0 };

// Symmetric key used by Bob for serialization/deserialization
uint8_t bob_srlz_key[AEAD_KEY_SIZE] = {
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
};

// Bob's DH keys
uint8_t *bob_spriv = alice_spriv;

uint8_t *bob_spub = alice_spub;

// Pre-shared key
uint8_t psk[PSK_SIZE] = {
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
};

int main (int argc, char *arg[]) {
    uint8_t prologue[10] = "Noise* 1.0";
    rcode res;

    Noise_dh_secret_to_public(alice_spub, alice_spriv);

    /*
     * Initialize Alice's device
     */
    // Create the device
    device *alice_device = Noise_device_create(10, prologue, "Alice", alice_srlz_key, alice_spriv);
    
    // Register Bob
    peer *peer_bob = Noise_device_add_peer(alice_device, "Bob", bob_spub, psk);
    if (!peer_bob) return 1;
    peer_id bob_id = Noise_peer_get_id(peer_bob);

    /*
     * Initialize Bob's device
     */
    // Create the device
    device *bob_device = Noise_device_create(10, prologue, "Bob", bob_srlz_key, bob_spriv);

    // Register Alice
    peer *peer_alice = Noise_device_add_peer(bob_device, "Alice", alice_spub, psk);
    if (!peer_alice) return 1;
    peer_id alice_id = Noise_peer_get_id(peer_alice);

    /*
     * Start communicating
     */
    // We first need to create communication sessions.
    // Alice being the initiator, she needs to know who to send the first
    // message, hence the bob_id parameter.
    session *alice_session = Noise_session_create_initiator(alice_device, bob_id);
    if (!alice_session) return 1;
    printf("Alice's session created\n");

    // Bob, however, needs to wait for the first message to learn Alice's identity.
    session *bob_session = Noise_session_create_responder(bob_device);
    if (!bob_session) return 1;
    printf("Bob's session created\n");
      
    // # Step 1: Send an empty message from Alice to Bob
    encap_message *encap_msg0;

    // ## Alice: generate the message

    // Before sending a message, we need to pack it with a confidentiality
    // level. Upon sending the message, the session state will dynamically
    // check that it can provide the requested security guarantees, and will
    // fail otherwise.
    encap_msg0 = Noise_pack_message_with_conf_level(NOISE_CONF_ZERO, 0, NULL);
    uint32_t cipher_msg0_len;
    uint8_t *cipher_msg0;
    res = Noise_session_write(encap_msg0, alice_session, &cipher_msg0_len, &cipher_msg0);
    if (!Noise_rcode_is_success(res)) return 1;
    Noise_encap_message_p_free(encap_msg0);
    printf("Message 0 sent\n");

    // ## Bob: read the message
    res = Noise_session_read(&encap_msg0, bob_session, cipher_msg0_len, cipher_msg0);
    if (!Noise_rcode_is_success(res)) return res.tag == Noise_Error? res.val.case_Error : res.val.case_Stuck;
    printf("Message 0 received\n");

    // In order to actually read the message, Bob needs to unpack it.
    // Unpacking is similar to packing, but here we use an authentication level:
    // if at the current step the protocol doesn't provide enough authentication
    // guarantees, then the unpacking fails.
    uint32_t plain_msg0_len;
    uint8_t *plain_msg0;
    if (!Noise_unpack_message_with_auth_level(&plain_msg0_len, &plain_msg0,
                                              NOISE_AUTH_ZERO, encap_msg0))
        return 1;
    Noise_encap_message_p_free(encap_msg0);
    printf("Message 0 unpacked\n");
    
    // # Step 2: Send an empty message from Bob to Alice.
    // Very similar to step 1.
    

    // By then, Alice should have reached the best security level.
    // Send a secret message, and request the highest confidentiality
    // guarantee.
    
    // Same for Bob: we can now send messages with the highest confidentiality level.
    

    return 0;
}
