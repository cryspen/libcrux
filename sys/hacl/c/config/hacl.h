/*
 * Meta header to include all the main header files we care about.
 */
#pragma once

#include "config.h"

#include "Hacl_AEAD_Chacha20Poly1305.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_Hash_SHA1.h"
#include "Hacl_Hash_SHA2.h"
#include "Hacl_Hash_SHA3.h"
#include "Hacl_Hash_Blake2b.h"
#include "Hacl_Hash_Blake2s.h"
#include "Hacl_HMAC_DRBG.h"
#include "Hacl_Ed25519.h"
#include "Hacl_Streaming_Types.h"
#include "Hacl_HKDF.h"
#include "Hacl_HMAC.h"
#include "Hacl_P256.h"
#include "Hacl_RSAPSS.h"

void hacl_free(void *ptr);
