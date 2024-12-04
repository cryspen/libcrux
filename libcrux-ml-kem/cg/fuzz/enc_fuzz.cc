// Basic fuzz test for encapsulate operation.

#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "libcrux_mlkem768_portable.h"

extern "C"
{

	int LLVMFuzzerTestOneInput(const uint8_t *input, size_t len)
	{
		uint8_t rnd[32];
		libcrux_ml_kem_mlkem768_MlKem768PublicKey pk;

		memset(rnd, 0, sizeof(rnd));
		memset(&pk, 0, sizeof(pk));
		if (len > sizeof(pk.value))
		{
			len = sizeof(pk.value);
		}
		memcpy(pk.value, input, len);

		(void)libcrux_ml_kem_mlkem768_portable_encapsulate(&pk, rnd);
		(void)getentropy(rnd, sizeof(rnd));
		(void)libcrux_ml_kem_mlkem768_portable_encapsulate(&pk, rnd);
		return 0;
	}

} // extern
