import os
# from cryptography.hazmat.primitives.ciphers import (
#     Cipher, algorithms, modes
# )
# from cryptography.hazmat.backends import default_backend
# from cryptography.exceptions import InvalidTag

# --- AES Key Schedule Generation (for demonstration) ---

# S-box: The substitution table for AES
_S_BOX = (
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
)

# Rcon: The round constant word array
_R_CON = (
    0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36,
)

def _generate_and_print_key_schedule(key: bytes):
    """
    Generates and prints the AES-256 key schedule from a 32-byte key.
    This is for educational purposes to show the key expansion process.
    """
    print("--- AES-256 Key Schedule Expansion ---")
    
    # AES-256 constants
    Nk = 8  # Number of 32-bit words in the key
    Nr = 14 # Number of rounds
    
    # The expanded key schedule will hold 4 * (14 + 1) = 60 words
    w = [0] * (4 * (Nr + 1))

    # The first Nk words are the original key
    for i in range(Nk):
        w[i] = int.from_bytes(key[i*4 : i*4+4], 'big')

    # Generate the rest of the words for the schedule
    for i in range(Nk, len(w)):
        temp = w[i - 1]
        print(f"{i}: {i % Nk == 0} | {i % Nk ==4}")
        print(f"{temp:08x}")
        if i % Nk == 0:
            print(f"{i} % Nk == 0")
            # Rotate the word
            temp = ((temp << 8) & 0xffffffff) | (temp >> 24)
            # Apply S-box to each byte
            temp = (_S_BOX[(temp >> 24) & 0xff] << 24) | \
                   (_S_BOX[(temp >> 16) & 0xff] << 16) | \
                   (_S_BOX[(temp >>  8) & 0xff] <<  8) | \
                   (_S_BOX[ temp        & 0xff])
            # XOR with the round constant
            temp ^= (_R_CON[i // Nk] << 24)
        elif i % Nk == 4: # Extra S-box substitution for AES-256
            print(f"{i} % Nk == 4")
            temp = (_S_BOX[(temp >> 24) & 0xff] << 24) | \
                   (_S_BOX[(temp >> 16) & 0xff] << 16) | \
                   (_S_BOX[(temp >>  8) & 0xff] <<  8) | \
                   (_S_BOX[ temp        & 0xff])
            print(f"{temp:08x}")
        
        w[i] = w[i - Nk] ^ temp

    # Print the round keys
    for r in range(Nr + 1):
        round_key_words = w[r*4 : r*4+4]
        round_key_hex = "".join([f'{word:08x}' for word in round_key_words])
        print(f"Round {r:2d} Key: {round_key_hex}")
    print("------------------------------------")


# class AES_GCM_256:
#     """
#     A toy implementation of AES-GCM-256 encryption and decryption.

#     This class demonstrates the core components of an AES-GCM authenticated
#     encryption scheme. It is for educational purposes and uses the `cryptography`
#     library for the underlying cryptographic operations.
#     """

#     def __init__(self, key: bytes):
#         """
#         Initializes the cipher with a 256-bit (32-byte) key.

#         Args:
#             key: A 32-byte key.

#         Raises:
#             ValueError: If the key is not 32 bytes long.
#         """
#         if len(key) != 32:
#             raise ValueError("Key must be 256 bits (32 bytes) for AES-GCM-256.")
#         self.key = key
#         self.backend = default_backend()

#     @staticmethod
#     def generate_key() -> bytes:
#         """
#         Generates a random 256-bit (32-byte) key suitable for AES-GCM-256.

#         Returns:
#             A 32-byte key.
#         """
#         return os.urandom(32)

#     def encrypt(self, plaintext: bytes, associated_data: bytes, nonce: bytes) -> tuple[bytes, bytes]:
#         """
#         Encrypts plaintext and authenticates associated data using AES-GCM.

#         Args:
#             plaintext: The data to encrypt.
#             associated_data: Additional data to authenticate but not encrypt.
#             nonce: A 12-byte (96-bit) nonce. Should be unique for each encryption
#                    with the same key.

#         Returns:
#             A tuple containing the ciphertext and the authentication tag.
        
#         Raises:
#             ValueError: If the nonce is not 12 bytes long.
#         """
#         if len(nonce) != 12:
#             raise ValueError("Nonce must be 96 bits (12 bytes) for AES-GCM.")

#         # Create an AES-GCM cipher object
#         cipher = Cipher(algorithms.AES(self.key), modes.GCM(nonce), backend=self.backend)
#         encryptor = cipher.encryptor()

#         # Add the associated data. This data is authenticated but not encrypted.
#         encryptor.authenticate_additional_data(associated_data)

#         # Encrypt the plaintext
#         ciphertext = encryptor.update(plaintext) + encryptor.finalize()

#         # The authentication tag is generated automatically and is available after finalization.
#         tag = encryptor.tag

#         return ciphertext, tag

#     def decrypt(self, ciphertext: bytes, associated_data: bytes, nonce: bytes, tag: bytes) -> bytes:
#         """
#         Decrypts ciphertext and verifies the authentication tag using AES-GCM.

#         Args:
#             ciphertext: The encrypted data.
#             associated_data: The associated data that was authenticated.
#             nonce: The 12-byte nonce used during encryption.
#             tag: The 16-byte authentication tag generated during encryption.

#         Returns:
#             The original plaintext if decryption and authentication are successful.

#         Raises:
#             cryptography.exceptions.InvalidTag: If the authentication fails.
#             ValueError: If the nonce is not 12 bytes long.
#         """
#         if len(nonce) != 12:
#             raise ValueError("Nonce must be 96 bits (12 bytes) for AES-GCM.")

#         # Create an AES-GCM cipher object with the nonce and tag
#         cipher = Cipher(algorithms.AES(self.key), modes.GCM(nonce, tag), backend=self.backend)
#         decryptor = cipher.decryptor()

#         # Add the associated data for authentication verification.
#         decryptor.authenticate_additional_data(associated_data)

#         # Decrypt the ciphertext.
#         # An InvalidTag exception will be raised if the tag does not match.
#         try:
#             plaintext = decryptor.update(ciphertext) + decryptor.finalize()
#             return plaintext
#         except InvalidTag as e:
#             # Re-raising with a more informative message can be helpful.
#             print(f"Decryption failed: Invalid authentication tag.")
#             raise
#         except Exception as e:
#             print(f"An unexpected error occurred during decryption: {e}")
#             raise

def run_tests():
    """
    A suite of tests to verify the AES_GCM_256 implementation.
    """
    print("--- Running AES-GCM-256 Tests ---")

    # 1. Generate a key
    key = "92ace3e348cd821092cd921aa3546374299ab46209691bc28b8752d17f123c20"
    key = bytes.fromhex(key)
    # aes_cipher = AES_GCM_256(key)
    print(f"Generated Key (hex): {key.hex()}")
    _generate_and_print_key_schedule(key)


    # # 2. Define test data
    # plaintext = b"This is a secret message that needs to be encrypted."
    # associated_data = b"This is metadata that is authenticated but not secret."
    # # A nonce should be unique for every encryption with the same key.
    # # For this test, we'll generate a random 12-byte nonce.
    # nonce = os.urandom(12)
    
    # print(f"Original Plaintext: {plaintext.decode()}")
    # print(f"Associated Data: {associated_data.decode()}")
    # print(f"Nonce (hex): {nonce.hex()}")

    # # 3. Test successful encryption and decryption
    # print("\n--- Test 1: Successful Encryption/Decryption ---")
    # try:
    #     ciphertext, tag = aes_cipher.encrypt(plaintext, associated_data, nonce)
    #     print(f"Ciphertext (hex): {ciphertext.hex()}")
    #     print(f"Authentication Tag (hex): {tag.hex()}")

    #     decrypted_plaintext = aes_cipher.decrypt(ciphertext, associated_data, nonce, tag)
    #     print(f"Decrypted Plaintext: {decrypted_plaintext.decode()}")

    #     assert plaintext == decrypted_plaintext
    #     print("SUCCESS: Decrypted plaintext matches original plaintext.")
    # except Exception as e:
    #     print(f"FAILURE: An unexpected error occurred: {e}")


    # # 4. Test failure: incorrect tag
    # print("\n--- Test 2: Decryption with Incorrect Tag ---")
    # try:
    #     invalid_tag = os.urandom(16) # A random, incorrect tag
    #     print(f"Using incorrect tag (hex): {invalid_tag.hex()}")
    #     aes_cipher.decrypt(ciphertext, associated_data, nonce, invalid_tag)
    #     # The line above should raise an exception, so we should not reach here.
    #     print("FAILURE: Decryption succeeded with an invalid tag.")
    # except InvalidTag:
    #     print(f"SUCCESS: Decryption failed as expected due to InvalidTag.")
    # except Exception as e:
    #     print(f"FAILURE: An unexpected error occurred: {e}")

    # # 5. Test failure: modified ciphertext
    # print("\n--- Test 3: Decryption with Modified Ciphertext ---")
    # try:
    #     # Tamper with the ciphertext (flip the first byte)
    #     modified_ciphertext = bytes([ciphertext[0] ^ 0xFF]) + ciphertext[1:]
    #     print(f"Using modified ciphertext (hex): {modified_ciphertext.hex()}")
    #     aes_cipher.decrypt(modified_ciphertext, associated_data, nonce, tag)
    #     print("FAILURE: Decryption succeeded with modified ciphertext.")
    # except InvalidTag:
    #     print(f"SUCCESS: Decryption failed as expected due to InvalidTag.")
    # except Exception as e:
    #     print(f"FAILURE: An unexpected error occurred: {e}")

    # # 6. Test failure: modified associated data
    # print("\n--- Test 4: Decryption with Modified Associated Data ---")
    # try:
    #     modified_ad = b"This is incorrect metadata."
    #     print(f"Using modified AAD: {modified_ad.decode()}")
    #     aes_cipher.decrypt(ciphertext, modified_ad, nonce, tag)
    #     print("FAILURE: Decryption succeeded with modified associated data.")
    # except InvalidTag:
    #     print(f"SUCCESS: Decryption failed as expected due to InvalidTag.")
    # except Exception as e:
    #     print(f"FAILURE: An unexpected error occurred: {e}")

    # # 7. Test with user-provided specific vector
    # print("\n--- Test 5: Specific Vector Test Case ---")
    # try:
    #     key_hex = "92ace3e348cd821092cd921aa3546374299ab46209691bc28b8752d17f123c20"
    #     aad_hex = "00000000ffffffff"
    #     plaintext_hex = "00010203040506070809"
    #     # A fixed nonce is used for this specific test vector.
    #     nonce_hex = "00112233445566778899aabb"

    #     key_vec = bytes.fromhex(key_hex)
    #     aad_vec = bytes.fromhex(aad_hex)
    #     plaintext_vec = bytes.fromhex(plaintext_hex)
    #     nonce_vec = bytes.fromhex(nonce_hex)

    #     print(f"Using Key (hex): {key_vec.hex()}")
    #     _generate_and_print_key_schedule(key_vec)
    #     print(f"Using AAD (hex): {aad_vec.hex()}")
    #     print(f"Using Plaintext (hex): {plaintext_vec.hex()}")
    #     print(f"Using Nonce (hex): {nonce_vec.hex()}")

    #     specific_cipher = AES_GCM_256(key_vec)
    #     ciphertext_vec, tag_vec = specific_cipher.encrypt(plaintext_vec, aad_vec, nonce_vec)

    #     print(f"Resulting Ciphertext (hex): {ciphertext_vec.hex()}")
    #     print(f"Resulting Tag (hex): {tag_vec.hex()}")

    #     decrypted_plaintext_vec = specific_cipher.decrypt(ciphertext_vec, aad_vec, nonce_vec, tag_vec)
    #     print(f"Decrypted Plaintext (hex): {decrypted_plaintext_vec.hex()}")

    #     assert plaintext_vec == decrypted_plaintext_vec
    #     print("SUCCESS: Specific vector test passed. Decrypted plaintext matches original.")

    # except Exception as e:
    #     print(f"FAILURE: An unexpected error occurred in the specific vector test: {e}")
        
    print("\n--- All tests completed. ---")


if __name__ == "__main__":
    run_tests()

# --- Running AES-GCM-256 Tests ---
# Generated Key (hex): 92ace3e348cd821092cd921aa3546374299ab46209691bc28b8752d17f123c20
# --- AES-256 Key Schedule Expansion ---
# 8: True | False
# 7f123c20
# 8 % Nk == 0
# 9: False | False
# 5a475431
# 10: False | False
# 128ad621
# 11: False | False
# 8047443b
# 12: False | True
# 2313274f
# 12 % Nk == 4
# 267dcc84
# 13: False | False
# 0fe778e6
# 14: False | False
# 068e6324
# 15: False | False
# 8d0931f5
# 16: True | False
# f21b0dd5
# 16 % Nk == 0
# 17: False | False
# f79057b8
# 18: False | False
# e51a8199
# 19: False | False
# 655dc5a2
# 20: False | True
# 464ee2ed
# 20 % Nk == 4
# 5a2f9855
# 21: False | False
# 55c8e0b3
# 22: False | False
# 53468397
# 23: False | False
# de4fb262
# 24: True | False
# 2c54bfb7
# 24 % Nk == 0
# 25: False | False
# d398fec9
# 26: False | False
# 36827f50
# 27: False | False
# 53dfbaf2
# 28: False | True
# 1591581f
# 28 % Nk == 4
# 59816ac0
# 29: False | False
# 0c498a73
# 30: False | False
# 5f0f09e4
# 31: False | False
# 8140bb86
# 32: True | False
# ad140431
# 32 % Nk == 0
# 33: False | False
# 216a395c
# 34: False | False
# 17e8460c
# 35: False | False
# 4437fcfe
# 36: False | True
# 51a6a4e1
# 36 % Nk == 4
# d12449f8
# 37: False | False
# dd6dc38b
# 38: False | False
# 8262ca6f
# 39: False | False
# 032271e9
# 40: True | False
# ae3675d8
# 40 % Nk == 0
# 41: False | False
# 34f758b8
# 42: False | False
# 231f1eb4
# 43: False | False
# 6728e24a
# 44: False | True
# 368e46ab
# 44 % Nk == 4
# 05195a62
# 45: False | False
# d87499e9
# 46: False | False
# 5a165386
# 47: False | False
# 5934226f
# 48: True | False
# f70257b7
# 48 % Nk == 0
# 49: False | False
# 63acf1d0
# 50: False | False
# 40b3ef64
# 51: False | False
# 279b0d2e
# 52: False | True
# 11154b85
# 52 % Nk == 4
# 8259b397
# 53: False | False
# 5a2d2a7e
# 54: False | False
# 003b79f8
# 55: False | False
# 590f5b97
# 56: True | False
# ae0d0c20
# 56 % Nk == 0
# 57: False | False
# f4524634
# 58: False | False
# b4e1a950
# 59: False | False
# 937aa47e
# Round  0 Key: 92ace3e348cd821092cd921aa3546374
# Round  1 Key: 299ab46209691bc28b8752d17f123c20
# Round  2 Key: 5a475431128ad6218047443b2313274f
# Round  3 Key: 0fe778e6068e63248d0931f5f21b0dd5
# Round  4 Key: f79057b8e51a8199655dc5a2464ee2ed
# Round  5 Key: 55c8e0b353468397de4fb2622c54bfb7
# Round  6 Key: d398fec936827f5053dfbaf21591581f
# Round  7 Key: 0c498a735f0f09e48140bb86ad140431
# Round  8 Key: 216a395c17e8460c4437fcfe51a6a4e1
# Round  9 Key: dd6dc38b8262ca6f032271e9ae3675d8
# Round 10 Key: 34f758b8231f1eb46728e24a368e46ab
# Round 11 Key: d87499e95a1653865934226ff70257b7
# Round 12 Key: 63acf1d040b3ef64279b0d2e11154b85
# Round 13 Key: 5a2d2a7e003b79f8590f5b97ae0d0c20
# Round 14 Key: f4524634b4e1a950937aa47e826feffb
