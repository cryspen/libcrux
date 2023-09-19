package main

import (
	"github.com/cloudflare/circl/kem/schemes"
	"testing"
)

func BenchmarkKyber768KeyGeneration(b *testing.B) {
	scheme := schemes.ByName("Kyber768")

	for i := 0; i < b.N; i++ {
		pk, sk, _ := scheme.GenerateKeyPair()
		_, _ = pk.MarshalBinary()
		_, _ = sk.MarshalBinary()
	}
}

func BenchmarkKyber768Encapsulation(b *testing.B) {
	scheme := schemes.ByName("Kyber768")

	pk, _, _ := scheme.GenerateKeyPair()
	pkBytes, _ := pk.MarshalBinary()

	for i := 0; i < b.N; i++ {
		pk, _ := scheme.UnmarshalBinaryPublicKey(pkBytes)
		_, _, _ = scheme.Encapsulate(pk)
	}
}

func BenchmarkKyber768Decapsulation(b *testing.B) {
	scheme := schemes.ByName("Kyber768")

	pk, sk, _ := scheme.GenerateKeyPair()
	skBytes, _ := sk.MarshalBinary()
	ct, _, _ := scheme.Encapsulate(pk)

	for i := 0; i < b.N; i++ {
		sk, _ := scheme.UnmarshalBinaryPrivateKey(skBytes)
		_, _ = scheme.Decapsulate(sk, ct)
	}
}
