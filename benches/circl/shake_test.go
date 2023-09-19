package main

import (
	"github.com/cloudflare/circl/xof"
	"testing"
)

func BenchmarkSHAKE128(b *testing.B) {
	input := make([]byte, 0, 34)
	for i := 0; i < len(input); i++ {
		input[i] = byte(i)
	}

	bytesToOutput := 840
	output := make([]byte, bytesToOutput)

	xof := xof.SHAKE128.New()
	_, err := xof.Write([]byte(input))
	if err != nil {
		b.Fatal(err)
	}

	for i := 0; i < b.N; i++ {
		_, _ = xof.Read(output)
	}
}

func BenchmarkSHAKE256(b *testing.B) {
	input := make([]byte, 0, 33)
	for i := 0; i < len(input); i++ {
		input[i] = byte(i)
	}

	bytesToOutput := 128
	output := make([]byte, bytesToOutput)

	xof := xof.SHAKE256.New()
	_, err := xof.Write([]byte(input))
	if err != nil {
		b.Fatal(err)
	}

	for i := 0; i < b.N; i++ {
		_, _ = xof.Read(output)
	}
}
