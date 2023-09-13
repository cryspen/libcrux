package main

import (
	"github.com/cloudflare/circl/xof"
	"testing"
)

const bytesToOutput = 10000

func BenchmarkSHAKE128(b *testing.B) {
	input := make([]byte, 0, 34)
	output := make([]byte, bytesToOutput)

	xof := xof.SHAKE128.New()
	_, err := xof.Write([]byte(input))
	if err != nil {
		b.Fatal(err)
	}

	for i := 0; i < b.N; i++ {
		n, err := xof.Read(output)
		if n != bytesToOutput || err != nil {
			b.Fatal()
		}
	}
}

func BenchmarkSHAKE256(b *testing.B) {
	input := make([]byte, 0, 34)
	output := make([]byte, bytesToOutput)

	xof := xof.SHAKE256.New()
	_, err := xof.Write([]byte(input))
	if err != nil {
		b.Fatal(err)
	}

	for i := 0; i < b.N; i++ {
		n, err := xof.Read(output)
		if n != bytesToOutput || err != nil {
			b.Fatal()
		}
	}
}
