	.att_syntax
	.text
	.p2align	5
	.globl	_jade_stream_chacha_chacha20_ietf_amd64_avx
	.globl	jade_stream_chacha_chacha20_ietf_amd64_avx
	.globl	_jade_stream_chacha_chacha20_ietf_amd64_avx_xor
	.globl	jade_stream_chacha_chacha20_ietf_amd64_avx_xor
_jade_stream_chacha_chacha20_ietf_amd64_avx:
jade_stream_chacha_chacha20_ietf_amd64_avx:
	movq	%rsp, %r10
	leaq	-592(%rsp), %rsp
	andq	$-16, %rsp
	cmpq	$129, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx$1
	vmovdqu	glob_data + 64(%rip), %xmm0
	vmovdqu	glob_data + 48(%rip), %xmm1
	vmovdqu	%xmm0, (%rsp)
	vmovdqu	%xmm1, 16(%rsp)
	vmovdqu	glob_data + 112(%rip), %xmm0
	vmovdqu	glob_data + 128(%rip), %xmm1
	vmovdqu	glob_data + 144(%rip), %xmm2
	vmovdqu	glob_data + 160(%rip), %xmm3
	vpbroadcastd	(%rcx), %xmm4
	vpbroadcastd	4(%rcx), %xmm5
	vpbroadcastd	8(%rcx), %xmm6
	vpbroadcastd	12(%rcx), %xmm7
	vpbroadcastd	16(%rcx), %xmm8
	vpbroadcastd	20(%rcx), %xmm9
	vpbroadcastd	24(%rcx), %xmm10
	vpbroadcastd	28(%rcx), %xmm11
	vmovdqu	glob_data + 96(%rip), %xmm12
	vpbroadcastd	(%rdx), %xmm13
	vpbroadcastd	4(%rdx), %xmm14
	vpbroadcastd	8(%rdx), %xmm15
	vmovdqu	%xmm0, 336(%rsp)
	vmovdqu	%xmm1, 352(%rsp)
	vmovdqu	%xmm2, 368(%rsp)
	vmovdqu	%xmm3, 384(%rsp)
	vmovdqu	%xmm4, 400(%rsp)
	vmovdqu	%xmm5, 416(%rsp)
	vmovdqu	%xmm6, 432(%rsp)
	vmovdqu	%xmm7, 448(%rsp)
	vmovdqu	%xmm8, 464(%rsp)
	vmovdqu	%xmm9, 480(%rsp)
	vmovdqu	%xmm10, 496(%rsp)
	vmovdqu	%xmm11, 512(%rsp)
	vmovdqu	%xmm12, 528(%rsp)
	vmovdqu	%xmm13, 544(%rsp)
	vmovdqu	%xmm14, 560(%rsp)
	vmovdqu	%xmm15, 576(%rsp)
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx$29
Ljade_stream_chacha_chacha20_ietf_amd64_avx$30:
	vmovdqu	336(%rsp), %xmm0
	vmovdqu	352(%rsp), %xmm1
	vmovdqu	368(%rsp), %xmm2
	vmovdqu	384(%rsp), %xmm3
	vmovdqu	400(%rsp), %xmm4
	vmovdqu	416(%rsp), %xmm5
	vmovdqu	432(%rsp), %xmm6
	vmovdqu	448(%rsp), %xmm7
	vmovdqu	464(%rsp), %xmm8
	vmovdqu	480(%rsp), %xmm9
	vmovdqu	496(%rsp), %xmm10
	vmovdqu	512(%rsp), %xmm11
	vmovdqu	528(%rsp), %xmm12
	vmovdqu	544(%rsp), %xmm13
	vmovdqu	560(%rsp), %xmm14
	vmovdqu	576(%rsp), %xmm15
	vmovdqu	%xmm15, 32(%rsp)
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx$31:
	vpaddd	%xmm4, %xmm0, %xmm0
	vpxor	%xmm0, %xmm12, %xmm12
	vpshufb	(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm8, %xmm8
	vpxor	%xmm8, %xmm4, %xmm4
	vpslld	$12, %xmm4, %xmm15
	vpsrld	$20, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm4, %xmm0, %xmm0
	vpxor	%xmm0, %xmm12, %xmm12
	vpshufb	16(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm8, %xmm8
	vpxor	%xmm8, %xmm4, %xmm4
	vpslld	$7, %xmm4, %xmm15
	vpsrld	$25, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm5, %xmm1, %xmm1
	vpxor	%xmm1, %xmm13, %xmm13
	vpshufb	(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm9, %xmm9
	vpxor	%xmm9, %xmm5, %xmm5
	vpslld	$12, %xmm5, %xmm15
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm5, %xmm1, %xmm1
	vpxor	%xmm1, %xmm13, %xmm13
	vpshufb	16(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm9, %xmm9
	vpxor	%xmm9, %xmm5, %xmm5
	vpslld	$7, %xmm5, %xmm15
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm6, %xmm2, %xmm2
	vpxor	%xmm2, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm6, %xmm6
	vpslld	$12, %xmm6, %xmm15
	vpsrld	$20, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm6, %xmm2, %xmm2
	vpxor	%xmm2, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm6, %xmm6
	vpslld	$7, %xmm6, %xmm15
	vpsrld	$25, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vmovdqu	%xmm14, 48(%rsp)
	vmovdqu	32(%rsp), %xmm14
	vpaddd	%xmm7, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm11, %xmm11
	vpxor	%xmm11, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm15
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm11, %xmm11
	vpxor	%xmm11, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm15
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vmovdqu	%xmm14, 64(%rsp)
	vmovdqu	48(%rsp), %xmm14
	vmovdqu	%xmm14, 48(%rsp)
	vmovdqu	64(%rsp), %xmm14
	vpaddd	%xmm5, %xmm0, %xmm0
	vpxor	%xmm0, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm5, %xmm5
	vpslld	$12, %xmm5, %xmm15
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm5, %xmm0, %xmm0
	vpxor	%xmm0, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm5, %xmm5
	vpslld	$7, %xmm5, %xmm15
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vmovdqu	%xmm14, 32(%rsp)
	vmovdqu	48(%rsp), %xmm14
	vpaddd	%xmm6, %xmm1, %xmm1
	vpxor	%xmm1, %xmm12, %xmm12
	vpshufb	(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm11, %xmm11
	vpxor	%xmm11, %xmm6, %xmm6
	vpslld	$12, %xmm6, %xmm15
	vpsrld	$20, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm6, %xmm1, %xmm1
	vpxor	%xmm1, %xmm12, %xmm12
	vpshufb	16(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm11, %xmm11
	vpxor	%xmm11, %xmm6, %xmm6
	vpslld	$7, %xmm6, %xmm15
	vpsrld	$25, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm7, %xmm2, %xmm2
	vpxor	%xmm2, %xmm13, %xmm13
	vpshufb	(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm15
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm2, %xmm2
	vpxor	%xmm2, %xmm13, %xmm13
	vpshufb	16(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm15
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm4, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm9, %xmm9
	vpxor	%xmm9, %xmm4, %xmm4
	vpslld	$12, %xmm4, %xmm15
	vpsrld	$20, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm4, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm9, %xmm9
	vpxor	%xmm9, %xmm4, %xmm4
	vpslld	$7, %xmm4, %xmm15
	vpsrld	$25, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx$31
	vmovdqu	32(%rsp), %xmm15
	vpaddd	336(%rsp), %xmm0, %xmm0
	vpaddd	352(%rsp), %xmm1, %xmm1
	vpaddd	368(%rsp), %xmm2, %xmm2
	vpaddd	384(%rsp), %xmm3, %xmm3
	vpaddd	400(%rsp), %xmm4, %xmm4
	vpaddd	416(%rsp), %xmm5, %xmm5
	vpaddd	432(%rsp), %xmm6, %xmm6
	vpaddd	448(%rsp), %xmm7, %xmm7
	vpaddd	464(%rsp), %xmm8, %xmm8
	vpaddd	480(%rsp), %xmm9, %xmm9
	vpaddd	496(%rsp), %xmm10, %xmm10
	vpaddd	512(%rsp), %xmm11, %xmm11
	vpaddd	528(%rsp), %xmm12, %xmm12
	vpaddd	544(%rsp), %xmm13, %xmm13
	vpaddd	560(%rsp), %xmm14, %xmm14
	vpaddd	576(%rsp), %xmm15, %xmm15
	vmovdqu	%xmm8, 80(%rsp)
	vmovdqu	%xmm9, 96(%rsp)
	vmovdqu	%xmm10, 112(%rsp)
	vmovdqu	%xmm11, 128(%rsp)
	vmovdqu	%xmm12, 144(%rsp)
	vmovdqu	%xmm13, 160(%rsp)
	vmovdqu	%xmm14, 176(%rsp)
	vmovdqu	%xmm15, 192(%rsp)
	vpunpckldq	%xmm1, %xmm0, %xmm8
	vpunpckhdq	%xmm1, %xmm0, %xmm0
	vpunpckldq	%xmm3, %xmm2, %xmm1
	vpunpckhdq	%xmm3, %xmm2, %xmm2
	vpunpckldq	%xmm5, %xmm4, %xmm3
	vpunpckhdq	%xmm5, %xmm4, %xmm4
	vpunpckldq	%xmm7, %xmm6, %xmm5
	vpunpckhdq	%xmm7, %xmm6, %xmm6
	vpunpcklqdq	%xmm1, %xmm8, %xmm7
	vpunpcklqdq	%xmm5, %xmm3, %xmm9
	vpunpckhqdq	%xmm1, %xmm8, %xmm1
	vpunpckhqdq	%xmm5, %xmm3, %xmm3
	vpunpcklqdq	%xmm2, %xmm0, %xmm5
	vpunpcklqdq	%xmm6, %xmm4, %xmm8
	vpunpckhqdq	%xmm2, %xmm0, %xmm0
	vpunpckhqdq	%xmm6, %xmm4, %xmm2
	vmovdqu	%xmm7, (%rdi)
	vmovdqu	%xmm9, 16(%rdi)
	vmovdqu	%xmm1, 64(%rdi)
	vmovdqu	%xmm3, 80(%rdi)
	vmovdqu	%xmm5, 128(%rdi)
	vmovdqu	%xmm8, 144(%rdi)
	vmovdqu	%xmm0, 192(%rdi)
	vmovdqu	%xmm2, 208(%rdi)
	vmovdqu	80(%rsp), %xmm0
	vmovdqu	112(%rsp), %xmm1
	vmovdqu	144(%rsp), %xmm2
	vmovdqu	176(%rsp), %xmm3
	vpunpckldq	96(%rsp), %xmm0, %xmm4
	vpunpckhdq	96(%rsp), %xmm0, %xmm0
	vpunpckldq	128(%rsp), %xmm1, %xmm5
	vpunpckhdq	128(%rsp), %xmm1, %xmm1
	vpunpckldq	160(%rsp), %xmm2, %xmm6
	vpunpckhdq	160(%rsp), %xmm2, %xmm2
	vpunpckldq	192(%rsp), %xmm3, %xmm7
	vpunpckhdq	192(%rsp), %xmm3, %xmm3
	vpunpcklqdq	%xmm5, %xmm4, %xmm8
	vpunpcklqdq	%xmm7, %xmm6, %xmm9
	vpunpckhqdq	%xmm5, %xmm4, %xmm4
	vpunpckhqdq	%xmm7, %xmm6, %xmm5
	vpunpcklqdq	%xmm1, %xmm0, %xmm6
	vpunpcklqdq	%xmm3, %xmm2, %xmm7
	vpunpckhqdq	%xmm1, %xmm0, %xmm0
	vpunpckhqdq	%xmm3, %xmm2, %xmm1
	vmovdqu	%xmm8, 32(%rdi)
	vmovdqu	%xmm9, 48(%rdi)
	vmovdqu	%xmm4, 96(%rdi)
	vmovdqu	%xmm5, 112(%rdi)
	vmovdqu	%xmm6, 160(%rdi)
	vmovdqu	%xmm7, 176(%rdi)
	vmovdqu	%xmm0, 224(%rdi)
	vmovdqu	%xmm1, 240(%rdi)
	addq	$256, %rdi
	addq	$-256, %rsi
	vmovdqu	glob_data + 0(%rip), %xmm0
	vpaddd	528(%rsp), %xmm0, %xmm0
	vmovdqu	%xmm0, 528(%rsp)
Ljade_stream_chacha_chacha20_ietf_amd64_avx$29:
	cmpq	$256, %rsi
	jnb 	Ljade_stream_chacha_chacha20_ietf_amd64_avx$30
	cmpq	$0, %rsi
	jbe 	Ljade_stream_chacha_chacha20_ietf_amd64_avx$2
	vmovdqu	336(%rsp), %xmm0
	vmovdqu	352(%rsp), %xmm1
	vmovdqu	368(%rsp), %xmm2
	vmovdqu	384(%rsp), %xmm3
	vmovdqu	400(%rsp), %xmm4
	vmovdqu	416(%rsp), %xmm5
	vmovdqu	432(%rsp), %xmm6
	vmovdqu	448(%rsp), %xmm7
	vmovdqu	464(%rsp), %xmm8
	vmovdqu	480(%rsp), %xmm9
	vmovdqu	496(%rsp), %xmm10
	vmovdqu	512(%rsp), %xmm11
	vmovdqu	528(%rsp), %xmm12
	vmovdqu	544(%rsp), %xmm13
	vmovdqu	560(%rsp), %xmm14
	vmovdqu	576(%rsp), %xmm15
	vmovdqu	%xmm15, 32(%rsp)
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx$28:
	vpaddd	%xmm4, %xmm0, %xmm0
	vpxor	%xmm0, %xmm12, %xmm12
	vpshufb	(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm8, %xmm8
	vpxor	%xmm8, %xmm4, %xmm4
	vpslld	$12, %xmm4, %xmm15
	vpsrld	$20, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm4, %xmm0, %xmm0
	vpxor	%xmm0, %xmm12, %xmm12
	vpshufb	16(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm8, %xmm8
	vpxor	%xmm8, %xmm4, %xmm4
	vpslld	$7, %xmm4, %xmm15
	vpsrld	$25, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm5, %xmm1, %xmm1
	vpxor	%xmm1, %xmm13, %xmm13
	vpshufb	(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm9, %xmm9
	vpxor	%xmm9, %xmm5, %xmm5
	vpslld	$12, %xmm5, %xmm15
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm5, %xmm1, %xmm1
	vpxor	%xmm1, %xmm13, %xmm13
	vpshufb	16(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm9, %xmm9
	vpxor	%xmm9, %xmm5, %xmm5
	vpslld	$7, %xmm5, %xmm15
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm6, %xmm2, %xmm2
	vpxor	%xmm2, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm6, %xmm6
	vpslld	$12, %xmm6, %xmm15
	vpsrld	$20, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm6, %xmm2, %xmm2
	vpxor	%xmm2, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm6, %xmm6
	vpslld	$7, %xmm6, %xmm15
	vpsrld	$25, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vmovdqu	%xmm14, 48(%rsp)
	vmovdqu	32(%rsp), %xmm14
	vpaddd	%xmm7, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm11, %xmm11
	vpxor	%xmm11, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm15
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm11, %xmm11
	vpxor	%xmm11, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm15
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vmovdqu	%xmm14, 64(%rsp)
	vmovdqu	48(%rsp), %xmm14
	vmovdqu	%xmm14, 48(%rsp)
	vmovdqu	64(%rsp), %xmm14
	vpaddd	%xmm5, %xmm0, %xmm0
	vpxor	%xmm0, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm5, %xmm5
	vpslld	$12, %xmm5, %xmm15
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm5, %xmm0, %xmm0
	vpxor	%xmm0, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm5, %xmm5
	vpslld	$7, %xmm5, %xmm15
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vmovdqu	%xmm14, 32(%rsp)
	vmovdqu	48(%rsp), %xmm14
	vpaddd	%xmm6, %xmm1, %xmm1
	vpxor	%xmm1, %xmm12, %xmm12
	vpshufb	(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm11, %xmm11
	vpxor	%xmm11, %xmm6, %xmm6
	vpslld	$12, %xmm6, %xmm15
	vpsrld	$20, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm6, %xmm1, %xmm1
	vpxor	%xmm1, %xmm12, %xmm12
	vpshufb	16(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm11, %xmm11
	vpxor	%xmm11, %xmm6, %xmm6
	vpslld	$7, %xmm6, %xmm15
	vpsrld	$25, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm7, %xmm2, %xmm2
	vpxor	%xmm2, %xmm13, %xmm13
	vpshufb	(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm15
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm2, %xmm2
	vpxor	%xmm2, %xmm13, %xmm13
	vpshufb	16(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm15
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm4, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm9, %xmm9
	vpxor	%xmm9, %xmm4, %xmm4
	vpslld	$12, %xmm4, %xmm15
	vpsrld	$20, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm4, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm9, %xmm9
	vpxor	%xmm9, %xmm4, %xmm4
	vpslld	$7, %xmm4, %xmm15
	vpsrld	$25, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx$28
	vmovdqu	32(%rsp), %xmm15
	vpaddd	336(%rsp), %xmm0, %xmm0
	vpaddd	352(%rsp), %xmm1, %xmm1
	vpaddd	368(%rsp), %xmm2, %xmm2
	vpaddd	384(%rsp), %xmm3, %xmm3
	vpaddd	400(%rsp), %xmm4, %xmm4
	vpaddd	416(%rsp), %xmm5, %xmm5
	vpaddd	432(%rsp), %xmm6, %xmm6
	vpaddd	448(%rsp), %xmm7, %xmm7
	vpaddd	464(%rsp), %xmm8, %xmm8
	vpaddd	480(%rsp), %xmm9, %xmm9
	vpaddd	496(%rsp), %xmm10, %xmm10
	vpaddd	512(%rsp), %xmm11, %xmm11
	vpaddd	528(%rsp), %xmm12, %xmm12
	vpaddd	544(%rsp), %xmm13, %xmm13
	vpaddd	560(%rsp), %xmm14, %xmm14
	vpaddd	576(%rsp), %xmm15, %xmm15
	vmovdqu	%xmm8, 80(%rsp)
	vmovdqu	%xmm9, 96(%rsp)
	vmovdqu	%xmm10, 112(%rsp)
	vmovdqu	%xmm11, 128(%rsp)
	vmovdqu	%xmm12, 144(%rsp)
	vmovdqu	%xmm13, 160(%rsp)
	vmovdqu	%xmm14, 176(%rsp)
	vmovdqu	%xmm15, 192(%rsp)
	vpunpckldq	%xmm1, %xmm0, %xmm8
	vpunpckhdq	%xmm1, %xmm0, %xmm0
	vpunpckldq	%xmm3, %xmm2, %xmm1
	vpunpckhdq	%xmm3, %xmm2, %xmm2
	vpunpckldq	%xmm5, %xmm4, %xmm3
	vpunpckhdq	%xmm5, %xmm4, %xmm4
	vpunpckldq	%xmm7, %xmm6, %xmm5
	vpunpckhdq	%xmm7, %xmm6, %xmm6
	vpunpcklqdq	%xmm1, %xmm8, %xmm7
	vpunpcklqdq	%xmm5, %xmm3, %xmm9
	vpunpckhqdq	%xmm1, %xmm8, %xmm1
	vpunpckhqdq	%xmm5, %xmm3, %xmm3
	vpunpcklqdq	%xmm2, %xmm0, %xmm5
	vpunpcklqdq	%xmm6, %xmm4, %xmm8
	vpunpckhqdq	%xmm2, %xmm0, %xmm0
	vpunpckhqdq	%xmm6, %xmm4, %xmm2
	vmovdqu	%xmm7, 208(%rsp)
	vmovdqu	%xmm9, 224(%rsp)
	vmovdqu	%xmm1, 240(%rsp)
	vmovdqu	%xmm3, 256(%rsp)
	vmovdqu	%xmm5, 272(%rsp)
	vmovdqu	%xmm8, 288(%rsp)
	vmovdqu	%xmm0, 304(%rsp)
	vmovdqu	%xmm2, 320(%rsp)
	vmovdqu	80(%rsp), %xmm0
	vmovdqu	112(%rsp), %xmm1
	vmovdqu	144(%rsp), %xmm2
	vmovdqu	176(%rsp), %xmm3
	vpunpckldq	96(%rsp), %xmm0, %xmm4
	vpunpckhdq	96(%rsp), %xmm0, %xmm0
	vpunpckldq	128(%rsp), %xmm1, %xmm5
	vpunpckhdq	128(%rsp), %xmm1, %xmm1
	vpunpckldq	160(%rsp), %xmm2, %xmm6
	vpunpckhdq	160(%rsp), %xmm2, %xmm2
	vpunpckldq	192(%rsp), %xmm3, %xmm7
	vpunpckhdq	192(%rsp), %xmm3, %xmm3
	vpunpcklqdq	%xmm5, %xmm4, %xmm8
	vpunpcklqdq	%xmm7, %xmm6, %xmm9
	vpunpckhqdq	%xmm5, %xmm4, %xmm4
	vpunpckhqdq	%xmm7, %xmm6, %xmm5
	vpunpcklqdq	%xmm1, %xmm0, %xmm6
	vpunpcklqdq	%xmm3, %xmm2, %xmm7
	vpunpckhqdq	%xmm1, %xmm0, %xmm0
	vpunpckhqdq	%xmm3, %xmm2, %xmm1
	vmovdqu	208(%rsp), %xmm13
	vmovdqu	224(%rsp), %xmm12
	vmovdqu	%xmm8, %xmm11
	vmovdqu	%xmm9, %xmm10
	vmovdqu	240(%rsp), %xmm9
	vmovdqu	256(%rsp), %xmm8
	vmovdqu	%xmm4, %xmm3
	vmovdqu	%xmm5, %xmm2
	cmpq	$128, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx$27
	vmovdqu	%xmm13, (%rdi)
	vmovdqu	%xmm12, 16(%rdi)
	vmovdqu	%xmm11, 32(%rdi)
	vmovdqu	%xmm10, 48(%rdi)
	vmovdqu	%xmm9, 64(%rdi)
	vmovdqu	%xmm8, 80(%rdi)
	vmovdqu	%xmm3, 96(%rdi)
	vmovdqu	%xmm2, 112(%rdi)
	addq	$128, %rdi
	addq	$-128, %rsi
	vmovdqu	272(%rsp), %xmm13
	vmovdqu	288(%rsp), %xmm12
	vmovdqu	%xmm6, %xmm11
	vmovdqu	%xmm7, %xmm10
	vmovdqu	304(%rsp), %xmm9
	vmovdqu	320(%rsp), %xmm8
	vmovdqu	%xmm0, %xmm3
	vmovdqu	%xmm1, %xmm2
Ljade_stream_chacha_chacha20_ietf_amd64_avx$27:
	cmpq	$64, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx$26
	vmovdqu	%xmm13, (%rdi)
	vmovdqu	%xmm12, 16(%rdi)
	vmovdqu	%xmm11, 32(%rdi)
	vmovdqu	%xmm10, 48(%rdi)
	addq	$64, %rdi
	addq	$-64, %rsi
	vmovdqu	%xmm9, %xmm13
	vmovdqu	%xmm8, %xmm12
	vmovdqu	%xmm3, %xmm11
	vmovdqu	%xmm2, %xmm10
Ljade_stream_chacha_chacha20_ietf_amd64_avx$26:
	cmpq	$32, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx$25
	vmovdqu	%xmm13, (%rdi)
	vmovdqu	%xmm12, 16(%rdi)
	addq	$32, %rdi
	addq	$-32, %rsi
	vmovdqu	%xmm11, %xmm13
	vmovdqu	%xmm10, %xmm12
Ljade_stream_chacha_chacha20_ietf_amd64_avx$25:
	cmpq	$16, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx$24
	vmovdqu	%xmm13, (%rdi)
	addq	$16, %rdi
	addq	$-16, %rsi
	vmovdqu	%xmm12, %xmm13
Ljade_stream_chacha_chacha20_ietf_amd64_avx$24:
	vpextrq	$0, %xmm13, %rax
	cmpq	$8, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx$21
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$-8, %rsi
	vpextrq	$1, %xmm13, %rax
Ljade_stream_chacha_chacha20_ietf_amd64_avx$23:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx$21
Ljade_stream_chacha_chacha20_ietf_amd64_avx$22:
	movb	%al, %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	addq	$-1, %rsi
Ljade_stream_chacha_chacha20_ietf_amd64_avx$21:
	cmpq	$0, %rsi
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx$22
Ljade_stream_chacha_chacha20_ietf_amd64_avx$20:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx$2
Ljade_stream_chacha_chacha20_ietf_amd64_avx$1:
	vmovdqu	glob_data + 64(%rip), %xmm0
	vmovdqu	glob_data + 48(%rip), %xmm1
	vmovdqu	glob_data + 208(%rip), %xmm2
	vmovdqu	(%rcx), %xmm3
	vmovdqu	16(%rcx), %xmm4
	vpxor	%xmm5, %xmm5, %xmm5
	vpinsrd	$1, (%rdx), %xmm5, %xmm5
	vpinsrq	$1, 4(%rdx), %xmm5, %xmm5
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx$17
Ljade_stream_chacha_chacha20_ietf_amd64_avx$18:
	vmovdqu	%xmm2, %xmm6
	vmovdqu	%xmm3, %xmm7
	vmovdqu	%xmm4, %xmm8
	vmovdqu	%xmm5, %xmm9
	vmovdqu	%xmm2, %xmm10
	vmovdqu	%xmm3, %xmm11
	vmovdqu	%xmm4, %xmm12
	vmovdqu	%xmm5, %xmm13
	vpaddd	glob_data + 32(%rip), %xmm13, %xmm13
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx$19:
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm0, %xmm9, %xmm9
	vpshufb	%xmm0, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm14
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$12, %xmm11, %xmm14
	vpsrld	$20, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm1, %xmm9, %xmm9
	vpshufb	%xmm1, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm14
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$7, %xmm11, %xmm14
	vpsrld	$25, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpshufd	$57, %xmm7, %xmm7
	vpshufd	$78, %xmm8, %xmm8
	vpshufd	$-109, %xmm9, %xmm9
	vpshufd	$57, %xmm11, %xmm11
	vpshufd	$78, %xmm12, %xmm12
	vpshufd	$-109, %xmm13, %xmm13
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm0, %xmm9, %xmm9
	vpshufb	%xmm0, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm14
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$12, %xmm11, %xmm14
	vpsrld	$20, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm1, %xmm9, %xmm9
	vpshufb	%xmm1, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm14
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$7, %xmm11, %xmm14
	vpsrld	$25, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpshufd	$-109, %xmm7, %xmm7
	vpshufd	$78, %xmm8, %xmm8
	vpshufd	$57, %xmm9, %xmm9
	vpshufd	$-109, %xmm11, %xmm11
	vpshufd	$78, %xmm12, %xmm12
	vpshufd	$57, %xmm13, %xmm13
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx$19
	vpaddd	%xmm2, %xmm6, %xmm6
	vpaddd	%xmm3, %xmm7, %xmm7
	vpaddd	%xmm4, %xmm8, %xmm8
	vpaddd	%xmm5, %xmm9, %xmm9
	vpaddd	%xmm2, %xmm10, %xmm10
	vpaddd	%xmm3, %xmm11, %xmm11
	vpaddd	%xmm4, %xmm12, %xmm12
	vpaddd	%xmm5, %xmm13, %xmm13
	vpaddd	glob_data + 32(%rip), %xmm13, %xmm13
	vmovdqu	%xmm6, (%rdi)
	vmovdqu	%xmm7, 16(%rdi)
	vmovdqu	%xmm8, 32(%rdi)
	vmovdqu	%xmm9, 48(%rdi)
	vmovdqu	%xmm10, 64(%rdi)
	vmovdqu	%xmm11, 80(%rdi)
	vmovdqu	%xmm12, 96(%rdi)
	vmovdqu	%xmm13, 112(%rdi)
	addq	$128, %rdi
	addq	$-128, %rsi
	vpaddd	glob_data + 16(%rip), %xmm5, %xmm5
Ljade_stream_chacha_chacha20_ietf_amd64_avx$17:
	cmpq	$128, %rsi
	jnb 	Ljade_stream_chacha_chacha20_ietf_amd64_avx$18
	cmpq	$64, %rsi
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx$3
	vmovdqu	%xmm2, %xmm6
	vmovdqu	%xmm3, %xmm7
	vmovdqu	%xmm4, %xmm8
	vmovdqu	%xmm5, %xmm9
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx$16:
	vpaddd	%xmm7, %xmm6, %xmm6
	vpxor	%xmm6, %xmm9, %xmm9
	vpshufb	%xmm0, %xmm9, %xmm9
	vpaddd	%xmm9, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm10
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm10, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm6, %xmm6
	vpxor	%xmm6, %xmm9, %xmm9
	vpshufb	%xmm1, %xmm9, %xmm9
	vpaddd	%xmm9, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm10
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm10, %xmm7, %xmm7
	vpshufd	$57, %xmm7, %xmm7
	vpshufd	$78, %xmm8, %xmm8
	vpshufd	$-109, %xmm9, %xmm9
	vpaddd	%xmm7, %xmm6, %xmm6
	vpxor	%xmm6, %xmm9, %xmm9
	vpshufb	%xmm0, %xmm9, %xmm9
	vpaddd	%xmm9, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm10
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm10, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm6, %xmm6
	vpxor	%xmm6, %xmm9, %xmm9
	vpshufb	%xmm1, %xmm9, %xmm9
	vpaddd	%xmm9, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm10
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm10, %xmm7, %xmm7
	vpshufd	$-109, %xmm7, %xmm7
	vpshufd	$78, %xmm8, %xmm8
	vpshufd	$57, %xmm9, %xmm9
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx$16
	vpaddd	%xmm2, %xmm6, %xmm6
	vpaddd	%xmm3, %xmm7, %xmm2
	vpaddd	%xmm4, %xmm8, %xmm0
	vpaddd	%xmm5, %xmm9, %xmm1
	cmpq	$32, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx$15
	vmovdqu	%xmm6, (%rdi)
	vmovdqu	%xmm2, 16(%rdi)
	addq	$32, %rdi
	addq	$-32, %rsi
	vmovdqu	%xmm0, %xmm6
	vmovdqu	%xmm1, %xmm2
Ljade_stream_chacha_chacha20_ietf_amd64_avx$15:
	cmpq	$16, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx$14
	vmovdqu	%xmm6, (%rdi)
	addq	$16, %rdi
	addq	$-16, %rsi
	vmovdqu	%xmm2, %xmm6
Ljade_stream_chacha_chacha20_ietf_amd64_avx$14:
	vpextrq	$0, %xmm6, %rax
	cmpq	$8, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx$11
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$-8, %rsi
	vpextrq	$1, %xmm6, %rax
Ljade_stream_chacha_chacha20_ietf_amd64_avx$13:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx$11
Ljade_stream_chacha_chacha20_ietf_amd64_avx$12:
	movb	%al, %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	addq	$-1, %rsi
Ljade_stream_chacha_chacha20_ietf_amd64_avx$11:
	cmpq	$0, %rsi
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx$12
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx$2
Ljade_stream_chacha_chacha20_ietf_amd64_avx$3:
	vmovdqu	%xmm2, %xmm6
	vmovdqu	%xmm3, %xmm7
	vmovdqu	%xmm4, %xmm8
	vmovdqu	%xmm5, %xmm9
	vmovdqu	%xmm2, %xmm10
	vmovdqu	%xmm3, %xmm11
	vmovdqu	%xmm4, %xmm12
	vmovdqu	%xmm5, %xmm13
	vpaddd	glob_data + 32(%rip), %xmm13, %xmm13
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx$10:
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm0, %xmm9, %xmm9
	vpshufb	%xmm0, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm14
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$12, %xmm11, %xmm14
	vpsrld	$20, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm1, %xmm9, %xmm9
	vpshufb	%xmm1, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm14
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$7, %xmm11, %xmm14
	vpsrld	$25, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpshufd	$57, %xmm7, %xmm7
	vpshufd	$78, %xmm8, %xmm8
	vpshufd	$-109, %xmm9, %xmm9
	vpshufd	$57, %xmm11, %xmm11
	vpshufd	$78, %xmm12, %xmm12
	vpshufd	$-109, %xmm13, %xmm13
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm0, %xmm9, %xmm9
	vpshufb	%xmm0, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm14
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$12, %xmm11, %xmm14
	vpsrld	$20, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm1, %xmm9, %xmm9
	vpshufb	%xmm1, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm14
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$7, %xmm11, %xmm14
	vpsrld	$25, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpshufd	$-109, %xmm7, %xmm7
	vpshufd	$78, %xmm8, %xmm8
	vpshufd	$57, %xmm9, %xmm9
	vpshufd	$-109, %xmm11, %xmm11
	vpshufd	$78, %xmm12, %xmm12
	vpshufd	$57, %xmm13, %xmm13
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx$10
	vpaddd	%xmm2, %xmm6, %xmm0
	vpaddd	%xmm3, %xmm7, %xmm1
	vpaddd	%xmm4, %xmm8, %xmm6
	vpaddd	%xmm5, %xmm9, %xmm7
	vpaddd	%xmm2, %xmm10, %xmm9
	vpaddd	%xmm3, %xmm11, %xmm8
	vpaddd	%xmm4, %xmm12, %xmm2
	vpaddd	%xmm5, %xmm13, %xmm3
	vpaddd	glob_data + 32(%rip), %xmm3, %xmm3
	vmovdqu	%xmm0, (%rdi)
	vmovdqu	%xmm1, 16(%rdi)
	vmovdqu	%xmm6, 32(%rdi)
	vmovdqu	%xmm7, 48(%rdi)
	addq	$64, %rdi
	addq	$-64, %rsi
	cmpq	$32, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx$9
	vmovdqu	%xmm9, (%rdi)
	vmovdqu	%xmm8, 16(%rdi)
	addq	$32, %rdi
	addq	$-32, %rsi
	vmovdqu	%xmm2, %xmm9
	vmovdqu	%xmm3, %xmm8
Ljade_stream_chacha_chacha20_ietf_amd64_avx$9:
	cmpq	$16, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx$8
	vmovdqu	%xmm9, (%rdi)
	addq	$16, %rdi
	addq	$-16, %rsi
	vmovdqu	%xmm8, %xmm9
Ljade_stream_chacha_chacha20_ietf_amd64_avx$8:
	vpextrq	$0, %xmm9, %rax
	cmpq	$8, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx$5
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$-8, %rsi
	vpextrq	$1, %xmm9, %rax
Ljade_stream_chacha_chacha20_ietf_amd64_avx$7:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx$5
Ljade_stream_chacha_chacha20_ietf_amd64_avx$6:
	movb	%al, %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	addq	$-1, %rsi
Ljade_stream_chacha_chacha20_ietf_amd64_avx$5:
	cmpq	$0, %rsi
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx$6
Ljade_stream_chacha_chacha20_ietf_amd64_avx$4:
Ljade_stream_chacha_chacha20_ietf_amd64_avx$2:
	xorq	%rax, %rax
	movq	%r10, %rsp
	ret 
_jade_stream_chacha_chacha20_ietf_amd64_avx_xor:
jade_stream_chacha_chacha20_ietf_amd64_avx_xor:
	movq	%rsp, %r10
	leaq	-592(%rsp), %rsp
	andq	$-16, %rsp
	cmpq	$129, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$1
	vmovdqu	glob_data + 64(%rip), %xmm0
	vmovdqu	glob_data + 48(%rip), %xmm1
	vmovdqu	%xmm0, (%rsp)
	vmovdqu	%xmm1, 16(%rsp)
	vmovdqu	glob_data + 112(%rip), %xmm0
	vmovdqu	glob_data + 128(%rip), %xmm1
	vmovdqu	glob_data + 144(%rip), %xmm2
	vmovdqu	glob_data + 160(%rip), %xmm3
	vpbroadcastd	(%r8), %xmm4
	vpbroadcastd	4(%r8), %xmm5
	vpbroadcastd	8(%r8), %xmm6
	vpbroadcastd	12(%r8), %xmm7
	vpbroadcastd	16(%r8), %xmm8
	vpbroadcastd	20(%r8), %xmm9
	vpbroadcastd	24(%r8), %xmm10
	vpbroadcastd	28(%r8), %xmm11
	vmovdqu	glob_data + 96(%rip), %xmm12
	vpbroadcastd	(%rcx), %xmm13
	vpbroadcastd	4(%rcx), %xmm14
	vpbroadcastd	8(%rcx), %xmm15
	vmovdqu	%xmm0, 336(%rsp)
	vmovdqu	%xmm1, 352(%rsp)
	vmovdqu	%xmm2, 368(%rsp)
	vmovdqu	%xmm3, 384(%rsp)
	vmovdqu	%xmm4, 400(%rsp)
	vmovdqu	%xmm5, 416(%rsp)
	vmovdqu	%xmm6, 432(%rsp)
	vmovdqu	%xmm7, 448(%rsp)
	vmovdqu	%xmm8, 464(%rsp)
	vmovdqu	%xmm9, 480(%rsp)
	vmovdqu	%xmm10, 496(%rsp)
	vmovdqu	%xmm11, 512(%rsp)
	vmovdqu	%xmm12, 528(%rsp)
	vmovdqu	%xmm13, 544(%rsp)
	vmovdqu	%xmm14, 560(%rsp)
	vmovdqu	%xmm15, 576(%rsp)
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$29
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$30:
	vmovdqu	336(%rsp), %xmm0
	vmovdqu	352(%rsp), %xmm1
	vmovdqu	368(%rsp), %xmm2
	vmovdqu	384(%rsp), %xmm3
	vmovdqu	400(%rsp), %xmm4
	vmovdqu	416(%rsp), %xmm5
	vmovdqu	432(%rsp), %xmm6
	vmovdqu	448(%rsp), %xmm7
	vmovdqu	464(%rsp), %xmm8
	vmovdqu	480(%rsp), %xmm9
	vmovdqu	496(%rsp), %xmm10
	vmovdqu	512(%rsp), %xmm11
	vmovdqu	528(%rsp), %xmm12
	vmovdqu	544(%rsp), %xmm13
	vmovdqu	560(%rsp), %xmm14
	vmovdqu	576(%rsp), %xmm15
	vmovdqu	%xmm15, 32(%rsp)
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$31:
	vpaddd	%xmm4, %xmm0, %xmm0
	vpxor	%xmm0, %xmm12, %xmm12
	vpshufb	(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm8, %xmm8
	vpxor	%xmm8, %xmm4, %xmm4
	vpslld	$12, %xmm4, %xmm15
	vpsrld	$20, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm4, %xmm0, %xmm0
	vpxor	%xmm0, %xmm12, %xmm12
	vpshufb	16(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm8, %xmm8
	vpxor	%xmm8, %xmm4, %xmm4
	vpslld	$7, %xmm4, %xmm15
	vpsrld	$25, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm5, %xmm1, %xmm1
	vpxor	%xmm1, %xmm13, %xmm13
	vpshufb	(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm9, %xmm9
	vpxor	%xmm9, %xmm5, %xmm5
	vpslld	$12, %xmm5, %xmm15
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm5, %xmm1, %xmm1
	vpxor	%xmm1, %xmm13, %xmm13
	vpshufb	16(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm9, %xmm9
	vpxor	%xmm9, %xmm5, %xmm5
	vpslld	$7, %xmm5, %xmm15
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm6, %xmm2, %xmm2
	vpxor	%xmm2, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm6, %xmm6
	vpslld	$12, %xmm6, %xmm15
	vpsrld	$20, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm6, %xmm2, %xmm2
	vpxor	%xmm2, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm6, %xmm6
	vpslld	$7, %xmm6, %xmm15
	vpsrld	$25, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vmovdqu	%xmm14, 48(%rsp)
	vmovdqu	32(%rsp), %xmm14
	vpaddd	%xmm7, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm11, %xmm11
	vpxor	%xmm11, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm15
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm11, %xmm11
	vpxor	%xmm11, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm15
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vmovdqu	%xmm14, 64(%rsp)
	vmovdqu	48(%rsp), %xmm14
	vmovdqu	%xmm14, 48(%rsp)
	vmovdqu	64(%rsp), %xmm14
	vpaddd	%xmm5, %xmm0, %xmm0
	vpxor	%xmm0, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm5, %xmm5
	vpslld	$12, %xmm5, %xmm15
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm5, %xmm0, %xmm0
	vpxor	%xmm0, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm5, %xmm5
	vpslld	$7, %xmm5, %xmm15
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vmovdqu	%xmm14, 32(%rsp)
	vmovdqu	48(%rsp), %xmm14
	vpaddd	%xmm6, %xmm1, %xmm1
	vpxor	%xmm1, %xmm12, %xmm12
	vpshufb	(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm11, %xmm11
	vpxor	%xmm11, %xmm6, %xmm6
	vpslld	$12, %xmm6, %xmm15
	vpsrld	$20, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm6, %xmm1, %xmm1
	vpxor	%xmm1, %xmm12, %xmm12
	vpshufb	16(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm11, %xmm11
	vpxor	%xmm11, %xmm6, %xmm6
	vpslld	$7, %xmm6, %xmm15
	vpsrld	$25, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm7, %xmm2, %xmm2
	vpxor	%xmm2, %xmm13, %xmm13
	vpshufb	(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm15
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm2, %xmm2
	vpxor	%xmm2, %xmm13, %xmm13
	vpshufb	16(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm15
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm4, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm9, %xmm9
	vpxor	%xmm9, %xmm4, %xmm4
	vpslld	$12, %xmm4, %xmm15
	vpsrld	$20, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm4, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm9, %xmm9
	vpxor	%xmm9, %xmm4, %xmm4
	vpslld	$7, %xmm4, %xmm15
	vpsrld	$25, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$31
	vmovdqu	32(%rsp), %xmm15
	vpaddd	336(%rsp), %xmm0, %xmm0
	vpaddd	352(%rsp), %xmm1, %xmm1
	vpaddd	368(%rsp), %xmm2, %xmm2
	vpaddd	384(%rsp), %xmm3, %xmm3
	vpaddd	400(%rsp), %xmm4, %xmm4
	vpaddd	416(%rsp), %xmm5, %xmm5
	vpaddd	432(%rsp), %xmm6, %xmm6
	vpaddd	448(%rsp), %xmm7, %xmm7
	vpaddd	464(%rsp), %xmm8, %xmm8
	vpaddd	480(%rsp), %xmm9, %xmm9
	vpaddd	496(%rsp), %xmm10, %xmm10
	vpaddd	512(%rsp), %xmm11, %xmm11
	vpaddd	528(%rsp), %xmm12, %xmm12
	vpaddd	544(%rsp), %xmm13, %xmm13
	vpaddd	560(%rsp), %xmm14, %xmm14
	vpaddd	576(%rsp), %xmm15, %xmm15
	vmovdqu	%xmm8, 80(%rsp)
	vmovdqu	%xmm9, 96(%rsp)
	vmovdqu	%xmm10, 112(%rsp)
	vmovdqu	%xmm11, 128(%rsp)
	vmovdqu	%xmm12, 144(%rsp)
	vmovdqu	%xmm13, 160(%rsp)
	vmovdqu	%xmm14, 176(%rsp)
	vmovdqu	%xmm15, 192(%rsp)
	vpunpckldq	%xmm1, %xmm0, %xmm8
	vpunpckhdq	%xmm1, %xmm0, %xmm0
	vpunpckldq	%xmm3, %xmm2, %xmm1
	vpunpckhdq	%xmm3, %xmm2, %xmm2
	vpunpckldq	%xmm5, %xmm4, %xmm3
	vpunpckhdq	%xmm5, %xmm4, %xmm4
	vpunpckldq	%xmm7, %xmm6, %xmm5
	vpunpckhdq	%xmm7, %xmm6, %xmm6
	vpunpcklqdq	%xmm1, %xmm8, %xmm7
	vpunpcklqdq	%xmm5, %xmm3, %xmm9
	vpunpckhqdq	%xmm1, %xmm8, %xmm1
	vpunpckhqdq	%xmm5, %xmm3, %xmm3
	vpunpcklqdq	%xmm2, %xmm0, %xmm5
	vpunpcklqdq	%xmm6, %xmm4, %xmm8
	vpunpckhqdq	%xmm2, %xmm0, %xmm0
	vpunpckhqdq	%xmm6, %xmm4, %xmm2
	vpxor	(%rsi), %xmm7, %xmm4
	vpxor	16(%rsi), %xmm9, %xmm6
	vpxor	64(%rsi), %xmm1, %xmm1
	vpxor	80(%rsi), %xmm3, %xmm3
	vpxor	128(%rsi), %xmm5, %xmm5
	vpxor	144(%rsi), %xmm8, %xmm7
	vpxor	192(%rsi), %xmm0, %xmm0
	vpxor	208(%rsi), %xmm2, %xmm2
	vmovdqu	%xmm4, (%rdi)
	vmovdqu	%xmm6, 16(%rdi)
	vmovdqu	%xmm1, 64(%rdi)
	vmovdqu	%xmm3, 80(%rdi)
	vmovdqu	%xmm5, 128(%rdi)
	vmovdqu	%xmm7, 144(%rdi)
	vmovdqu	%xmm0, 192(%rdi)
	vmovdqu	%xmm2, 208(%rdi)
	vmovdqu	80(%rsp), %xmm0
	vmovdqu	112(%rsp), %xmm1
	vmovdqu	144(%rsp), %xmm2
	vmovdqu	176(%rsp), %xmm3
	vpunpckldq	96(%rsp), %xmm0, %xmm4
	vpunpckhdq	96(%rsp), %xmm0, %xmm0
	vpunpckldq	128(%rsp), %xmm1, %xmm5
	vpunpckhdq	128(%rsp), %xmm1, %xmm1
	vpunpckldq	160(%rsp), %xmm2, %xmm6
	vpunpckhdq	160(%rsp), %xmm2, %xmm2
	vpunpckldq	192(%rsp), %xmm3, %xmm7
	vpunpckhdq	192(%rsp), %xmm3, %xmm3
	vpunpcklqdq	%xmm5, %xmm4, %xmm8
	vpunpcklqdq	%xmm7, %xmm6, %xmm9
	vpunpckhqdq	%xmm5, %xmm4, %xmm4
	vpunpckhqdq	%xmm7, %xmm6, %xmm5
	vpunpcklqdq	%xmm1, %xmm0, %xmm6
	vpunpcklqdq	%xmm3, %xmm2, %xmm7
	vpunpckhqdq	%xmm1, %xmm0, %xmm0
	vpunpckhqdq	%xmm3, %xmm2, %xmm1
	vpxor	32(%rsi), %xmm8, %xmm2
	vpxor	48(%rsi), %xmm9, %xmm3
	vpxor	96(%rsi), %xmm4, %xmm4
	vpxor	112(%rsi), %xmm5, %xmm5
	vpxor	160(%rsi), %xmm6, %xmm6
	vpxor	176(%rsi), %xmm7, %xmm7
	vpxor	224(%rsi), %xmm0, %xmm0
	vpxor	240(%rsi), %xmm1, %xmm1
	vmovdqu	%xmm2, 32(%rdi)
	vmovdqu	%xmm3, 48(%rdi)
	vmovdqu	%xmm4, 96(%rdi)
	vmovdqu	%xmm5, 112(%rdi)
	vmovdqu	%xmm6, 160(%rdi)
	vmovdqu	%xmm7, 176(%rdi)
	vmovdqu	%xmm0, 224(%rdi)
	vmovdqu	%xmm1, 240(%rdi)
	addq	$256, %rdi
	addq	$256, %rsi
	addq	$-256, %rdx
	vmovdqu	glob_data + 0(%rip), %xmm0
	vpaddd	528(%rsp), %xmm0, %xmm0
	vmovdqu	%xmm0, 528(%rsp)
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$29:
	cmpq	$256, %rdx
	jnb 	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$30
	cmpq	$0, %rdx
	jbe 	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$2
	vmovdqu	336(%rsp), %xmm0
	vmovdqu	352(%rsp), %xmm1
	vmovdqu	368(%rsp), %xmm2
	vmovdqu	384(%rsp), %xmm3
	vmovdqu	400(%rsp), %xmm4
	vmovdqu	416(%rsp), %xmm5
	vmovdqu	432(%rsp), %xmm6
	vmovdqu	448(%rsp), %xmm7
	vmovdqu	464(%rsp), %xmm8
	vmovdqu	480(%rsp), %xmm9
	vmovdqu	496(%rsp), %xmm10
	vmovdqu	512(%rsp), %xmm11
	vmovdqu	528(%rsp), %xmm12
	vmovdqu	544(%rsp), %xmm13
	vmovdqu	560(%rsp), %xmm14
	vmovdqu	576(%rsp), %xmm15
	vmovdqu	%xmm15, 32(%rsp)
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$28:
	vpaddd	%xmm4, %xmm0, %xmm0
	vpxor	%xmm0, %xmm12, %xmm12
	vpshufb	(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm8, %xmm8
	vpxor	%xmm8, %xmm4, %xmm4
	vpslld	$12, %xmm4, %xmm15
	vpsrld	$20, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm4, %xmm0, %xmm0
	vpxor	%xmm0, %xmm12, %xmm12
	vpshufb	16(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm8, %xmm8
	vpxor	%xmm8, %xmm4, %xmm4
	vpslld	$7, %xmm4, %xmm15
	vpsrld	$25, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm5, %xmm1, %xmm1
	vpxor	%xmm1, %xmm13, %xmm13
	vpshufb	(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm9, %xmm9
	vpxor	%xmm9, %xmm5, %xmm5
	vpslld	$12, %xmm5, %xmm15
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm5, %xmm1, %xmm1
	vpxor	%xmm1, %xmm13, %xmm13
	vpshufb	16(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm9, %xmm9
	vpxor	%xmm9, %xmm5, %xmm5
	vpslld	$7, %xmm5, %xmm15
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm6, %xmm2, %xmm2
	vpxor	%xmm2, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm6, %xmm6
	vpslld	$12, %xmm6, %xmm15
	vpsrld	$20, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm6, %xmm2, %xmm2
	vpxor	%xmm2, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm6, %xmm6
	vpslld	$7, %xmm6, %xmm15
	vpsrld	$25, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vmovdqu	%xmm14, 48(%rsp)
	vmovdqu	32(%rsp), %xmm14
	vpaddd	%xmm7, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm11, %xmm11
	vpxor	%xmm11, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm15
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm11, %xmm11
	vpxor	%xmm11, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm15
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vmovdqu	%xmm14, 64(%rsp)
	vmovdqu	48(%rsp), %xmm14
	vmovdqu	%xmm14, 48(%rsp)
	vmovdqu	64(%rsp), %xmm14
	vpaddd	%xmm5, %xmm0, %xmm0
	vpxor	%xmm0, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm5, %xmm5
	vpslld	$12, %xmm5, %xmm15
	vpsrld	$20, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vpaddd	%xmm5, %xmm0, %xmm0
	vpxor	%xmm0, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm10, %xmm10
	vpxor	%xmm10, %xmm5, %xmm5
	vpslld	$7, %xmm5, %xmm15
	vpsrld	$25, %xmm5, %xmm5
	vpxor	%xmm15, %xmm5, %xmm5
	vmovdqu	%xmm14, 32(%rsp)
	vmovdqu	48(%rsp), %xmm14
	vpaddd	%xmm6, %xmm1, %xmm1
	vpxor	%xmm1, %xmm12, %xmm12
	vpshufb	(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm11, %xmm11
	vpxor	%xmm11, %xmm6, %xmm6
	vpslld	$12, %xmm6, %xmm15
	vpsrld	$20, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm6, %xmm1, %xmm1
	vpxor	%xmm1, %xmm12, %xmm12
	vpshufb	16(%rsp), %xmm12, %xmm12
	vpaddd	%xmm12, %xmm11, %xmm11
	vpxor	%xmm11, %xmm6, %xmm6
	vpslld	$7, %xmm6, %xmm15
	vpsrld	$25, %xmm6, %xmm6
	vpxor	%xmm15, %xmm6, %xmm6
	vpaddd	%xmm7, %xmm2, %xmm2
	vpxor	%xmm2, %xmm13, %xmm13
	vpshufb	(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm15
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm2, %xmm2
	vpxor	%xmm2, %xmm13, %xmm13
	vpshufb	16(%rsp), %xmm13, %xmm13
	vpaddd	%xmm13, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm15
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm15, %xmm7, %xmm7
	vpaddd	%xmm4, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm9, %xmm9
	vpxor	%xmm9, %xmm4, %xmm4
	vpslld	$12, %xmm4, %xmm15
	vpsrld	$20, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	vpaddd	%xmm4, %xmm3, %xmm3
	vpxor	%xmm3, %xmm14, %xmm14
	vpshufb	16(%rsp), %xmm14, %xmm14
	vpaddd	%xmm14, %xmm9, %xmm9
	vpxor	%xmm9, %xmm4, %xmm4
	vpslld	$7, %xmm4, %xmm15
	vpsrld	$25, %xmm4, %xmm4
	vpxor	%xmm15, %xmm4, %xmm4
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$28
	vmovdqu	32(%rsp), %xmm15
	vpaddd	336(%rsp), %xmm0, %xmm0
	vpaddd	352(%rsp), %xmm1, %xmm1
	vpaddd	368(%rsp), %xmm2, %xmm2
	vpaddd	384(%rsp), %xmm3, %xmm3
	vpaddd	400(%rsp), %xmm4, %xmm4
	vpaddd	416(%rsp), %xmm5, %xmm5
	vpaddd	432(%rsp), %xmm6, %xmm6
	vpaddd	448(%rsp), %xmm7, %xmm7
	vpaddd	464(%rsp), %xmm8, %xmm8
	vpaddd	480(%rsp), %xmm9, %xmm9
	vpaddd	496(%rsp), %xmm10, %xmm10
	vpaddd	512(%rsp), %xmm11, %xmm11
	vpaddd	528(%rsp), %xmm12, %xmm12
	vpaddd	544(%rsp), %xmm13, %xmm13
	vpaddd	560(%rsp), %xmm14, %xmm14
	vpaddd	576(%rsp), %xmm15, %xmm15
	vmovdqu	%xmm8, 80(%rsp)
	vmovdqu	%xmm9, 96(%rsp)
	vmovdqu	%xmm10, 112(%rsp)
	vmovdqu	%xmm11, 128(%rsp)
	vmovdqu	%xmm12, 144(%rsp)
	vmovdqu	%xmm13, 160(%rsp)
	vmovdqu	%xmm14, 176(%rsp)
	vmovdqu	%xmm15, 192(%rsp)
	vpunpckldq	%xmm1, %xmm0, %xmm8
	vpunpckhdq	%xmm1, %xmm0, %xmm0
	vpunpckldq	%xmm3, %xmm2, %xmm1
	vpunpckhdq	%xmm3, %xmm2, %xmm2
	vpunpckldq	%xmm5, %xmm4, %xmm3
	vpunpckhdq	%xmm5, %xmm4, %xmm4
	vpunpckldq	%xmm7, %xmm6, %xmm5
	vpunpckhdq	%xmm7, %xmm6, %xmm6
	vpunpcklqdq	%xmm1, %xmm8, %xmm7
	vpunpcklqdq	%xmm5, %xmm3, %xmm9
	vpunpckhqdq	%xmm1, %xmm8, %xmm1
	vpunpckhqdq	%xmm5, %xmm3, %xmm3
	vpunpcklqdq	%xmm2, %xmm0, %xmm5
	vpunpcklqdq	%xmm6, %xmm4, %xmm8
	vpunpckhqdq	%xmm2, %xmm0, %xmm0
	vpunpckhqdq	%xmm6, %xmm4, %xmm2
	vmovdqu	%xmm7, 208(%rsp)
	vmovdqu	%xmm9, 224(%rsp)
	vmovdqu	%xmm1, 240(%rsp)
	vmovdqu	%xmm3, 256(%rsp)
	vmovdqu	%xmm5, 272(%rsp)
	vmovdqu	%xmm8, 288(%rsp)
	vmovdqu	%xmm0, 304(%rsp)
	vmovdqu	%xmm2, 320(%rsp)
	vmovdqu	80(%rsp), %xmm0
	vmovdqu	112(%rsp), %xmm1
	vmovdqu	144(%rsp), %xmm2
	vmovdqu	176(%rsp), %xmm3
	vpunpckldq	96(%rsp), %xmm0, %xmm4
	vpunpckhdq	96(%rsp), %xmm0, %xmm0
	vpunpckldq	128(%rsp), %xmm1, %xmm5
	vpunpckhdq	128(%rsp), %xmm1, %xmm1
	vpunpckldq	160(%rsp), %xmm2, %xmm6
	vpunpckhdq	160(%rsp), %xmm2, %xmm2
	vpunpckldq	192(%rsp), %xmm3, %xmm7
	vpunpckhdq	192(%rsp), %xmm3, %xmm3
	vpunpcklqdq	%xmm5, %xmm4, %xmm8
	vpunpcklqdq	%xmm7, %xmm6, %xmm9
	vpunpckhqdq	%xmm5, %xmm4, %xmm4
	vpunpckhqdq	%xmm7, %xmm6, %xmm5
	vpunpcklqdq	%xmm1, %xmm0, %xmm6
	vpunpcklqdq	%xmm3, %xmm2, %xmm7
	vpunpckhqdq	%xmm1, %xmm0, %xmm0
	vpunpckhqdq	%xmm3, %xmm2, %xmm1
	vmovdqu	208(%rsp), %xmm2
	vmovdqu	224(%rsp), %xmm12
	vmovdqu	%xmm8, %xmm11
	vmovdqu	%xmm9, %xmm10
	vmovdqu	240(%rsp), %xmm9
	vmovdqu	256(%rsp), %xmm8
	vmovdqu	%xmm5, %xmm3
	cmpq	$128, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$27
	vpxor	(%rsi), %xmm2, %xmm2
	vmovdqu	%xmm2, (%rdi)
	vpxor	16(%rsi), %xmm12, %xmm2
	vmovdqu	%xmm2, 16(%rdi)
	vpxor	32(%rsi), %xmm11, %xmm2
	vmovdqu	%xmm2, 32(%rdi)
	vpxor	48(%rsi), %xmm10, %xmm2
	vmovdqu	%xmm2, 48(%rdi)
	vpxor	64(%rsi), %xmm9, %xmm2
	vmovdqu	%xmm2, 64(%rdi)
	vpxor	80(%rsi), %xmm8, %xmm2
	vmovdqu	%xmm2, 80(%rdi)
	vpxor	96(%rsi), %xmm4, %xmm2
	vmovdqu	%xmm2, 96(%rdi)
	vpxor	112(%rsi), %xmm3, %xmm2
	vmovdqu	%xmm2, 112(%rdi)
	addq	$128, %rdi
	addq	$128, %rsi
	addq	$-128, %rdx
	vmovdqu	272(%rsp), %xmm2
	vmovdqu	288(%rsp), %xmm12
	vmovdqu	%xmm6, %xmm11
	vmovdqu	%xmm7, %xmm10
	vmovdqu	304(%rsp), %xmm9
	vmovdqu	320(%rsp), %xmm8
	vmovdqu	%xmm0, %xmm4
	vmovdqu	%xmm1, %xmm3
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$27:
	cmpq	$64, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$26
	vpxor	(%rsi), %xmm2, %xmm0
	vmovdqu	%xmm0, (%rdi)
	vpxor	16(%rsi), %xmm12, %xmm0
	vmovdqu	%xmm0, 16(%rdi)
	vpxor	32(%rsi), %xmm11, %xmm0
	vmovdqu	%xmm0, 32(%rdi)
	vpxor	48(%rsi), %xmm10, %xmm0
	vmovdqu	%xmm0, 48(%rdi)
	addq	$64, %rdi
	addq	$64, %rsi
	addq	$-64, %rdx
	vmovdqu	%xmm9, %xmm2
	vmovdqu	%xmm8, %xmm12
	vmovdqu	%xmm4, %xmm11
	vmovdqu	%xmm3, %xmm10
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$26:
	cmpq	$32, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$25
	vpxor	(%rsi), %xmm2, %xmm0
	vmovdqu	%xmm0, (%rdi)
	vpxor	16(%rsi), %xmm12, %xmm0
	vmovdqu	%xmm0, 16(%rdi)
	addq	$32, %rdi
	addq	$32, %rsi
	addq	$-32, %rdx
	vmovdqu	%xmm11, %xmm2
	vmovdqu	%xmm10, %xmm12
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$25:
	cmpq	$16, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$24
	vpxor	(%rsi), %xmm2, %xmm0
	vmovdqu	%xmm0, (%rdi)
	addq	$16, %rdi
	addq	$16, %rsi
	addq	$-16, %rdx
	vmovdqu	%xmm12, %xmm2
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$24:
	vpextrq	$0, %xmm2, %rax
	cmpq	$8, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$21
	xorq	(%rsi), %rax
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$8, %rsi
	addq	$-8, %rdx
	vpextrq	$1, %xmm2, %rax
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$23:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$21
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$22:
	movb	%al, %cl
	xorb	(%rsi), %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	incq	%rsi
	addq	$-1, %rdx
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$21:
	cmpq	$0, %rdx
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$22
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$20:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$2
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$1:
	vmovdqu	glob_data + 64(%rip), %xmm0
	vmovdqu	glob_data + 48(%rip), %xmm1
	vmovdqu	glob_data + 208(%rip), %xmm2
	vmovdqu	(%r8), %xmm3
	vmovdqu	16(%r8), %xmm4
	vpxor	%xmm5, %xmm5, %xmm5
	vpinsrd	$1, (%rcx), %xmm5, %xmm5
	vpinsrq	$1, 4(%rcx), %xmm5, %xmm5
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$17
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$18:
	vmovdqu	%xmm2, %xmm6
	vmovdqu	%xmm3, %xmm7
	vmovdqu	%xmm4, %xmm8
	vmovdqu	%xmm5, %xmm9
	vmovdqu	%xmm2, %xmm10
	vmovdqu	%xmm3, %xmm11
	vmovdqu	%xmm4, %xmm12
	vmovdqu	%xmm5, %xmm13
	vpaddd	glob_data + 32(%rip), %xmm13, %xmm13
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$19:
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm0, %xmm9, %xmm9
	vpshufb	%xmm0, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm14
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$12, %xmm11, %xmm14
	vpsrld	$20, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm1, %xmm9, %xmm9
	vpshufb	%xmm1, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm14
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$7, %xmm11, %xmm14
	vpsrld	$25, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpshufd	$57, %xmm7, %xmm7
	vpshufd	$78, %xmm8, %xmm8
	vpshufd	$-109, %xmm9, %xmm9
	vpshufd	$57, %xmm11, %xmm11
	vpshufd	$78, %xmm12, %xmm12
	vpshufd	$-109, %xmm13, %xmm13
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm0, %xmm9, %xmm9
	vpshufb	%xmm0, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm14
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$12, %xmm11, %xmm14
	vpsrld	$20, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm1, %xmm9, %xmm9
	vpshufb	%xmm1, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm14
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$7, %xmm11, %xmm14
	vpsrld	$25, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpshufd	$-109, %xmm7, %xmm7
	vpshufd	$78, %xmm8, %xmm8
	vpshufd	$57, %xmm9, %xmm9
	vpshufd	$-109, %xmm11, %xmm11
	vpshufd	$78, %xmm12, %xmm12
	vpshufd	$57, %xmm13, %xmm13
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$19
	vpaddd	%xmm2, %xmm6, %xmm6
	vpaddd	%xmm3, %xmm7, %xmm7
	vpaddd	%xmm4, %xmm8, %xmm8
	vpaddd	%xmm5, %xmm9, %xmm9
	vpaddd	%xmm2, %xmm10, %xmm10
	vpaddd	%xmm3, %xmm11, %xmm11
	vpaddd	%xmm4, %xmm12, %xmm12
	vpaddd	%xmm5, %xmm13, %xmm13
	vpaddd	glob_data + 32(%rip), %xmm13, %xmm13
	vpxor	(%rsi), %xmm6, %xmm6
	vmovdqu	%xmm6, (%rdi)
	vpxor	16(%rsi), %xmm7, %xmm6
	vmovdqu	%xmm6, 16(%rdi)
	vpxor	32(%rsi), %xmm8, %xmm6
	vmovdqu	%xmm6, 32(%rdi)
	vpxor	48(%rsi), %xmm9, %xmm6
	vmovdqu	%xmm6, 48(%rdi)
	vpxor	64(%rsi), %xmm10, %xmm6
	vmovdqu	%xmm6, 64(%rdi)
	vpxor	80(%rsi), %xmm11, %xmm6
	vmovdqu	%xmm6, 80(%rdi)
	vpxor	96(%rsi), %xmm12, %xmm6
	vmovdqu	%xmm6, 96(%rdi)
	vpxor	112(%rsi), %xmm13, %xmm6
	vmovdqu	%xmm6, 112(%rdi)
	addq	$128, %rdi
	addq	$128, %rsi
	addq	$-128, %rdx
	vpaddd	glob_data + 16(%rip), %xmm5, %xmm5
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$17:
	cmpq	$128, %rdx
	jnb 	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$18
	cmpq	$64, %rdx
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$3
	vmovdqu	%xmm2, %xmm6
	vmovdqu	%xmm3, %xmm7
	vmovdqu	%xmm4, %xmm8
	vmovdqu	%xmm5, %xmm9
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$16:
	vpaddd	%xmm7, %xmm6, %xmm6
	vpxor	%xmm6, %xmm9, %xmm9
	vpshufb	%xmm0, %xmm9, %xmm9
	vpaddd	%xmm9, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm10
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm10, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm6, %xmm6
	vpxor	%xmm6, %xmm9, %xmm9
	vpshufb	%xmm1, %xmm9, %xmm9
	vpaddd	%xmm9, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm10
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm10, %xmm7, %xmm7
	vpshufd	$57, %xmm7, %xmm7
	vpshufd	$78, %xmm8, %xmm8
	vpshufd	$-109, %xmm9, %xmm9
	vpaddd	%xmm7, %xmm6, %xmm6
	vpxor	%xmm6, %xmm9, %xmm9
	vpshufb	%xmm0, %xmm9, %xmm9
	vpaddd	%xmm9, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm10
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm10, %xmm7, %xmm7
	vpaddd	%xmm7, %xmm6, %xmm6
	vpxor	%xmm6, %xmm9, %xmm9
	vpshufb	%xmm1, %xmm9, %xmm9
	vpaddd	%xmm9, %xmm8, %xmm8
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm10
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm10, %xmm7, %xmm7
	vpshufd	$-109, %xmm7, %xmm7
	vpshufd	$78, %xmm8, %xmm8
	vpshufd	$57, %xmm9, %xmm9
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$16
	vpaddd	%xmm2, %xmm6, %xmm2
	vpaddd	%xmm3, %xmm7, %xmm3
	vpaddd	%xmm4, %xmm8, %xmm0
	vpaddd	%xmm5, %xmm9, %xmm1
	cmpq	$32, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$15
	vpxor	(%rsi), %xmm2, %xmm2
	vmovdqu	%xmm2, (%rdi)
	vpxor	16(%rsi), %xmm3, %xmm2
	vmovdqu	%xmm2, 16(%rdi)
	addq	$32, %rdi
	addq	$32, %rsi
	addq	$-32, %rdx
	vmovdqu	%xmm0, %xmm2
	vmovdqu	%xmm1, %xmm3
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$15:
	cmpq	$16, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$14
	vpxor	(%rsi), %xmm2, %xmm0
	vmovdqu	%xmm0, (%rdi)
	addq	$16, %rdi
	addq	$16, %rsi
	addq	$-16, %rdx
	vmovdqu	%xmm3, %xmm2
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$14:
	vpextrq	$0, %xmm2, %rax
	cmpq	$8, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$11
	xorq	(%rsi), %rax
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$8, %rsi
	addq	$-8, %rdx
	vpextrq	$1, %xmm2, %rax
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$13:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$11
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$12:
	movb	%al, %cl
	xorb	(%rsi), %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	incq	%rsi
	addq	$-1, %rdx
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$11:
	cmpq	$0, %rdx
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$12
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$2
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$3:
	vmovdqu	%xmm2, %xmm6
	vmovdqu	%xmm3, %xmm7
	vmovdqu	%xmm4, %xmm8
	vmovdqu	%xmm5, %xmm9
	vmovdqu	%xmm2, %xmm10
	vmovdqu	%xmm3, %xmm11
	vmovdqu	%xmm4, %xmm12
	vmovdqu	%xmm5, %xmm13
	vpaddd	glob_data + 32(%rip), %xmm13, %xmm13
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$10:
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm0, %xmm9, %xmm9
	vpshufb	%xmm0, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm14
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$12, %xmm11, %xmm14
	vpsrld	$20, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm1, %xmm9, %xmm9
	vpshufb	%xmm1, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm14
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$7, %xmm11, %xmm14
	vpsrld	$25, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpshufd	$57, %xmm7, %xmm7
	vpshufd	$78, %xmm8, %xmm8
	vpshufd	$-109, %xmm9, %xmm9
	vpshufd	$57, %xmm11, %xmm11
	vpshufd	$78, %xmm12, %xmm12
	vpshufd	$-109, %xmm13, %xmm13
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm0, %xmm9, %xmm9
	vpshufb	%xmm0, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$12, %xmm7, %xmm14
	vpsrld	$20, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$12, %xmm11, %xmm14
	vpsrld	$20, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpaddd	%xmm7, %xmm6, %xmm6
	vpaddd	%xmm11, %xmm10, %xmm10
	vpxor	%xmm6, %xmm9, %xmm9
	vpxor	%xmm10, %xmm13, %xmm13
	vpshufb	%xmm1, %xmm9, %xmm9
	vpshufb	%xmm1, %xmm13, %xmm13
	vpaddd	%xmm9, %xmm8, %xmm8
	vpaddd	%xmm13, %xmm12, %xmm12
	vpxor	%xmm8, %xmm7, %xmm7
	vpslld	$7, %xmm7, %xmm14
	vpsrld	$25, %xmm7, %xmm7
	vpxor	%xmm12, %xmm11, %xmm11
	vpxor	%xmm14, %xmm7, %xmm7
	vpslld	$7, %xmm11, %xmm14
	vpsrld	$25, %xmm11, %xmm11
	vpxor	%xmm14, %xmm11, %xmm11
	vpshufd	$-109, %xmm7, %xmm7
	vpshufd	$78, %xmm8, %xmm8
	vpshufd	$57, %xmm9, %xmm9
	vpshufd	$-109, %xmm11, %xmm11
	vpshufd	$78, %xmm12, %xmm12
	vpshufd	$57, %xmm13, %xmm13
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$10
	vpaddd	%xmm2, %xmm6, %xmm0
	vpaddd	%xmm3, %xmm7, %xmm1
	vpaddd	%xmm4, %xmm8, %xmm6
	vpaddd	%xmm5, %xmm9, %xmm7
	vpaddd	%xmm2, %xmm10, %xmm9
	vpaddd	%xmm3, %xmm11, %xmm8
	vpaddd	%xmm4, %xmm12, %xmm2
	vpaddd	%xmm5, %xmm13, %xmm3
	vpaddd	glob_data + 32(%rip), %xmm3, %xmm3
	vpxor	(%rsi), %xmm0, %xmm0
	vmovdqu	%xmm0, (%rdi)
	vpxor	16(%rsi), %xmm1, %xmm0
	vmovdqu	%xmm0, 16(%rdi)
	vpxor	32(%rsi), %xmm6, %xmm0
	vmovdqu	%xmm0, 32(%rdi)
	vpxor	48(%rsi), %xmm7, %xmm0
	vmovdqu	%xmm0, 48(%rdi)
	addq	$64, %rdi
	addq	$64, %rsi
	addq	$-64, %rdx
	cmpq	$32, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$9
	vpxor	(%rsi), %xmm9, %xmm0
	vmovdqu	%xmm0, (%rdi)
	vpxor	16(%rsi), %xmm8, %xmm0
	vmovdqu	%xmm0, 16(%rdi)
	addq	$32, %rdi
	addq	$32, %rsi
	addq	$-32, %rdx
	vmovdqu	%xmm2, %xmm9
	vmovdqu	%xmm3, %xmm8
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$9:
	cmpq	$16, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$8
	vpxor	(%rsi), %xmm9, %xmm0
	vmovdqu	%xmm0, (%rdi)
	addq	$16, %rdi
	addq	$16, %rsi
	addq	$-16, %rdx
	vmovdqu	%xmm8, %xmm9
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$8:
	vpextrq	$0, %xmm9, %rax
	cmpq	$8, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$5
	xorq	(%rsi), %rax
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$8, %rsi
	addq	$-8, %rdx
	vpextrq	$1, %xmm9, %rax
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$7:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$5
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$6:
	movb	%al, %cl
	xorb	(%rsi), %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	incq	%rsi
	addq	$-1, %rdx
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$5:
	cmpq	$0, %rdx
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$6
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$4:
Ljade_stream_chacha_chacha20_ietf_amd64_avx_xor$2:
	xorq	%rax, %rax
	movq	%r10, %rsp
	ret 
	.data
	.p2align	5
_glob_data:
glob_data:
      .byte 4
      .byte 0
      .byte 0
      .byte 0
      .byte 4
      .byte 0
      .byte 0
      .byte 0
      .byte 4
      .byte 0
      .byte 0
      .byte 0
      .byte 4
      .byte 0
      .byte 0
      .byte 0
      .byte 2
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 1
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 3
      .byte 0
      .byte 1
      .byte 2
      .byte 7
      .byte 4
      .byte 5
      .byte 6
      .byte 11
      .byte 8
      .byte 9
      .byte 10
      .byte 15
      .byte 12
      .byte 13
      .byte 14
      .byte 2
      .byte 3
      .byte 0
      .byte 1
      .byte 6
      .byte 7
      .byte 4
      .byte 5
      .byte 10
      .byte 11
      .byte 8
      .byte 9
      .byte 14
      .byte 15
      .byte 12
      .byte 13
      .byte 4
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 4
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 1
      .byte 0
      .byte 0
      .byte 0
      .byte 2
      .byte 0
      .byte 0
      .byte 0
      .byte 3
      .byte 0
      .byte 0
      .byte 0
      .byte 101
      .byte 120
      .byte 112
      .byte 97
      .byte 101
      .byte 120
      .byte 112
      .byte 97
      .byte 101
      .byte 120
      .byte 112
      .byte 97
      .byte 101
      .byte 120
      .byte 112
      .byte 97
      .byte 110
      .byte 100
      .byte 32
      .byte 51
      .byte 110
      .byte 100
      .byte 32
      .byte 51
      .byte 110
      .byte 100
      .byte 32
      .byte 51
      .byte 110
      .byte 100
      .byte 32
      .byte 51
      .byte 50
      .byte 45
      .byte 98
      .byte 121
      .byte 50
      .byte 45
      .byte 98
      .byte 121
      .byte 50
      .byte 45
      .byte 98
      .byte 121
      .byte 50
      .byte 45
      .byte 98
      .byte 121
      .byte 116
      .byte 101
      .byte 32
      .byte 107
      .byte 116
      .byte 101
      .byte 32
      .byte 107
      .byte 116
      .byte 101
      .byte 32
      .byte 107
      .byte 116
      .byte 101
      .byte 32
      .byte 107
      .byte 2
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 1
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 101
      .byte 120
      .byte 112
      .byte 97
      .byte 110
      .byte 100
      .byte 32
      .byte 51
      .byte 50
      .byte 45
      .byte 98
      .byte 121
      .byte 116
      .byte 101
      .byte 32
      .byte 107
