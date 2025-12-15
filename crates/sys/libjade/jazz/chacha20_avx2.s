	.att_syntax
	.text
	.p2align	5
	.globl	_jade_stream_chacha_chacha20_ietf_amd64_avx2
	.globl	jade_stream_chacha_chacha20_ietf_amd64_avx2
	.globl	_jade_stream_chacha_chacha20_ietf_amd64_avx2_xor
	.globl	jade_stream_chacha_chacha20_ietf_amd64_avx2_xor
_jade_stream_chacha_chacha20_ietf_amd64_avx2:
jade_stream_chacha_chacha20_ietf_amd64_avx2:
	movq	%rsp, %r10
	leaq	-1152(%rsp), %rsp
	andq	$-32, %rsp
	cmpq	$257, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$1
	vmovdqu	glob_data + 160(%rip), %ymm0
	vmovdqu	glob_data + 128(%rip), %ymm1
	vmovdqu	%ymm0, (%rsp)
	vmovdqu	%ymm1, 32(%rsp)
	vmovdqu	glob_data + 256(%rip), %ymm0
	vmovdqu	glob_data + 288(%rip), %ymm1
	vmovdqu	glob_data + 320(%rip), %ymm2
	vmovdqu	glob_data + 352(%rip), %ymm3
	vpbroadcastd	(%rcx), %ymm4
	vpbroadcastd	4(%rcx), %ymm5
	vpbroadcastd	8(%rcx), %ymm6
	vpbroadcastd	12(%rcx), %ymm7
	vpbroadcastd	16(%rcx), %ymm8
	vpbroadcastd	20(%rcx), %ymm9
	vpbroadcastd	24(%rcx), %ymm10
	vpbroadcastd	28(%rcx), %ymm11
	vmovdqu	glob_data + 224(%rip), %ymm12
	vpbroadcastd	(%rdx), %ymm13
	vpbroadcastd	4(%rdx), %ymm14
	vpbroadcastd	8(%rdx), %ymm15
	vmovdqu	%ymm0, 640(%rsp)
	vmovdqu	%ymm1, 672(%rsp)
	vmovdqu	%ymm2, 704(%rsp)
	vmovdqu	%ymm3, 736(%rsp)
	vmovdqu	%ymm4, 768(%rsp)
	vmovdqu	%ymm5, 800(%rsp)
	vmovdqu	%ymm6, 832(%rsp)
	vmovdqu	%ymm7, 864(%rsp)
	vmovdqu	%ymm8, 896(%rsp)
	vmovdqu	%ymm9, 928(%rsp)
	vmovdqu	%ymm10, 960(%rsp)
	vmovdqu	%ymm11, 992(%rsp)
	vmovdqu	%ymm12, 1024(%rsp)
	vmovdqu	%ymm13, 1056(%rsp)
	vmovdqu	%ymm14, 1088(%rsp)
	vmovdqu	%ymm15, 1120(%rsp)
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$32
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$33:
	vmovdqu	640(%rsp), %ymm0
	vmovdqu	672(%rsp), %ymm1
	vmovdqu	704(%rsp), %ymm2
	vmovdqu	736(%rsp), %ymm3
	vmovdqu	768(%rsp), %ymm4
	vmovdqu	800(%rsp), %ymm5
	vmovdqu	832(%rsp), %ymm6
	vmovdqu	864(%rsp), %ymm7
	vmovdqu	896(%rsp), %ymm8
	vmovdqu	928(%rsp), %ymm9
	vmovdqu	960(%rsp), %ymm10
	vmovdqu	992(%rsp), %ymm11
	vmovdqu	1024(%rsp), %ymm12
	vmovdqu	1056(%rsp), %ymm13
	vmovdqu	1088(%rsp), %ymm14
	vmovdqu	1120(%rsp), %ymm15
	vmovdqu	%ymm15, 64(%rsp)
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$34:
	vpaddd	%ymm4, %ymm0, %ymm0
	vpxor	%ymm0, %ymm12, %ymm12
	vpshufb	(%rsp), %ymm12, %ymm12
	vpaddd	%ymm12, %ymm8, %ymm8
	vpaddd	%ymm6, %ymm2, %ymm2
	vpxor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm2, %ymm14, %ymm14
	vpslld	$12, %ymm4, %ymm15
	vpsrld	$20, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm4, %ymm0, %ymm0
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm0, %ymm12, %ymm12
	vpxor	%ymm10, %ymm6, %ymm6
	vpshufb	32(%rsp), %ymm12, %ymm12
	vpslld	$12, %ymm6, %ymm15
	vpsrld	$20, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpaddd	%ymm12, %ymm8, %ymm8
	vpaddd	%ymm6, %ymm2, %ymm2
	vpxor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm2, %ymm14, %ymm14
	vpslld	$7, %ymm4, %ymm15
	vpsrld	$25, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm10, %ymm6, %ymm6
	vpslld	$7, %ymm6, %ymm15
	vpsrld	$25, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vmovdqu	64(%rsp), %ymm15
	vmovdqu	%ymm14, 96(%rsp)
	vpaddd	%ymm5, %ymm1, %ymm1
	vpxor	%ymm1, %ymm13, %ymm13
	vpshufb	(%rsp), %ymm13, %ymm13
	vpaddd	%ymm13, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm3, %ymm3
	vpxor	%ymm9, %ymm5, %ymm5
	vpxor	%ymm3, %ymm15, %ymm14
	vpslld	$12, %ymm5, %ymm15
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm5, %ymm1, %ymm1
	vpaddd	%ymm14, %ymm11, %ymm11
	vpxor	%ymm1, %ymm13, %ymm13
	vpxor	%ymm11, %ymm7, %ymm7
	vpshufb	32(%rsp), %ymm13, %ymm13
	vpslld	$12, %ymm7, %ymm15
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpaddd	%ymm13, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm3, %ymm3
	vpxor	%ymm9, %ymm5, %ymm5
	vpxor	%ymm3, %ymm14, %ymm14
	vpslld	$7, %ymm5, %ymm15
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm11, %ymm11
	vpxor	%ymm11, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm15
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpaddd	%ymm6, %ymm1, %ymm1
	vpxor	%ymm1, %ymm12, %ymm12
	vpshufb	(%rsp), %ymm12, %ymm12
	vpaddd	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm0, %ymm0
	vpxor	%ymm11, %ymm6, %ymm6
	vpxor	%ymm0, %ymm14, %ymm14
	vpslld	$12, %ymm6, %ymm15
	vpsrld	$20, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm6, %ymm1, %ymm1
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm1, %ymm12, %ymm12
	vpxor	%ymm10, %ymm5, %ymm5
	vpshufb	32(%rsp), %ymm12, %ymm12
	vpslld	$12, %ymm5, %ymm15
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpaddd	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm0, %ymm0
	vpxor	%ymm11, %ymm6, %ymm6
	vpxor	%ymm0, %ymm14, %ymm14
	vpslld	$7, %ymm6, %ymm15
	vpsrld	$25, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm10, %ymm5, %ymm5
	vpslld	$7, %ymm5, %ymm15
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vmovdqu	96(%rsp), %ymm15
	vmovdqu	%ymm14, 64(%rsp)
	vpaddd	%ymm7, %ymm2, %ymm2
	vpxor	%ymm2, %ymm13, %ymm13
	vpshufb	(%rsp), %ymm13, %ymm13
	vpaddd	%ymm13, %ymm8, %ymm8
	vpaddd	%ymm4, %ymm3, %ymm3
	vpxor	%ymm8, %ymm7, %ymm7
	vpxor	%ymm3, %ymm15, %ymm14
	vpslld	$12, %ymm7, %ymm15
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm7, %ymm2, %ymm2
	vpaddd	%ymm14, %ymm9, %ymm9
	vpxor	%ymm2, %ymm13, %ymm13
	vpxor	%ymm9, %ymm4, %ymm4
	vpshufb	32(%rsp), %ymm13, %ymm13
	vpslld	$12, %ymm4, %ymm15
	vpsrld	$20, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpaddd	%ymm13, %ymm8, %ymm8
	vpaddd	%ymm4, %ymm3, %ymm3
	vpxor	%ymm8, %ymm7, %ymm7
	vpxor	%ymm3, %ymm14, %ymm14
	vpslld	$7, %ymm7, %ymm15
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm9, %ymm9
	vpxor	%ymm9, %ymm4, %ymm4
	vpslld	$7, %ymm4, %ymm15
	vpsrld	$25, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$34
	vmovdqu	64(%rsp), %ymm15
	vpaddd	640(%rsp), %ymm0, %ymm0
	vpaddd	672(%rsp), %ymm1, %ymm1
	vpaddd	704(%rsp), %ymm2, %ymm2
	vpaddd	736(%rsp), %ymm3, %ymm3
	vpaddd	768(%rsp), %ymm4, %ymm4
	vpaddd	800(%rsp), %ymm5, %ymm5
	vpaddd	832(%rsp), %ymm6, %ymm6
	vpaddd	864(%rsp), %ymm7, %ymm7
	vpaddd	896(%rsp), %ymm8, %ymm8
	vpaddd	928(%rsp), %ymm9, %ymm9
	vpaddd	960(%rsp), %ymm10, %ymm10
	vpaddd	992(%rsp), %ymm11, %ymm11
	vpaddd	1024(%rsp), %ymm12, %ymm12
	vpaddd	1056(%rsp), %ymm13, %ymm13
	vpaddd	1088(%rsp), %ymm14, %ymm14
	vpaddd	1120(%rsp), %ymm15, %ymm15
	vmovdqu	%ymm8, 128(%rsp)
	vmovdqu	%ymm9, 160(%rsp)
	vmovdqu	%ymm10, 192(%rsp)
	vmovdqu	%ymm11, 224(%rsp)
	vmovdqu	%ymm12, 256(%rsp)
	vmovdqu	%ymm13, 288(%rsp)
	vmovdqu	%ymm14, 320(%rsp)
	vmovdqu	%ymm15, 352(%rsp)
	vpunpckldq	%ymm1, %ymm0, %ymm8
	vpunpckhdq	%ymm1, %ymm0, %ymm0
	vpunpckldq	%ymm3, %ymm2, %ymm1
	vpunpckhdq	%ymm3, %ymm2, %ymm2
	vpunpckldq	%ymm5, %ymm4, %ymm3
	vpunpckhdq	%ymm5, %ymm4, %ymm4
	vpunpckldq	%ymm7, %ymm6, %ymm5
	vpunpckhdq	%ymm7, %ymm6, %ymm6
	vpunpcklqdq	%ymm1, %ymm8, %ymm7
	vpunpcklqdq	%ymm5, %ymm3, %ymm9
	vpunpckhqdq	%ymm1, %ymm8, %ymm1
	vpunpckhqdq	%ymm5, %ymm3, %ymm3
	vpunpcklqdq	%ymm2, %ymm0, %ymm5
	vpunpcklqdq	%ymm6, %ymm4, %ymm8
	vpunpckhqdq	%ymm2, %ymm0, %ymm0
	vpunpckhqdq	%ymm6, %ymm4, %ymm2
	vperm2i128	$32, %ymm9, %ymm7, %ymm4
	vperm2i128	$49, %ymm9, %ymm7, %ymm6
	vperm2i128	$32, %ymm3, %ymm1, %ymm7
	vperm2i128	$49, %ymm3, %ymm1, %ymm1
	vperm2i128	$32, %ymm8, %ymm5, %ymm3
	vperm2i128	$49, %ymm8, %ymm5, %ymm5
	vperm2i128	$32, %ymm2, %ymm0, %ymm8
	vperm2i128	$49, %ymm2, %ymm0, %ymm0
	vmovdqu	%ymm4, (%rdi)
	vmovdqu	%ymm7, 64(%rdi)
	vmovdqu	%ymm3, 128(%rdi)
	vmovdqu	%ymm8, 192(%rdi)
	vmovdqu	%ymm6, 256(%rdi)
	vmovdqu	%ymm1, 320(%rdi)
	vmovdqu	%ymm5, 384(%rdi)
	vmovdqu	%ymm0, 448(%rdi)
	vmovdqu	128(%rsp), %ymm0
	vmovdqu	192(%rsp), %ymm1
	vmovdqu	256(%rsp), %ymm2
	vmovdqu	320(%rsp), %ymm3
	vpunpckldq	160(%rsp), %ymm0, %ymm4
	vpunpckhdq	160(%rsp), %ymm0, %ymm0
	vpunpckldq	224(%rsp), %ymm1, %ymm5
	vpunpckhdq	224(%rsp), %ymm1, %ymm1
	vpunpckldq	288(%rsp), %ymm2, %ymm6
	vpunpckhdq	288(%rsp), %ymm2, %ymm2
	vpunpckldq	352(%rsp), %ymm3, %ymm7
	vpunpckhdq	352(%rsp), %ymm3, %ymm3
	vpunpcklqdq	%ymm5, %ymm4, %ymm8
	vpunpcklqdq	%ymm7, %ymm6, %ymm9
	vpunpckhqdq	%ymm5, %ymm4, %ymm4
	vpunpckhqdq	%ymm7, %ymm6, %ymm5
	vpunpcklqdq	%ymm1, %ymm0, %ymm6
	vpunpcklqdq	%ymm3, %ymm2, %ymm7
	vpunpckhqdq	%ymm1, %ymm0, %ymm0
	vpunpckhqdq	%ymm3, %ymm2, %ymm1
	vperm2i128	$32, %ymm9, %ymm8, %ymm2
	vperm2i128	$49, %ymm9, %ymm8, %ymm3
	vperm2i128	$32, %ymm5, %ymm4, %ymm8
	vperm2i128	$49, %ymm5, %ymm4, %ymm4
	vperm2i128	$32, %ymm7, %ymm6, %ymm5
	vperm2i128	$49, %ymm7, %ymm6, %ymm6
	vperm2i128	$32, %ymm1, %ymm0, %ymm7
	vperm2i128	$49, %ymm1, %ymm0, %ymm0
	vmovdqu	%ymm2, 32(%rdi)
	vmovdqu	%ymm8, 96(%rdi)
	vmovdqu	%ymm5, 160(%rdi)
	vmovdqu	%ymm7, 224(%rdi)
	vmovdqu	%ymm3, 288(%rdi)
	vmovdqu	%ymm4, 352(%rdi)
	vmovdqu	%ymm6, 416(%rdi)
	vmovdqu	%ymm0, 480(%rdi)
	addq	$512, %rdi
	addq	$-512, %rsi
	vmovdqu	glob_data + 0(%rip), %ymm0
	vpaddd	1024(%rsp), %ymm0, %ymm0
	vmovdqu	%ymm0, 1024(%rsp)
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$32:
	cmpq	$512, %rsi
	jnb 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$33
	cmpq	$0, %rsi
	jbe 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$2
	vmovdqu	640(%rsp), %ymm0
	vmovdqu	672(%rsp), %ymm1
	vmovdqu	704(%rsp), %ymm2
	vmovdqu	736(%rsp), %ymm3
	vmovdqu	768(%rsp), %ymm4
	vmovdqu	800(%rsp), %ymm5
	vmovdqu	832(%rsp), %ymm6
	vmovdqu	864(%rsp), %ymm7
	vmovdqu	896(%rsp), %ymm8
	vmovdqu	928(%rsp), %ymm9
	vmovdqu	960(%rsp), %ymm10
	vmovdqu	992(%rsp), %ymm11
	vmovdqu	1024(%rsp), %ymm12
	vmovdqu	1056(%rsp), %ymm13
	vmovdqu	1088(%rsp), %ymm14
	vmovdqu	1120(%rsp), %ymm15
	vmovdqu	%ymm15, 64(%rsp)
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$31:
	vpaddd	%ymm4, %ymm0, %ymm0
	vpxor	%ymm0, %ymm12, %ymm12
	vpshufb	(%rsp), %ymm12, %ymm12
	vpaddd	%ymm12, %ymm8, %ymm8
	vpaddd	%ymm6, %ymm2, %ymm2
	vpxor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm2, %ymm14, %ymm14
	vpslld	$12, %ymm4, %ymm15
	vpsrld	$20, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm4, %ymm0, %ymm0
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm0, %ymm12, %ymm12
	vpxor	%ymm10, %ymm6, %ymm6
	vpshufb	32(%rsp), %ymm12, %ymm12
	vpslld	$12, %ymm6, %ymm15
	vpsrld	$20, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpaddd	%ymm12, %ymm8, %ymm8
	vpaddd	%ymm6, %ymm2, %ymm2
	vpxor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm2, %ymm14, %ymm14
	vpslld	$7, %ymm4, %ymm15
	vpsrld	$25, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm10, %ymm6, %ymm6
	vpslld	$7, %ymm6, %ymm15
	vpsrld	$25, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vmovdqu	64(%rsp), %ymm15
	vmovdqu	%ymm14, 96(%rsp)
	vpaddd	%ymm5, %ymm1, %ymm1
	vpxor	%ymm1, %ymm13, %ymm13
	vpshufb	(%rsp), %ymm13, %ymm13
	vpaddd	%ymm13, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm3, %ymm3
	vpxor	%ymm9, %ymm5, %ymm5
	vpxor	%ymm3, %ymm15, %ymm14
	vpslld	$12, %ymm5, %ymm15
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm5, %ymm1, %ymm1
	vpaddd	%ymm14, %ymm11, %ymm11
	vpxor	%ymm1, %ymm13, %ymm13
	vpxor	%ymm11, %ymm7, %ymm7
	vpshufb	32(%rsp), %ymm13, %ymm13
	vpslld	$12, %ymm7, %ymm15
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpaddd	%ymm13, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm3, %ymm3
	vpxor	%ymm9, %ymm5, %ymm5
	vpxor	%ymm3, %ymm14, %ymm14
	vpslld	$7, %ymm5, %ymm15
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm11, %ymm11
	vpxor	%ymm11, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm15
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpaddd	%ymm6, %ymm1, %ymm1
	vpxor	%ymm1, %ymm12, %ymm12
	vpshufb	(%rsp), %ymm12, %ymm12
	vpaddd	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm0, %ymm0
	vpxor	%ymm11, %ymm6, %ymm6
	vpxor	%ymm0, %ymm14, %ymm14
	vpslld	$12, %ymm6, %ymm15
	vpsrld	$20, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm6, %ymm1, %ymm1
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm1, %ymm12, %ymm12
	vpxor	%ymm10, %ymm5, %ymm5
	vpshufb	32(%rsp), %ymm12, %ymm12
	vpslld	$12, %ymm5, %ymm15
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpaddd	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm0, %ymm0
	vpxor	%ymm11, %ymm6, %ymm6
	vpxor	%ymm0, %ymm14, %ymm14
	vpslld	$7, %ymm6, %ymm15
	vpsrld	$25, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm10, %ymm5, %ymm5
	vpslld	$7, %ymm5, %ymm15
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vmovdqu	96(%rsp), %ymm15
	vmovdqu	%ymm14, 64(%rsp)
	vpaddd	%ymm7, %ymm2, %ymm2
	vpxor	%ymm2, %ymm13, %ymm13
	vpshufb	(%rsp), %ymm13, %ymm13
	vpaddd	%ymm13, %ymm8, %ymm8
	vpaddd	%ymm4, %ymm3, %ymm3
	vpxor	%ymm8, %ymm7, %ymm7
	vpxor	%ymm3, %ymm15, %ymm14
	vpslld	$12, %ymm7, %ymm15
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm7, %ymm2, %ymm2
	vpaddd	%ymm14, %ymm9, %ymm9
	vpxor	%ymm2, %ymm13, %ymm13
	vpxor	%ymm9, %ymm4, %ymm4
	vpshufb	32(%rsp), %ymm13, %ymm13
	vpslld	$12, %ymm4, %ymm15
	vpsrld	$20, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpaddd	%ymm13, %ymm8, %ymm8
	vpaddd	%ymm4, %ymm3, %ymm3
	vpxor	%ymm8, %ymm7, %ymm7
	vpxor	%ymm3, %ymm14, %ymm14
	vpslld	$7, %ymm7, %ymm15
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm9, %ymm9
	vpxor	%ymm9, %ymm4, %ymm4
	vpslld	$7, %ymm4, %ymm15
	vpsrld	$25, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$31
	vmovdqu	64(%rsp), %ymm15
	vpaddd	640(%rsp), %ymm0, %ymm0
	vpaddd	672(%rsp), %ymm1, %ymm1
	vpaddd	704(%rsp), %ymm2, %ymm2
	vpaddd	736(%rsp), %ymm3, %ymm3
	vpaddd	768(%rsp), %ymm4, %ymm4
	vpaddd	800(%rsp), %ymm5, %ymm5
	vpaddd	832(%rsp), %ymm6, %ymm6
	vpaddd	864(%rsp), %ymm7, %ymm7
	vpaddd	896(%rsp), %ymm8, %ymm8
	vpaddd	928(%rsp), %ymm9, %ymm9
	vpaddd	960(%rsp), %ymm10, %ymm10
	vpaddd	992(%rsp), %ymm11, %ymm11
	vpaddd	1024(%rsp), %ymm12, %ymm12
	vpaddd	1056(%rsp), %ymm13, %ymm13
	vpaddd	1088(%rsp), %ymm14, %ymm14
	vpaddd	1120(%rsp), %ymm15, %ymm15
	vmovdqu	%ymm8, 128(%rsp)
	vmovdqu	%ymm9, 160(%rsp)
	vmovdqu	%ymm10, 192(%rsp)
	vmovdqu	%ymm11, 224(%rsp)
	vmovdqu	%ymm12, 256(%rsp)
	vmovdqu	%ymm13, 288(%rsp)
	vmovdqu	%ymm14, 320(%rsp)
	vmovdqu	%ymm15, 352(%rsp)
	vpunpckldq	%ymm1, %ymm0, %ymm8
	vpunpckhdq	%ymm1, %ymm0, %ymm0
	vpunpckldq	%ymm3, %ymm2, %ymm1
	vpunpckhdq	%ymm3, %ymm2, %ymm2
	vpunpckldq	%ymm5, %ymm4, %ymm3
	vpunpckhdq	%ymm5, %ymm4, %ymm4
	vpunpckldq	%ymm7, %ymm6, %ymm5
	vpunpckhdq	%ymm7, %ymm6, %ymm6
	vpunpcklqdq	%ymm1, %ymm8, %ymm7
	vpunpcklqdq	%ymm5, %ymm3, %ymm9
	vpunpckhqdq	%ymm1, %ymm8, %ymm1
	vpunpckhqdq	%ymm5, %ymm3, %ymm3
	vpunpcklqdq	%ymm2, %ymm0, %ymm5
	vpunpcklqdq	%ymm6, %ymm4, %ymm8
	vpunpckhqdq	%ymm2, %ymm0, %ymm0
	vpunpckhqdq	%ymm6, %ymm4, %ymm2
	vperm2i128	$32, %ymm9, %ymm7, %ymm4
	vperm2i128	$49, %ymm9, %ymm7, %ymm6
	vperm2i128	$32, %ymm3, %ymm1, %ymm7
	vperm2i128	$49, %ymm3, %ymm1, %ymm1
	vperm2i128	$32, %ymm8, %ymm5, %ymm3
	vperm2i128	$49, %ymm8, %ymm5, %ymm5
	vperm2i128	$32, %ymm2, %ymm0, %ymm8
	vperm2i128	$49, %ymm2, %ymm0, %ymm0
	vmovdqu	%ymm4, 384(%rsp)
	vmovdqu	%ymm7, 416(%rsp)
	vmovdqu	%ymm3, 448(%rsp)
	vmovdqu	%ymm8, 480(%rsp)
	vmovdqu	%ymm6, 512(%rsp)
	vmovdqu	%ymm1, 544(%rsp)
	vmovdqu	%ymm5, 576(%rsp)
	vmovdqu	%ymm0, 608(%rsp)
	vmovdqu	128(%rsp), %ymm0
	vmovdqu	192(%rsp), %ymm1
	vmovdqu	256(%rsp), %ymm2
	vmovdqu	320(%rsp), %ymm3
	vpunpckldq	160(%rsp), %ymm0, %ymm4
	vpunpckhdq	160(%rsp), %ymm0, %ymm0
	vpunpckldq	224(%rsp), %ymm1, %ymm5
	vpunpckhdq	224(%rsp), %ymm1, %ymm1
	vpunpckldq	288(%rsp), %ymm2, %ymm6
	vpunpckhdq	288(%rsp), %ymm2, %ymm2
	vpunpckldq	352(%rsp), %ymm3, %ymm7
	vpunpckhdq	352(%rsp), %ymm3, %ymm3
	vpunpcklqdq	%ymm5, %ymm4, %ymm8
	vpunpcklqdq	%ymm7, %ymm6, %ymm9
	vpunpckhqdq	%ymm5, %ymm4, %ymm4
	vpunpckhqdq	%ymm7, %ymm6, %ymm5
	vpunpcklqdq	%ymm1, %ymm0, %ymm6
	vpunpcklqdq	%ymm3, %ymm2, %ymm7
	vpunpckhqdq	%ymm1, %ymm0, %ymm0
	vpunpckhqdq	%ymm3, %ymm2, %ymm1
	vperm2i128	$32, %ymm9, %ymm8, %ymm2
	vperm2i128	$49, %ymm9, %ymm8, %ymm3
	vperm2i128	$32, %ymm5, %ymm4, %ymm8
	vperm2i128	$49, %ymm5, %ymm4, %ymm4
	vperm2i128	$32, %ymm7, %ymm6, %ymm5
	vperm2i128	$49, %ymm7, %ymm6, %ymm6
	vperm2i128	$32, %ymm1, %ymm0, %ymm7
	vperm2i128	$49, %ymm1, %ymm0, %ymm0
	vmovdqu	384(%rsp), %ymm12
	vmovdqu	%ymm2, %ymm11
	vmovdqu	416(%rsp), %ymm10
	vmovdqu	%ymm8, %ymm9
	vmovdqu	448(%rsp), %ymm8
	vmovdqu	480(%rsp), %ymm2
	vmovdqu	%ymm7, %ymm1
	cmpq	$256, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$30
	vmovdqu	%ymm12, (%rdi)
	vmovdqu	%ymm11, 32(%rdi)
	vmovdqu	%ymm10, 64(%rdi)
	vmovdqu	%ymm9, 96(%rdi)
	vmovdqu	%ymm8, 128(%rdi)
	vmovdqu	%ymm5, 160(%rdi)
	vmovdqu	%ymm2, 192(%rdi)
	vmovdqu	%ymm1, 224(%rdi)
	addq	$256, %rdi
	addq	$-256, %rsi
	vmovdqu	512(%rsp), %ymm12
	vmovdqu	%ymm3, %ymm11
	vmovdqu	544(%rsp), %ymm10
	vmovdqu	%ymm4, %ymm9
	vmovdqu	576(%rsp), %ymm8
	vmovdqu	%ymm6, %ymm5
	vmovdqu	608(%rsp), %ymm2
	vmovdqu	%ymm0, %ymm1
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$30:
	cmpq	$128, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$29
	vmovdqu	%ymm12, (%rdi)
	vmovdqu	%ymm11, 32(%rdi)
	vmovdqu	%ymm10, 64(%rdi)
	vmovdqu	%ymm9, 96(%rdi)
	addq	$128, %rdi
	addq	$-128, %rsi
	vmovdqu	%ymm8, %ymm12
	vmovdqu	%ymm5, %ymm11
	vmovdqu	%ymm2, %ymm10
	vmovdqu	%ymm1, %ymm9
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$29:
	cmpq	$64, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$28
	vmovdqu	%ymm12, (%rdi)
	vmovdqu	%ymm11, 32(%rdi)
	addq	$64, %rdi
	addq	$-64, %rsi
	vmovdqu	%ymm10, %ymm12
	vmovdqu	%ymm9, %ymm11
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$28:
	cmpq	$32, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$27
	vmovdqu	%ymm12, (%rdi)
	addq	$32, %rdi
	addq	$-32, %rsi
	vmovdqu	%ymm11, %ymm12
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$27:
	vmovdqu	%xmm12, %xmm0
	cmpq	$16, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$26
	vmovdqu	%xmm0, (%rdi)
	addq	$16, %rdi
	addq	$-16, %rsi
	vextracti128	$1, %ymm12, %xmm0
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$26:
	vpextrq	$0, %xmm0, %rax
	cmpq	$8, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$23
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$-8, %rsi
	vpextrq	$1, %xmm0, %rax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$25:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$23
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$24:
	movb	%al, %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	addq	$-1, %rsi
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$23:
	cmpq	$0, %rsi
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$24
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$22:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$2
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$1:
	vmovdqu	glob_data + 160(%rip), %ymm0
	vmovdqu	glob_data + 128(%rip), %ymm1
	vmovdqu	glob_data + 480(%rip), %ymm2
	vbroadcasti128	(%rcx), %ymm3
	vbroadcasti128	16(%rcx), %ymm4
	vpxor	%xmm5, %xmm5, %xmm5
	vpinsrd	$1, (%rdx), %xmm5, %xmm5
	vpinsrq	$1, 4(%rdx), %xmm5, %xmm5
	vpxor	%ymm6, %ymm6, %ymm6
	vinserti128	$0, %xmm5, %ymm6, %ymm6
	vinserti128	$1, %xmm5, %ymm6, %ymm5
	vpaddd	glob_data + 96(%rip), %ymm5, %ymm5
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$19
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$20:
	vmovdqu	%ymm2, %ymm6
	vmovdqu	%ymm3, %ymm7
	vmovdqu	%ymm4, %ymm8
	vmovdqu	%ymm5, %ymm9
	vmovdqu	%ymm2, %ymm10
	vmovdqu	%ymm3, %ymm11
	vmovdqu	%ymm4, %ymm12
	vmovdqu	%ymm5, %ymm13
	vpaddd	glob_data + 64(%rip), %ymm13, %ymm13
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$21:
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm0, %ymm9, %ymm9
	vpshufb	%ymm0, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$12, %ymm7, %ymm14
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$12, %ymm11, %ymm14
	vpsrld	$20, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm1, %ymm9, %ymm9
	vpshufb	%ymm1, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm14
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$7, %ymm11, %ymm14
	vpsrld	$25, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpshufd	$57, %ymm7, %ymm7
	vpshufd	$78, %ymm8, %ymm8
	vpshufd	$-109, %ymm9, %ymm9
	vpshufd	$57, %ymm11, %ymm11
	vpshufd	$78, %ymm12, %ymm12
	vpshufd	$-109, %ymm13, %ymm13
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm0, %ymm9, %ymm9
	vpshufb	%ymm0, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$12, %ymm7, %ymm14
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$12, %ymm11, %ymm14
	vpsrld	$20, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm1, %ymm9, %ymm9
	vpshufb	%ymm1, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm14
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$7, %ymm11, %ymm14
	vpsrld	$25, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpshufd	$-109, %ymm7, %ymm7
	vpshufd	$78, %ymm8, %ymm8
	vpshufd	$57, %ymm9, %ymm9
	vpshufd	$-109, %ymm11, %ymm11
	vpshufd	$78, %ymm12, %ymm12
	vpshufd	$57, %ymm13, %ymm13
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$21
	vpaddd	%ymm2, %ymm6, %ymm6
	vpaddd	%ymm3, %ymm7, %ymm7
	vpaddd	%ymm4, %ymm8, %ymm8
	vpaddd	%ymm5, %ymm9, %ymm9
	vpaddd	%ymm2, %ymm10, %ymm10
	vpaddd	%ymm3, %ymm11, %ymm11
	vpaddd	%ymm4, %ymm12, %ymm12
	vpaddd	%ymm5, %ymm13, %ymm13
	vpaddd	glob_data + 64(%rip), %ymm13, %ymm13
	vperm2i128	$32, %ymm7, %ymm6, %ymm14
	vperm2i128	$32, %ymm9, %ymm8, %ymm15
	vperm2i128	$49, %ymm7, %ymm6, %ymm6
	vperm2i128	$49, %ymm9, %ymm8, %ymm7
	vperm2i128	$32, %ymm11, %ymm10, %ymm8
	vperm2i128	$32, %ymm13, %ymm12, %ymm9
	vperm2i128	$49, %ymm11, %ymm10, %ymm10
	vperm2i128	$49, %ymm13, %ymm12, %ymm11
	vmovdqu	%ymm14, (%rdi)
	vmovdqu	%ymm15, 32(%rdi)
	vmovdqu	%ymm6, 64(%rdi)
	vmovdqu	%ymm7, 96(%rdi)
	vmovdqu	%ymm8, 128(%rdi)
	vmovdqu	%ymm9, 160(%rdi)
	vmovdqu	%ymm10, 192(%rdi)
	vmovdqu	%ymm11, 224(%rdi)
	addq	$256, %rdi
	addq	$-256, %rsi
	vpaddd	glob_data + 32(%rip), %ymm5, %ymm5
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$19:
	cmpq	$256, %rsi
	jnb 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$20
	cmpq	$128, %rsi
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$3
	vmovdqu	%ymm2, %ymm6
	vmovdqu	%ymm3, %ymm7
	vmovdqu	%ymm4, %ymm8
	vmovdqu	%ymm5, %ymm9
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$18:
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm9, %ymm9
	vpshufb	%ymm0, %ymm9, %ymm9
	vpaddd	%ymm9, %ymm8, %ymm8
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$12, %ymm7, %ymm10
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm10, %ymm7, %ymm7
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm9, %ymm9
	vpshufb	%ymm1, %ymm9, %ymm9
	vpaddd	%ymm9, %ymm8, %ymm8
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm10
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm10, %ymm7, %ymm7
	vpshufd	$57, %ymm7, %ymm7
	vpshufd	$78, %ymm8, %ymm8
	vpshufd	$-109, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm9, %ymm9
	vpshufb	%ymm0, %ymm9, %ymm9
	vpaddd	%ymm9, %ymm8, %ymm8
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$12, %ymm7, %ymm10
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm10, %ymm7, %ymm7
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm9, %ymm9
	vpshufb	%ymm1, %ymm9, %ymm9
	vpaddd	%ymm9, %ymm8, %ymm8
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm10
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm10, %ymm7, %ymm7
	vpshufd	$-109, %ymm7, %ymm7
	vpshufd	$78, %ymm8, %ymm8
	vpshufd	$57, %ymm9, %ymm9
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$18
	vpaddd	%ymm2, %ymm6, %ymm0
	vpaddd	%ymm3, %ymm7, %ymm1
	vpaddd	%ymm4, %ymm8, %ymm2
	vpaddd	%ymm5, %ymm9, %ymm3
	vperm2i128	$32, %ymm1, %ymm0, %ymm5
	vperm2i128	$32, %ymm3, %ymm2, %ymm4
	vperm2i128	$49, %ymm1, %ymm0, %ymm0
	vperm2i128	$49, %ymm3, %ymm2, %ymm1
	cmpq	$64, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$17
	vmovdqu	%ymm5, (%rdi)
	vmovdqu	%ymm4, 32(%rdi)
	addq	$64, %rdi
	addq	$-64, %rsi
	vmovdqu	%ymm0, %ymm5
	vmovdqu	%ymm1, %ymm4
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$17:
	cmpq	$32, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$16
	vmovdqu	%ymm5, (%rdi)
	addq	$32, %rdi
	addq	$-32, %rsi
	vmovdqu	%ymm4, %ymm5
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$16:
	vmovdqu	%xmm5, %xmm0
	cmpq	$16, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$15
	vmovdqu	%xmm0, (%rdi)
	addq	$16, %rdi
	addq	$-16, %rsi
	vextracti128	$1, %ymm5, %xmm0
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$15:
	vpextrq	$0, %xmm0, %rax
	cmpq	$8, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$12
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$-8, %rsi
	vpextrq	$1, %xmm0, %rax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$14:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$12
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$13:
	movb	%al, %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	addq	$-1, %rsi
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$12:
	cmpq	$0, %rsi
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$13
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$2
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$3:
	vmovdqu	%ymm2, %ymm6
	vmovdqu	%ymm3, %ymm7
	vmovdqu	%ymm4, %ymm8
	vmovdqu	%ymm5, %ymm9
	vmovdqu	%ymm2, %ymm10
	vmovdqu	%ymm3, %ymm11
	vmovdqu	%ymm4, %ymm12
	vmovdqu	%ymm5, %ymm13
	vpaddd	glob_data + 64(%rip), %ymm13, %ymm13
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$11:
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm0, %ymm9, %ymm9
	vpshufb	%ymm0, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$12, %ymm7, %ymm14
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$12, %ymm11, %ymm14
	vpsrld	$20, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm1, %ymm9, %ymm9
	vpshufb	%ymm1, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm14
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$7, %ymm11, %ymm14
	vpsrld	$25, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpshufd	$57, %ymm7, %ymm7
	vpshufd	$78, %ymm8, %ymm8
	vpshufd	$-109, %ymm9, %ymm9
	vpshufd	$57, %ymm11, %ymm11
	vpshufd	$78, %ymm12, %ymm12
	vpshufd	$-109, %ymm13, %ymm13
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm0, %ymm9, %ymm9
	vpshufb	%ymm0, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$12, %ymm7, %ymm14
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$12, %ymm11, %ymm14
	vpsrld	$20, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm1, %ymm9, %ymm9
	vpshufb	%ymm1, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm14
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$7, %ymm11, %ymm14
	vpsrld	$25, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpshufd	$-109, %ymm7, %ymm7
	vpshufd	$78, %ymm8, %ymm8
	vpshufd	$57, %ymm9, %ymm9
	vpshufd	$-109, %ymm11, %ymm11
	vpshufd	$78, %ymm12, %ymm12
	vpshufd	$57, %ymm13, %ymm13
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$11
	vpaddd	%ymm2, %ymm6, %ymm0
	vpaddd	%ymm3, %ymm7, %ymm1
	vpaddd	%ymm4, %ymm8, %ymm6
	vpaddd	%ymm5, %ymm9, %ymm7
	vpaddd	%ymm2, %ymm10, %ymm2
	vpaddd	%ymm3, %ymm11, %ymm3
	vpaddd	%ymm4, %ymm12, %ymm4
	vpaddd	%ymm5, %ymm13, %ymm5
	vpaddd	glob_data + 64(%rip), %ymm5, %ymm5
	vperm2i128	$32, %ymm1, %ymm0, %ymm8
	vperm2i128	$32, %ymm7, %ymm6, %ymm9
	vperm2i128	$49, %ymm1, %ymm0, %ymm0
	vperm2i128	$49, %ymm7, %ymm6, %ymm1
	vperm2i128	$32, %ymm3, %ymm2, %ymm7
	vperm2i128	$32, %ymm5, %ymm4, %ymm6
	vperm2i128	$49, %ymm3, %ymm2, %ymm2
	vperm2i128	$49, %ymm5, %ymm4, %ymm3
	vmovdqu	%ymm8, (%rdi)
	vmovdqu	%ymm9, 32(%rdi)
	vmovdqu	%ymm0, 64(%rdi)
	vmovdqu	%ymm1, 96(%rdi)
	addq	$128, %rdi
	addq	$-128, %rsi
	cmpq	$64, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$10
	vmovdqu	%ymm7, (%rdi)
	vmovdqu	%ymm6, 32(%rdi)
	addq	$64, %rdi
	addq	$-64, %rsi
	vmovdqu	%ymm2, %ymm7
	vmovdqu	%ymm3, %ymm6
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$10:
	cmpq	$32, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$9
	vmovdqu	%ymm7, (%rdi)
	addq	$32, %rdi
	addq	$-32, %rsi
	vmovdqu	%ymm6, %ymm7
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$9:
	vmovdqu	%xmm7, %xmm0
	cmpq	$16, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$8
	vmovdqu	%xmm0, (%rdi)
	addq	$16, %rdi
	addq	$-16, %rsi
	vextracti128	$1, %ymm7, %xmm0
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$8:
	vpextrq	$0, %xmm0, %rax
	cmpq	$8, %rsi
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$5
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$-8, %rsi
	vpextrq	$1, %xmm0, %rax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$7:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$5
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$6:
	movb	%al, %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	addq	$-1, %rsi
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$5:
	cmpq	$0, %rsi
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2$6
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$4:
Ljade_stream_chacha_chacha20_ietf_amd64_avx2$2:
	xorq	%rax, %rax
	movq	%r10, %rsp
	ret 
_jade_stream_chacha_chacha20_ietf_amd64_avx2_xor:
jade_stream_chacha_chacha20_ietf_amd64_avx2_xor:
	movq	%rsp, %r10
	leaq	-1152(%rsp), %rsp
	andq	$-32, %rsp
	cmpq	$257, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$1
	vmovdqu	glob_data + 160(%rip), %ymm0
	vmovdqu	glob_data + 128(%rip), %ymm1
	vmovdqu	%ymm0, (%rsp)
	vmovdqu	%ymm1, 32(%rsp)
	vmovdqu	glob_data + 256(%rip), %ymm0
	vmovdqu	glob_data + 288(%rip), %ymm1
	vmovdqu	glob_data + 320(%rip), %ymm2
	vmovdqu	glob_data + 352(%rip), %ymm3
	vpbroadcastd	(%r8), %ymm4
	vpbroadcastd	4(%r8), %ymm5
	vpbroadcastd	8(%r8), %ymm6
	vpbroadcastd	12(%r8), %ymm7
	vpbroadcastd	16(%r8), %ymm8
	vpbroadcastd	20(%r8), %ymm9
	vpbroadcastd	24(%r8), %ymm10
	vpbroadcastd	28(%r8), %ymm11
	vmovdqu	glob_data + 224(%rip), %ymm12
	vpbroadcastd	(%rcx), %ymm13
	vpbroadcastd	4(%rcx), %ymm14
	vpbroadcastd	8(%rcx), %ymm15
	vmovdqu	%ymm0, 640(%rsp)
	vmovdqu	%ymm1, 672(%rsp)
	vmovdqu	%ymm2, 704(%rsp)
	vmovdqu	%ymm3, 736(%rsp)
	vmovdqu	%ymm4, 768(%rsp)
	vmovdqu	%ymm5, 800(%rsp)
	vmovdqu	%ymm6, 832(%rsp)
	vmovdqu	%ymm7, 864(%rsp)
	vmovdqu	%ymm8, 896(%rsp)
	vmovdqu	%ymm9, 928(%rsp)
	vmovdqu	%ymm10, 960(%rsp)
	vmovdqu	%ymm11, 992(%rsp)
	vmovdqu	%ymm12, 1024(%rsp)
	vmovdqu	%ymm13, 1056(%rsp)
	vmovdqu	%ymm14, 1088(%rsp)
	vmovdqu	%ymm15, 1120(%rsp)
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$32
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$33:
	vmovdqu	640(%rsp), %ymm0
	vmovdqu	672(%rsp), %ymm1
	vmovdqu	704(%rsp), %ymm2
	vmovdqu	736(%rsp), %ymm3
	vmovdqu	768(%rsp), %ymm4
	vmovdqu	800(%rsp), %ymm5
	vmovdqu	832(%rsp), %ymm6
	vmovdqu	864(%rsp), %ymm7
	vmovdqu	896(%rsp), %ymm8
	vmovdqu	928(%rsp), %ymm9
	vmovdqu	960(%rsp), %ymm10
	vmovdqu	992(%rsp), %ymm11
	vmovdqu	1024(%rsp), %ymm12
	vmovdqu	1056(%rsp), %ymm13
	vmovdqu	1088(%rsp), %ymm14
	vmovdqu	1120(%rsp), %ymm15
	vmovdqu	%ymm15, 64(%rsp)
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$34:
	vpaddd	%ymm4, %ymm0, %ymm0
	vpxor	%ymm0, %ymm12, %ymm12
	vpshufb	(%rsp), %ymm12, %ymm12
	vpaddd	%ymm12, %ymm8, %ymm8
	vpaddd	%ymm6, %ymm2, %ymm2
	vpxor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm2, %ymm14, %ymm14
	vpslld	$12, %ymm4, %ymm15
	vpsrld	$20, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm4, %ymm0, %ymm0
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm0, %ymm12, %ymm12
	vpxor	%ymm10, %ymm6, %ymm6
	vpshufb	32(%rsp), %ymm12, %ymm12
	vpslld	$12, %ymm6, %ymm15
	vpsrld	$20, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpaddd	%ymm12, %ymm8, %ymm8
	vpaddd	%ymm6, %ymm2, %ymm2
	vpxor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm2, %ymm14, %ymm14
	vpslld	$7, %ymm4, %ymm15
	vpsrld	$25, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm10, %ymm6, %ymm6
	vpslld	$7, %ymm6, %ymm15
	vpsrld	$25, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vmovdqu	64(%rsp), %ymm15
	vmovdqu	%ymm14, 96(%rsp)
	vpaddd	%ymm5, %ymm1, %ymm1
	vpxor	%ymm1, %ymm13, %ymm13
	vpshufb	(%rsp), %ymm13, %ymm13
	vpaddd	%ymm13, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm3, %ymm3
	vpxor	%ymm9, %ymm5, %ymm5
	vpxor	%ymm3, %ymm15, %ymm14
	vpslld	$12, %ymm5, %ymm15
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm5, %ymm1, %ymm1
	vpaddd	%ymm14, %ymm11, %ymm11
	vpxor	%ymm1, %ymm13, %ymm13
	vpxor	%ymm11, %ymm7, %ymm7
	vpshufb	32(%rsp), %ymm13, %ymm13
	vpslld	$12, %ymm7, %ymm15
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpaddd	%ymm13, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm3, %ymm3
	vpxor	%ymm9, %ymm5, %ymm5
	vpxor	%ymm3, %ymm14, %ymm14
	vpslld	$7, %ymm5, %ymm15
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm11, %ymm11
	vpxor	%ymm11, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm15
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpaddd	%ymm6, %ymm1, %ymm1
	vpxor	%ymm1, %ymm12, %ymm12
	vpshufb	(%rsp), %ymm12, %ymm12
	vpaddd	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm0, %ymm0
	vpxor	%ymm11, %ymm6, %ymm6
	vpxor	%ymm0, %ymm14, %ymm14
	vpslld	$12, %ymm6, %ymm15
	vpsrld	$20, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm6, %ymm1, %ymm1
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm1, %ymm12, %ymm12
	vpxor	%ymm10, %ymm5, %ymm5
	vpshufb	32(%rsp), %ymm12, %ymm12
	vpslld	$12, %ymm5, %ymm15
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpaddd	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm0, %ymm0
	vpxor	%ymm11, %ymm6, %ymm6
	vpxor	%ymm0, %ymm14, %ymm14
	vpslld	$7, %ymm6, %ymm15
	vpsrld	$25, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm10, %ymm5, %ymm5
	vpslld	$7, %ymm5, %ymm15
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vmovdqu	96(%rsp), %ymm15
	vmovdqu	%ymm14, 64(%rsp)
	vpaddd	%ymm7, %ymm2, %ymm2
	vpxor	%ymm2, %ymm13, %ymm13
	vpshufb	(%rsp), %ymm13, %ymm13
	vpaddd	%ymm13, %ymm8, %ymm8
	vpaddd	%ymm4, %ymm3, %ymm3
	vpxor	%ymm8, %ymm7, %ymm7
	vpxor	%ymm3, %ymm15, %ymm14
	vpslld	$12, %ymm7, %ymm15
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm7, %ymm2, %ymm2
	vpaddd	%ymm14, %ymm9, %ymm9
	vpxor	%ymm2, %ymm13, %ymm13
	vpxor	%ymm9, %ymm4, %ymm4
	vpshufb	32(%rsp), %ymm13, %ymm13
	vpslld	$12, %ymm4, %ymm15
	vpsrld	$20, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpaddd	%ymm13, %ymm8, %ymm8
	vpaddd	%ymm4, %ymm3, %ymm3
	vpxor	%ymm8, %ymm7, %ymm7
	vpxor	%ymm3, %ymm14, %ymm14
	vpslld	$7, %ymm7, %ymm15
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm9, %ymm9
	vpxor	%ymm9, %ymm4, %ymm4
	vpslld	$7, %ymm4, %ymm15
	vpsrld	$25, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$34
	vmovdqu	64(%rsp), %ymm15
	vpaddd	640(%rsp), %ymm0, %ymm0
	vpaddd	672(%rsp), %ymm1, %ymm1
	vpaddd	704(%rsp), %ymm2, %ymm2
	vpaddd	736(%rsp), %ymm3, %ymm3
	vpaddd	768(%rsp), %ymm4, %ymm4
	vpaddd	800(%rsp), %ymm5, %ymm5
	vpaddd	832(%rsp), %ymm6, %ymm6
	vpaddd	864(%rsp), %ymm7, %ymm7
	vpaddd	896(%rsp), %ymm8, %ymm8
	vpaddd	928(%rsp), %ymm9, %ymm9
	vpaddd	960(%rsp), %ymm10, %ymm10
	vpaddd	992(%rsp), %ymm11, %ymm11
	vpaddd	1024(%rsp), %ymm12, %ymm12
	vpaddd	1056(%rsp), %ymm13, %ymm13
	vpaddd	1088(%rsp), %ymm14, %ymm14
	vpaddd	1120(%rsp), %ymm15, %ymm15
	vmovdqu	%ymm8, 128(%rsp)
	vmovdqu	%ymm9, 160(%rsp)
	vmovdqu	%ymm10, 192(%rsp)
	vmovdqu	%ymm11, 224(%rsp)
	vmovdqu	%ymm12, 256(%rsp)
	vmovdqu	%ymm13, 288(%rsp)
	vmovdqu	%ymm14, 320(%rsp)
	vmovdqu	%ymm15, 352(%rsp)
	vpunpckldq	%ymm1, %ymm0, %ymm8
	vpunpckhdq	%ymm1, %ymm0, %ymm0
	vpunpckldq	%ymm3, %ymm2, %ymm1
	vpunpckhdq	%ymm3, %ymm2, %ymm2
	vpunpckldq	%ymm5, %ymm4, %ymm3
	vpunpckhdq	%ymm5, %ymm4, %ymm4
	vpunpckldq	%ymm7, %ymm6, %ymm5
	vpunpckhdq	%ymm7, %ymm6, %ymm6
	vpunpcklqdq	%ymm1, %ymm8, %ymm7
	vpunpcklqdq	%ymm5, %ymm3, %ymm9
	vpunpckhqdq	%ymm1, %ymm8, %ymm1
	vpunpckhqdq	%ymm5, %ymm3, %ymm3
	vpunpcklqdq	%ymm2, %ymm0, %ymm5
	vpunpcklqdq	%ymm6, %ymm4, %ymm8
	vpunpckhqdq	%ymm2, %ymm0, %ymm0
	vpunpckhqdq	%ymm6, %ymm4, %ymm2
	vperm2i128	$32, %ymm9, %ymm7, %ymm4
	vperm2i128	$49, %ymm9, %ymm7, %ymm6
	vperm2i128	$32, %ymm3, %ymm1, %ymm7
	vperm2i128	$49, %ymm3, %ymm1, %ymm1
	vperm2i128	$32, %ymm8, %ymm5, %ymm3
	vperm2i128	$49, %ymm8, %ymm5, %ymm5
	vperm2i128	$32, %ymm2, %ymm0, %ymm8
	vperm2i128	$49, %ymm2, %ymm0, %ymm0
	vpxor	(%rsi), %ymm4, %ymm2
	vpxor	64(%rsi), %ymm7, %ymm4
	vpxor	128(%rsi), %ymm3, %ymm3
	vpxor	192(%rsi), %ymm8, %ymm7
	vpxor	256(%rsi), %ymm6, %ymm6
	vpxor	320(%rsi), %ymm1, %ymm1
	vpxor	384(%rsi), %ymm5, %ymm5
	vpxor	448(%rsi), %ymm0, %ymm0
	vmovdqu	%ymm2, (%rdi)
	vmovdqu	%ymm4, 64(%rdi)
	vmovdqu	%ymm3, 128(%rdi)
	vmovdqu	%ymm7, 192(%rdi)
	vmovdqu	%ymm6, 256(%rdi)
	vmovdqu	%ymm1, 320(%rdi)
	vmovdqu	%ymm5, 384(%rdi)
	vmovdqu	%ymm0, 448(%rdi)
	vmovdqu	128(%rsp), %ymm0
	vmovdqu	192(%rsp), %ymm1
	vmovdqu	256(%rsp), %ymm2
	vmovdqu	320(%rsp), %ymm3
	vpunpckldq	160(%rsp), %ymm0, %ymm4
	vpunpckhdq	160(%rsp), %ymm0, %ymm0
	vpunpckldq	224(%rsp), %ymm1, %ymm5
	vpunpckhdq	224(%rsp), %ymm1, %ymm1
	vpunpckldq	288(%rsp), %ymm2, %ymm6
	vpunpckhdq	288(%rsp), %ymm2, %ymm2
	vpunpckldq	352(%rsp), %ymm3, %ymm7
	vpunpckhdq	352(%rsp), %ymm3, %ymm3
	vpunpcklqdq	%ymm5, %ymm4, %ymm8
	vpunpcklqdq	%ymm7, %ymm6, %ymm9
	vpunpckhqdq	%ymm5, %ymm4, %ymm4
	vpunpckhqdq	%ymm7, %ymm6, %ymm5
	vpunpcklqdq	%ymm1, %ymm0, %ymm6
	vpunpcklqdq	%ymm3, %ymm2, %ymm7
	vpunpckhqdq	%ymm1, %ymm0, %ymm0
	vpunpckhqdq	%ymm3, %ymm2, %ymm1
	vperm2i128	$32, %ymm9, %ymm8, %ymm2
	vperm2i128	$49, %ymm9, %ymm8, %ymm3
	vperm2i128	$32, %ymm5, %ymm4, %ymm8
	vperm2i128	$49, %ymm5, %ymm4, %ymm4
	vperm2i128	$32, %ymm7, %ymm6, %ymm5
	vperm2i128	$49, %ymm7, %ymm6, %ymm6
	vperm2i128	$32, %ymm1, %ymm0, %ymm7
	vperm2i128	$49, %ymm1, %ymm0, %ymm0
	vpxor	32(%rsi), %ymm2, %ymm1
	vpxor	96(%rsi), %ymm8, %ymm2
	vpxor	160(%rsi), %ymm5, %ymm5
	vpxor	224(%rsi), %ymm7, %ymm7
	vpxor	288(%rsi), %ymm3, %ymm3
	vpxor	352(%rsi), %ymm4, %ymm4
	vpxor	416(%rsi), %ymm6, %ymm6
	vpxor	480(%rsi), %ymm0, %ymm0
	vmovdqu	%ymm1, 32(%rdi)
	vmovdqu	%ymm2, 96(%rdi)
	vmovdqu	%ymm5, 160(%rdi)
	vmovdqu	%ymm7, 224(%rdi)
	vmovdqu	%ymm3, 288(%rdi)
	vmovdqu	%ymm4, 352(%rdi)
	vmovdqu	%ymm6, 416(%rdi)
	vmovdqu	%ymm0, 480(%rdi)
	addq	$512, %rdi
	addq	$512, %rsi
	addq	$-512, %rdx
	vmovdqu	glob_data + 0(%rip), %ymm0
	vpaddd	1024(%rsp), %ymm0, %ymm0
	vmovdqu	%ymm0, 1024(%rsp)
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$32:
	cmpq	$512, %rdx
	jnb 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$33
	cmpq	$0, %rdx
	jbe 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$2
	vmovdqu	640(%rsp), %ymm0
	vmovdqu	672(%rsp), %ymm1
	vmovdqu	704(%rsp), %ymm2
	vmovdqu	736(%rsp), %ymm3
	vmovdqu	768(%rsp), %ymm4
	vmovdqu	800(%rsp), %ymm5
	vmovdqu	832(%rsp), %ymm6
	vmovdqu	864(%rsp), %ymm7
	vmovdqu	896(%rsp), %ymm8
	vmovdqu	928(%rsp), %ymm9
	vmovdqu	960(%rsp), %ymm10
	vmovdqu	992(%rsp), %ymm11
	vmovdqu	1024(%rsp), %ymm12
	vmovdqu	1056(%rsp), %ymm13
	vmovdqu	1088(%rsp), %ymm14
	vmovdqu	1120(%rsp), %ymm15
	vmovdqu	%ymm15, 64(%rsp)
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$31:
	vpaddd	%ymm4, %ymm0, %ymm0
	vpxor	%ymm0, %ymm12, %ymm12
	vpshufb	(%rsp), %ymm12, %ymm12
	vpaddd	%ymm12, %ymm8, %ymm8
	vpaddd	%ymm6, %ymm2, %ymm2
	vpxor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm2, %ymm14, %ymm14
	vpslld	$12, %ymm4, %ymm15
	vpsrld	$20, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm4, %ymm0, %ymm0
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm0, %ymm12, %ymm12
	vpxor	%ymm10, %ymm6, %ymm6
	vpshufb	32(%rsp), %ymm12, %ymm12
	vpslld	$12, %ymm6, %ymm15
	vpsrld	$20, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpaddd	%ymm12, %ymm8, %ymm8
	vpaddd	%ymm6, %ymm2, %ymm2
	vpxor	%ymm8, %ymm4, %ymm4
	vpxor	%ymm2, %ymm14, %ymm14
	vpslld	$7, %ymm4, %ymm15
	vpsrld	$25, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm10, %ymm6, %ymm6
	vpslld	$7, %ymm6, %ymm15
	vpsrld	$25, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vmovdqu	64(%rsp), %ymm15
	vmovdqu	%ymm14, 96(%rsp)
	vpaddd	%ymm5, %ymm1, %ymm1
	vpxor	%ymm1, %ymm13, %ymm13
	vpshufb	(%rsp), %ymm13, %ymm13
	vpaddd	%ymm13, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm3, %ymm3
	vpxor	%ymm9, %ymm5, %ymm5
	vpxor	%ymm3, %ymm15, %ymm14
	vpslld	$12, %ymm5, %ymm15
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm5, %ymm1, %ymm1
	vpaddd	%ymm14, %ymm11, %ymm11
	vpxor	%ymm1, %ymm13, %ymm13
	vpxor	%ymm11, %ymm7, %ymm7
	vpshufb	32(%rsp), %ymm13, %ymm13
	vpslld	$12, %ymm7, %ymm15
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpaddd	%ymm13, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm3, %ymm3
	vpxor	%ymm9, %ymm5, %ymm5
	vpxor	%ymm3, %ymm14, %ymm14
	vpslld	$7, %ymm5, %ymm15
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm11, %ymm11
	vpxor	%ymm11, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm15
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpaddd	%ymm6, %ymm1, %ymm1
	vpxor	%ymm1, %ymm12, %ymm12
	vpshufb	(%rsp), %ymm12, %ymm12
	vpaddd	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm0, %ymm0
	vpxor	%ymm11, %ymm6, %ymm6
	vpxor	%ymm0, %ymm14, %ymm14
	vpslld	$12, %ymm6, %ymm15
	vpsrld	$20, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm6, %ymm1, %ymm1
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm1, %ymm12, %ymm12
	vpxor	%ymm10, %ymm5, %ymm5
	vpshufb	32(%rsp), %ymm12, %ymm12
	vpslld	$12, %ymm5, %ymm15
	vpsrld	$20, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vpaddd	%ymm12, %ymm11, %ymm11
	vpaddd	%ymm5, %ymm0, %ymm0
	vpxor	%ymm11, %ymm6, %ymm6
	vpxor	%ymm0, %ymm14, %ymm14
	vpslld	$7, %ymm6, %ymm15
	vpsrld	$25, %ymm6, %ymm6
	vpxor	%ymm15, %ymm6, %ymm6
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm10, %ymm10
	vpxor	%ymm10, %ymm5, %ymm5
	vpslld	$7, %ymm5, %ymm15
	vpsrld	$25, %ymm5, %ymm5
	vpxor	%ymm15, %ymm5, %ymm5
	vmovdqu	96(%rsp), %ymm15
	vmovdqu	%ymm14, 64(%rsp)
	vpaddd	%ymm7, %ymm2, %ymm2
	vpxor	%ymm2, %ymm13, %ymm13
	vpshufb	(%rsp), %ymm13, %ymm13
	vpaddd	%ymm13, %ymm8, %ymm8
	vpaddd	%ymm4, %ymm3, %ymm3
	vpxor	%ymm8, %ymm7, %ymm7
	vpxor	%ymm3, %ymm15, %ymm14
	vpslld	$12, %ymm7, %ymm15
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpshufb	(%rsp), %ymm14, %ymm14
	vpaddd	%ymm7, %ymm2, %ymm2
	vpaddd	%ymm14, %ymm9, %ymm9
	vpxor	%ymm2, %ymm13, %ymm13
	vpxor	%ymm9, %ymm4, %ymm4
	vpshufb	32(%rsp), %ymm13, %ymm13
	vpslld	$12, %ymm4, %ymm15
	vpsrld	$20, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	vpaddd	%ymm13, %ymm8, %ymm8
	vpaddd	%ymm4, %ymm3, %ymm3
	vpxor	%ymm8, %ymm7, %ymm7
	vpxor	%ymm3, %ymm14, %ymm14
	vpslld	$7, %ymm7, %ymm15
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm15, %ymm7, %ymm7
	vpshufb	32(%rsp), %ymm14, %ymm14
	vpaddd	%ymm14, %ymm9, %ymm9
	vpxor	%ymm9, %ymm4, %ymm4
	vpslld	$7, %ymm4, %ymm15
	vpsrld	$25, %ymm4, %ymm4
	vpxor	%ymm15, %ymm4, %ymm4
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$31
	vmovdqu	64(%rsp), %ymm15
	vpaddd	640(%rsp), %ymm0, %ymm0
	vpaddd	672(%rsp), %ymm1, %ymm1
	vpaddd	704(%rsp), %ymm2, %ymm2
	vpaddd	736(%rsp), %ymm3, %ymm3
	vpaddd	768(%rsp), %ymm4, %ymm4
	vpaddd	800(%rsp), %ymm5, %ymm5
	vpaddd	832(%rsp), %ymm6, %ymm6
	vpaddd	864(%rsp), %ymm7, %ymm7
	vpaddd	896(%rsp), %ymm8, %ymm8
	vpaddd	928(%rsp), %ymm9, %ymm9
	vpaddd	960(%rsp), %ymm10, %ymm10
	vpaddd	992(%rsp), %ymm11, %ymm11
	vpaddd	1024(%rsp), %ymm12, %ymm12
	vpaddd	1056(%rsp), %ymm13, %ymm13
	vpaddd	1088(%rsp), %ymm14, %ymm14
	vpaddd	1120(%rsp), %ymm15, %ymm15
	vmovdqu	%ymm8, 128(%rsp)
	vmovdqu	%ymm9, 160(%rsp)
	vmovdqu	%ymm10, 192(%rsp)
	vmovdqu	%ymm11, 224(%rsp)
	vmovdqu	%ymm12, 256(%rsp)
	vmovdqu	%ymm13, 288(%rsp)
	vmovdqu	%ymm14, 320(%rsp)
	vmovdqu	%ymm15, 352(%rsp)
	vpunpckldq	%ymm1, %ymm0, %ymm8
	vpunpckhdq	%ymm1, %ymm0, %ymm0
	vpunpckldq	%ymm3, %ymm2, %ymm1
	vpunpckhdq	%ymm3, %ymm2, %ymm2
	vpunpckldq	%ymm5, %ymm4, %ymm3
	vpunpckhdq	%ymm5, %ymm4, %ymm4
	vpunpckldq	%ymm7, %ymm6, %ymm5
	vpunpckhdq	%ymm7, %ymm6, %ymm6
	vpunpcklqdq	%ymm1, %ymm8, %ymm7
	vpunpcklqdq	%ymm5, %ymm3, %ymm9
	vpunpckhqdq	%ymm1, %ymm8, %ymm1
	vpunpckhqdq	%ymm5, %ymm3, %ymm3
	vpunpcklqdq	%ymm2, %ymm0, %ymm5
	vpunpcklqdq	%ymm6, %ymm4, %ymm8
	vpunpckhqdq	%ymm2, %ymm0, %ymm0
	vpunpckhqdq	%ymm6, %ymm4, %ymm2
	vperm2i128	$32, %ymm9, %ymm7, %ymm4
	vperm2i128	$49, %ymm9, %ymm7, %ymm6
	vperm2i128	$32, %ymm3, %ymm1, %ymm7
	vperm2i128	$49, %ymm3, %ymm1, %ymm1
	vperm2i128	$32, %ymm8, %ymm5, %ymm3
	vperm2i128	$49, %ymm8, %ymm5, %ymm5
	vperm2i128	$32, %ymm2, %ymm0, %ymm8
	vperm2i128	$49, %ymm2, %ymm0, %ymm0
	vmovdqu	%ymm4, 384(%rsp)
	vmovdqu	%ymm7, 416(%rsp)
	vmovdqu	%ymm3, 448(%rsp)
	vmovdqu	%ymm8, 480(%rsp)
	vmovdqu	%ymm6, 512(%rsp)
	vmovdqu	%ymm1, 544(%rsp)
	vmovdqu	%ymm5, 576(%rsp)
	vmovdqu	%ymm0, 608(%rsp)
	vmovdqu	128(%rsp), %ymm0
	vmovdqu	192(%rsp), %ymm1
	vmovdqu	256(%rsp), %ymm2
	vmovdqu	320(%rsp), %ymm3
	vpunpckldq	160(%rsp), %ymm0, %ymm4
	vpunpckhdq	160(%rsp), %ymm0, %ymm0
	vpunpckldq	224(%rsp), %ymm1, %ymm5
	vpunpckhdq	224(%rsp), %ymm1, %ymm1
	vpunpckldq	288(%rsp), %ymm2, %ymm6
	vpunpckhdq	288(%rsp), %ymm2, %ymm2
	vpunpckldq	352(%rsp), %ymm3, %ymm7
	vpunpckhdq	352(%rsp), %ymm3, %ymm3
	vpunpcklqdq	%ymm5, %ymm4, %ymm8
	vpunpcklqdq	%ymm7, %ymm6, %ymm9
	vpunpckhqdq	%ymm5, %ymm4, %ymm4
	vpunpckhqdq	%ymm7, %ymm6, %ymm5
	vpunpcklqdq	%ymm1, %ymm0, %ymm6
	vpunpcklqdq	%ymm3, %ymm2, %ymm7
	vpunpckhqdq	%ymm1, %ymm0, %ymm0
	vpunpckhqdq	%ymm3, %ymm2, %ymm1
	vperm2i128	$32, %ymm9, %ymm8, %ymm2
	vperm2i128	$49, %ymm9, %ymm8, %ymm3
	vperm2i128	$32, %ymm5, %ymm4, %ymm8
	vperm2i128	$49, %ymm5, %ymm4, %ymm4
	vperm2i128	$32, %ymm7, %ymm6, %ymm5
	vperm2i128	$49, %ymm7, %ymm6, %ymm6
	vperm2i128	$32, %ymm1, %ymm0, %ymm7
	vperm2i128	$49, %ymm1, %ymm0, %ymm0
	vmovdqu	384(%rsp), %ymm1
	vmovdqu	%ymm2, %ymm12
	vmovdqu	416(%rsp), %ymm11
	vmovdqu	%ymm8, %ymm10
	vmovdqu	448(%rsp), %ymm9
	vmovdqu	%ymm5, %ymm8
	vmovdqu	480(%rsp), %ymm5
	vmovdqu	%ymm7, %ymm2
	cmpq	$256, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$30
	vpxor	(%rsi), %ymm1, %ymm1
	vmovdqu	%ymm1, (%rdi)
	vpxor	32(%rsi), %ymm12, %ymm1
	vmovdqu	%ymm1, 32(%rdi)
	vpxor	64(%rsi), %ymm11, %ymm1
	vmovdqu	%ymm1, 64(%rdi)
	vpxor	96(%rsi), %ymm10, %ymm1
	vmovdqu	%ymm1, 96(%rdi)
	vpxor	128(%rsi), %ymm9, %ymm1
	vmovdqu	%ymm1, 128(%rdi)
	vpxor	160(%rsi), %ymm8, %ymm1
	vmovdqu	%ymm1, 160(%rdi)
	vpxor	192(%rsi), %ymm5, %ymm1
	vmovdqu	%ymm1, 192(%rdi)
	vpxor	224(%rsi), %ymm2, %ymm1
	vmovdqu	%ymm1, 224(%rdi)
	addq	$256, %rdi
	addq	$256, %rsi
	addq	$-256, %rdx
	vmovdqu	512(%rsp), %ymm1
	vmovdqu	%ymm3, %ymm12
	vmovdqu	544(%rsp), %ymm11
	vmovdqu	%ymm4, %ymm10
	vmovdqu	576(%rsp), %ymm9
	vmovdqu	%ymm6, %ymm8
	vmovdqu	608(%rsp), %ymm5
	vmovdqu	%ymm0, %ymm2
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$30:
	cmpq	$128, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$29
	vpxor	(%rsi), %ymm1, %ymm0
	vmovdqu	%ymm0, (%rdi)
	vpxor	32(%rsi), %ymm12, %ymm0
	vmovdqu	%ymm0, 32(%rdi)
	vpxor	64(%rsi), %ymm11, %ymm0
	vmovdqu	%ymm0, 64(%rdi)
	vpxor	96(%rsi), %ymm10, %ymm0
	vmovdqu	%ymm0, 96(%rdi)
	addq	$128, %rdi
	addq	$128, %rsi
	addq	$-128, %rdx
	vmovdqu	%ymm9, %ymm1
	vmovdqu	%ymm8, %ymm12
	vmovdqu	%ymm5, %ymm11
	vmovdqu	%ymm2, %ymm10
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$29:
	cmpq	$64, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$28
	vpxor	(%rsi), %ymm1, %ymm0
	vmovdqu	%ymm0, (%rdi)
	vpxor	32(%rsi), %ymm12, %ymm0
	vmovdqu	%ymm0, 32(%rdi)
	addq	$64, %rdi
	addq	$64, %rsi
	addq	$-64, %rdx
	vmovdqu	%ymm11, %ymm1
	vmovdqu	%ymm10, %ymm12
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$28:
	cmpq	$32, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$27
	vpxor	(%rsi), %ymm1, %ymm0
	vmovdqu	%ymm0, (%rdi)
	addq	$32, %rdi
	addq	$32, %rsi
	addq	$-32, %rdx
	vmovdqu	%ymm12, %ymm1
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$27:
	vmovdqu	%xmm1, %xmm0
	cmpq	$16, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$26
	vpxor	(%rsi), %xmm0, %xmm0
	vmovdqu	%xmm0, (%rdi)
	addq	$16, %rdi
	addq	$16, %rsi
	addq	$-16, %rdx
	vextracti128	$1, %ymm1, %xmm0
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$26:
	vpextrq	$0, %xmm0, %rax
	cmpq	$8, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$23
	xorq	(%rsi), %rax
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$8, %rsi
	addq	$-8, %rdx
	vpextrq	$1, %xmm0, %rax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$25:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$23
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$24:
	movb	%al, %cl
	xorb	(%rsi), %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	incq	%rsi
	addq	$-1, %rdx
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$23:
	cmpq	$0, %rdx
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$24
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$22:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$2
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$1:
	vmovdqu	glob_data + 160(%rip), %ymm0
	vmovdqu	glob_data + 128(%rip), %ymm1
	vmovdqu	glob_data + 480(%rip), %ymm2
	vbroadcasti128	(%r8), %ymm3
	vbroadcasti128	16(%r8), %ymm4
	vpxor	%xmm5, %xmm5, %xmm5
	vpinsrd	$1, (%rcx), %xmm5, %xmm5
	vpinsrq	$1, 4(%rcx), %xmm5, %xmm5
	vpxor	%ymm6, %ymm6, %ymm6
	vinserti128	$0, %xmm5, %ymm6, %ymm6
	vinserti128	$1, %xmm5, %ymm6, %ymm5
	vpaddd	glob_data + 96(%rip), %ymm5, %ymm5
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$19
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$20:
	vmovdqu	%ymm2, %ymm6
	vmovdqu	%ymm3, %ymm7
	vmovdqu	%ymm4, %ymm8
	vmovdqu	%ymm5, %ymm9
	vmovdqu	%ymm2, %ymm10
	vmovdqu	%ymm3, %ymm11
	vmovdqu	%ymm4, %ymm12
	vmovdqu	%ymm5, %ymm13
	vpaddd	glob_data + 64(%rip), %ymm13, %ymm13
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$21:
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm0, %ymm9, %ymm9
	vpshufb	%ymm0, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$12, %ymm7, %ymm14
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$12, %ymm11, %ymm14
	vpsrld	$20, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm1, %ymm9, %ymm9
	vpshufb	%ymm1, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm14
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$7, %ymm11, %ymm14
	vpsrld	$25, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpshufd	$57, %ymm7, %ymm7
	vpshufd	$78, %ymm8, %ymm8
	vpshufd	$-109, %ymm9, %ymm9
	vpshufd	$57, %ymm11, %ymm11
	vpshufd	$78, %ymm12, %ymm12
	vpshufd	$-109, %ymm13, %ymm13
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm0, %ymm9, %ymm9
	vpshufb	%ymm0, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$12, %ymm7, %ymm14
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$12, %ymm11, %ymm14
	vpsrld	$20, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm1, %ymm9, %ymm9
	vpshufb	%ymm1, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm14
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$7, %ymm11, %ymm14
	vpsrld	$25, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpshufd	$-109, %ymm7, %ymm7
	vpshufd	$78, %ymm8, %ymm8
	vpshufd	$57, %ymm9, %ymm9
	vpshufd	$-109, %ymm11, %ymm11
	vpshufd	$78, %ymm12, %ymm12
	vpshufd	$57, %ymm13, %ymm13
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$21
	vpaddd	%ymm2, %ymm6, %ymm6
	vpaddd	%ymm3, %ymm7, %ymm7
	vpaddd	%ymm4, %ymm8, %ymm8
	vpaddd	%ymm5, %ymm9, %ymm9
	vpaddd	%ymm2, %ymm10, %ymm10
	vpaddd	%ymm3, %ymm11, %ymm11
	vpaddd	%ymm4, %ymm12, %ymm12
	vpaddd	%ymm5, %ymm13, %ymm13
	vpaddd	glob_data + 64(%rip), %ymm13, %ymm13
	vperm2i128	$32, %ymm7, %ymm6, %ymm14
	vperm2i128	$32, %ymm9, %ymm8, %ymm15
	vperm2i128	$49, %ymm7, %ymm6, %ymm6
	vperm2i128	$49, %ymm9, %ymm8, %ymm7
	vperm2i128	$32, %ymm11, %ymm10, %ymm8
	vperm2i128	$32, %ymm13, %ymm12, %ymm9
	vperm2i128	$49, %ymm11, %ymm10, %ymm10
	vperm2i128	$49, %ymm13, %ymm12, %ymm11
	vpxor	(%rsi), %ymm14, %ymm12
	vmovdqu	%ymm12, (%rdi)
	vpxor	32(%rsi), %ymm15, %ymm12
	vmovdqu	%ymm12, 32(%rdi)
	vpxor	64(%rsi), %ymm6, %ymm6
	vmovdqu	%ymm6, 64(%rdi)
	vpxor	96(%rsi), %ymm7, %ymm6
	vmovdqu	%ymm6, 96(%rdi)
	vpxor	128(%rsi), %ymm8, %ymm6
	vmovdqu	%ymm6, 128(%rdi)
	vpxor	160(%rsi), %ymm9, %ymm6
	vmovdqu	%ymm6, 160(%rdi)
	vpxor	192(%rsi), %ymm10, %ymm6
	vmovdqu	%ymm6, 192(%rdi)
	vpxor	224(%rsi), %ymm11, %ymm6
	vmovdqu	%ymm6, 224(%rdi)
	addq	$256, %rdi
	addq	$256, %rsi
	addq	$-256, %rdx
	vpaddd	glob_data + 32(%rip), %ymm5, %ymm5
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$19:
	cmpq	$256, %rdx
	jnb 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$20
	cmpq	$128, %rdx
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$3
	vmovdqu	%ymm2, %ymm6
	vmovdqu	%ymm3, %ymm7
	vmovdqu	%ymm4, %ymm8
	vmovdqu	%ymm5, %ymm9
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$18:
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm9, %ymm9
	vpshufb	%ymm0, %ymm9, %ymm9
	vpaddd	%ymm9, %ymm8, %ymm8
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$12, %ymm7, %ymm10
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm10, %ymm7, %ymm7
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm9, %ymm9
	vpshufb	%ymm1, %ymm9, %ymm9
	vpaddd	%ymm9, %ymm8, %ymm8
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm10
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm10, %ymm7, %ymm7
	vpshufd	$57, %ymm7, %ymm7
	vpshufd	$78, %ymm8, %ymm8
	vpshufd	$-109, %ymm9, %ymm9
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm9, %ymm9
	vpshufb	%ymm0, %ymm9, %ymm9
	vpaddd	%ymm9, %ymm8, %ymm8
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$12, %ymm7, %ymm10
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm10, %ymm7, %ymm7
	vpaddd	%ymm7, %ymm6, %ymm6
	vpxor	%ymm6, %ymm9, %ymm9
	vpshufb	%ymm1, %ymm9, %ymm9
	vpaddd	%ymm9, %ymm8, %ymm8
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm10
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm10, %ymm7, %ymm7
	vpshufd	$-109, %ymm7, %ymm7
	vpshufd	$78, %ymm8, %ymm8
	vpshufd	$57, %ymm9, %ymm9
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$18
	vpaddd	%ymm2, %ymm6, %ymm0
	vpaddd	%ymm3, %ymm7, %ymm1
	vpaddd	%ymm4, %ymm8, %ymm2
	vpaddd	%ymm5, %ymm9, %ymm3
	vperm2i128	$32, %ymm1, %ymm0, %ymm5
	vperm2i128	$32, %ymm3, %ymm2, %ymm4
	vperm2i128	$49, %ymm1, %ymm0, %ymm0
	vperm2i128	$49, %ymm3, %ymm2, %ymm1
	cmpq	$64, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$17
	vpxor	(%rsi), %ymm5, %ymm2
	vmovdqu	%ymm2, (%rdi)
	vpxor	32(%rsi), %ymm4, %ymm2
	vmovdqu	%ymm2, 32(%rdi)
	addq	$64, %rdi
	addq	$64, %rsi
	addq	$-64, %rdx
	vmovdqu	%ymm0, %ymm5
	vmovdqu	%ymm1, %ymm4
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$17:
	cmpq	$32, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$16
	vpxor	(%rsi), %ymm5, %ymm0
	vmovdqu	%ymm0, (%rdi)
	addq	$32, %rdi
	addq	$32, %rsi
	addq	$-32, %rdx
	vmovdqu	%ymm4, %ymm5
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$16:
	vmovdqu	%xmm5, %xmm0
	cmpq	$16, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$15
	vpxor	(%rsi), %xmm0, %xmm0
	vmovdqu	%xmm0, (%rdi)
	addq	$16, %rdi
	addq	$16, %rsi
	addq	$-16, %rdx
	vextracti128	$1, %ymm5, %xmm0
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$15:
	vpextrq	$0, %xmm0, %rax
	cmpq	$8, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$12
	xorq	(%rsi), %rax
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$8, %rsi
	addq	$-8, %rdx
	vpextrq	$1, %xmm0, %rax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$14:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$12
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$13:
	movb	%al, %cl
	xorb	(%rsi), %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	incq	%rsi
	addq	$-1, %rdx
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$12:
	cmpq	$0, %rdx
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$13
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$2
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$3:
	vmovdqu	%ymm2, %ymm6
	vmovdqu	%ymm3, %ymm7
	vmovdqu	%ymm4, %ymm8
	vmovdqu	%ymm5, %ymm9
	vmovdqu	%ymm2, %ymm10
	vmovdqu	%ymm3, %ymm11
	vmovdqu	%ymm4, %ymm12
	vmovdqu	%ymm5, %ymm13
	vpaddd	glob_data + 64(%rip), %ymm13, %ymm13
	movl	$10, %eax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$11:
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm0, %ymm9, %ymm9
	vpshufb	%ymm0, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$12, %ymm7, %ymm14
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$12, %ymm11, %ymm14
	vpsrld	$20, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm1, %ymm9, %ymm9
	vpshufb	%ymm1, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm14
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$7, %ymm11, %ymm14
	vpsrld	$25, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpshufd	$57, %ymm7, %ymm7
	vpshufd	$78, %ymm8, %ymm8
	vpshufd	$-109, %ymm9, %ymm9
	vpshufd	$57, %ymm11, %ymm11
	vpshufd	$78, %ymm12, %ymm12
	vpshufd	$-109, %ymm13, %ymm13
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm0, %ymm9, %ymm9
	vpshufb	%ymm0, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$12, %ymm7, %ymm14
	vpsrld	$20, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$12, %ymm11, %ymm14
	vpsrld	$20, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpaddd	%ymm7, %ymm6, %ymm6
	vpaddd	%ymm11, %ymm10, %ymm10
	vpxor	%ymm6, %ymm9, %ymm9
	vpxor	%ymm10, %ymm13, %ymm13
	vpshufb	%ymm1, %ymm9, %ymm9
	vpshufb	%ymm1, %ymm13, %ymm13
	vpaddd	%ymm9, %ymm8, %ymm8
	vpaddd	%ymm13, %ymm12, %ymm12
	vpxor	%ymm8, %ymm7, %ymm7
	vpslld	$7, %ymm7, %ymm14
	vpsrld	$25, %ymm7, %ymm7
	vpxor	%ymm12, %ymm11, %ymm11
	vpxor	%ymm14, %ymm7, %ymm7
	vpslld	$7, %ymm11, %ymm14
	vpsrld	$25, %ymm11, %ymm11
	vpxor	%ymm14, %ymm11, %ymm11
	vpshufd	$-109, %ymm7, %ymm7
	vpshufd	$78, %ymm8, %ymm8
	vpshufd	$57, %ymm9, %ymm9
	vpshufd	$-109, %ymm11, %ymm11
	vpshufd	$78, %ymm12, %ymm12
	vpshufd	$57, %ymm13, %ymm13
	decl	%eax
	cmpl	$0, %eax
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$11
	vpaddd	%ymm2, %ymm6, %ymm0
	vpaddd	%ymm3, %ymm7, %ymm1
	vpaddd	%ymm4, %ymm8, %ymm6
	vpaddd	%ymm5, %ymm9, %ymm7
	vpaddd	%ymm2, %ymm10, %ymm2
	vpaddd	%ymm3, %ymm11, %ymm3
	vpaddd	%ymm4, %ymm12, %ymm4
	vpaddd	%ymm5, %ymm13, %ymm5
	vpaddd	glob_data + 64(%rip), %ymm5, %ymm5
	vperm2i128	$32, %ymm1, %ymm0, %ymm8
	vperm2i128	$32, %ymm7, %ymm6, %ymm9
	vperm2i128	$49, %ymm1, %ymm0, %ymm0
	vperm2i128	$49, %ymm7, %ymm6, %ymm1
	vperm2i128	$32, %ymm3, %ymm2, %ymm7
	vperm2i128	$32, %ymm5, %ymm4, %ymm6
	vperm2i128	$49, %ymm3, %ymm2, %ymm2
	vperm2i128	$49, %ymm5, %ymm4, %ymm3
	vpxor	(%rsi), %ymm8, %ymm4
	vmovdqu	%ymm4, (%rdi)
	vpxor	32(%rsi), %ymm9, %ymm4
	vmovdqu	%ymm4, 32(%rdi)
	vpxor	64(%rsi), %ymm0, %ymm0
	vmovdqu	%ymm0, 64(%rdi)
	vpxor	96(%rsi), %ymm1, %ymm0
	vmovdqu	%ymm0, 96(%rdi)
	addq	$128, %rdi
	addq	$128, %rsi
	addq	$-128, %rdx
	cmpq	$64, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$10
	vpxor	(%rsi), %ymm7, %ymm0
	vmovdqu	%ymm0, (%rdi)
	vpxor	32(%rsi), %ymm6, %ymm0
	vmovdqu	%ymm0, 32(%rdi)
	addq	$64, %rdi
	addq	$64, %rsi
	addq	$-64, %rdx
	vmovdqu	%ymm2, %ymm7
	vmovdqu	%ymm3, %ymm6
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$10:
	cmpq	$32, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$9
	vpxor	(%rsi), %ymm7, %ymm0
	vmovdqu	%ymm0, (%rdi)
	addq	$32, %rdi
	addq	$32, %rsi
	addq	$-32, %rdx
	vmovdqu	%ymm6, %ymm7
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$9:
	vmovdqu	%xmm7, %xmm0
	cmpq	$16, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$8
	vpxor	(%rsi), %xmm0, %xmm0
	vmovdqu	%xmm0, (%rdi)
	addq	$16, %rdi
	addq	$16, %rsi
	addq	$-16, %rdx
	vextracti128	$1, %ymm7, %xmm0
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$8:
	vpextrq	$0, %xmm0, %rax
	cmpq	$8, %rdx
	jb  	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$5
	xorq	(%rsi), %rax
	movq	%rax, (%rdi)
	addq	$8, %rdi
	addq	$8, %rsi
	addq	$-8, %rdx
	vpextrq	$1, %xmm0, %rax
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$7:
	jmp 	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$5
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$6:
	movb	%al, %cl
	xorb	(%rsi), %cl
	movb	%cl, (%rdi)
	shrq	$8, %rax
	incq	%rdi
	incq	%rsi
	addq	$-1, %rdx
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$5:
	cmpq	$0, %rdx
	jnbe	Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$6
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$4:
Ljade_stream_chacha_chacha20_ietf_amd64_avx2_xor$2:
	xorq	%rax, %rax
	movq	%r10, %rsp
	ret 
	.data
	.p2align	5
_glob_data:
glob_data:
      .byte 8
      .byte 0
      .byte 0
      .byte 0
      .byte 8
      .byte 0
      .byte 0
      .byte 0
      .byte 8
      .byte 0
      .byte 0
      .byte 0
      .byte 8
      .byte 0
      .byte 0
      .byte 0
      .byte 8
      .byte 0
      .byte 0
      .byte 0
      .byte 8
      .byte 0
      .byte 0
      .byte 0
      .byte 8
      .byte 0
      .byte 0
      .byte 0
      .byte 8
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
      .byte 0
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
      .byte 8
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 8
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 8
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 8
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
      .byte 4
      .byte 0
      .byte 0
      .byte 0
      .byte 5
      .byte 0
      .byte 0
      .byte 0
      .byte 6
      .byte 0
      .byte 0
      .byte 0
      .byte 7
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
      .byte 0
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
