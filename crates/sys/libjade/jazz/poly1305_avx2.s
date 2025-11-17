	.att_syntax
	.text
	.p2align	5
	.globl	_jade_onetimeauth_poly1305_amd64_avx2_verify
	.globl	jade_onetimeauth_poly1305_amd64_avx2_verify
	.globl	_jade_onetimeauth_poly1305_amd64_avx2
	.globl	jade_onetimeauth_poly1305_amd64_avx2
_jade_onetimeauth_poly1305_amd64_avx2_verify:
jade_onetimeauth_poly1305_amd64_avx2_verify:
	movq	%rsp, %rax
	leaq	-696(%rsp), %rsp
	andq	$-32, %rsp
	movq	%rax, 688(%rsp)
	movq	%rbx, 640(%rsp)
	movq	%rbp, 648(%rsp)
	movq	%r12, 656(%rsp)
	movq	%r13, 664(%rsp)
	movq	%r14, 672(%rsp)
	movq	%r15, 680(%rsp)
	movq	%rdx, %r14
	movq	%rcx, %r15
	cmpq	$256, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx2_verify$1
	movq	$0, %rbx
	movq	$0, %r12
	movq	$0, %r8
	movq	(%r15), %rbp
	movq	8(%r15), %r13
	movq	$1152921487695413247, %rax
	andq	%rax, %rbp
	movq	$1152921487695413244, %rax
	andq	%rax, %r13
	movq	%r13, %r9
	shrq	$2, %r9
	addq	%r13, %r9
	addq	$16, %r15
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx2_verify$9
Ljade_onetimeauth_poly1305_amd64_avx2_verify$10:
	addq	(%rsi), %rbx
	adcq	8(%rsi), %r12
	adcq	$1, %r8
	movq	%r9, %r11
	imulq	%r8, %r11
	imulq	%rbp, %r8
	movq	%rbp, %rax
	mulq	%rbx
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%rbp, %rax
	mulq	%r12
	addq	%rax, %r10
	adcq	%rdx, %r8
	movq	%r9, %rax
	mulq	%r12
	movq	%rdx, %r12
	addq	%r11, %r12
	movq	%rax, %r11
	movq	%r13, %rax
	mulq	%rbx
	addq	%r11, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %r8
	movq	$-4, %rbx
	movq	%r8, %rax
	shrq	$2, %rax
	andq	%r8, %rbx
	addq	%rax, %rbx
	andq	$3, %r8
	addq	%rcx, %rbx
	adcq	%r10, %r12
	adcq	$0, %r8
	addq	$16, %rsi
	addq	$-16, %r14
Ljade_onetimeauth_poly1305_amd64_avx2_verify$9:
	cmpq	$16, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx2_verify$10
	cmpq	$0, %r14
	jbe 	Ljade_onetimeauth_poly1305_amd64_avx2_verify$8
	xorq	%rcx, %rcx
	movq	%r14, %rax
	andq	$7, %rax
	shlq	$3, %rax
	shrq	$3, %r14
	movq	%r14, %rdx
	xorq	$1, %rdx
	movq	%r14, %r10
	addq	$-1, %r10
	movq	%rax, %r11
	andq	%r10, %r11
	xorq	%r11, %rcx
	xorq	%r11, %rax
	shlq	%cl, %rdx
	movq	%rax, %rcx
	shlq	%cl, %r14
	movq	%rdx, %rax
	movq	%r14, %rcx
	subq	$1, %rax
	sbbq	$0, %rcx
	movq	(%rsi), %r10
	andq	%rax, %r10
	orq 	%rdx, %r10
	movq	8(%rsi), %rax
	andq	%rcx, %rax
	orq 	%r14, %rax
	addq	%r10, %rbx
	adcq	%rax, %r12
	adcq	$0, %r8
	movq	%r9, %rsi
	imulq	%r8, %rsi
	imulq	%rbp, %r8
	movq	%rbp, %rax
	mulq	%rbx
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%rbp, %rax
	mulq	%r12
	addq	%rax, %r10
	adcq	%rdx, %r8
	movq	%r9, %rax
	mulq	%r12
	movq	%rdx, %r12
	addq	%rsi, %r12
	movq	%rax, %rsi
	movq	%r13, %rax
	mulq	%rbx
	addq	%rsi, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %r8
	movq	$-4, %rbx
	movq	%r8, %rax
	shrq	$2, %rax
	andq	%r8, %rbx
	addq	%rax, %rbx
	andq	$3, %r8
	addq	%rcx, %rbx
	adcq	%r10, %r12
	adcq	$0, %r8
Ljade_onetimeauth_poly1305_amd64_avx2_verify$8:
	movq	%rbx, %rax
	movq	%r12, %rcx
	addq	$5, %rax
	adcq	$0, %rcx
	adcq	$0, %r8
	shrq	$2, %r8
	negq	%r8
	xorq	%rbx, %rax
	xorq	%r12, %rcx
	andq	%r8, %rax
	andq	%r8, %rcx
	xorq	%rbx, %rax
	xorq	%r12, %rcx
	movq	(%r15), %rdx
	movq	8(%r15), %rsi
	addq	%rdx, %rax
	adcq	%rsi, %rcx
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx2_verify$2
Ljade_onetimeauth_poly1305_amd64_avx2_verify$1:
	movq	(%r15), %rbp
	movq	8(%r15), %r13
	movq	$1152921487695413247, %rax
	andq	%rax, %rbp
	movq	$1152921487695413244, %rax
	andq	%rax, %r13
	movq	%r13, %r12
	shrq	$2, %r12
	addq	%r13, %r12
	addq	$16, %r15
	movq	%rbp, %r8
	movq	%r13, %r11
	movq	$0, %rbx
	movq	%r8, %rax
	andq	$67108863, %rax
	movq	%rax, 344(%rsp)
	movq	%r8, %rax
	shrq	$26, %rax
	andq	$67108863, %rax
	movq	%rax, 376(%rsp)
	movq	%r8, %rax
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 408(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 440(%rsp)
	movq	%r11, %rax
	shrdq	$40, %rbx, %rax
	movq	%rax, 472(%rsp)
	movq	%r12, %r10
	imulq	%rbx, %r10
	imulq	%rbp, %rbx
	movq	%rbp, %rax
	mulq	%r8
	movq	%rax, %rcx
	movq	%rdx, %r9
	movq	%rbp, %rax
	mulq	%r11
	addq	%rax, %r9
	adcq	%rdx, %rbx
	movq	%r12, %rax
	mulq	%r11
	movq	%rdx, %r11
	addq	%r10, %r11
	movq	%rax, %r10
	movq	%r13, %rax
	mulq	%r8
	addq	%r10, %rcx
	adcq	%rax, %r9
	adcq	%rdx, %rbx
	movq	$-4, %r8
	movq	%rbx, %rax
	shrq	$2, %rax
	andq	%rbx, %r8
	addq	%rax, %r8
	andq	$3, %rbx
	addq	%rcx, %r8
	adcq	%r9, %r11
	adcq	$0, %rbx
	movq	%r8, %rax
	andq	$67108863, %rax
	movq	%rax, 336(%rsp)
	movq	%r8, %rax
	shrq	$26, %rax
	andq	$67108863, %rax
	movq	%rax, 368(%rsp)
	movq	%r8, %rax
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 400(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 432(%rsp)
	movq	%r11, %rax
	shrdq	$40, %rbx, %rax
	movq	%rax, 464(%rsp)
	movq	%r12, %r10
	imulq	%rbx, %r10
	imulq	%rbp, %rbx
	movq	%rbp, %rax
	mulq	%r8
	movq	%rax, %rcx
	movq	%rdx, %r9
	movq	%rbp, %rax
	mulq	%r11
	addq	%rax, %r9
	adcq	%rdx, %rbx
	movq	%r12, %rax
	mulq	%r11
	movq	%rdx, %r11
	addq	%r10, %r11
	movq	%rax, %r10
	movq	%r13, %rax
	mulq	%r8
	addq	%r10, %rcx
	adcq	%rax, %r9
	adcq	%rdx, %rbx
	movq	$-4, %r8
	movq	%rbx, %rax
	shrq	$2, %rax
	andq	%rbx, %r8
	addq	%rax, %r8
	andq	$3, %rbx
	addq	%rcx, %r8
	adcq	%r9, %r11
	adcq	$0, %rbx
	movq	%r8, %rax
	andq	$67108863, %rax
	movq	%rax, 328(%rsp)
	movq	%r8, %rax
	shrq	$26, %rax
	andq	$67108863, %rax
	movq	%rax, 360(%rsp)
	movq	%r8, %rax
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 392(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 424(%rsp)
	movq	%r11, %rax
	shrdq	$40, %rbx, %rax
	movq	%rax, 456(%rsp)
	movq	%r12, %r9
	imulq	%rbx, %r9
	imulq	%rbp, %rbx
	movq	%rbp, %rax
	mulq	%r8
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%rbp, %rax
	mulq	%r11
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	%r12, %rax
	mulq	%r11
	movq	%rdx, %r11
	addq	%r9, %r11
	movq	%rax, %r9
	movq	%r13, %rax
	mulq	%r8
	addq	%r9, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %rbx
	movq	$-4, %rax
	movq	%rbx, %rdx
	shrq	$2, %rdx
	andq	%rbx, %rax
	addq	%rdx, %rax
	andq	$3, %rbx
	addq	%rcx, %rax
	adcq	%r10, %r11
	adcq	$0, %rbx
	movq	%rax, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 320(%rsp)
	movq	%rax, %rcx
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 352(%rsp)
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 384(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 416(%rsp)
	shrdq	$40, %rbx, %r11
	movq	%r11, 448(%rsp)
	vpbroadcastq	glob_data + 16(%rip), %ymm0
	vpmuludq	352(%rsp), %ymm0, %ymm1
	vmovdqu	%ymm1, 64(%rsp)
	vpmuludq	384(%rsp), %ymm0, %ymm1
	vmovdqu	%ymm1, 96(%rsp)
	vpmuludq	416(%rsp), %ymm0, %ymm1
	vmovdqu	%ymm1, 128(%rsp)
	vpmuludq	448(%rsp), %ymm0, %ymm0
	vmovdqu	%ymm0, 160(%rsp)
	vpbroadcastq	320(%rsp), %ymm0
	vmovdqu	%ymm0, 480(%rsp)
	vpbroadcastq	352(%rsp), %ymm0
	vmovdqu	%ymm0, 512(%rsp)
	vpbroadcastq	384(%rsp), %ymm0
	vmovdqu	%ymm0, 544(%rsp)
	vpbroadcastq	416(%rsp), %ymm0
	vmovdqu	%ymm0, 576(%rsp)
	vpbroadcastq	448(%rsp), %ymm0
	vmovdqu	%ymm0, 608(%rsp)
	vpbroadcastq	64(%rsp), %ymm0
	vmovdqu	%ymm0, 192(%rsp)
	vpbroadcastq	96(%rsp), %ymm0
	vmovdqu	%ymm0, 224(%rsp)
	vpbroadcastq	128(%rsp), %ymm0
	vmovdqu	%ymm0, 256(%rsp)
	vpbroadcastq	160(%rsp), %ymm0
	vmovdqu	%ymm0, 288(%rsp)
	vpxor	%ymm0, %ymm0, %ymm0
	vpxor	%ymm1, %ymm1, %ymm1
	vpxor	%ymm6, %ymm6, %ymm6
	vpxor	%ymm3, %ymm3, %ymm3
	vpxor	%ymm4, %ymm4, %ymm4
	vpbroadcastq	glob_data + 8(%rip), %ymm7
	vmovdqu	%ymm7, (%rsp)
	vpbroadcastq	glob_data + 0(%rip), %ymm2
	vmovdqu	%ymm2, 32(%rsp)
	vmovdqu	(%rsi), %ymm2
	vmovdqu	32(%rsi), %ymm5
	addq	$64, %rsi
	vperm2i128	$32, %ymm5, %ymm2, %ymm9
	vperm2i128	$49, %ymm5, %ymm2, %ymm2
	vpsrldq	$6, %ymm9, %ymm5
	vpsrldq	$6, %ymm2, %ymm10
	vpunpckhqdq	%ymm2, %ymm9, %ymm8
	vpunpcklqdq	%ymm2, %ymm9, %ymm9
	vpunpcklqdq	%ymm10, %ymm5, %ymm10
	vpsrlq	$4, %ymm10, %ymm2
	vpand	%ymm7, %ymm2, %ymm2
	vpsrlq	$26, %ymm9, %ymm11
	vpand	%ymm7, %ymm9, %ymm5
	vpsrlq	$30, %ymm10, %ymm9
	vpand	%ymm7, %ymm9, %ymm9
	vpsrlq	$40, %ymm8, %ymm8
	vpor	32(%rsp), %ymm8, %ymm10
	vpand	%ymm7, %ymm11, %ymm11
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx2_verify$6
Ljade_onetimeauth_poly1305_amd64_avx2_verify$7:
	vmovdqu	480(%rsp), %ymm8
	vmovdqu	512(%rsp), %ymm7
	vmovdqu	288(%rsp), %ymm13
	vpaddq	%ymm5, %ymm0, %ymm0
	vpaddq	%ymm11, %ymm1, %ymm1
	vpmuludq	%ymm8, %ymm0, %ymm5
	vpaddq	%ymm2, %ymm6, %ymm2
	vpmuludq	%ymm7, %ymm0, %ymm6
	vpaddq	%ymm9, %ymm3, %ymm3
	vpmuludq	%ymm8, %ymm1, %ymm9
	vpaddq	%ymm10, %ymm4, %ymm4
	vpmuludq	%ymm7, %ymm1, %ymm12
	vpmuludq	%ymm8, %ymm2, %ymm14
	vpmuludq	%ymm7, %ymm2, %ymm10
	vpmuludq	%ymm8, %ymm3, %ymm11
	vpaddq	%ymm6, %ymm9, %ymm6
	vpmuludq	%ymm7, %ymm3, %ymm9
	vpaddq	%ymm12, %ymm14, %ymm7
	vpmuludq	%ymm8, %ymm4, %ymm8
	vpaddq	%ymm10, %ymm11, %ymm11
	vpaddq	%ymm9, %ymm8, %ymm12
	vpmuludq	%ymm13, %ymm1, %ymm14
	vmovdqu	(%rsi), %ymm8
	vpmuludq	%ymm13, %ymm2, %ymm15
	vmovdqu	544(%rsp), %ymm9
	vpmuludq	%ymm13, %ymm3, %ymm10
	vpmuludq	%ymm13, %ymm4, %ymm13
	vpaddq	%ymm14, %ymm5, %ymm5
	vmovdqu	32(%rsi), %ymm14
	vpaddq	%ymm15, %ymm6, %ymm6
	vpaddq	%ymm10, %ymm7, %ymm10
	vpaddq	%ymm13, %ymm11, %ymm11
	vpmuludq	%ymm9, %ymm0, %ymm15
	vperm2i128	$32, %ymm14, %ymm8, %ymm7
	vpmuludq	%ymm9, %ymm1, %ymm13
	vperm2i128	$49, %ymm14, %ymm8, %ymm8
	vpmuludq	%ymm9, %ymm2, %ymm14
	vpaddq	%ymm15, %ymm10, %ymm9
	vmovdqu	256(%rsp), %ymm10
	vpaddq	%ymm13, %ymm11, %ymm11
	vpaddq	%ymm14, %ymm12, %ymm12
	vpmuludq	%ymm10, %ymm2, %ymm2
	vpmuludq	%ymm10, %ymm3, %ymm13
	vmovdqu	576(%rsp), %ymm14
	vpmuludq	%ymm10, %ymm4, %ymm10
	vpsrldq	$6, %ymm7, %ymm15
	vpaddq	%ymm2, %ymm5, %ymm2
	vpsrldq	$6, %ymm8, %ymm5
	vpaddq	%ymm13, %ymm6, %ymm6
	vpaddq	%ymm9, %ymm10, %ymm9
	vmovdqu	224(%rsp), %ymm10
	vpmuludq	%ymm14, %ymm0, %ymm13
	vpmuludq	%ymm14, %ymm1, %ymm1
	vpunpckhqdq	%ymm8, %ymm7, %ymm14
	vpunpcklqdq	%ymm8, %ymm7, %ymm7
	vpaddq	%ymm13, %ymm11, %ymm11
	vpaddq	%ymm1, %ymm12, %ymm1
	vpmuludq	%ymm10, %ymm3, %ymm3
	vpmuludq	%ymm10, %ymm4, %ymm8
	vpaddq	%ymm3, %ymm2, %ymm2
	vpaddq	%ymm6, %ymm8, %ymm3
	vmovdqu	(%rsp), %ymm8
	vpmuludq	192(%rsp), %ymm4, %ymm4
	vpmuludq	608(%rsp), %ymm0, %ymm0
	vpunpcklqdq	%ymm5, %ymm15, %ymm10
	vpsrlq	$4, %ymm10, %ymm6
	vpaddq	%ymm4, %ymm2, %ymm2
	vpsrlq	$26, %ymm2, %ymm12
	vpand	%ymm8, %ymm2, %ymm4
	vpand	%ymm8, %ymm11, %ymm5
	vpsrlq	$26, %ymm11, %ymm13
	vpaddq	%ymm0, %ymm1, %ymm1
	vpand	%ymm8, %ymm6, %ymm2
	vpsrlq	$26, %ymm7, %ymm11
	vpaddq	%ymm12, %ymm3, %ymm0
	vpaddq	%ymm13, %ymm1, %ymm6
	vpsrlq	$26, %ymm0, %ymm1
	vpsrlq	$26, %ymm6, %ymm3
	vpsllq	$2, %ymm3, %ymm12
	vpaddq	%ymm12, %ymm3, %ymm13
	vpand	%ymm8, %ymm0, %ymm3
	vpand	%ymm8, %ymm6, %ymm12
	vpaddq	%ymm1, %ymm9, %ymm0
	vpaddq	%ymm13, %ymm4, %ymm1
	vpsrlq	$26, %ymm0, %ymm4
	vpsrlq	$26, %ymm1, %ymm9
	vpand	%ymm8, %ymm0, %ymm6
	vpand	%ymm8, %ymm1, %ymm0
	vpaddq	%ymm4, %ymm5, %ymm4
	vpaddq	%ymm9, %ymm3, %ymm1
	vpsrlq	$26, %ymm4, %ymm5
	vpand	%ymm8, %ymm4, %ymm3
	vpaddq	%ymm5, %ymm12, %ymm4
	addq	$64, %rsi
	vpand	%ymm8, %ymm7, %ymm5
	vpsrlq	$30, %ymm10, %ymm7
	vpand	%ymm8, %ymm7, %ymm9
	vpsrlq	$40, %ymm14, %ymm7
	vpor	32(%rsp), %ymm7, %ymm10
	vpand	%ymm8, %ymm11, %ymm11
	addq	$-64, %r14
Ljade_onetimeauth_poly1305_amd64_avx2_verify$6:
	cmpq	$128, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx2_verify$7
	addq	$-64, %r14
	vmovdqu	320(%rsp), %ymm7
	vmovdqu	352(%rsp), %ymm8
	vmovdqu	160(%rsp), %ymm12
	vpaddq	%ymm5, %ymm0, %ymm0
	vpaddq	%ymm11, %ymm1, %ymm1
	vpaddq	%ymm2, %ymm6, %ymm2
	vpaddq	%ymm9, %ymm3, %ymm3
	vpaddq	%ymm10, %ymm4, %ymm4
	vpmuludq	%ymm7, %ymm0, %ymm5
	vpmuludq	%ymm7, %ymm1, %ymm6
	vpmuludq	%ymm7, %ymm2, %ymm9
	vpmuludq	%ymm7, %ymm3, %ymm10
	vpmuludq	%ymm7, %ymm4, %ymm7
	vpmuludq	%ymm8, %ymm0, %ymm11
	vpmuludq	%ymm8, %ymm1, %ymm13
	vpmuludq	%ymm8, %ymm2, %ymm14
	vpmuludq	%ymm8, %ymm3, %ymm8
	vmovdqu	384(%rsp), %ymm15
	vpaddq	%ymm11, %ymm6, %ymm6
	vpaddq	%ymm13, %ymm9, %ymm9
	vpaddq	%ymm14, %ymm10, %ymm10
	vpaddq	%ymm8, %ymm7, %ymm7
	vpmuludq	%ymm12, %ymm1, %ymm8
	vpmuludq	%ymm12, %ymm2, %ymm11
	vpmuludq	%ymm12, %ymm3, %ymm13
	vpmuludq	%ymm12, %ymm4, %ymm12
	vmovdqu	128(%rsp), %ymm14
	vpaddq	%ymm8, %ymm5, %ymm5
	vpaddq	%ymm11, %ymm6, %ymm6
	vpaddq	%ymm13, %ymm9, %ymm8
	vpaddq	%ymm12, %ymm10, %ymm10
	vpmuludq	%ymm15, %ymm0, %ymm13
	vpmuludq	%ymm15, %ymm1, %ymm11
	vpmuludq	%ymm15, %ymm2, %ymm12
	vmovdqu	416(%rsp), %ymm9
	vpaddq	%ymm13, %ymm8, %ymm8
	vpaddq	%ymm11, %ymm10, %ymm10
	vpaddq	%ymm12, %ymm7, %ymm7
	vpmuludq	%ymm14, %ymm2, %ymm2
	vpmuludq	%ymm14, %ymm3, %ymm12
	vpmuludq	%ymm14, %ymm4, %ymm13
	vmovdqu	96(%rsp), %ymm11
	vpaddq	%ymm2, %ymm5, %ymm5
	vpaddq	%ymm12, %ymm6, %ymm6
	vpaddq	%ymm8, %ymm13, %ymm2
	vpmuludq	%ymm9, %ymm0, %ymm8
	vpmuludq	%ymm9, %ymm1, %ymm9
	vpaddq	%ymm8, %ymm10, %ymm1
	vpaddq	%ymm9, %ymm7, %ymm7
	vpmuludq	%ymm11, %ymm3, %ymm3
	vpmuludq	%ymm11, %ymm4, %ymm8
	vpaddq	%ymm3, %ymm5, %ymm5
	vpaddq	%ymm6, %ymm8, %ymm3
	vpmuludq	64(%rsp), %ymm4, %ymm4
	vpmuludq	448(%rsp), %ymm0, %ymm0
	vpaddq	%ymm4, %ymm5, %ymm4
	vmovdqu	%ymm1, %ymm5
	vpaddq	%ymm0, %ymm7, %ymm6
	vmovdqu	(%rsp), %ymm0
	vpsrlq	$26, %ymm4, %ymm7
	vpsrlq	$26, %ymm5, %ymm8
	vpand	%ymm0, %ymm4, %ymm1
	vpand	%ymm0, %ymm5, %ymm4
	vpaddq	%ymm7, %ymm3, %ymm3
	vpaddq	%ymm8, %ymm6, %ymm5
	vpsrlq	$26, %ymm3, %ymm6
	vpsrlq	$26, %ymm5, %ymm7
	vpsllq	$2, %ymm7, %ymm8
	vpaddq	%ymm8, %ymm7, %ymm7
	vpand	%ymm0, %ymm3, %ymm8
	vpand	%ymm0, %ymm5, %ymm3
	vpaddq	%ymm6, %ymm2, %ymm2
	vpaddq	%ymm7, %ymm1, %ymm5
	vpsrlq	$26, %ymm2, %ymm6
	vpsrlq	$26, %ymm5, %ymm7
	vpand	%ymm0, %ymm2, %ymm1
	vpand	%ymm0, %ymm5, %ymm2
	vpaddq	%ymm6, %ymm4, %ymm4
	vpaddq	%ymm7, %ymm8, %ymm5
	vpsrlq	$26, %ymm4, %ymm6
	vpand	%ymm0, %ymm4, %ymm0
	vpaddq	%ymm6, %ymm3, %ymm3
	vpsllq	$26, %ymm5, %ymm4
	vpaddq	%ymm2, %ymm4, %ymm2
	vpsllq	$26, %ymm0, %ymm0
	vpaddq	%ymm1, %ymm0, %ymm0
	vpsrldq	$8, %ymm3, %ymm1
	vpaddq	%ymm3, %ymm1, %ymm1
	vpermq	$-128, %ymm1, %ymm1
	vperm2i128	$32, %ymm0, %ymm2, %ymm3
	vperm2i128	$49, %ymm0, %ymm2, %ymm0
	vpaddq	%ymm0, %ymm3, %ymm0
	vpunpcklqdq	%ymm1, %ymm0, %ymm2
	vpunpckhqdq	%ymm1, %ymm0, %ymm0
	vpaddq	%ymm0, %ymm2, %ymm0
	vextracti128	$1, %ymm0, %xmm1
	vpextrq	$0, %xmm0, %rax
	vpextrq	$0, %xmm1, %r9
	vpextrq	$1, %xmm1, %rcx
	movq	%r9, %rbx
	shlq	$52, %rbx
	shrq	$12, %r9
	movq	%rcx, %r8
	shrq	$24, %r8
	shlq	$40, %rcx
	addq	%rax, %rbx
	adcq	%rcx, %r9
	adcq	$0, %r8
	movq	%r8, %rax
	movq	%r8, %rcx
	andq	$3, %r8
	shrq	$2, %rax
	andq	$-4, %rcx
	addq	%rcx, %rax
	addq	%rax, %rbx
	adcq	$0, %r9
	adcq	$0, %r8
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx2_verify$4
Ljade_onetimeauth_poly1305_amd64_avx2_verify$5:
	addq	(%rsi), %rbx
	adcq	8(%rsi), %r9
	adcq	$1, %r8
	movq	%r12, %r10
	imulq	%r8, %r10
	imulq	%rbp, %r8
	movq	%rbp, %rax
	mulq	%rbx
	movq	%rax, %rcx
	movq	%rdx, %r11
	movq	%rbp, %rax
	mulq	%r9
	addq	%rax, %r11
	adcq	%rdx, %r8
	movq	%r12, %rax
	mulq	%r9
	movq	%rdx, %r9
	addq	%r10, %r9
	movq	%rax, %r10
	movq	%r13, %rax
	mulq	%rbx
	addq	%r10, %rcx
	adcq	%rax, %r11
	adcq	%rdx, %r8
	movq	$-4, %rbx
	movq	%r8, %rax
	shrq	$2, %rax
	andq	%r8, %rbx
	addq	%rax, %rbx
	andq	$3, %r8
	addq	%rcx, %rbx
	adcq	%r11, %r9
	adcq	$0, %r8
	addq	$16, %rsi
	addq	$-16, %r14
Ljade_onetimeauth_poly1305_amd64_avx2_verify$4:
	cmpq	$16, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx2_verify$5
	cmpq	$0, %r14
	jbe 	Ljade_onetimeauth_poly1305_amd64_avx2_verify$3
	xorq	%rcx, %rcx
	movq	%r14, %rax
	andq	$7, %rax
	shlq	$3, %rax
	shrq	$3, %r14
	movq	%r14, %rdx
	xorq	$1, %rdx
	movq	%r14, %r10
	addq	$-1, %r10
	movq	%rax, %r11
	andq	%r10, %r11
	xorq	%r11, %rcx
	xorq	%r11, %rax
	shlq	%cl, %rdx
	movq	%rax, %rcx
	shlq	%cl, %r14
	movq	%rdx, %rax
	movq	%r14, %rcx
	subq	$1, %rax
	sbbq	$0, %rcx
	movq	(%rsi), %r10
	andq	%rax, %r10
	orq 	%rdx, %r10
	movq	8(%rsi), %rax
	andq	%rcx, %rax
	orq 	%r14, %rax
	addq	%r10, %rbx
	adcq	%rax, %r9
	adcq	$0, %r8
	movq	%r12, %rsi
	imulq	%r8, %rsi
	imulq	%rbp, %r8
	movq	%rbp, %rax
	mulq	%rbx
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%rbp, %rax
	mulq	%r9
	addq	%rax, %r10
	adcq	%rdx, %r8
	movq	%r12, %rax
	mulq	%r9
	movq	%rdx, %r9
	addq	%rsi, %r9
	movq	%rax, %rsi
	movq	%r13, %rax
	mulq	%rbx
	addq	%rsi, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %r8
	movq	$-4, %rbx
	movq	%r8, %rax
	shrq	$2, %rax
	andq	%r8, %rbx
	addq	%rax, %rbx
	andq	$3, %r8
	addq	%rcx, %rbx
	adcq	%r10, %r9
	adcq	$0, %r8
Ljade_onetimeauth_poly1305_amd64_avx2_verify$3:
	movq	%rbx, %rax
	movq	%r9, %rcx
	addq	$5, %rax
	adcq	$0, %rcx
	adcq	$0, %r8
	shrq	$2, %r8
	negq	%r8
	xorq	%rbx, %rax
	xorq	%r9, %rcx
	andq	%r8, %rax
	andq	%r8, %rcx
	xorq	%rbx, %rax
	xorq	%r9, %rcx
	movq	(%r15), %rdx
	movq	8(%r15), %rsi
	addq	%rdx, %rax
	adcq	%rsi, %rcx
Ljade_onetimeauth_poly1305_amd64_avx2_verify$2:
	movq	%rax, %rdx
	xorq	(%rdi), %rdx
	xorq	8(%rdi), %rcx
	orq 	%rcx, %rdx
	xorq	%rax, %rax
	subq	$1, %rdx
	adcq	$0, %rax
	addq	$-1, %rax
	movq	640(%rsp), %rbx
	movq	648(%rsp), %rbp
	movq	656(%rsp), %r12
	movq	664(%rsp), %r13
	movq	672(%rsp), %r14
	movq	680(%rsp), %r15
	movq	688(%rsp), %rsp
	ret 
_jade_onetimeauth_poly1305_amd64_avx2:
jade_onetimeauth_poly1305_amd64_avx2:
	movq	%rsp, %rax
	leaq	-696(%rsp), %rsp
	andq	$-32, %rsp
	movq	%rax, 688(%rsp)
	movq	%rbx, 640(%rsp)
	movq	%rbp, 648(%rsp)
	movq	%r12, 656(%rsp)
	movq	%r13, 664(%rsp)
	movq	%r14, 672(%rsp)
	movq	%r15, 680(%rsp)
	movq	%rdx, %r14
	movq	%rcx, %r15
	cmpq	$256, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx2$1
	movq	$0, %rbp
	movq	$0, %r12
	movq	$0, %r8
	movq	(%r15), %r9
	movq	8(%r15), %r13
	movq	$1152921487695413247, %rax
	andq	%rax, %r9
	movq	$1152921487695413244, %rax
	andq	%rax, %r13
	movq	%r13, %rbx
	shrq	$2, %rbx
	addq	%r13, %rbx
	addq	$16, %r15
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx2$9
Ljade_onetimeauth_poly1305_amd64_avx2$10:
	addq	(%rsi), %rbp
	adcq	8(%rsi), %r12
	adcq	$1, %r8
	movq	%rbx, %r11
	imulq	%r8, %r11
	imulq	%r9, %r8
	movq	%r9, %rax
	mulq	%rbp
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%r9, %rax
	mulq	%r12
	addq	%rax, %r10
	adcq	%rdx, %r8
	movq	%rbx, %rax
	mulq	%r12
	movq	%rdx, %r12
	addq	%r11, %r12
	movq	%rax, %r11
	movq	%r13, %rax
	mulq	%rbp
	addq	%r11, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %r8
	movq	$-4, %rbp
	movq	%r8, %rax
	shrq	$2, %rax
	andq	%r8, %rbp
	addq	%rax, %rbp
	andq	$3, %r8
	addq	%rcx, %rbp
	adcq	%r10, %r12
	adcq	$0, %r8
	addq	$16, %rsi
	addq	$-16, %r14
Ljade_onetimeauth_poly1305_amd64_avx2$9:
	cmpq	$16, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx2$10
	cmpq	$0, %r14
	jbe 	Ljade_onetimeauth_poly1305_amd64_avx2$8
	xorq	%rcx, %rcx
	movq	%r14, %rax
	andq	$7, %rax
	shlq	$3, %rax
	shrq	$3, %r14
	movq	%r14, %rdx
	xorq	$1, %rdx
	movq	%r14, %r10
	addq	$-1, %r10
	movq	%rax, %r11
	andq	%r10, %r11
	xorq	%r11, %rcx
	xorq	%r11, %rax
	shlq	%cl, %rdx
	movq	%rax, %rcx
	shlq	%cl, %r14
	movq	%rdx, %rax
	movq	%r14, %rcx
	subq	$1, %rax
	sbbq	$0, %rcx
	movq	(%rsi), %r10
	andq	%rax, %r10
	orq 	%rdx, %r10
	movq	8(%rsi), %rax
	andq	%rcx, %rax
	orq 	%r14, %rax
	addq	%r10, %rbp
	adcq	%rax, %r12
	adcq	$0, %r8
	movq	%rbx, %rsi
	imulq	%r8, %rsi
	imulq	%r9, %r8
	movq	%r9, %rax
	mulq	%rbp
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%r9, %rax
	mulq	%r12
	addq	%rax, %r10
	adcq	%rdx, %r8
	movq	%rbx, %rax
	mulq	%r12
	movq	%rdx, %r12
	addq	%rsi, %r12
	movq	%rax, %rsi
	movq	%r13, %rax
	mulq	%rbp
	addq	%rsi, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %r8
	movq	$-4, %rbp
	movq	%r8, %rax
	shrq	$2, %rax
	andq	%r8, %rbp
	addq	%rax, %rbp
	andq	$3, %r8
	addq	%rcx, %rbp
	adcq	%r10, %r12
	adcq	$0, %r8
Ljade_onetimeauth_poly1305_amd64_avx2$8:
	movq	%rbp, %rax
	movq	%r12, %rcx
	addq	$5, %rax
	adcq	$0, %rcx
	adcq	$0, %r8
	shrq	$2, %r8
	negq	%r8
	xorq	%rbp, %rax
	xorq	%r12, %rcx
	andq	%r8, %rax
	andq	%r8, %rcx
	xorq	%rbp, %rax
	xorq	%r12, %rcx
	movq	(%r15), %rdx
	movq	8(%r15), %rsi
	addq	%rdx, %rax
	adcq	%rsi, %rcx
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx2$2
Ljade_onetimeauth_poly1305_amd64_avx2$1:
	movq	(%r15), %r13
	movq	8(%r15), %r12
	movq	$1152921487695413247, %rax
	andq	%rax, %r13
	movq	$1152921487695413244, %rax
	andq	%rax, %r12
	movq	%r12, %rbp
	shrq	$2, %rbp
	addq	%r12, %rbp
	addq	$16, %r15
	movq	%r13, %r8
	movq	%r12, %r11
	movq	$0, %rbx
	movq	%r8, %rax
	andq	$67108863, %rax
	movq	%rax, 344(%rsp)
	movq	%r8, %rax
	shrq	$26, %rax
	andq	$67108863, %rax
	movq	%rax, 376(%rsp)
	movq	%r8, %rax
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 408(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 440(%rsp)
	movq	%r11, %rax
	shrdq	$40, %rbx, %rax
	movq	%rax, 472(%rsp)
	movq	%rbp, %r10
	imulq	%rbx, %r10
	imulq	%r13, %rbx
	movq	%r13, %rax
	mulq	%r8
	movq	%rax, %rcx
	movq	%rdx, %r9
	movq	%r13, %rax
	mulq	%r11
	addq	%rax, %r9
	adcq	%rdx, %rbx
	movq	%rbp, %rax
	mulq	%r11
	movq	%rdx, %r11
	addq	%r10, %r11
	movq	%rax, %r10
	movq	%r12, %rax
	mulq	%r8
	addq	%r10, %rcx
	adcq	%rax, %r9
	adcq	%rdx, %rbx
	movq	$-4, %r8
	movq	%rbx, %rax
	shrq	$2, %rax
	andq	%rbx, %r8
	addq	%rax, %r8
	andq	$3, %rbx
	addq	%rcx, %r8
	adcq	%r9, %r11
	adcq	$0, %rbx
	movq	%r8, %rax
	andq	$67108863, %rax
	movq	%rax, 336(%rsp)
	movq	%r8, %rax
	shrq	$26, %rax
	andq	$67108863, %rax
	movq	%rax, 368(%rsp)
	movq	%r8, %rax
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 400(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 432(%rsp)
	movq	%r11, %rax
	shrdq	$40, %rbx, %rax
	movq	%rax, 464(%rsp)
	movq	%rbp, %r10
	imulq	%rbx, %r10
	imulq	%r13, %rbx
	movq	%r13, %rax
	mulq	%r8
	movq	%rax, %rcx
	movq	%rdx, %r9
	movq	%r13, %rax
	mulq	%r11
	addq	%rax, %r9
	adcq	%rdx, %rbx
	movq	%rbp, %rax
	mulq	%r11
	movq	%rdx, %r11
	addq	%r10, %r11
	movq	%rax, %r10
	movq	%r12, %rax
	mulq	%r8
	addq	%r10, %rcx
	adcq	%rax, %r9
	adcq	%rdx, %rbx
	movq	$-4, %r8
	movq	%rbx, %rax
	shrq	$2, %rax
	andq	%rbx, %r8
	addq	%rax, %r8
	andq	$3, %rbx
	addq	%rcx, %r8
	adcq	%r9, %r11
	adcq	$0, %rbx
	movq	%r8, %rax
	andq	$67108863, %rax
	movq	%rax, 328(%rsp)
	movq	%r8, %rax
	shrq	$26, %rax
	andq	$67108863, %rax
	movq	%rax, 360(%rsp)
	movq	%r8, %rax
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 392(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 424(%rsp)
	movq	%r11, %rax
	shrdq	$40, %rbx, %rax
	movq	%rax, 456(%rsp)
	movq	%rbp, %r9
	imulq	%rbx, %r9
	imulq	%r13, %rbx
	movq	%r13, %rax
	mulq	%r8
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%r13, %rax
	mulq	%r11
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	%rbp, %rax
	mulq	%r11
	movq	%rdx, %r11
	addq	%r9, %r11
	movq	%rax, %r9
	movq	%r12, %rax
	mulq	%r8
	addq	%r9, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %rbx
	movq	$-4, %rax
	movq	%rbx, %rdx
	shrq	$2, %rdx
	andq	%rbx, %rax
	addq	%rdx, %rax
	andq	$3, %rbx
	addq	%rcx, %rax
	adcq	%r10, %r11
	adcq	$0, %rbx
	movq	%rax, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 320(%rsp)
	movq	%rax, %rcx
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 352(%rsp)
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 384(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 416(%rsp)
	shrdq	$40, %rbx, %r11
	movq	%r11, 448(%rsp)
	vpbroadcastq	glob_data + 16(%rip), %ymm0
	vpmuludq	352(%rsp), %ymm0, %ymm1
	vmovdqu	%ymm1, 64(%rsp)
	vpmuludq	384(%rsp), %ymm0, %ymm1
	vmovdqu	%ymm1, 96(%rsp)
	vpmuludq	416(%rsp), %ymm0, %ymm1
	vmovdqu	%ymm1, 128(%rsp)
	vpmuludq	448(%rsp), %ymm0, %ymm0
	vmovdqu	%ymm0, 160(%rsp)
	vpbroadcastq	320(%rsp), %ymm0
	vmovdqu	%ymm0, 480(%rsp)
	vpbroadcastq	352(%rsp), %ymm0
	vmovdqu	%ymm0, 512(%rsp)
	vpbroadcastq	384(%rsp), %ymm0
	vmovdqu	%ymm0, 544(%rsp)
	vpbroadcastq	416(%rsp), %ymm0
	vmovdqu	%ymm0, 576(%rsp)
	vpbroadcastq	448(%rsp), %ymm0
	vmovdqu	%ymm0, 608(%rsp)
	vpbroadcastq	64(%rsp), %ymm0
	vmovdqu	%ymm0, 192(%rsp)
	vpbroadcastq	96(%rsp), %ymm0
	vmovdqu	%ymm0, 224(%rsp)
	vpbroadcastq	128(%rsp), %ymm0
	vmovdqu	%ymm0, 256(%rsp)
	vpbroadcastq	160(%rsp), %ymm0
	vmovdqu	%ymm0, 288(%rsp)
	vpxor	%ymm0, %ymm0, %ymm0
	vpxor	%ymm1, %ymm1, %ymm1
	vpxor	%ymm6, %ymm6, %ymm6
	vpxor	%ymm3, %ymm3, %ymm3
	vpxor	%ymm4, %ymm4, %ymm4
	vpbroadcastq	glob_data + 8(%rip), %ymm7
	vmovdqu	%ymm7, (%rsp)
	vpbroadcastq	glob_data + 0(%rip), %ymm2
	vmovdqu	%ymm2, 32(%rsp)
	vmovdqu	(%rsi), %ymm2
	vmovdqu	32(%rsi), %ymm5
	addq	$64, %rsi
	vperm2i128	$32, %ymm5, %ymm2, %ymm9
	vperm2i128	$49, %ymm5, %ymm2, %ymm2
	vpsrldq	$6, %ymm9, %ymm5
	vpsrldq	$6, %ymm2, %ymm10
	vpunpckhqdq	%ymm2, %ymm9, %ymm8
	vpunpcklqdq	%ymm2, %ymm9, %ymm9
	vpunpcklqdq	%ymm10, %ymm5, %ymm10
	vpsrlq	$4, %ymm10, %ymm2
	vpand	%ymm7, %ymm2, %ymm2
	vpsrlq	$26, %ymm9, %ymm11
	vpand	%ymm7, %ymm9, %ymm5
	vpsrlq	$30, %ymm10, %ymm9
	vpand	%ymm7, %ymm9, %ymm9
	vpsrlq	$40, %ymm8, %ymm8
	vpor	32(%rsp), %ymm8, %ymm10
	vpand	%ymm7, %ymm11, %ymm11
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx2$6
Ljade_onetimeauth_poly1305_amd64_avx2$7:
	vmovdqu	480(%rsp), %ymm8
	vmovdqu	512(%rsp), %ymm7
	vmovdqu	288(%rsp), %ymm13
	vpaddq	%ymm5, %ymm0, %ymm0
	vpaddq	%ymm11, %ymm1, %ymm1
	vpmuludq	%ymm8, %ymm0, %ymm5
	vpaddq	%ymm2, %ymm6, %ymm2
	vpmuludq	%ymm7, %ymm0, %ymm6
	vpaddq	%ymm9, %ymm3, %ymm3
	vpmuludq	%ymm8, %ymm1, %ymm9
	vpaddq	%ymm10, %ymm4, %ymm4
	vpmuludq	%ymm7, %ymm1, %ymm12
	vpmuludq	%ymm8, %ymm2, %ymm14
	vpmuludq	%ymm7, %ymm2, %ymm10
	vpmuludq	%ymm8, %ymm3, %ymm11
	vpaddq	%ymm6, %ymm9, %ymm6
	vpmuludq	%ymm7, %ymm3, %ymm9
	vpaddq	%ymm12, %ymm14, %ymm7
	vpmuludq	%ymm8, %ymm4, %ymm8
	vpaddq	%ymm10, %ymm11, %ymm11
	vpaddq	%ymm9, %ymm8, %ymm12
	vpmuludq	%ymm13, %ymm1, %ymm14
	vmovdqu	(%rsi), %ymm8
	vpmuludq	%ymm13, %ymm2, %ymm15
	vmovdqu	544(%rsp), %ymm9
	vpmuludq	%ymm13, %ymm3, %ymm10
	vpmuludq	%ymm13, %ymm4, %ymm13
	vpaddq	%ymm14, %ymm5, %ymm5
	vmovdqu	32(%rsi), %ymm14
	vpaddq	%ymm15, %ymm6, %ymm6
	vpaddq	%ymm10, %ymm7, %ymm10
	vpaddq	%ymm13, %ymm11, %ymm11
	vpmuludq	%ymm9, %ymm0, %ymm15
	vperm2i128	$32, %ymm14, %ymm8, %ymm7
	vpmuludq	%ymm9, %ymm1, %ymm13
	vperm2i128	$49, %ymm14, %ymm8, %ymm8
	vpmuludq	%ymm9, %ymm2, %ymm14
	vpaddq	%ymm15, %ymm10, %ymm9
	vmovdqu	256(%rsp), %ymm10
	vpaddq	%ymm13, %ymm11, %ymm11
	vpaddq	%ymm14, %ymm12, %ymm12
	vpmuludq	%ymm10, %ymm2, %ymm2
	vpmuludq	%ymm10, %ymm3, %ymm13
	vmovdqu	576(%rsp), %ymm14
	vpmuludq	%ymm10, %ymm4, %ymm10
	vpsrldq	$6, %ymm7, %ymm15
	vpaddq	%ymm2, %ymm5, %ymm2
	vpsrldq	$6, %ymm8, %ymm5
	vpaddq	%ymm13, %ymm6, %ymm6
	vpaddq	%ymm9, %ymm10, %ymm9
	vmovdqu	224(%rsp), %ymm10
	vpmuludq	%ymm14, %ymm0, %ymm13
	vpmuludq	%ymm14, %ymm1, %ymm1
	vpunpckhqdq	%ymm8, %ymm7, %ymm14
	vpunpcklqdq	%ymm8, %ymm7, %ymm7
	vpaddq	%ymm13, %ymm11, %ymm11
	vpaddq	%ymm1, %ymm12, %ymm1
	vpmuludq	%ymm10, %ymm3, %ymm3
	vpmuludq	%ymm10, %ymm4, %ymm8
	vpaddq	%ymm3, %ymm2, %ymm2
	vpaddq	%ymm6, %ymm8, %ymm3
	vmovdqu	(%rsp), %ymm8
	vpmuludq	192(%rsp), %ymm4, %ymm4
	vpmuludq	608(%rsp), %ymm0, %ymm0
	vpunpcklqdq	%ymm5, %ymm15, %ymm10
	vpsrlq	$4, %ymm10, %ymm6
	vpaddq	%ymm4, %ymm2, %ymm2
	vpsrlq	$26, %ymm2, %ymm12
	vpand	%ymm8, %ymm2, %ymm4
	vpand	%ymm8, %ymm11, %ymm5
	vpsrlq	$26, %ymm11, %ymm13
	vpaddq	%ymm0, %ymm1, %ymm1
	vpand	%ymm8, %ymm6, %ymm2
	vpsrlq	$26, %ymm7, %ymm11
	vpaddq	%ymm12, %ymm3, %ymm0
	vpaddq	%ymm13, %ymm1, %ymm6
	vpsrlq	$26, %ymm0, %ymm1
	vpsrlq	$26, %ymm6, %ymm3
	vpsllq	$2, %ymm3, %ymm12
	vpaddq	%ymm12, %ymm3, %ymm13
	vpand	%ymm8, %ymm0, %ymm3
	vpand	%ymm8, %ymm6, %ymm12
	vpaddq	%ymm1, %ymm9, %ymm0
	vpaddq	%ymm13, %ymm4, %ymm1
	vpsrlq	$26, %ymm0, %ymm4
	vpsrlq	$26, %ymm1, %ymm9
	vpand	%ymm8, %ymm0, %ymm6
	vpand	%ymm8, %ymm1, %ymm0
	vpaddq	%ymm4, %ymm5, %ymm4
	vpaddq	%ymm9, %ymm3, %ymm1
	vpsrlq	$26, %ymm4, %ymm5
	vpand	%ymm8, %ymm4, %ymm3
	vpaddq	%ymm5, %ymm12, %ymm4
	addq	$64, %rsi
	vpand	%ymm8, %ymm7, %ymm5
	vpsrlq	$30, %ymm10, %ymm7
	vpand	%ymm8, %ymm7, %ymm9
	vpsrlq	$40, %ymm14, %ymm7
	vpor	32(%rsp), %ymm7, %ymm10
	vpand	%ymm8, %ymm11, %ymm11
	addq	$-64, %r14
Ljade_onetimeauth_poly1305_amd64_avx2$6:
	cmpq	$128, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx2$7
	addq	$-64, %r14
	vmovdqu	320(%rsp), %ymm7
	vmovdqu	352(%rsp), %ymm8
	vmovdqu	160(%rsp), %ymm12
	vpaddq	%ymm5, %ymm0, %ymm0
	vpaddq	%ymm11, %ymm1, %ymm1
	vpaddq	%ymm2, %ymm6, %ymm2
	vpaddq	%ymm9, %ymm3, %ymm3
	vpaddq	%ymm10, %ymm4, %ymm4
	vpmuludq	%ymm7, %ymm0, %ymm5
	vpmuludq	%ymm7, %ymm1, %ymm6
	vpmuludq	%ymm7, %ymm2, %ymm9
	vpmuludq	%ymm7, %ymm3, %ymm10
	vpmuludq	%ymm7, %ymm4, %ymm7
	vpmuludq	%ymm8, %ymm0, %ymm11
	vpmuludq	%ymm8, %ymm1, %ymm13
	vpmuludq	%ymm8, %ymm2, %ymm14
	vpmuludq	%ymm8, %ymm3, %ymm8
	vmovdqu	384(%rsp), %ymm15
	vpaddq	%ymm11, %ymm6, %ymm6
	vpaddq	%ymm13, %ymm9, %ymm9
	vpaddq	%ymm14, %ymm10, %ymm10
	vpaddq	%ymm8, %ymm7, %ymm7
	vpmuludq	%ymm12, %ymm1, %ymm8
	vpmuludq	%ymm12, %ymm2, %ymm11
	vpmuludq	%ymm12, %ymm3, %ymm13
	vpmuludq	%ymm12, %ymm4, %ymm12
	vmovdqu	128(%rsp), %ymm14
	vpaddq	%ymm8, %ymm5, %ymm5
	vpaddq	%ymm11, %ymm6, %ymm6
	vpaddq	%ymm13, %ymm9, %ymm8
	vpaddq	%ymm12, %ymm10, %ymm10
	vpmuludq	%ymm15, %ymm0, %ymm13
	vpmuludq	%ymm15, %ymm1, %ymm11
	vpmuludq	%ymm15, %ymm2, %ymm12
	vmovdqu	416(%rsp), %ymm9
	vpaddq	%ymm13, %ymm8, %ymm8
	vpaddq	%ymm11, %ymm10, %ymm10
	vpaddq	%ymm12, %ymm7, %ymm7
	vpmuludq	%ymm14, %ymm2, %ymm2
	vpmuludq	%ymm14, %ymm3, %ymm12
	vpmuludq	%ymm14, %ymm4, %ymm13
	vmovdqu	96(%rsp), %ymm11
	vpaddq	%ymm2, %ymm5, %ymm5
	vpaddq	%ymm12, %ymm6, %ymm6
	vpaddq	%ymm8, %ymm13, %ymm2
	vpmuludq	%ymm9, %ymm0, %ymm8
	vpmuludq	%ymm9, %ymm1, %ymm9
	vpaddq	%ymm8, %ymm10, %ymm1
	vpaddq	%ymm9, %ymm7, %ymm7
	vpmuludq	%ymm11, %ymm3, %ymm3
	vpmuludq	%ymm11, %ymm4, %ymm8
	vpaddq	%ymm3, %ymm5, %ymm5
	vpaddq	%ymm6, %ymm8, %ymm3
	vpmuludq	64(%rsp), %ymm4, %ymm4
	vpmuludq	448(%rsp), %ymm0, %ymm0
	vpaddq	%ymm4, %ymm5, %ymm4
	vmovdqu	%ymm1, %ymm5
	vpaddq	%ymm0, %ymm7, %ymm6
	vmovdqu	(%rsp), %ymm0
	vpsrlq	$26, %ymm4, %ymm7
	vpsrlq	$26, %ymm5, %ymm8
	vpand	%ymm0, %ymm4, %ymm1
	vpand	%ymm0, %ymm5, %ymm4
	vpaddq	%ymm7, %ymm3, %ymm3
	vpaddq	%ymm8, %ymm6, %ymm5
	vpsrlq	$26, %ymm3, %ymm6
	vpsrlq	$26, %ymm5, %ymm7
	vpsllq	$2, %ymm7, %ymm8
	vpaddq	%ymm8, %ymm7, %ymm7
	vpand	%ymm0, %ymm3, %ymm8
	vpand	%ymm0, %ymm5, %ymm3
	vpaddq	%ymm6, %ymm2, %ymm2
	vpaddq	%ymm7, %ymm1, %ymm5
	vpsrlq	$26, %ymm2, %ymm6
	vpsrlq	$26, %ymm5, %ymm7
	vpand	%ymm0, %ymm2, %ymm1
	vpand	%ymm0, %ymm5, %ymm2
	vpaddq	%ymm6, %ymm4, %ymm4
	vpaddq	%ymm7, %ymm8, %ymm5
	vpsrlq	$26, %ymm4, %ymm6
	vpand	%ymm0, %ymm4, %ymm0
	vpaddq	%ymm6, %ymm3, %ymm3
	vpsllq	$26, %ymm5, %ymm4
	vpaddq	%ymm2, %ymm4, %ymm2
	vpsllq	$26, %ymm0, %ymm0
	vpaddq	%ymm1, %ymm0, %ymm0
	vpsrldq	$8, %ymm3, %ymm1
	vpaddq	%ymm3, %ymm1, %ymm1
	vpermq	$-128, %ymm1, %ymm1
	vperm2i128	$32, %ymm0, %ymm2, %ymm3
	vperm2i128	$49, %ymm0, %ymm2, %ymm0
	vpaddq	%ymm0, %ymm3, %ymm0
	vpunpcklqdq	%ymm1, %ymm0, %ymm2
	vpunpckhqdq	%ymm1, %ymm0, %ymm0
	vpaddq	%ymm0, %ymm2, %ymm0
	vextracti128	$1, %ymm0, %xmm1
	vpextrq	$0, %xmm0, %rax
	vpextrq	$0, %xmm1, %r8
	vpextrq	$1, %xmm1, %rcx
	movq	%r8, %r9
	shlq	$52, %r9
	shrq	$12, %r8
	movq	%rcx, %rbx
	shrq	$24, %rbx
	shlq	$40, %rcx
	addq	%rax, %r9
	adcq	%rcx, %r8
	adcq	$0, %rbx
	movq	%rbx, %rax
	movq	%rbx, %rcx
	andq	$3, %rbx
	shrq	$2, %rax
	andq	$-4, %rcx
	addq	%rcx, %rax
	addq	%rax, %r9
	adcq	$0, %r8
	adcq	$0, %rbx
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx2$4
Ljade_onetimeauth_poly1305_amd64_avx2$5:
	addq	(%rsi), %r9
	adcq	8(%rsi), %r8
	adcq	$1, %rbx
	movq	%rbp, %r11
	imulq	%rbx, %r11
	imulq	%r13, %rbx
	movq	%r13, %rax
	mulq	%r9
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%r13, %rax
	mulq	%r8
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	%rbp, %rax
	mulq	%r8
	movq	%rdx, %r8
	addq	%r11, %r8
	movq	%rax, %r11
	movq	%r12, %rax
	mulq	%r9
	addq	%r11, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %rbx
	movq	$-4, %r9
	movq	%rbx, %rax
	shrq	$2, %rax
	andq	%rbx, %r9
	addq	%rax, %r9
	andq	$3, %rbx
	addq	%rcx, %r9
	adcq	%r10, %r8
	adcq	$0, %rbx
	addq	$16, %rsi
	addq	$-16, %r14
Ljade_onetimeauth_poly1305_amd64_avx2$4:
	cmpq	$16, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx2$5
	cmpq	$0, %r14
	jbe 	Ljade_onetimeauth_poly1305_amd64_avx2$3
	xorq	%rcx, %rcx
	movq	%r14, %rax
	andq	$7, %rax
	shlq	$3, %rax
	shrq	$3, %r14
	movq	%r14, %rdx
	xorq	$1, %rdx
	movq	%r14, %r10
	addq	$-1, %r10
	movq	%rax, %r11
	andq	%r10, %r11
	xorq	%r11, %rcx
	xorq	%r11, %rax
	shlq	%cl, %rdx
	movq	%rax, %rcx
	shlq	%cl, %r14
	movq	%rdx, %rax
	movq	%r14, %rcx
	subq	$1, %rax
	sbbq	$0, %rcx
	movq	(%rsi), %r10
	andq	%rax, %r10
	orq 	%rdx, %r10
	movq	8(%rsi), %rax
	andq	%rcx, %rax
	orq 	%r14, %rax
	addq	%r10, %r9
	adcq	%rax, %r8
	adcq	$0, %rbx
	movq	%rbp, %rsi
	imulq	%rbx, %rsi
	imulq	%r13, %rbx
	movq	%r13, %rax
	mulq	%r9
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%r13, %rax
	mulq	%r8
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	%rbp, %rax
	mulq	%r8
	movq	%rdx, %r8
	addq	%rsi, %r8
	movq	%rax, %rsi
	movq	%r12, %rax
	mulq	%r9
	addq	%rsi, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %rbx
	movq	$-4, %r9
	movq	%rbx, %rax
	shrq	$2, %rax
	andq	%rbx, %r9
	addq	%rax, %r9
	andq	$3, %rbx
	addq	%rcx, %r9
	adcq	%r10, %r8
	adcq	$0, %rbx
Ljade_onetimeauth_poly1305_amd64_avx2$3:
	movq	%r9, %rax
	movq	%r8, %rcx
	addq	$5, %rax
	adcq	$0, %rcx
	adcq	$0, %rbx
	shrq	$2, %rbx
	negq	%rbx
	xorq	%r9, %rax
	xorq	%r8, %rcx
	andq	%rbx, %rax
	andq	%rbx, %rcx
	xorq	%r9, %rax
	xorq	%r8, %rcx
	movq	(%r15), %rdx
	movq	8(%r15), %rsi
	addq	%rdx, %rax
	adcq	%rsi, %rcx
Ljade_onetimeauth_poly1305_amd64_avx2$2:
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	xorq	%rax, %rax
	movq	640(%rsp), %rbx
	movq	648(%rsp), %rbp
	movq	656(%rsp), %r12
	movq	664(%rsp), %r13
	movq	672(%rsp), %r14
	movq	680(%rsp), %r15
	movq	688(%rsp), %rsp
	ret 
	.data
	.p2align	5
_glob_data:
glob_data:
      .byte 0
      .byte 0
      .byte 0
      .byte 1
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -1
      .byte -1
      .byte -1
      .byte 3
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 5
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
