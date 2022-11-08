	.att_syntax
	.text
	.p2align	5
	.globl	_jade_onetimeauth_poly1305_amd64_avx_verify
	.globl	jade_onetimeauth_poly1305_amd64_avx_verify
	.globl	_jade_onetimeauth_poly1305_amd64_avx
	.globl	jade_onetimeauth_poly1305_amd64_avx
_jade_onetimeauth_poly1305_amd64_avx_verify:
jade_onetimeauth_poly1305_amd64_avx_verify:
	movq	%rsp, %rax
	leaq	-600(%rsp), %rsp
	andq	$-16, %rsp
	movq	%rax, 592(%rsp)
	movq	%rbx, 544(%rsp)
	movq	%rbp, 552(%rsp)
	movq	%r12, 560(%rsp)
	movq	%r13, 568(%rsp)
	movq	%r14, 576(%rsp)
	movq	%r15, 584(%rsp)
	movq	%rdx, %r14
	movq	%rcx, %r15
	cmpq	$1024, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx_verify$1
	movq	$0, %r8
	movq	$0, %r12
	movq	$0, %r13
	movq	(%r15), %rbp
	movq	8(%r15), %rbx
	movq	$1152921487695413247, %rax
	andq	%rax, %rbp
	movq	$1152921487695413244, %rax
	andq	%rax, %rbx
	movq	%rbx, %r9
	shrq	$2, %r9
	addq	%rbx, %r9
	addq	$16, %r15
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx_verify$9
Ljade_onetimeauth_poly1305_amd64_avx_verify$10:
	addq	(%rsi), %r8
	adcq	8(%rsi), %r12
	adcq	$1, %r13
	movq	%r9, %r10
	imulq	%r13, %r10
	imulq	%rbp, %r13
	movq	%rbp, %rax
	mulq	%r8
	movq	%rax, %rcx
	movq	%rdx, %r11
	movq	%rbp, %rax
	mulq	%r12
	addq	%rax, %r11
	adcq	%rdx, %r13
	movq	%r9, %rax
	mulq	%r12
	movq	%rdx, %r12
	addq	%r10, %r12
	movq	%rax, %r10
	movq	%rbx, %rax
	mulq	%r8
	addq	%r10, %rcx
	adcq	%rax, %r11
	adcq	%rdx, %r13
	movq	$-4, %r8
	movq	%r13, %rax
	shrq	$2, %rax
	andq	%r13, %r8
	addq	%rax, %r8
	andq	$3, %r13
	addq	%rcx, %r8
	adcq	%r11, %r12
	adcq	$0, %r13
	addq	$16, %rsi
	addq	$-16, %r14
Ljade_onetimeauth_poly1305_amd64_avx_verify$9:
	cmpq	$16, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx_verify$10
	cmpq	$0, %r14
	jbe 	Ljade_onetimeauth_poly1305_amd64_avx_verify$8
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
	addq	%r10, %r8
	adcq	%rax, %r12
	adcq	$0, %r13
	movq	%r9, %rsi
	imulq	%r13, %rsi
	imulq	%rbp, %r13
	movq	%rbp, %rax
	mulq	%r8
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%rbp, %rax
	mulq	%r12
	addq	%rax, %r10
	adcq	%rdx, %r13
	movq	%r9, %rax
	mulq	%r12
	movq	%rdx, %r12
	addq	%rsi, %r12
	movq	%rax, %rsi
	movq	%rbx, %rax
	mulq	%r8
	addq	%rsi, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %r13
	movq	$-4, %r8
	movq	%r13, %rax
	shrq	$2, %rax
	andq	%r13, %r8
	addq	%rax, %r8
	andq	$3, %r13
	addq	%rcx, %r8
	adcq	%r10, %r12
	adcq	$0, %r13
Ljade_onetimeauth_poly1305_amd64_avx_verify$8:
	movq	%r8, %rax
	movq	%r12, %rcx
	addq	$5, %rax
	adcq	$0, %rcx
	adcq	$0, %r13
	shrq	$2, %r13
	negq	%r13
	xorq	%r8, %rax
	xorq	%r12, %rcx
	andq	%r13, %rax
	andq	%r13, %rcx
	xorq	%r8, %rax
	xorq	%r12, %rcx
	movq	(%r15), %rdx
	movq	8(%r15), %rsi
	addq	%rdx, %rax
	adcq	%rsi, %rcx
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx_verify$2
Ljade_onetimeauth_poly1305_amd64_avx_verify$1:
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
	movq	%rax, 232(%rsp)
	movq	%r8, %rax
	shrq	$26, %rax
	andq	$67108863, %rax
	movq	%rax, 248(%rsp)
	movq	%r8, %rax
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 264(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 280(%rsp)
	movq	%r11, %rax
	shrdq	$40, %rbx, %rax
	movq	%rax, 296(%rsp)
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
	movq	%rax, 224(%rsp)
	movq	%r8, %rax
	shrq	$26, %rax
	andq	$67108863, %rax
	movq	%rax, 240(%rsp)
	movq	%r8, %rax
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 256(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 272(%rsp)
	movq	%r11, %rax
	shrdq	$40, %rbx, %rax
	movq	%rax, 288(%rsp)
	vpbroadcastq	glob_data + 16(%rip), %xmm0
	vpmuludq	240(%rsp), %xmm0, %xmm1
	vmovdqu	%xmm1, 32(%rsp)
	vpmuludq	256(%rsp), %xmm0, %xmm1
	vmovdqu	%xmm1, 48(%rsp)
	vpmuludq	272(%rsp), %xmm0, %xmm1
	vmovdqu	%xmm1, 64(%rsp)
	vpmuludq	288(%rsp), %xmm0, %xmm0
	vmovdqu	%xmm0, 80(%rsp)
	vpbroadcastq	224(%rsp), %xmm0
	vmovdqu	%xmm0, 304(%rsp)
	vpbroadcastq	240(%rsp), %xmm0
	vmovdqu	%xmm0, 320(%rsp)
	vpbroadcastq	256(%rsp), %xmm0
	vmovdqu	%xmm0, 336(%rsp)
	vpbroadcastq	272(%rsp), %xmm0
	vmovdqu	%xmm0, 352(%rsp)
	vpbroadcastq	288(%rsp), %xmm0
	vmovdqu	%xmm0, 368(%rsp)
	vpbroadcastq	32(%rsp), %xmm0
	vmovdqu	%xmm0, 96(%rsp)
	vpbroadcastq	48(%rsp), %xmm0
	vmovdqu	%xmm0, 112(%rsp)
	vpbroadcastq	64(%rsp), %xmm0
	vmovdqu	%xmm0, 128(%rsp)
	vpbroadcastq	80(%rsp), %xmm0
	vmovdqu	%xmm0, 144(%rsp)
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
	movq	%rcx, 384(%rsp)
	movq	%rax, %rcx
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 400(%rsp)
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 416(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 432(%rsp)
	shrdq	$40, %rbx, %r11
	movq	%r11, 448(%rsp)
	movq	384(%rsp), %rax
	movq	%rax, 392(%rsp)
	movq	400(%rsp), %rax
	movq	%rax, 408(%rsp)
	movq	416(%rsp), %rax
	movq	%rax, 424(%rsp)
	movq	432(%rsp), %rax
	movq	%rax, 440(%rsp)
	movq	448(%rsp), %rax
	movq	%rax, 456(%rsp)
	vpbroadcastq	glob_data + 16(%rip), %xmm0
	vpmuludq	400(%rsp), %xmm0, %xmm1
	vmovdqu	%xmm1, 160(%rsp)
	vpmuludq	416(%rsp), %xmm0, %xmm1
	vmovdqu	%xmm1, 176(%rsp)
	vpmuludq	432(%rsp), %xmm0, %xmm1
	vmovdqu	%xmm1, 192(%rsp)
	vpmuludq	448(%rsp), %xmm0, %xmm0
	vmovdqu	%xmm0, 208(%rsp)
	vpxor	%xmm3, %xmm3, %xmm3
	vpxor	%xmm2, %xmm2, %xmm2
	vpxor	%xmm1, %xmm1, %xmm1
	vpxor	%xmm4, %xmm4, %xmm4
	vpxor	%xmm5, %xmm5, %xmm5
	vpbroadcastq	glob_data + 8(%rip), %xmm0
	vmovdqu	%xmm0, (%rsp)
	vpbroadcastq	glob_data + 0(%rip), %xmm0
	vmovdqu	%xmm0, 16(%rsp)
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx_verify$6
Ljade_onetimeauth_poly1305_amd64_avx_verify$7:
	vmovdqu	384(%rsp), %xmm0
	vmovdqu	400(%rsp), %xmm12
	vmovdqu	208(%rsp), %xmm14
	vpmuludq	%xmm0, %xmm3, %xmm7
	vpmuludq	%xmm12, %xmm3, %xmm8
	vpmuludq	%xmm0, %xmm2, %xmm13
	vpmuludq	%xmm12, %xmm2, %xmm6
	vpmuludq	%xmm0, %xmm1, %xmm9
	vpmuludq	%xmm12, %xmm1, %xmm10
	vpmuludq	%xmm0, %xmm4, %xmm11
	vpaddq	%xmm8, %xmm13, %xmm8
	vpmuludq	%xmm12, %xmm4, %xmm12
	vpaddq	%xmm6, %xmm9, %xmm9
	vpmuludq	%xmm0, %xmm5, %xmm0
	vpaddq	%xmm10, %xmm11, %xmm10
	vpaddq	%xmm12, %xmm0, %xmm6
	vpmuludq	%xmm14, %xmm2, %xmm15
	vmovdqu	(%rsi), %xmm0
	vpmuludq	%xmm14, %xmm1, %xmm13
	vmovdqu	416(%rsp), %xmm12
	vpmuludq	%xmm14, %xmm4, %xmm11
	vpmuludq	%xmm14, %xmm5, %xmm14
	vpaddq	%xmm15, %xmm7, %xmm7
	vmovdqu	16(%rsi), %xmm15
	vpaddq	%xmm13, %xmm8, %xmm8
	vpaddq	%xmm11, %xmm9, %xmm13
	vpaddq	%xmm14, %xmm10, %xmm9
	vpmuludq	%xmm12, %xmm3, %xmm14
	vpunpcklqdq	%xmm15, %xmm0, %xmm10
	vpmuludq	%xmm12, %xmm2, %xmm11
	vpunpckhqdq	%xmm15, %xmm0, %xmm0
	vpmuludq	%xmm12, %xmm1, %xmm12
	vpaddq	%xmm14, %xmm13, %xmm13
	vmovdqu	192(%rsp), %xmm14
	vpaddq	%xmm11, %xmm9, %xmm9
	vpaddq	%xmm12, %xmm6, %xmm6
	vpmuludq	%xmm14, %xmm1, %xmm11
	vpmuludq	%xmm14, %xmm4, %xmm12
	vmovdqu	%xmm10, %xmm1
	vpmuludq	%xmm14, %xmm5, %xmm14
	vpsrlq	$26, %xmm1, %xmm1
	vpand	(%rsp), %xmm1, %xmm1
	vmovdqu	432(%rsp), %xmm15
	vpaddq	%xmm11, %xmm7, %xmm7
	vpaddq	%xmm12, %xmm8, %xmm8
	vpaddq	%xmm13, %xmm14, %xmm12
	vpmuludq	%xmm15, %xmm3, %xmm11
	vmovdqu	%xmm0, %xmm13
	vmovdqu	%xmm12, 496(%rsp)
	vpmuludq	%xmm15, %xmm2, %xmm12
	vpsrlq	$40, %xmm13, %xmm2
	vpor	16(%rsp), %xmm2, %xmm2
	vmovdqu	176(%rsp), %xmm13
	vpaddq	%xmm11, %xmm9, %xmm9
	vpaddq	%xmm12, %xmm6, %xmm6
	vpmuludq	%xmm13, %xmm4, %xmm11
	vmovdqu	%xmm10, %xmm4
	vmovdqu	%xmm9, 512(%rsp)
	vpmuludq	%xmm13, %xmm5, %xmm9
	vpsrlq	$52, %xmm4, %xmm4
	vpaddq	%xmm11, %xmm7, %xmm7
	vpaddq	%xmm8, %xmm9, %xmm8
	vpmuludq	160(%rsp), %xmm5, %xmm5
	vpsllq	$12, %xmm0, %xmm9
	vmovdqu	%xmm8, 480(%rsp)
	vpmuludq	448(%rsp), %xmm3, %xmm3
	vpor	%xmm9, %xmm4, %xmm4
	vmovdqu	(%rsp), %xmm8
	vpaddq	%xmm5, %xmm7, %xmm5
	vpaddq	%xmm3, %xmm6, %xmm3
	vmovdqu	%xmm5, 464(%rsp)
	vmovdqu	%xmm3, 528(%rsp)
	vpand	%xmm8, %xmm10, %xmm3
	vpand	%xmm8, %xmm4, %xmm4
	vpsrlq	$14, %xmm0, %xmm0
	vpand	%xmm8, %xmm0, %xmm0
	vmovdqu	304(%rsp), %xmm5
	vmovdqu	320(%rsp), %xmm9
	vmovdqu	144(%rsp), %xmm12
	vpmuludq	%xmm5, %xmm3, %xmm7
	vpmuludq	%xmm9, %xmm3, %xmm8
	vpmuludq	%xmm5, %xmm1, %xmm14
	vpmuludq	%xmm9, %xmm1, %xmm11
	vpmuludq	%xmm5, %xmm4, %xmm13
	vpmuludq	%xmm9, %xmm4, %xmm6
	vpaddq	464(%rsp), %xmm7, %xmm7
	vpmuludq	%xmm5, %xmm0, %xmm10
	vpaddq	480(%rsp), %xmm14, %xmm14
	vpaddq	%xmm8, %xmm14, %xmm8
	vpmuludq	%xmm9, %xmm0, %xmm14
	vpaddq	496(%rsp), %xmm13, %xmm9
	vpaddq	%xmm11, %xmm9, %xmm9
	vpmuludq	%xmm5, %xmm2, %xmm5
	vpaddq	512(%rsp), %xmm10, %xmm10
	vpaddq	%xmm6, %xmm10, %xmm10
	vpaddq	528(%rsp), %xmm5, %xmm5
	vpaddq	%xmm14, %xmm5, %xmm5
	vpmuludq	%xmm12, %xmm1, %xmm15
	vmovdqu	32(%rsi), %xmm14
	vpmuludq	%xmm12, %xmm4, %xmm13
	vmovdqu	336(%rsp), %xmm6
	vpmuludq	%xmm12, %xmm0, %xmm11
	vpmuludq	%xmm12, %xmm2, %xmm12
	vpaddq	%xmm15, %xmm7, %xmm7
	vmovdqu	48(%rsi), %xmm15
	vpaddq	%xmm13, %xmm8, %xmm8
	vpaddq	%xmm11, %xmm9, %xmm9
	vpaddq	%xmm12, %xmm10, %xmm10
	vpmuludq	%xmm6, %xmm3, %xmm11
	vpunpcklqdq	%xmm15, %xmm14, %xmm12
	vpmuludq	%xmm6, %xmm1, %xmm13
	vpunpckhqdq	%xmm15, %xmm14, %xmm14
	vpmuludq	%xmm6, %xmm4, %xmm6
	vpaddq	%xmm11, %xmm9, %xmm9
	vmovdqu	128(%rsp), %xmm11
	vpaddq	%xmm13, %xmm10, %xmm10
	vpaddq	%xmm6, %xmm5, %xmm5
	vpmuludq	%xmm11, %xmm4, %xmm4
	vpmuludq	%xmm11, %xmm0, %xmm6
	vmovdqu	%xmm12, %xmm13
	vpmuludq	%xmm11, %xmm2, %xmm11
	vpsrlq	$26, %xmm13, %xmm13
	vpand	(%rsp), %xmm13, %xmm13
	vmovdqu	352(%rsp), %xmm15
	vpaddq	%xmm4, %xmm7, %xmm4
	vpaddq	%xmm6, %xmm8, %xmm6
	vpaddq	%xmm9, %xmm11, %xmm7
	vpmuludq	%xmm15, %xmm3, %xmm8
	vmovdqu	%xmm14, %xmm9
	vpmuludq	%xmm15, %xmm1, %xmm11
	vpsrlq	$40, %xmm9, %xmm1
	vpor	16(%rsp), %xmm1, %xmm1
	vmovdqu	112(%rsp), %xmm9
	vpaddq	%xmm8, %xmm10, %xmm8
	vpaddq	%xmm11, %xmm5, %xmm5
	vpmuludq	%xmm9, %xmm0, %xmm0
	vmovdqu	%xmm12, %xmm10
	vpmuludq	%xmm9, %xmm2, %xmm11
	vpsrlq	$52, %xmm10, %xmm9
	vpaddq	%xmm0, %xmm4, %xmm10
	vpaddq	%xmm6, %xmm11, %xmm0
	vpmuludq	96(%rsp), %xmm2, %xmm6
	vpsllq	$12, %xmm14, %xmm4
	vpmuludq	368(%rsp), %xmm3, %xmm2
	vpor	%xmm4, %xmm9, %xmm3
	vmovdqu	(%rsp), %xmm4
	vpaddq	%xmm6, %xmm10, %xmm6
	vpaddq	%xmm2, %xmm5, %xmm2
	vpand	%xmm4, %xmm12, %xmm5
	vpaddq	%xmm6, %xmm5, %xmm5
	vpand	%xmm4, %xmm3, %xmm3
	vpaddq	%xmm7, %xmm3, %xmm3
	vpsrlq	$14, %xmm14, %xmm6
	vpand	%xmm4, %xmm6, %xmm6
	vpaddq	%xmm8, %xmm6, %xmm6
	addq	$64, %rsi
	vpaddq	%xmm0, %xmm13, %xmm7
	vpaddq	%xmm2, %xmm1, %xmm1
	vpsrlq	$26, %xmm5, %xmm8
	vpsrlq	$26, %xmm6, %xmm9
	vpand	%xmm4, %xmm5, %xmm0
	vpand	%xmm4, %xmm6, %xmm2
	vpaddq	%xmm8, %xmm7, %xmm5
	vpaddq	%xmm9, %xmm1, %xmm1
	vpsrlq	$26, %xmm5, %xmm6
	vpsrlq	$26, %xmm1, %xmm7
	vpsllq	$2, %xmm7, %xmm8
	vpaddq	%xmm8, %xmm7, %xmm7
	vpand	%xmm4, %xmm5, %xmm8
	vpand	%xmm4, %xmm1, %xmm5
	vpaddq	%xmm6, %xmm3, %xmm1
	vpaddq	%xmm7, %xmm0, %xmm0
	vpsrlq	$26, %xmm1, %xmm6
	vpsrlq	$26, %xmm0, %xmm7
	vpand	%xmm4, %xmm1, %xmm1
	vpand	%xmm4, %xmm0, %xmm3
	vpaddq	%xmm6, %xmm2, %xmm0
	vpaddq	%xmm7, %xmm8, %xmm2
	vpsrlq	$26, %xmm0, %xmm6
	vpand	%xmm4, %xmm0, %xmm4
	vpaddq	%xmm6, %xmm5, %xmm5
	addq	$-64, %r14
Ljade_onetimeauth_poly1305_amd64_avx_verify$6:
	cmpq	$64, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx_verify$7
	vmovdqu	224(%rsp), %xmm6
	vmovdqu	240(%rsp), %xmm11
	vmovdqu	80(%rsp), %xmm14
	vpmuludq	%xmm6, %xmm3, %xmm0
	vpmuludq	%xmm6, %xmm2, %xmm7
	vpmuludq	%xmm6, %xmm1, %xmm8
	vpmuludq	%xmm6, %xmm4, %xmm9
	vpmuludq	%xmm6, %xmm5, %xmm10
	vpmuludq	%xmm11, %xmm3, %xmm15
	vpmuludq	%xmm11, %xmm2, %xmm12
	vpmuludq	%xmm11, %xmm1, %xmm13
	vpmuludq	%xmm11, %xmm4, %xmm11
	vmovdqu	256(%rsp), %xmm6
	vpaddq	%xmm15, %xmm7, %xmm7
	vpaddq	%xmm12, %xmm8, %xmm8
	vpaddq	%xmm13, %xmm9, %xmm9
	vpaddq	%xmm11, %xmm10, %xmm10
	vpmuludq	%xmm14, %xmm2, %xmm11
	vpmuludq	%xmm14, %xmm1, %xmm12
	vpmuludq	%xmm14, %xmm4, %xmm13
	vpmuludq	%xmm14, %xmm5, %xmm14
	vmovdqu	64(%rsp), %xmm15
	vpaddq	%xmm11, %xmm0, %xmm0
	vpaddq	%xmm12, %xmm7, %xmm7
	vpaddq	%xmm13, %xmm8, %xmm8
	vpaddq	%xmm14, %xmm9, %xmm9
	vpmuludq	%xmm6, %xmm3, %xmm13
	vpmuludq	%xmm6, %xmm2, %xmm11
	vpmuludq	%xmm6, %xmm1, %xmm12
	vmovdqu	272(%rsp), %xmm6
	vpaddq	%xmm13, %xmm8, %xmm8
	vpaddq	%xmm11, %xmm9, %xmm9
	vpaddq	%xmm12, %xmm10, %xmm10
	vpmuludq	%xmm15, %xmm1, %xmm11
	vpmuludq	%xmm15, %xmm4, %xmm12
	vpmuludq	%xmm15, %xmm5, %xmm13
	vmovdqu	48(%rsp), %xmm1
	vpaddq	%xmm11, %xmm0, %xmm11
	vpaddq	%xmm12, %xmm7, %xmm7
	vpaddq	%xmm8, %xmm13, %xmm0
	vpmuludq	%xmm6, %xmm3, %xmm8
	vpmuludq	%xmm6, %xmm2, %xmm6
	vpaddq	%xmm8, %xmm9, %xmm2
	vpaddq	%xmm6, %xmm10, %xmm6
	vpmuludq	%xmm1, %xmm4, %xmm4
	vpmuludq	%xmm1, %xmm5, %xmm1
	vpaddq	%xmm4, %xmm11, %xmm4
	vpaddq	%xmm7, %xmm1, %xmm1
	vpmuludq	32(%rsp), %xmm5, %xmm5
	vpmuludq	288(%rsp), %xmm3, %xmm3
	vpaddq	%xmm5, %xmm4, %xmm4
	vmovdqu	%xmm2, %xmm5
	vpaddq	%xmm3, %xmm6, %xmm6
	vmovdqu	(%rsp), %xmm2
	vpsrlq	$26, %xmm4, %xmm7
	vpsrlq	$26, %xmm5, %xmm8
	vpand	%xmm2, %xmm4, %xmm3
	vpand	%xmm2, %xmm5, %xmm4
	vpaddq	%xmm7, %xmm1, %xmm1
	vpaddq	%xmm8, %xmm6, %xmm5
	vpsrlq	$26, %xmm1, %xmm6
	vpsrlq	$26, %xmm5, %xmm7
	vpsllq	$2, %xmm7, %xmm8
	vpaddq	%xmm8, %xmm7, %xmm7
	vpand	%xmm2, %xmm1, %xmm8
	vpand	%xmm2, %xmm5, %xmm1
	vpaddq	%xmm6, %xmm0, %xmm0
	vpaddq	%xmm7, %xmm3, %xmm3
	vpsrlq	$26, %xmm0, %xmm5
	vpsrlq	$26, %xmm3, %xmm6
	vpand	%xmm2, %xmm0, %xmm0
	vpand	%xmm2, %xmm3, %xmm3
	vpaddq	%xmm5, %xmm4, %xmm4
	vpaddq	%xmm6, %xmm8, %xmm5
	vpsrlq	$26, %xmm4, %xmm6
	vpand	%xmm2, %xmm4, %xmm2
	vpaddq	%xmm6, %xmm1, %xmm1
	vpsllq	$26, %xmm5, %xmm4
	vpaddq	%xmm3, %xmm4, %xmm3
	vpsllq	$26, %xmm2, %xmm2
	vpaddq	%xmm0, %xmm2, %xmm0
	vpsrldq	$8, %xmm1, %xmm2
	vpaddq	%xmm1, %xmm2, %xmm1
	vpunpcklqdq	%xmm0, %xmm3, %xmm2
	vpunpckhqdq	%xmm0, %xmm3, %xmm0
	vpaddq	%xmm0, %xmm2, %xmm0
	vpextrq	$0, %xmm0, %rax
	vpextrq	$1, %xmm0, %r8
	vpextrq	$0, %xmm1, %rcx
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
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx_verify$4
Ljade_onetimeauth_poly1305_amd64_avx_verify$5:
	addq	(%rsi), %r9
	adcq	8(%rsi), %r8
	adcq	$1, %rbx
	movq	%r12, %rcx
	imulq	%rbx, %rcx
	imulq	%rbp, %rbx
	movq	%rbp, %rax
	mulq	%r9
	movq	%rax, %r11
	movq	%rdx, %r10
	movq	%rbp, %rax
	mulq	%r8
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	%r12, %rax
	mulq	%r8
	movq	%rdx, %r8
	addq	%rcx, %r8
	movq	%rax, %rcx
	movq	%r13, %rax
	mulq	%r9
	addq	%rcx, %r11
	adcq	%rax, %r10
	adcq	%rdx, %rbx
	movq	$-4, %r9
	movq	%rbx, %rax
	shrq	$2, %rax
	andq	%rbx, %r9
	addq	%rax, %r9
	andq	$3, %rbx
	addq	%r11, %r9
	adcq	%r10, %r8
	adcq	$0, %rbx
	addq	$16, %rsi
	addq	$-16, %r14
Ljade_onetimeauth_poly1305_amd64_avx_verify$4:
	cmpq	$16, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx_verify$5
	cmpq	$0, %r14
	jbe 	Ljade_onetimeauth_poly1305_amd64_avx_verify$3
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
	movq	%r12, %rsi
	imulq	%rbx, %rsi
	imulq	%rbp, %rbx
	movq	%rbp, %rax
	mulq	%r9
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%rbp, %rax
	mulq	%r8
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	%r12, %rax
	mulq	%r8
	movq	%rdx, %r8
	addq	%rsi, %r8
	movq	%rax, %rsi
	movq	%r13, %rax
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
Ljade_onetimeauth_poly1305_amd64_avx_verify$3:
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
Ljade_onetimeauth_poly1305_amd64_avx_verify$2:
	movq	%rax, %rdx
	xorq	(%rdi), %rdx
	xorq	8(%rdi), %rcx
	orq 	%rcx, %rdx
	xorq	%rax, %rax
	subq	$1, %rdx
	adcq	$0, %rax
	addq	$-1, %rax
	movq	544(%rsp), %rbx
	movq	552(%rsp), %rbp
	movq	560(%rsp), %r12
	movq	568(%rsp), %r13
	movq	576(%rsp), %r14
	movq	584(%rsp), %r15
	movq	592(%rsp), %rsp
	ret 
_jade_onetimeauth_poly1305_amd64_avx:
jade_onetimeauth_poly1305_amd64_avx:
	movq	%rsp, %rax
	leaq	-600(%rsp), %rsp
	andq	$-16, %rsp
	movq	%rax, 592(%rsp)
	movq	%rbx, 544(%rsp)
	movq	%rbp, 552(%rsp)
	movq	%r12, 560(%rsp)
	movq	%r13, 568(%rsp)
	movq	%r14, 576(%rsp)
	movq	%r15, 584(%rsp)
	movq	%rdx, %r14
	movq	%rcx, %r15
	cmpq	$1024, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx$1
	movq	$0, %rbx
	movq	$0, %r9
	movq	$0, %rbp
	movq	(%r15), %r13
	movq	8(%r15), %r12
	movq	$1152921487695413247, %rax
	andq	%rax, %r13
	movq	$1152921487695413244, %rax
	andq	%rax, %r12
	movq	%r12, %r8
	shrq	$2, %r8
	addq	%r12, %r8
	addq	$16, %r15
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx$9
Ljade_onetimeauth_poly1305_amd64_avx$10:
	addq	(%rsi), %rbx
	adcq	8(%rsi), %r9
	adcq	$1, %rbp
	movq	%r8, %r11
	imulq	%rbp, %r11
	imulq	%r13, %rbp
	movq	%r13, %rax
	mulq	%rbx
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%r13, %rax
	mulq	%r9
	addq	%rax, %r10
	adcq	%rdx, %rbp
	movq	%r8, %rax
	mulq	%r9
	movq	%rdx, %r9
	addq	%r11, %r9
	movq	%rax, %r11
	movq	%r12, %rax
	mulq	%rbx
	addq	%r11, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %rbp
	movq	$-4, %rbx
	movq	%rbp, %rax
	shrq	$2, %rax
	andq	%rbp, %rbx
	addq	%rax, %rbx
	andq	$3, %rbp
	addq	%rcx, %rbx
	adcq	%r10, %r9
	adcq	$0, %rbp
	addq	$16, %rsi
	addq	$-16, %r14
Ljade_onetimeauth_poly1305_amd64_avx$9:
	cmpq	$16, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx$10
	cmpq	$0, %r14
	jbe 	Ljade_onetimeauth_poly1305_amd64_avx$8
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
	adcq	$0, %rbp
	movq	%r8, %rsi
	imulq	%rbp, %rsi
	imulq	%r13, %rbp
	movq	%r13, %rax
	mulq	%rbx
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%r13, %rax
	mulq	%r9
	addq	%rax, %r10
	adcq	%rdx, %rbp
	movq	%r8, %rax
	mulq	%r9
	movq	%rdx, %r9
	addq	%rsi, %r9
	movq	%rax, %rsi
	movq	%r12, %rax
	mulq	%rbx
	addq	%rsi, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %rbp
	movq	$-4, %rbx
	movq	%rbp, %rax
	shrq	$2, %rax
	andq	%rbp, %rbx
	addq	%rax, %rbx
	andq	$3, %rbp
	addq	%rcx, %rbx
	adcq	%r10, %r9
	adcq	$0, %rbp
Ljade_onetimeauth_poly1305_amd64_avx$8:
	movq	%rbx, %rax
	movq	%r9, %rcx
	addq	$5, %rax
	adcq	$0, %rcx
	adcq	$0, %rbp
	shrq	$2, %rbp
	negq	%rbp
	xorq	%rbx, %rax
	xorq	%r9, %rcx
	andq	%rbp, %rax
	andq	%rbp, %rcx
	xorq	%rbx, %rax
	xorq	%r9, %rcx
	movq	(%r15), %rdx
	movq	8(%r15), %rsi
	addq	%rdx, %rax
	adcq	%rsi, %rcx
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx$2
Ljade_onetimeauth_poly1305_amd64_avx$1:
	movq	(%r15), %rbp
	movq	8(%r15), %r12
	movq	$1152921487695413247, %rax
	andq	%rax, %rbp
	movq	$1152921487695413244, %rax
	andq	%rax, %r12
	movq	%r12, %r13
	shrq	$2, %r13
	addq	%r12, %r13
	addq	$16, %r15
	movq	%rbp, %r8
	movq	%r12, %r11
	movq	$0, %rbx
	movq	%r8, %rax
	andq	$67108863, %rax
	movq	%rax, 232(%rsp)
	movq	%r8, %rax
	shrq	$26, %rax
	andq	$67108863, %rax
	movq	%rax, 248(%rsp)
	movq	%r8, %rax
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 264(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 280(%rsp)
	movq	%r11, %rax
	shrdq	$40, %rbx, %rax
	movq	%rax, 296(%rsp)
	movq	%r13, %r10
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
	movq	%r13, %rax
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
	movq	%rax, 224(%rsp)
	movq	%r8, %rax
	shrq	$26, %rax
	andq	$67108863, %rax
	movq	%rax, 240(%rsp)
	movq	%r8, %rax
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 256(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 272(%rsp)
	movq	%r11, %rax
	shrdq	$40, %rbx, %rax
	movq	%rax, 288(%rsp)
	vpbroadcastq	glob_data + 16(%rip), %xmm0
	vpmuludq	240(%rsp), %xmm0, %xmm1
	vmovdqu	%xmm1, 32(%rsp)
	vpmuludq	256(%rsp), %xmm0, %xmm1
	vmovdqu	%xmm1, 48(%rsp)
	vpmuludq	272(%rsp), %xmm0, %xmm1
	vmovdqu	%xmm1, 64(%rsp)
	vpmuludq	288(%rsp), %xmm0, %xmm0
	vmovdqu	%xmm0, 80(%rsp)
	vpbroadcastq	224(%rsp), %xmm0
	vmovdqu	%xmm0, 304(%rsp)
	vpbroadcastq	240(%rsp), %xmm0
	vmovdqu	%xmm0, 320(%rsp)
	vpbroadcastq	256(%rsp), %xmm0
	vmovdqu	%xmm0, 336(%rsp)
	vpbroadcastq	272(%rsp), %xmm0
	vmovdqu	%xmm0, 352(%rsp)
	vpbroadcastq	288(%rsp), %xmm0
	vmovdqu	%xmm0, 368(%rsp)
	vpbroadcastq	32(%rsp), %xmm0
	vmovdqu	%xmm0, 96(%rsp)
	vpbroadcastq	48(%rsp), %xmm0
	vmovdqu	%xmm0, 112(%rsp)
	vpbroadcastq	64(%rsp), %xmm0
	vmovdqu	%xmm0, 128(%rsp)
	vpbroadcastq	80(%rsp), %xmm0
	vmovdqu	%xmm0, 144(%rsp)
	movq	%r13, %r10
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
	movq	%r13, %rax
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
	movq	%r13, %r9
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
	movq	%r13, %rax
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
	movq	%rcx, 384(%rsp)
	movq	%rax, %rcx
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 400(%rsp)
	shrdq	$52, %r11, %rax
	movq	%rax, %rcx
	andq	$67108863, %rax
	movq	%rax, 416(%rsp)
	shrq	$26, %rcx
	andq	$67108863, %rcx
	movq	%rcx, 432(%rsp)
	shrdq	$40, %rbx, %r11
	movq	%r11, 448(%rsp)
	movq	384(%rsp), %rax
	movq	%rax, 392(%rsp)
	movq	400(%rsp), %rax
	movq	%rax, 408(%rsp)
	movq	416(%rsp), %rax
	movq	%rax, 424(%rsp)
	movq	432(%rsp), %rax
	movq	%rax, 440(%rsp)
	movq	448(%rsp), %rax
	movq	%rax, 456(%rsp)
	vpbroadcastq	glob_data + 16(%rip), %xmm0
	vpmuludq	400(%rsp), %xmm0, %xmm1
	vmovdqu	%xmm1, 160(%rsp)
	vpmuludq	416(%rsp), %xmm0, %xmm1
	vmovdqu	%xmm1, 176(%rsp)
	vpmuludq	432(%rsp), %xmm0, %xmm1
	vmovdqu	%xmm1, 192(%rsp)
	vpmuludq	448(%rsp), %xmm0, %xmm0
	vmovdqu	%xmm0, 208(%rsp)
	vpxor	%xmm3, %xmm3, %xmm3
	vpxor	%xmm2, %xmm2, %xmm2
	vpxor	%xmm1, %xmm1, %xmm1
	vpxor	%xmm4, %xmm4, %xmm4
	vpxor	%xmm5, %xmm5, %xmm5
	vpbroadcastq	glob_data + 8(%rip), %xmm0
	vmovdqu	%xmm0, (%rsp)
	vpbroadcastq	glob_data + 0(%rip), %xmm0
	vmovdqu	%xmm0, 16(%rsp)
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx$6
Ljade_onetimeauth_poly1305_amd64_avx$7:
	vmovdqu	384(%rsp), %xmm0
	vmovdqu	400(%rsp), %xmm12
	vmovdqu	208(%rsp), %xmm14
	vpmuludq	%xmm0, %xmm3, %xmm7
	vpmuludq	%xmm12, %xmm3, %xmm8
	vpmuludq	%xmm0, %xmm2, %xmm13
	vpmuludq	%xmm12, %xmm2, %xmm6
	vpmuludq	%xmm0, %xmm1, %xmm9
	vpmuludq	%xmm12, %xmm1, %xmm10
	vpmuludq	%xmm0, %xmm4, %xmm11
	vpaddq	%xmm8, %xmm13, %xmm8
	vpmuludq	%xmm12, %xmm4, %xmm12
	vpaddq	%xmm6, %xmm9, %xmm9
	vpmuludq	%xmm0, %xmm5, %xmm0
	vpaddq	%xmm10, %xmm11, %xmm10
	vpaddq	%xmm12, %xmm0, %xmm6
	vpmuludq	%xmm14, %xmm2, %xmm15
	vmovdqu	(%rsi), %xmm0
	vpmuludq	%xmm14, %xmm1, %xmm13
	vmovdqu	416(%rsp), %xmm12
	vpmuludq	%xmm14, %xmm4, %xmm11
	vpmuludq	%xmm14, %xmm5, %xmm14
	vpaddq	%xmm15, %xmm7, %xmm7
	vmovdqu	16(%rsi), %xmm15
	vpaddq	%xmm13, %xmm8, %xmm8
	vpaddq	%xmm11, %xmm9, %xmm13
	vpaddq	%xmm14, %xmm10, %xmm9
	vpmuludq	%xmm12, %xmm3, %xmm14
	vpunpcklqdq	%xmm15, %xmm0, %xmm10
	vpmuludq	%xmm12, %xmm2, %xmm11
	vpunpckhqdq	%xmm15, %xmm0, %xmm0
	vpmuludq	%xmm12, %xmm1, %xmm12
	vpaddq	%xmm14, %xmm13, %xmm13
	vmovdqu	192(%rsp), %xmm14
	vpaddq	%xmm11, %xmm9, %xmm9
	vpaddq	%xmm12, %xmm6, %xmm6
	vpmuludq	%xmm14, %xmm1, %xmm11
	vpmuludq	%xmm14, %xmm4, %xmm12
	vmovdqu	%xmm10, %xmm1
	vpmuludq	%xmm14, %xmm5, %xmm14
	vpsrlq	$26, %xmm1, %xmm1
	vpand	(%rsp), %xmm1, %xmm1
	vmovdqu	432(%rsp), %xmm15
	vpaddq	%xmm11, %xmm7, %xmm7
	vpaddq	%xmm12, %xmm8, %xmm8
	vpaddq	%xmm13, %xmm14, %xmm12
	vpmuludq	%xmm15, %xmm3, %xmm11
	vmovdqu	%xmm0, %xmm13
	vmovdqu	%xmm12, 496(%rsp)
	vpmuludq	%xmm15, %xmm2, %xmm12
	vpsrlq	$40, %xmm13, %xmm2
	vpor	16(%rsp), %xmm2, %xmm2
	vmovdqu	176(%rsp), %xmm13
	vpaddq	%xmm11, %xmm9, %xmm9
	vpaddq	%xmm12, %xmm6, %xmm6
	vpmuludq	%xmm13, %xmm4, %xmm11
	vmovdqu	%xmm10, %xmm4
	vmovdqu	%xmm9, 512(%rsp)
	vpmuludq	%xmm13, %xmm5, %xmm9
	vpsrlq	$52, %xmm4, %xmm4
	vpaddq	%xmm11, %xmm7, %xmm7
	vpaddq	%xmm8, %xmm9, %xmm8
	vpmuludq	160(%rsp), %xmm5, %xmm5
	vpsllq	$12, %xmm0, %xmm9
	vmovdqu	%xmm8, 480(%rsp)
	vpmuludq	448(%rsp), %xmm3, %xmm3
	vpor	%xmm9, %xmm4, %xmm4
	vmovdqu	(%rsp), %xmm8
	vpaddq	%xmm5, %xmm7, %xmm5
	vpaddq	%xmm3, %xmm6, %xmm3
	vmovdqu	%xmm5, 464(%rsp)
	vmovdqu	%xmm3, 528(%rsp)
	vpand	%xmm8, %xmm10, %xmm3
	vpand	%xmm8, %xmm4, %xmm4
	vpsrlq	$14, %xmm0, %xmm0
	vpand	%xmm8, %xmm0, %xmm0
	vmovdqu	304(%rsp), %xmm5
	vmovdqu	320(%rsp), %xmm9
	vmovdqu	144(%rsp), %xmm12
	vpmuludq	%xmm5, %xmm3, %xmm7
	vpmuludq	%xmm9, %xmm3, %xmm8
	vpmuludq	%xmm5, %xmm1, %xmm14
	vpmuludq	%xmm9, %xmm1, %xmm11
	vpmuludq	%xmm5, %xmm4, %xmm13
	vpmuludq	%xmm9, %xmm4, %xmm6
	vpaddq	464(%rsp), %xmm7, %xmm7
	vpmuludq	%xmm5, %xmm0, %xmm10
	vpaddq	480(%rsp), %xmm14, %xmm14
	vpaddq	%xmm8, %xmm14, %xmm8
	vpmuludq	%xmm9, %xmm0, %xmm14
	vpaddq	496(%rsp), %xmm13, %xmm9
	vpaddq	%xmm11, %xmm9, %xmm9
	vpmuludq	%xmm5, %xmm2, %xmm5
	vpaddq	512(%rsp), %xmm10, %xmm10
	vpaddq	%xmm6, %xmm10, %xmm10
	vpaddq	528(%rsp), %xmm5, %xmm5
	vpaddq	%xmm14, %xmm5, %xmm5
	vpmuludq	%xmm12, %xmm1, %xmm15
	vmovdqu	32(%rsi), %xmm14
	vpmuludq	%xmm12, %xmm4, %xmm13
	vmovdqu	336(%rsp), %xmm6
	vpmuludq	%xmm12, %xmm0, %xmm11
	vpmuludq	%xmm12, %xmm2, %xmm12
	vpaddq	%xmm15, %xmm7, %xmm7
	vmovdqu	48(%rsi), %xmm15
	vpaddq	%xmm13, %xmm8, %xmm8
	vpaddq	%xmm11, %xmm9, %xmm9
	vpaddq	%xmm12, %xmm10, %xmm10
	vpmuludq	%xmm6, %xmm3, %xmm11
	vpunpcklqdq	%xmm15, %xmm14, %xmm12
	vpmuludq	%xmm6, %xmm1, %xmm13
	vpunpckhqdq	%xmm15, %xmm14, %xmm14
	vpmuludq	%xmm6, %xmm4, %xmm6
	vpaddq	%xmm11, %xmm9, %xmm9
	vmovdqu	128(%rsp), %xmm11
	vpaddq	%xmm13, %xmm10, %xmm10
	vpaddq	%xmm6, %xmm5, %xmm5
	vpmuludq	%xmm11, %xmm4, %xmm4
	vpmuludq	%xmm11, %xmm0, %xmm6
	vmovdqu	%xmm12, %xmm13
	vpmuludq	%xmm11, %xmm2, %xmm11
	vpsrlq	$26, %xmm13, %xmm13
	vpand	(%rsp), %xmm13, %xmm13
	vmovdqu	352(%rsp), %xmm15
	vpaddq	%xmm4, %xmm7, %xmm4
	vpaddq	%xmm6, %xmm8, %xmm6
	vpaddq	%xmm9, %xmm11, %xmm7
	vpmuludq	%xmm15, %xmm3, %xmm8
	vmovdqu	%xmm14, %xmm9
	vpmuludq	%xmm15, %xmm1, %xmm11
	vpsrlq	$40, %xmm9, %xmm1
	vpor	16(%rsp), %xmm1, %xmm1
	vmovdqu	112(%rsp), %xmm9
	vpaddq	%xmm8, %xmm10, %xmm8
	vpaddq	%xmm11, %xmm5, %xmm5
	vpmuludq	%xmm9, %xmm0, %xmm0
	vmovdqu	%xmm12, %xmm10
	vpmuludq	%xmm9, %xmm2, %xmm11
	vpsrlq	$52, %xmm10, %xmm9
	vpaddq	%xmm0, %xmm4, %xmm10
	vpaddq	%xmm6, %xmm11, %xmm0
	vpmuludq	96(%rsp), %xmm2, %xmm6
	vpsllq	$12, %xmm14, %xmm4
	vpmuludq	368(%rsp), %xmm3, %xmm2
	vpor	%xmm4, %xmm9, %xmm3
	vmovdqu	(%rsp), %xmm4
	vpaddq	%xmm6, %xmm10, %xmm6
	vpaddq	%xmm2, %xmm5, %xmm2
	vpand	%xmm4, %xmm12, %xmm5
	vpaddq	%xmm6, %xmm5, %xmm5
	vpand	%xmm4, %xmm3, %xmm3
	vpaddq	%xmm7, %xmm3, %xmm3
	vpsrlq	$14, %xmm14, %xmm6
	vpand	%xmm4, %xmm6, %xmm6
	vpaddq	%xmm8, %xmm6, %xmm6
	addq	$64, %rsi
	vpaddq	%xmm0, %xmm13, %xmm7
	vpaddq	%xmm2, %xmm1, %xmm1
	vpsrlq	$26, %xmm5, %xmm8
	vpsrlq	$26, %xmm6, %xmm9
	vpand	%xmm4, %xmm5, %xmm0
	vpand	%xmm4, %xmm6, %xmm2
	vpaddq	%xmm8, %xmm7, %xmm5
	vpaddq	%xmm9, %xmm1, %xmm1
	vpsrlq	$26, %xmm5, %xmm6
	vpsrlq	$26, %xmm1, %xmm7
	vpsllq	$2, %xmm7, %xmm8
	vpaddq	%xmm8, %xmm7, %xmm7
	vpand	%xmm4, %xmm5, %xmm8
	vpand	%xmm4, %xmm1, %xmm5
	vpaddq	%xmm6, %xmm3, %xmm1
	vpaddq	%xmm7, %xmm0, %xmm0
	vpsrlq	$26, %xmm1, %xmm6
	vpsrlq	$26, %xmm0, %xmm7
	vpand	%xmm4, %xmm1, %xmm1
	vpand	%xmm4, %xmm0, %xmm3
	vpaddq	%xmm6, %xmm2, %xmm0
	vpaddq	%xmm7, %xmm8, %xmm2
	vpsrlq	$26, %xmm0, %xmm6
	vpand	%xmm4, %xmm0, %xmm4
	vpaddq	%xmm6, %xmm5, %xmm5
	addq	$-64, %r14
Ljade_onetimeauth_poly1305_amd64_avx$6:
	cmpq	$64, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx$7
	vmovdqu	224(%rsp), %xmm6
	vmovdqu	240(%rsp), %xmm11
	vmovdqu	80(%rsp), %xmm14
	vpmuludq	%xmm6, %xmm3, %xmm0
	vpmuludq	%xmm6, %xmm2, %xmm7
	vpmuludq	%xmm6, %xmm1, %xmm8
	vpmuludq	%xmm6, %xmm4, %xmm9
	vpmuludq	%xmm6, %xmm5, %xmm10
	vpmuludq	%xmm11, %xmm3, %xmm15
	vpmuludq	%xmm11, %xmm2, %xmm12
	vpmuludq	%xmm11, %xmm1, %xmm13
	vpmuludq	%xmm11, %xmm4, %xmm11
	vmovdqu	256(%rsp), %xmm6
	vpaddq	%xmm15, %xmm7, %xmm7
	vpaddq	%xmm12, %xmm8, %xmm8
	vpaddq	%xmm13, %xmm9, %xmm9
	vpaddq	%xmm11, %xmm10, %xmm10
	vpmuludq	%xmm14, %xmm2, %xmm11
	vpmuludq	%xmm14, %xmm1, %xmm12
	vpmuludq	%xmm14, %xmm4, %xmm13
	vpmuludq	%xmm14, %xmm5, %xmm14
	vmovdqu	64(%rsp), %xmm15
	vpaddq	%xmm11, %xmm0, %xmm0
	vpaddq	%xmm12, %xmm7, %xmm7
	vpaddq	%xmm13, %xmm8, %xmm8
	vpaddq	%xmm14, %xmm9, %xmm9
	vpmuludq	%xmm6, %xmm3, %xmm13
	vpmuludq	%xmm6, %xmm2, %xmm11
	vpmuludq	%xmm6, %xmm1, %xmm12
	vmovdqu	272(%rsp), %xmm6
	vpaddq	%xmm13, %xmm8, %xmm8
	vpaddq	%xmm11, %xmm9, %xmm9
	vpaddq	%xmm12, %xmm10, %xmm10
	vpmuludq	%xmm15, %xmm1, %xmm11
	vpmuludq	%xmm15, %xmm4, %xmm12
	vpmuludq	%xmm15, %xmm5, %xmm13
	vmovdqu	48(%rsp), %xmm1
	vpaddq	%xmm11, %xmm0, %xmm11
	vpaddq	%xmm12, %xmm7, %xmm7
	vpaddq	%xmm8, %xmm13, %xmm0
	vpmuludq	%xmm6, %xmm3, %xmm8
	vpmuludq	%xmm6, %xmm2, %xmm6
	vpaddq	%xmm8, %xmm9, %xmm2
	vpaddq	%xmm6, %xmm10, %xmm6
	vpmuludq	%xmm1, %xmm4, %xmm4
	vpmuludq	%xmm1, %xmm5, %xmm1
	vpaddq	%xmm4, %xmm11, %xmm4
	vpaddq	%xmm7, %xmm1, %xmm1
	vpmuludq	32(%rsp), %xmm5, %xmm5
	vpmuludq	288(%rsp), %xmm3, %xmm3
	vpaddq	%xmm5, %xmm4, %xmm4
	vmovdqu	%xmm2, %xmm5
	vpaddq	%xmm3, %xmm6, %xmm6
	vmovdqu	(%rsp), %xmm2
	vpsrlq	$26, %xmm4, %xmm7
	vpsrlq	$26, %xmm5, %xmm8
	vpand	%xmm2, %xmm4, %xmm3
	vpand	%xmm2, %xmm5, %xmm4
	vpaddq	%xmm7, %xmm1, %xmm1
	vpaddq	%xmm8, %xmm6, %xmm5
	vpsrlq	$26, %xmm1, %xmm6
	vpsrlq	$26, %xmm5, %xmm7
	vpsllq	$2, %xmm7, %xmm8
	vpaddq	%xmm8, %xmm7, %xmm7
	vpand	%xmm2, %xmm1, %xmm8
	vpand	%xmm2, %xmm5, %xmm1
	vpaddq	%xmm6, %xmm0, %xmm0
	vpaddq	%xmm7, %xmm3, %xmm3
	vpsrlq	$26, %xmm0, %xmm5
	vpsrlq	$26, %xmm3, %xmm6
	vpand	%xmm2, %xmm0, %xmm0
	vpand	%xmm2, %xmm3, %xmm3
	vpaddq	%xmm5, %xmm4, %xmm4
	vpaddq	%xmm6, %xmm8, %xmm5
	vpsrlq	$26, %xmm4, %xmm6
	vpand	%xmm2, %xmm4, %xmm2
	vpaddq	%xmm6, %xmm1, %xmm1
	vpsllq	$26, %xmm5, %xmm4
	vpaddq	%xmm3, %xmm4, %xmm3
	vpsllq	$26, %xmm2, %xmm2
	vpaddq	%xmm0, %xmm2, %xmm0
	vpsrldq	$8, %xmm1, %xmm2
	vpaddq	%xmm1, %xmm2, %xmm1
	vpunpcklqdq	%xmm0, %xmm3, %xmm2
	vpunpckhqdq	%xmm0, %xmm3, %xmm0
	vpaddq	%xmm0, %xmm2, %xmm0
	vpextrq	$0, %xmm0, %rax
	vpextrq	$1, %xmm0, %rbx
	vpextrq	$0, %xmm1, %rcx
	movq	%rbx, %r11
	shlq	$52, %r11
	shrq	$12, %rbx
	movq	%rcx, %r8
	shrq	$24, %r8
	shlq	$40, %rcx
	addq	%rax, %r11
	adcq	%rcx, %rbx
	adcq	$0, %r8
	movq	%r8, %rax
	movq	%r8, %rcx
	andq	$3, %r8
	shrq	$2, %rax
	andq	$-4, %rcx
	addq	%rcx, %rax
	addq	%rax, %r11
	adcq	$0, %rbx
	adcq	$0, %r8
	jmp 	Ljade_onetimeauth_poly1305_amd64_avx$4
Ljade_onetimeauth_poly1305_amd64_avx$5:
	addq	(%rsi), %r11
	adcq	8(%rsi), %rbx
	adcq	$1, %r8
	movq	%r13, %r9
	imulq	%r8, %r9
	imulq	%rbp, %r8
	movq	%rbp, %rax
	mulq	%r11
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%rbp, %rax
	mulq	%rbx
	addq	%rax, %r10
	adcq	%rdx, %r8
	movq	%r13, %rax
	mulq	%rbx
	movq	%rdx, %rbx
	addq	%r9, %rbx
	movq	%rax, %r9
	movq	%r12, %rax
	mulq	%r11
	addq	%r9, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %r8
	movq	$-4, %r11
	movq	%r8, %rax
	shrq	$2, %rax
	andq	%r8, %r11
	addq	%rax, %r11
	andq	$3, %r8
	addq	%rcx, %r11
	adcq	%r10, %rbx
	adcq	$0, %r8
	addq	$16, %rsi
	addq	$-16, %r14
Ljade_onetimeauth_poly1305_amd64_avx$4:
	cmpq	$16, %r14
	jnb 	Ljade_onetimeauth_poly1305_amd64_avx$5
	cmpq	$0, %r14
	jbe 	Ljade_onetimeauth_poly1305_amd64_avx$3
	xorq	%rcx, %rcx
	movq	%r14, %rax
	andq	$7, %rax
	shlq	$3, %rax
	shrq	$3, %r14
	movq	%r14, %rdx
	xorq	$1, %rdx
	movq	%r14, %r9
	addq	$-1, %r9
	movq	%rax, %r10
	andq	%r9, %r10
	xorq	%r10, %rcx
	xorq	%r10, %rax
	shlq	%cl, %rdx
	movq	%rax, %rcx
	shlq	%cl, %r14
	movq	%rdx, %rax
	movq	%r14, %rcx
	subq	$1, %rax
	sbbq	$0, %rcx
	movq	(%rsi), %r9
	andq	%rax, %r9
	orq 	%rdx, %r9
	movq	8(%rsi), %rax
	andq	%rcx, %rax
	orq 	%r14, %rax
	addq	%r9, %r11
	adcq	%rax, %rbx
	adcq	$0, %r8
	movq	%r13, %rsi
	imulq	%r8, %rsi
	imulq	%rbp, %r8
	movq	%rbp, %rax
	mulq	%r11
	movq	%rax, %rcx
	movq	%rdx, %r9
	movq	%rbp, %rax
	mulq	%rbx
	addq	%rax, %r9
	adcq	%rdx, %r8
	movq	%r13, %rax
	mulq	%rbx
	movq	%rdx, %rbx
	addq	%rsi, %rbx
	movq	%rax, %rsi
	movq	%r12, %rax
	mulq	%r11
	addq	%rsi, %rcx
	adcq	%rax, %r9
	adcq	%rdx, %r8
	movq	$-4, %r11
	movq	%r8, %rax
	shrq	$2, %rax
	andq	%r8, %r11
	addq	%rax, %r11
	andq	$3, %r8
	addq	%rcx, %r11
	adcq	%r9, %rbx
	adcq	$0, %r8
Ljade_onetimeauth_poly1305_amd64_avx$3:
	movq	%r11, %rax
	movq	%rbx, %rcx
	addq	$5, %rax
	adcq	$0, %rcx
	adcq	$0, %r8
	shrq	$2, %r8
	negq	%r8
	xorq	%r11, %rax
	xorq	%rbx, %rcx
	andq	%r8, %rax
	andq	%r8, %rcx
	xorq	%r11, %rax
	xorq	%rbx, %rcx
	movq	(%r15), %rdx
	movq	8(%r15), %rsi
	addq	%rdx, %rax
	adcq	%rsi, %rcx
Ljade_onetimeauth_poly1305_amd64_avx$2:
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	xorq	%rax, %rax
	movq	544(%rsp), %rbx
	movq	552(%rsp), %rbp
	movq	560(%rsp), %r12
	movq	568(%rsp), %r13
	movq	576(%rsp), %r14
	movq	584(%rsp), %r15
	movq	592(%rsp), %rsp
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
