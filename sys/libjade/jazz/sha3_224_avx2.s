	.att_syntax
	.text
	.p2align	5
	.globl	_jade_hash_sha3_224_amd64_avx2
	.globl	jade_hash_sha3_224_amd64_avx2
_jade_hash_sha3_224_amd64_avx2:
jade_hash_sha3_224_amd64_avx2:
	movq	%rsp, %rax
	leaq	-32(%rsp), %rsp
	andq	$-32, %rsp
	movq	%rax, 24(%rsp)
	movq	%r12, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%rbx, 16(%rsp)
	movq	$28, %r9
	movb	$6, %al
	movq	$144, %rcx
	leaq	-248(%rsp), %rsp
	call	L_keccak1600_avx2$1
Ljade_hash_sha3_224_amd64_avx2$1:
	leaq	248(%rsp), %rsp
	xorq	%rax, %rax
	movq	(%rsp), %r12
	movq	8(%rsp), %rbp
	movq	16(%rsp), %rbx
	movq	24(%rsp), %rsp
	ret 
L_keccak1600_avx2$1:
	vpxor	%ymm6, %ymm6, %ymm6
	vpxor	%ymm3, %ymm3, %ymm3
	vpxor	%ymm4, %ymm4, %ymm4
	vpxor	%ymm0, %ymm0, %ymm0
	vpxor	%ymm5, %ymm5, %ymm5
	vpxor	%ymm1, %ymm1, %ymm1
	vpxor	%ymm2, %ymm2, %ymm2
	leaq	glob_data + 1152(%rip), %r8
	vpxor	%ymm7, %ymm7, %ymm7
	vmovdqu	%ymm7, 32(%rsp)
	vmovdqu	%ymm7, 64(%rsp)
	vmovdqu	%ymm7, 96(%rsp)
	vmovdqu	%ymm7, 128(%rsp)
	vmovdqu	%ymm7, 160(%rsp)
	vmovdqu	%ymm7, 192(%rsp)
	vmovdqu	%ymm7, 224(%rsp)
	jmp 	L_keccak1600_avx2$16
L_keccak1600_avx2$17:
	movq	%rcx, %r10
	shrq	$3, %r10
	movq	$0, %r11
	jmp 	L_keccak1600_avx2$19
L_keccak1600_avx2$20:
	movq	(%rsi,%r11,8), %rbx
	movq	(%r8,%r11,8), %rbp
	movq	%rbx, 32(%rsp,%rbp,8)
	incq	%r11
L_keccak1600_avx2$19:
	cmpq	%r10, %r11
	jb  	L_keccak1600_avx2$20
	movq	32(%rsp), %r10
	movq	%r10, 40(%rsp)
	movq	%r10, 48(%rsp)
	movq	%r10, 56(%rsp)
	vpxor	32(%rsp), %ymm6, %ymm6
	vpxor	64(%rsp), %ymm3, %ymm3
	vpxor	96(%rsp), %ymm4, %ymm4
	vpxor	128(%rsp), %ymm0, %ymm0
	vpxor	160(%rsp), %ymm5, %ymm5
	vpxor	192(%rsp), %ymm1, %ymm1
	vpxor	224(%rsp), %ymm2, %ymm2
	addq	%rcx, %rsi
	subq	%rcx, %rdx
	leaq	glob_data + 384(%rip), %r10
	movq	$0, %r11
	leaq	glob_data + 192(%rip), %rbx
	leaq	glob_data + 0(%rip), %rbp
	movq	$24, %r12
L_keccak1600_avx2$18:
	vpshufd	$78, %ymm4, %ymm8
	vpxor	%ymm0, %ymm1, %ymm7
	vpxor	%ymm2, %ymm5, %ymm9
	vpxor	%ymm3, %ymm7, %ymm7
	vpxor	%ymm9, %ymm7, %ymm10
	vpermq	$-109, %ymm10, %ymm7
	vpxor	%ymm4, %ymm8, %ymm8
	vpermq	$78, %ymm8, %ymm9
	vpsrlq	$63, %ymm10, %ymm11
	vpaddq	%ymm10, %ymm10, %ymm10
	vpor	%ymm10, %ymm11, %ymm11
	vpermq	$57, %ymm11, %ymm10
	vpxor	%ymm7, %ymm11, %ymm11
	vpermq	$0, %ymm11, %ymm11
	vpxor	%ymm6, %ymm8, %ymm8
	vpxor	%ymm9, %ymm8, %ymm8
	vpsrlq	$63, %ymm8, %ymm9
	vpaddq	%ymm8, %ymm8, %ymm12
	vpor	%ymm9, %ymm12, %ymm9
	vpxor	%ymm11, %ymm4, %ymm4
	vpxor	%ymm11, %ymm6, %ymm6
	vpblendd	$-64, %ymm9, %ymm10, %ymm9
	vpblendd	$3, %ymm8, %ymm7, %ymm7
	vpxor	%ymm7, %ymm9, %ymm9
	vpsllvq	(%rbx), %ymm4, %ymm7
	vpsrlvq	(%rbp), %ymm4, %ymm4
	vpor	%ymm7, %ymm4, %ymm4
	vpxor	%ymm9, %ymm0, %ymm0
	vpsllvq	64(%rbx), %ymm0, %ymm7
	vpsrlvq	64(%rbp), %ymm0, %ymm0
	vpor	%ymm7, %ymm0, %ymm0
	vpxor	%ymm9, %ymm5, %ymm5
	vpsllvq	96(%rbx), %ymm5, %ymm7
	vpsrlvq	96(%rbp), %ymm5, %ymm5
	vpor	%ymm7, %ymm5, %ymm10
	vpxor	%ymm9, %ymm1, %ymm1
	vpsllvq	128(%rbx), %ymm1, %ymm5
	vpsrlvq	128(%rbp), %ymm1, %ymm1
	vpor	%ymm5, %ymm1, %ymm1
	vpxor	%ymm9, %ymm2, %ymm2
	vpermq	$-115, %ymm4, %ymm5
	vpermq	$-115, %ymm0, %ymm7
	vpsllvq	160(%rbx), %ymm2, %ymm0
	vpsrlvq	160(%rbp), %ymm2, %ymm2
	vpor	%ymm0, %ymm2, %ymm8
	vpxor	%ymm9, %ymm3, %ymm0
	vpermq	$27, %ymm10, %ymm3
	vpermq	$114, %ymm1, %ymm9
	vpsllvq	32(%rbx), %ymm0, %ymm1
	vpsrlvq	32(%rbp), %ymm0, %ymm0
	vpor	%ymm1, %ymm0, %ymm10
	vpsrldq	$8, %ymm8, %ymm0
	vpandn	%ymm0, %ymm8, %ymm0
	vpblendd	$12, %ymm9, %ymm10, %ymm1
	vpblendd	$12, %ymm10, %ymm7, %ymm2
	vpblendd	$12, %ymm7, %ymm5, %ymm4
	vpblendd	$12, %ymm5, %ymm10, %ymm11
	vpblendd	$48, %ymm7, %ymm1, %ymm1
	vpblendd	$48, %ymm3, %ymm2, %ymm2
	vpblendd	$48, %ymm10, %ymm4, %ymm4
	vpblendd	$48, %ymm9, %ymm11, %ymm11
	vpblendd	$-64, %ymm3, %ymm1, %ymm1
	vpblendd	$-64, %ymm9, %ymm2, %ymm2
	vpblendd	$-64, %ymm9, %ymm4, %ymm4
	vpblendd	$-64, %ymm7, %ymm11, %ymm11
	vpandn	%ymm2, %ymm1, %ymm1
	vpandn	%ymm11, %ymm4, %ymm2
	vpblendd	$12, %ymm10, %ymm3, %ymm4
	vpblendd	$12, %ymm3, %ymm5, %ymm11
	vpxor	%ymm5, %ymm1, %ymm1
	vpblendd	$48, %ymm5, %ymm4, %ymm4
	vpblendd	$48, %ymm7, %ymm11, %ymm11
	vpxor	%ymm3, %ymm2, %ymm2
	vpblendd	$-64, %ymm7, %ymm4, %ymm4
	vpblendd	$-64, %ymm10, %ymm11, %ymm11
	vpandn	%ymm11, %ymm4, %ymm4
	vpxor	%ymm9, %ymm4, %ymm12
	vpermq	$30, %ymm8, %ymm4
	vpblendd	$48, %ymm6, %ymm4, %ymm4
	vpermq	$57, %ymm8, %ymm11
	vpblendd	$-64, %ymm6, %ymm11, %ymm11
	vpandn	%ymm4, %ymm11, %ymm11
	vpblendd	$12, %ymm3, %ymm7, %ymm4
	vpblendd	$12, %ymm7, %ymm9, %ymm13
	vpblendd	$48, %ymm9, %ymm4, %ymm4
	vpblendd	$48, %ymm5, %ymm13, %ymm13
	vpblendd	$-64, %ymm5, %ymm4, %ymm4
	vpblendd	$-64, %ymm3, %ymm13, %ymm13
	vpandn	%ymm13, %ymm4, %ymm4
	vpxor	%ymm10, %ymm4, %ymm4
	vpermq	$0, %ymm0, %ymm13
	vpermq	$27, %ymm1, %ymm0
	vpermq	$-115, %ymm2, %ymm1
	vpermq	$114, %ymm12, %ymm2
	vpblendd	$12, %ymm5, %ymm9, %ymm12
	vpblendd	$12, %ymm9, %ymm3, %ymm9
	vpblendd	$48, %ymm3, %ymm12, %ymm3
	vpblendd	$48, %ymm10, %ymm9, %ymm9
	vpblendd	$-64, %ymm10, %ymm3, %ymm3
	vpblendd	$-64, %ymm5, %ymm9, %ymm5
	vpandn	%ymm5, %ymm3, %ymm5
	vpxor	%ymm13, %ymm6, %ymm6
	vpxor	%ymm8, %ymm11, %ymm3
	vpxor	%ymm7, %ymm5, %ymm5
	vpxor	(%r10,%r11), %ymm6, %ymm6
	addq	$32, %r11
	decq	%r12
	jne 	L_keccak1600_avx2$18
L_keccak1600_avx2$16:
	cmpq	%rcx, %rdx
	jnb 	L_keccak1600_avx2$17
	vpxor	%ymm7, %ymm7, %ymm7
	vmovdqu	%ymm7, 32(%rsp)
	vmovdqu	%ymm7, 64(%rsp)
	vmovdqu	%ymm7, 96(%rsp)
	vmovdqu	%ymm7, 128(%rsp)
	vmovdqu	%ymm7, 160(%rsp)
	vmovdqu	%ymm7, 192(%rsp)
	vmovdqu	%ymm7, 224(%rsp)
	movq	%rdx, %r10
	shrq	$3, %r10
	movq	$0, %r11
	jmp 	L_keccak1600_avx2$14
L_keccak1600_avx2$15:
	movq	(%rsi,%r11,8), %rbx
	movq	(%r8,%r11,8), %rbp
	movq	%rbx, 32(%rsp,%rbp,8)
	incq	%r11
L_keccak1600_avx2$14:
	cmpq	%r10, %r11
	jb  	L_keccak1600_avx2$15
	movq	(%r8,%r11,8), %r10
	shlq	$3, %r10
	shlq	$3, %r11
	jmp 	L_keccak1600_avx2$12
L_keccak1600_avx2$13:
	movb	(%rsi,%r11), %bl
	movb	%bl, 32(%rsp,%r10)
	incq	%r11
	incq	%r10
L_keccak1600_avx2$12:
	cmpq	%rdx, %r11
	jb  	L_keccak1600_avx2$13
	movb	%al, 32(%rsp,%r10)
	movq	%rcx, %rax
	addq	$-1, %rax
	shrq	$3, %rax
	movq	(%r8,%rax,8), %rax
	shlq	$3, %rax
	movq	%rcx, %rdx
	addq	$-1, %rdx
	andq	$7, %rdx
	addq	%rdx, %rax
	xorb	$-128, 32(%rsp,%rax)
	movq	32(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	%rax, 48(%rsp)
	movq	%rax, 56(%rsp)
	vpxor	32(%rsp), %ymm6, %ymm6
	vpxor	64(%rsp), %ymm3, %ymm3
	vpxor	96(%rsp), %ymm4, %ymm4
	vpxor	128(%rsp), %ymm0, %ymm0
	vpxor	160(%rsp), %ymm5, %ymm5
	vpxor	192(%rsp), %ymm1, %ymm1
	vpxor	224(%rsp), %ymm2, %ymm2
	leaq	glob_data + 1152(%rip), %rax
	jmp 	L_keccak1600_avx2$7
L_keccak1600_avx2$8:
	leaq	glob_data + 384(%rip), %rdx
	movq	$0, %rsi
	leaq	glob_data + 192(%rip), %r8
	leaq	glob_data + 0(%rip), %r10
	movq	$24, %r11
L_keccak1600_avx2$11:
	vpshufd	$78, %ymm4, %ymm8
	vpxor	%ymm0, %ymm1, %ymm7
	vpxor	%ymm2, %ymm5, %ymm9
	vpxor	%ymm3, %ymm7, %ymm7
	vpxor	%ymm9, %ymm7, %ymm10
	vpermq	$-109, %ymm10, %ymm7
	vpxor	%ymm4, %ymm8, %ymm8
	vpermq	$78, %ymm8, %ymm9
	vpsrlq	$63, %ymm10, %ymm11
	vpaddq	%ymm10, %ymm10, %ymm10
	vpor	%ymm10, %ymm11, %ymm11
	vpermq	$57, %ymm11, %ymm10
	vpxor	%ymm7, %ymm11, %ymm11
	vpermq	$0, %ymm11, %ymm11
	vpxor	%ymm6, %ymm8, %ymm8
	vpxor	%ymm9, %ymm8, %ymm8
	vpsrlq	$63, %ymm8, %ymm9
	vpaddq	%ymm8, %ymm8, %ymm12
	vpor	%ymm9, %ymm12, %ymm9
	vpxor	%ymm11, %ymm4, %ymm4
	vpxor	%ymm11, %ymm6, %ymm6
	vpblendd	$-64, %ymm9, %ymm10, %ymm9
	vpblendd	$3, %ymm8, %ymm7, %ymm7
	vpxor	%ymm7, %ymm9, %ymm9
	vpsllvq	(%r8), %ymm4, %ymm7
	vpsrlvq	(%r10), %ymm4, %ymm4
	vpor	%ymm7, %ymm4, %ymm4
	vpxor	%ymm9, %ymm0, %ymm0
	vpsllvq	64(%r8), %ymm0, %ymm7
	vpsrlvq	64(%r10), %ymm0, %ymm0
	vpor	%ymm7, %ymm0, %ymm0
	vpxor	%ymm9, %ymm5, %ymm5
	vpsllvq	96(%r8), %ymm5, %ymm7
	vpsrlvq	96(%r10), %ymm5, %ymm5
	vpor	%ymm7, %ymm5, %ymm10
	vpxor	%ymm9, %ymm1, %ymm1
	vpsllvq	128(%r8), %ymm1, %ymm5
	vpsrlvq	128(%r10), %ymm1, %ymm1
	vpor	%ymm5, %ymm1, %ymm1
	vpxor	%ymm9, %ymm2, %ymm2
	vpermq	$-115, %ymm4, %ymm5
	vpermq	$-115, %ymm0, %ymm7
	vpsllvq	160(%r8), %ymm2, %ymm0
	vpsrlvq	160(%r10), %ymm2, %ymm2
	vpor	%ymm0, %ymm2, %ymm8
	vpxor	%ymm9, %ymm3, %ymm0
	vpermq	$27, %ymm10, %ymm3
	vpermq	$114, %ymm1, %ymm9
	vpsllvq	32(%r8), %ymm0, %ymm1
	vpsrlvq	32(%r10), %ymm0, %ymm0
	vpor	%ymm1, %ymm0, %ymm10
	vpsrldq	$8, %ymm8, %ymm0
	vpandn	%ymm0, %ymm8, %ymm0
	vpblendd	$12, %ymm9, %ymm10, %ymm1
	vpblendd	$12, %ymm10, %ymm7, %ymm2
	vpblendd	$12, %ymm7, %ymm5, %ymm4
	vpblendd	$12, %ymm5, %ymm10, %ymm11
	vpblendd	$48, %ymm7, %ymm1, %ymm1
	vpblendd	$48, %ymm3, %ymm2, %ymm2
	vpblendd	$48, %ymm10, %ymm4, %ymm4
	vpblendd	$48, %ymm9, %ymm11, %ymm11
	vpblendd	$-64, %ymm3, %ymm1, %ymm1
	vpblendd	$-64, %ymm9, %ymm2, %ymm2
	vpblendd	$-64, %ymm9, %ymm4, %ymm4
	vpblendd	$-64, %ymm7, %ymm11, %ymm11
	vpandn	%ymm2, %ymm1, %ymm1
	vpandn	%ymm11, %ymm4, %ymm2
	vpblendd	$12, %ymm10, %ymm3, %ymm4
	vpblendd	$12, %ymm3, %ymm5, %ymm11
	vpxor	%ymm5, %ymm1, %ymm1
	vpblendd	$48, %ymm5, %ymm4, %ymm4
	vpblendd	$48, %ymm7, %ymm11, %ymm11
	vpxor	%ymm3, %ymm2, %ymm2
	vpblendd	$-64, %ymm7, %ymm4, %ymm4
	vpblendd	$-64, %ymm10, %ymm11, %ymm11
	vpandn	%ymm11, %ymm4, %ymm4
	vpxor	%ymm9, %ymm4, %ymm12
	vpermq	$30, %ymm8, %ymm4
	vpblendd	$48, %ymm6, %ymm4, %ymm4
	vpermq	$57, %ymm8, %ymm11
	vpblendd	$-64, %ymm6, %ymm11, %ymm11
	vpandn	%ymm4, %ymm11, %ymm11
	vpblendd	$12, %ymm3, %ymm7, %ymm4
	vpblendd	$12, %ymm7, %ymm9, %ymm13
	vpblendd	$48, %ymm9, %ymm4, %ymm4
	vpblendd	$48, %ymm5, %ymm13, %ymm13
	vpblendd	$-64, %ymm5, %ymm4, %ymm4
	vpblendd	$-64, %ymm3, %ymm13, %ymm13
	vpandn	%ymm13, %ymm4, %ymm4
	vpxor	%ymm10, %ymm4, %ymm4
	vpermq	$0, %ymm0, %ymm13
	vpermq	$27, %ymm1, %ymm0
	vpermq	$-115, %ymm2, %ymm1
	vpermq	$114, %ymm12, %ymm2
	vpblendd	$12, %ymm5, %ymm9, %ymm12
	vpblendd	$12, %ymm9, %ymm3, %ymm9
	vpblendd	$48, %ymm3, %ymm12, %ymm3
	vpblendd	$48, %ymm10, %ymm9, %ymm9
	vpblendd	$-64, %ymm10, %ymm3, %ymm3
	vpblendd	$-64, %ymm5, %ymm9, %ymm5
	vpandn	%ymm5, %ymm3, %ymm5
	vpxor	%ymm13, %ymm6, %ymm6
	vpxor	%ymm8, %ymm11, %ymm3
	vpxor	%ymm7, %ymm5, %ymm5
	vpxor	(%rdx,%rsi), %ymm6, %ymm6
	addq	$32, %rsi
	decq	%r11
	jne 	L_keccak1600_avx2$11
	vmovdqu	%ymm6, 32(%rsp)
	vmovdqu	%ymm3, 64(%rsp)
	vmovdqu	%ymm4, 96(%rsp)
	vmovdqu	%ymm0, 128(%rsp)
	vmovdqu	%ymm5, 160(%rsp)
	vmovdqu	%ymm1, 192(%rsp)
	vmovdqu	%ymm2, 224(%rsp)
	movq	%rcx, %rdx
	shrq	$3, %rdx
	movq	$0, %rsi
	jmp 	L_keccak1600_avx2$9
L_keccak1600_avx2$10:
	movq	(%rax,%rsi,8), %r8
	movq	32(%rsp,%r8,8), %r8
	movq	%r8, (%rdi,%rsi,8)
	incq	%rsi
L_keccak1600_avx2$9:
	cmpq	%rdx, %rsi
	jb  	L_keccak1600_avx2$10
	addq	%rcx, %rdi
	subq	%rcx, %r9
L_keccak1600_avx2$7:
	cmpq	%rcx, %r9
	jnbe	L_keccak1600_avx2$8
	leaq	glob_data + 384(%rip), %rcx
	movq	$0, %rdx
	leaq	glob_data + 192(%rip), %rsi
	leaq	glob_data + 0(%rip), %r8
	movq	$24, %r10
L_keccak1600_avx2$6:
	vpshufd	$78, %ymm4, %ymm8
	vpxor	%ymm0, %ymm1, %ymm7
	vpxor	%ymm2, %ymm5, %ymm9
	vpxor	%ymm3, %ymm7, %ymm7
	vpxor	%ymm9, %ymm7, %ymm10
	vpermq	$-109, %ymm10, %ymm7
	vpxor	%ymm4, %ymm8, %ymm8
	vpermq	$78, %ymm8, %ymm9
	vpsrlq	$63, %ymm10, %ymm11
	vpaddq	%ymm10, %ymm10, %ymm10
	vpor	%ymm10, %ymm11, %ymm11
	vpermq	$57, %ymm11, %ymm10
	vpxor	%ymm7, %ymm11, %ymm11
	vpermq	$0, %ymm11, %ymm11
	vpxor	%ymm6, %ymm8, %ymm8
	vpxor	%ymm9, %ymm8, %ymm8
	vpsrlq	$63, %ymm8, %ymm9
	vpaddq	%ymm8, %ymm8, %ymm12
	vpor	%ymm9, %ymm12, %ymm9
	vpxor	%ymm11, %ymm4, %ymm4
	vpxor	%ymm11, %ymm6, %ymm6
	vpblendd	$-64, %ymm9, %ymm10, %ymm9
	vpblendd	$3, %ymm8, %ymm7, %ymm7
	vpxor	%ymm7, %ymm9, %ymm9
	vpsllvq	(%rsi), %ymm4, %ymm7
	vpsrlvq	(%r8), %ymm4, %ymm4
	vpor	%ymm7, %ymm4, %ymm4
	vpxor	%ymm9, %ymm0, %ymm0
	vpsllvq	64(%rsi), %ymm0, %ymm7
	vpsrlvq	64(%r8), %ymm0, %ymm0
	vpor	%ymm7, %ymm0, %ymm0
	vpxor	%ymm9, %ymm5, %ymm5
	vpsllvq	96(%rsi), %ymm5, %ymm7
	vpsrlvq	96(%r8), %ymm5, %ymm5
	vpor	%ymm7, %ymm5, %ymm10
	vpxor	%ymm9, %ymm1, %ymm1
	vpsllvq	128(%rsi), %ymm1, %ymm5
	vpsrlvq	128(%r8), %ymm1, %ymm1
	vpor	%ymm5, %ymm1, %ymm1
	vpxor	%ymm9, %ymm2, %ymm2
	vpermq	$-115, %ymm4, %ymm5
	vpermq	$-115, %ymm0, %ymm7
	vpsllvq	160(%rsi), %ymm2, %ymm0
	vpsrlvq	160(%r8), %ymm2, %ymm2
	vpor	%ymm0, %ymm2, %ymm8
	vpxor	%ymm9, %ymm3, %ymm0
	vpermq	$27, %ymm10, %ymm3
	vpermq	$114, %ymm1, %ymm9
	vpsllvq	32(%rsi), %ymm0, %ymm1
	vpsrlvq	32(%r8), %ymm0, %ymm0
	vpor	%ymm1, %ymm0, %ymm10
	vpsrldq	$8, %ymm8, %ymm0
	vpandn	%ymm0, %ymm8, %ymm0
	vpblendd	$12, %ymm9, %ymm10, %ymm1
	vpblendd	$12, %ymm10, %ymm7, %ymm2
	vpblendd	$12, %ymm7, %ymm5, %ymm4
	vpblendd	$12, %ymm5, %ymm10, %ymm11
	vpblendd	$48, %ymm7, %ymm1, %ymm1
	vpblendd	$48, %ymm3, %ymm2, %ymm2
	vpblendd	$48, %ymm10, %ymm4, %ymm4
	vpblendd	$48, %ymm9, %ymm11, %ymm11
	vpblendd	$-64, %ymm3, %ymm1, %ymm1
	vpblendd	$-64, %ymm9, %ymm2, %ymm2
	vpblendd	$-64, %ymm9, %ymm4, %ymm4
	vpblendd	$-64, %ymm7, %ymm11, %ymm11
	vpandn	%ymm2, %ymm1, %ymm1
	vpandn	%ymm11, %ymm4, %ymm2
	vpblendd	$12, %ymm10, %ymm3, %ymm4
	vpblendd	$12, %ymm3, %ymm5, %ymm11
	vpxor	%ymm5, %ymm1, %ymm1
	vpblendd	$48, %ymm5, %ymm4, %ymm4
	vpblendd	$48, %ymm7, %ymm11, %ymm11
	vpxor	%ymm3, %ymm2, %ymm2
	vpblendd	$-64, %ymm7, %ymm4, %ymm4
	vpblendd	$-64, %ymm10, %ymm11, %ymm11
	vpandn	%ymm11, %ymm4, %ymm4
	vpxor	%ymm9, %ymm4, %ymm12
	vpermq	$30, %ymm8, %ymm4
	vpblendd	$48, %ymm6, %ymm4, %ymm4
	vpermq	$57, %ymm8, %ymm11
	vpblendd	$-64, %ymm6, %ymm11, %ymm11
	vpandn	%ymm4, %ymm11, %ymm11
	vpblendd	$12, %ymm3, %ymm7, %ymm4
	vpblendd	$12, %ymm7, %ymm9, %ymm13
	vpblendd	$48, %ymm9, %ymm4, %ymm4
	vpblendd	$48, %ymm5, %ymm13, %ymm13
	vpblendd	$-64, %ymm5, %ymm4, %ymm4
	vpblendd	$-64, %ymm3, %ymm13, %ymm13
	vpandn	%ymm13, %ymm4, %ymm4
	vpxor	%ymm10, %ymm4, %ymm4
	vpermq	$0, %ymm0, %ymm13
	vpermq	$27, %ymm1, %ymm0
	vpermq	$-115, %ymm2, %ymm1
	vpermq	$114, %ymm12, %ymm2
	vpblendd	$12, %ymm5, %ymm9, %ymm12
	vpblendd	$12, %ymm9, %ymm3, %ymm9
	vpblendd	$48, %ymm3, %ymm12, %ymm3
	vpblendd	$48, %ymm10, %ymm9, %ymm9
	vpblendd	$-64, %ymm10, %ymm3, %ymm3
	vpblendd	$-64, %ymm5, %ymm9, %ymm5
	vpandn	%ymm5, %ymm3, %ymm5
	vpxor	%ymm13, %ymm6, %ymm6
	vpxor	%ymm8, %ymm11, %ymm3
	vpxor	%ymm7, %ymm5, %ymm5
	vpxor	(%rcx,%rdx), %ymm6, %ymm6
	addq	$32, %rdx
	decq	%r10
	jne 	L_keccak1600_avx2$6
	vmovdqu	%ymm6, 32(%rsp)
	vmovdqu	%ymm3, 64(%rsp)
	vmovdqu	%ymm4, 96(%rsp)
	vmovdqu	%ymm0, 128(%rsp)
	vmovdqu	%ymm5, 160(%rsp)
	vmovdqu	%ymm1, 192(%rsp)
	vmovdqu	%ymm2, 224(%rsp)
	movq	%r9, %rcx
	shrq	$3, %rcx
	movq	$0, %rdx
	jmp 	L_keccak1600_avx2$4
L_keccak1600_avx2$5:
	movq	(%rax,%rdx,8), %rsi
	movq	32(%rsp,%rsi,8), %rsi
	movq	%rsi, (%rdi,%rdx,8)
	incq	%rdx
L_keccak1600_avx2$4:
	cmpq	%rcx, %rdx
	jb  	L_keccak1600_avx2$5
	movq	(%rax,%rdx,8), %rax
	shlq	$3, %rdx
	shlq	$3, %rax
	jmp 	L_keccak1600_avx2$2
L_keccak1600_avx2$3:
	movb	32(%rsp,%rax), %cl
	movb	%cl, (%rdi,%rdx)
	incq	%rdx
	incq	%rax
L_keccak1600_avx2$2:
	cmpq	%r9, %rdx
	jb  	L_keccak1600_avx2$3
	ret 
	.data
	.p2align	5
_glob_data:
glob_data:
      .byte 61
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 46
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 28
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 23
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 63
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
      .byte 36
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 37
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 19
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 58
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
      .byte 25
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 54
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 3
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 9
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 56
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 62
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 49
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 39
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 44
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 20
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 21
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 43
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 50
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 3
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 18
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 36
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 41
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
      .byte 62
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 28
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 27
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 45
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 6
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 56
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 39
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 10
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 61
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 55
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
      .byte 2
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 15
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 25
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 20
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 44
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 43
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 21
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 14
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
      .byte 1
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
      .byte 1
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -126
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -126
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -126
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -126
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -118
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -118
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -118
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -118
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -117
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -117
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -117
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -117
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 1
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 1
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 1
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 1
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -127
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -127
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -127
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -127
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 9
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 9
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 9
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 9
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -118
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -118
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -118
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -118
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -120
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -120
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -120
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -120
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 9
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 9
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 9
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 9
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 10
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 10
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 10
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 10
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -117
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -117
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -117
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -117
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -117
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -117
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -117
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -117
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -119
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -119
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -119
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -119
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 3
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 3
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 3
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 3
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 2
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 2
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 2
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 2
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 10
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 10
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 10
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 10
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 10
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 10
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 10
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 10
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -127
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -127
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -127
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -127
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -128
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -128
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -128
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -128
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 1
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 1
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 1
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 1
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 8
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 8
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 8
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 8
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
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
      .byte 5
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 6
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 7
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 10
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 24
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 13
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 18
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 23
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
      .byte 16
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 25
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 22
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 15
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 11
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 12
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 21
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 26
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 19
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 9
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 20
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 17
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 14
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 27
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
