	.att_syntax
	.text
	.p2align	5
	.globl	_jade_onetimeauth_poly1305_amd64_ref_verify
	.globl	jade_onetimeauth_poly1305_amd64_ref_verify
	.globl	_jade_onetimeauth_poly1305_amd64_ref
	.globl	jade_onetimeauth_poly1305_amd64_ref
_jade_onetimeauth_poly1305_amd64_ref_verify:
jade_onetimeauth_poly1305_amd64_ref_verify:
	movq	%rsp, %rax
	leaq	-56(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rax, 48(%rsp)
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r13, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	%r15, 40(%rsp)
	movq	%rdx, %r11
	movq	%rcx, %r8
	movq	$0, %r15
	movq	$0, %rbp
	movq	$0, %r12
	movq	(%r8), %r9
	movq	8(%r8), %r14
	movq	$1152921487695413247, %rax
	andq	%rax, %r9
	movq	$1152921487695413244, %rax
	andq	%rax, %r14
	movq	%r14, %r13
	shrq	$2, %r13
	addq	%r14, %r13
	addq	$16, %r8
	jmp 	Ljade_onetimeauth_poly1305_amd64_ref_verify$2
Ljade_onetimeauth_poly1305_amd64_ref_verify$3:
	addq	(%rsi), %r15
	adcq	8(%rsi), %rbp
	adcq	$1, %r12
	movq	%r13, %rcx
	imulq	%r12, %rcx
	imulq	%r9, %r12
	movq	%r9, %rax
	mulq	%r15
	movq	%rax, %rbx
	movq	%rdx, %r10
	movq	%r9, %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	%rdx, %r12
	movq	%r13, %rax
	mulq	%rbp
	movq	%rdx, %rbp
	addq	%rcx, %rbp
	movq	%rax, %rcx
	movq	%r14, %rax
	mulq	%r15
	addq	%rcx, %rbx
	adcq	%rax, %r10
	adcq	%rdx, %r12
	movq	$-4, %r15
	movq	%r12, %rax
	shrq	$2, %rax
	andq	%r12, %r15
	addq	%rax, %r15
	andq	$3, %r12
	addq	%rbx, %r15
	adcq	%r10, %rbp
	adcq	$0, %r12
	addq	$16, %rsi
	addq	$-16, %r11
Ljade_onetimeauth_poly1305_amd64_ref_verify$2:
	cmpq	$16, %r11
	jnb 	Ljade_onetimeauth_poly1305_amd64_ref_verify$3
	cmpq	$0, %r11
	jbe 	Ljade_onetimeauth_poly1305_amd64_ref_verify$1
	xorq	%rcx, %rcx
	movq	%r11, %rax
	andq	$7, %rax
	shlq	$3, %rax
	shrq	$3, %r11
	movq	%r11, %rdx
	xorq	$1, %rdx
	movq	%r11, %r10
	addq	$-1, %r10
	movq	%rax, %rbx
	andq	%r10, %rbx
	xorq	%rbx, %rcx
	xorq	%rbx, %rax
	shlq	%cl, %rdx
	movq	%rax, %rcx
	shlq	%cl, %r11
	movq	%rdx, %rax
	movq	%r11, %rcx
	subq	$1, %rax
	sbbq	$0, %rcx
	movq	(%rsi), %r10
	andq	%rax, %r10
	orq 	%rdx, %r10
	movq	8(%rsi), %rax
	andq	%rcx, %rax
	orq 	%r11, %rax
	addq	%r10, %r15
	adcq	%rax, %rbp
	adcq	$0, %r12
	movq	%r13, %rsi
	imulq	%r12, %rsi
	imulq	%r9, %r12
	movq	%r9, %rax
	mulq	%r15
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%r9, %rax
	mulq	%rbp
	addq	%rax, %r10
	adcq	%rdx, %r12
	movq	%r13, %rax
	mulq	%rbp
	movq	%rdx, %rbp
	addq	%rsi, %rbp
	movq	%rax, %rsi
	movq	%r14, %rax
	mulq	%r15
	addq	%rsi, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %r12
	movq	$-4, %r15
	movq	%r12, %rax
	shrq	$2, %rax
	andq	%r12, %r15
	addq	%rax, %r15
	andq	$3, %r12
	addq	%rcx, %r15
	adcq	%r10, %rbp
	adcq	$0, %r12
Ljade_onetimeauth_poly1305_amd64_ref_verify$1:
	movq	%r15, %rax
	movq	%rbp, %rcx
	addq	$5, %rax
	adcq	$0, %rcx
	adcq	$0, %r12
	shrq	$2, %r12
	negq	%r12
	xorq	%r15, %rax
	xorq	%rbp, %rcx
	andq	%r12, %rax
	andq	%r12, %rcx
	xorq	%r15, %rax
	xorq	%rbp, %rcx
	movq	(%r8), %rdx
	movq	8(%r8), %rsi
	addq	%rdx, %rax
	adcq	%rsi, %rcx
	movq	%rax, %rdx
	xorq	(%rdi), %rdx
	xorq	8(%rdi), %rcx
	orq 	%rcx, %rdx
	xorq	%rax, %rax
	subq	$1, %rdx
	adcq	$0, %rax
	addq	$-1, %rax
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %r15
	movq	48(%rsp), %rsp
	ret 
_jade_onetimeauth_poly1305_amd64_ref:
jade_onetimeauth_poly1305_amd64_ref:
	movq	%rsp, %rax
	leaq	-56(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rax, 48(%rsp)
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r13, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	%r15, 40(%rsp)
	movq	%rdx, %rbx
	movq	%rcx, %r9
	movq	$0, %r15
	movq	$0, %r8
	movq	$0, %r14
	movq	(%r9), %r12
	movq	8(%r9), %r13
	movq	$1152921487695413247, %rax
	andq	%rax, %r12
	movq	$1152921487695413244, %rax
	andq	%rax, %r13
	movq	%r13, %rbp
	shrq	$2, %rbp
	addq	%r13, %rbp
	addq	$16, %r9
	jmp 	Ljade_onetimeauth_poly1305_amd64_ref$2
Ljade_onetimeauth_poly1305_amd64_ref$3:
	addq	(%rsi), %r15
	adcq	8(%rsi), %r8
	adcq	$1, %r14
	movq	%rbp, %rcx
	imulq	%r14, %rcx
	imulq	%r12, %r14
	movq	%r12, %rax
	mulq	%r15
	movq	%rax, %r11
	movq	%rdx, %r10
	movq	%r12, %rax
	mulq	%r8
	addq	%rax, %r10
	adcq	%rdx, %r14
	movq	%rbp, %rax
	mulq	%r8
	movq	%rdx, %r8
	addq	%rcx, %r8
	movq	%rax, %rcx
	movq	%r13, %rax
	mulq	%r15
	addq	%rcx, %r11
	adcq	%rax, %r10
	adcq	%rdx, %r14
	movq	$-4, %r15
	movq	%r14, %rax
	shrq	$2, %rax
	andq	%r14, %r15
	addq	%rax, %r15
	andq	$3, %r14
	addq	%r11, %r15
	adcq	%r10, %r8
	adcq	$0, %r14
	addq	$16, %rsi
	addq	$-16, %rbx
Ljade_onetimeauth_poly1305_amd64_ref$2:
	cmpq	$16, %rbx
	jnb 	Ljade_onetimeauth_poly1305_amd64_ref$3
	cmpq	$0, %rbx
	jbe 	Ljade_onetimeauth_poly1305_amd64_ref$1
	xorq	%rcx, %rcx
	movq	%rbx, %rax
	andq	$7, %rax
	shlq	$3, %rax
	shrq	$3, %rbx
	movq	%rbx, %rdx
	xorq	$1, %rdx
	movq	%rbx, %r10
	addq	$-1, %r10
	movq	%rax, %r11
	andq	%r10, %r11
	xorq	%r11, %rcx
	xorq	%r11, %rax
	shlq	%cl, %rdx
	movq	%rax, %rcx
	shlq	%cl, %rbx
	movq	%rdx, %rax
	movq	%rbx, %rcx
	subq	$1, %rax
	sbbq	$0, %rcx
	movq	(%rsi), %r10
	andq	%rax, %r10
	orq 	%rdx, %r10
	movq	8(%rsi), %rax
	andq	%rcx, %rax
	orq 	%rbx, %rax
	addq	%r10, %r15
	adcq	%rax, %r8
	adcq	$0, %r14
	movq	%rbp, %rsi
	imulq	%r14, %rsi
	imulq	%r12, %r14
	movq	%r12, %rax
	mulq	%r15
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	%r12, %rax
	mulq	%r8
	addq	%rax, %r10
	adcq	%rdx, %r14
	movq	%rbp, %rax
	mulq	%r8
	movq	%rdx, %r8
	addq	%rsi, %r8
	movq	%rax, %rsi
	movq	%r13, %rax
	mulq	%r15
	addq	%rsi, %rcx
	adcq	%rax, %r10
	adcq	%rdx, %r14
	movq	$-4, %r15
	movq	%r14, %rax
	shrq	$2, %rax
	andq	%r14, %r15
	addq	%rax, %r15
	andq	$3, %r14
	addq	%rcx, %r15
	adcq	%r10, %r8
	adcq	$0, %r14
Ljade_onetimeauth_poly1305_amd64_ref$1:
	movq	%r15, %rax
	movq	%r8, %rcx
	addq	$5, %rax
	adcq	$0, %rcx
	adcq	$0, %r14
	shrq	$2, %r14
	negq	%r14
	xorq	%r15, %rax
	xorq	%r8, %rcx
	andq	%r14, %rax
	andq	%r14, %rcx
	xorq	%r15, %rax
	xorq	%r8, %rcx
	movq	(%r9), %rdx
	movq	8(%r9), %rsi
	addq	%rdx, %rax
	adcq	%rsi, %rcx
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	xorq	%rax, %rax
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %r15
	movq	48(%rsp), %rsp
	ret 
