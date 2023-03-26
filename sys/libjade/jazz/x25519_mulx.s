	.att_syntax
	.text
	.p2align	5
	.globl	_jade_scalarmult_curve25519_amd64_mulx_base
	.globl	jade_scalarmult_curve25519_amd64_mulx_base
	.globl	_jade_scalarmult_curve25519_amd64_mulx
	.globl	jade_scalarmult_curve25519_amd64_mulx
_jade_scalarmult_curve25519_amd64_mulx_base:
jade_scalarmult_curve25519_amd64_mulx_base:
	movq	%rsp, %rax
	leaq	-408(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rax, 400(%rsp)
	movq	%rbx, 352(%rsp)
	movq	%rbp, 360(%rsp)
	movq	%r12, 368(%rsp)
	movq	%r13, 376(%rsp)
	movq	%r14, 384(%rsp)
	movq	%r15, 392(%rsp)
	movq	%rdi, (%rsp)
	movq	(%rsi), %rax
	movq	%rax, 24(%rsp)
	movq	8(%rsi), %rax
	movq	%rax, 32(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 40(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 48(%rsp)
	andb	$-8, 24(%rsp)
	andb	$127, 55(%rsp)
	orb 	$64, 55(%rsp)
	movq	$9, %rcx
	movq	$0, %rdx
	movq	$0, %r9
	movq	$0, %r10
	xorq	%r11, %r11
	movq	$1, 56(%rsp)
	movq	$0, %rax
	movq	%rcx, 88(%rsp)
	movq	%rdx, 96(%rsp)
	movq	%r9, 104(%rsp)
	movq	%r10, 112(%rsp)
	movq	$1, 120(%rsp)
	movq	%r11, 64(%rsp)
	movq	%r11, %r8
	movq	%r11, 128(%rsp)
	movq	%r11, 72(%rsp)
	movq	%r11, %rsi
	movq	%r11, 136(%rsp)
	movq	%r11, 80(%rsp)
	movq	%r11, %rdi
	movq	%r11, 144(%rsp)
	movq	%rcx, 152(%rsp)
	movq	%rdx, 160(%rsp)
	movq	%r9, 168(%rsp)
	movq	%r10, 176(%rsp)
	movq	$255, %rcx
	movq	$0, 8(%rsp)
Ljade_scalarmult_curve25519_amd64_mulx_base$9:
	addq	$-1, %rcx
	movq	%rcx, 16(%rsp)
	movq	%rcx, %rdx
	shrq	$3, %rdx
	movzbq	24(%rsp,%rdx), %rdx
	andq	$7, %rcx
	shrq	%cl, %rdx
	andq	$1, %rdx
	movq	8(%rsp), %r9
	xorq	%rdx, %r9
	xorq	%rcx, %rcx
	subq	%r9, %rcx
	movq	120(%rsp), %r9
	movq	128(%rsp), %r10
	movq	136(%rsp), %r11
	movq	144(%rsp), %rbx
	movq	%rax, %rbp
	movq	%r8, %r12
	movq	%rsi, %r13
	movq	%rdi, %r14
	xorq	%r9, %rbp
	xorq	%r10, %r12
	xorq	%r11, %r13
	xorq	%rbx, %r14
	andq	%rcx, %rbp
	andq	%rcx, %r12
	andq	%rcx, %r13
	andq	%rcx, %r14
	xorq	%rbp, %rax
	xorq	%rbp, %r9
	movq	%r9, 120(%rsp)
	xorq	%r12, %r8
	xorq	%r12, %r10
	movq	%r10, 128(%rsp)
	xorq	%r13, %rsi
	xorq	%r13, %r11
	movq	%r11, 136(%rsp)
	xorq	%r14, %rdi
	xorq	%r14, %rbx
	movq	%rbx, 144(%rsp)
	movq	88(%rsp), %r11
	movq	96(%rsp), %rbx
	movq	104(%rsp), %r9
	movq	112(%rsp), %r10
	movq	56(%rsp), %rbp
	movq	%r11, %r12
	xorq	%rbp, %r12
	andq	%rcx, %r12
	xorq	%r12, %rbp
	xorq	%r12, %r11
	movq	%rbp, 56(%rsp)
	movq	%r11, 88(%rsp)
	movq	64(%rsp), %r11
	movq	%rbx, %rbp
	xorq	%r11, %rbp
	andq	%rcx, %rbp
	xorq	%rbp, %r11
	xorq	%rbp, %rbx
	movq	%r11, 64(%rsp)
	movq	%rbx, 96(%rsp)
	movq	72(%rsp), %r11
	movq	%r9, %rbx
	xorq	%r11, %rbx
	andq	%rcx, %rbx
	xorq	%rbx, %r11
	xorq	%rbx, %r9
	movq	%r11, 72(%rsp)
	movq	%r9, 104(%rsp)
	movq	80(%rsp), %r9
	movq	%r10, %r11
	xorq	%r9, %r11
	andq	%rcx, %r11
	xorq	%r11, %r9
	xorq	%r11, %r10
	movq	%r9, 80(%rsp)
	movq	%r10, 112(%rsp)
	movq	%rdx, 8(%rsp)
	xorq	%rcx, %rcx
	movq	56(%rsp), %rdx
	movq	64(%rsp), %r9
	movq	72(%rsp), %r10
	movq	80(%rsp), %r11
	subq	%rax, %rdx
	sbbq	%r8, %r9
	sbbq	%rsi, %r10
	sbbq	%rdi, %r11
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	subq	%rcx, %rdx
	sbbq	$0, %r9
	sbbq	$0, %r10
	sbbq	$0, %r11
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	subq	%rcx, %rdx
	movq	%rdx, 184(%rsp)
	movq	%r9, 192(%rsp)
	movq	%r10, 200(%rsp)
	movq	%r11, 208(%rsp)
	xorq	%rcx, %rcx
	addq	56(%rsp), %rax
	adcq	64(%rsp), %r8
	adcq	72(%rsp), %rsi
	adcq	80(%rsp), %rdi
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	addq	%rcx, %rax
	adcq	$0, %r8
	adcq	$0, %rsi
	adcq	$0, %rdi
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	addq	%rcx, %rax
	movq	%rax, 216(%rsp)
	movq	%r8, 224(%rsp)
	movq	%rsi, 232(%rsp)
	movq	%rdi, 240(%rsp)
	movq	88(%rsp), %rax
	movq	96(%rsp), %rcx
	movq	104(%rsp), %rdx
	movq	112(%rsp), %rsi
	xorq	%rdi, %rdi
	subq	120(%rsp), %rax
	sbbq	128(%rsp), %rcx
	sbbq	136(%rsp), %rdx
	sbbq	144(%rsp), %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	subq	%rdi, %rax
	sbbq	$0, %rcx
	sbbq	$0, %rdx
	sbbq	$0, %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	subq	%rdi, %rax
	movq	%rax, 248(%rsp)
	movq	%rcx, 256(%rsp)
	movq	%rdx, 264(%rsp)
	movq	%rsi, 272(%rsp)
	movq	88(%rsp), %rax
	movq	96(%rsp), %rcx
	movq	104(%rsp), %rdx
	movq	112(%rsp), %rsi
	xorq	%rdi, %rdi
	addq	120(%rsp), %rax
	adcq	128(%rsp), %rcx
	adcq	136(%rsp), %rdx
	adcq	144(%rsp), %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %rax
	adcq	$0, %rcx
	adcq	$0, %rdx
	adcq	$0, %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %rax
	movq	%rax, 280(%rsp)
	movq	%rcx, 288(%rsp)
	movq	%rdx, 296(%rsp)
	movq	%rsi, 304(%rsp)
	movq	248(%rsp), %r9
	movq	256(%rsp), %r10
	movq	264(%rsp), %r11
	movq	272(%rsp), %rbx
	xorq	%rax, %rax
	movq	216(%rsp), %rdx
	MULXq	%r9, %rsi, %rcx
	MULXq	%r10, %r8, %rdi
	adcxq	%r8, %rcx
	MULXq	%r11, %rbp, %r8
	adcxq	%rbp, %rdi
	MULXq	%rbx, %rdx, %rbp
	adcxq	%rdx, %r8
	adcxq	%rax, %rbp
	movq	224(%rsp), %rdx
	MULXq	%r9, %r13, %r12
	adoxq	%r13, %rcx
	adcxq	%r12, %rdi
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %rdi
	adcxq	%r12, %r8
	MULXq	%r11, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %rbp
	MULXq	%rbx, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rax, %r12
	adoxq	%rax, %r12
	movq	232(%rsp), %rdx
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %rdi
	adcxq	%r13, %r8
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %rbp
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rbx, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	movq	240(%rsp), %rdx
	MULXq	%r9, %r14, %r9
	adoxq	%r14, %r8
	adcxq	%r9, %rbp
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rbp
	adcxq	%r9, %r12
	MULXq	%r11, %r10, %r9
	adoxq	%r10, %r12
	adcxq	%r9, %r13
	MULXq	%rbx, %rdx, %r9
	adoxq	%rdx, %r13
	adcxq	%rax, %r9
	adoxq	%rax, %r9
	movq	$38, %rdx
	MULXq	%rbp, %r11, %r10
	adoxq	%r11, %rsi
	adcxq	%r10, %rcx
	MULXq	%r12, %r11, %r10
	adoxq	%r11, %rcx
	adcxq	%r10, %rdi
	MULXq	%r13, %r11, %r10
	adoxq	%r11, %rdi
	adcxq	%r10, %r8
	MULXq	%r9, %r9, %rdx
	adoxq	%r9, %r8
	adcxq	%rax, %rdx
	adoxq	%rax, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rsi
	adcq	%rax, %rcx
	adcq	%rax, %rdi
	adcq	%rax, %r8
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rsi
	movq	%rsi, 248(%rsp)
	movq	%rcx, 256(%rsp)
	movq	%rdi, 264(%rsp)
	movq	%r8, 272(%rsp)
	movq	184(%rsp), %r9
	movq	192(%rsp), %r10
	movq	200(%rsp), %r11
	movq	208(%rsp), %rbx
	xorq	%rax, %rax
	movq	280(%rsp), %rdx
	MULXq	%r9, %rsi, %rcx
	MULXq	%r10, %r8, %rdi
	adcxq	%r8, %rcx
	MULXq	%r11, %rbp, %r8
	adcxq	%rbp, %rdi
	MULXq	%rbx, %rdx, %rbp
	adcxq	%rdx, %r8
	adcxq	%rax, %rbp
	movq	288(%rsp), %rdx
	MULXq	%r9, %r13, %r12
	adoxq	%r13, %rcx
	adcxq	%r12, %rdi
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %rdi
	adcxq	%r12, %r8
	MULXq	%r11, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %rbp
	MULXq	%rbx, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rax, %r12
	adoxq	%rax, %r12
	movq	296(%rsp), %rdx
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %rdi
	adcxq	%r13, %r8
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %rbp
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rbx, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	movq	304(%rsp), %rdx
	MULXq	%r9, %r14, %r9
	adoxq	%r14, %r8
	adcxq	%r9, %rbp
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rbp
	adcxq	%r9, %r12
	MULXq	%r11, %r10, %r9
	adoxq	%r10, %r12
	adcxq	%r9, %r13
	MULXq	%rbx, %rdx, %r9
	adoxq	%rdx, %r13
	adcxq	%rax, %r9
	adoxq	%rax, %r9
	movq	$38, %rdx
	MULXq	%rbp, %r11, %r10
	adoxq	%r11, %rsi
	adcxq	%r10, %rcx
	MULXq	%r12, %r11, %r10
	adoxq	%r11, %rcx
	adcxq	%r10, %rdi
	MULXq	%r13, %r11, %r10
	adoxq	%r11, %rdi
	adcxq	%r10, %r8
	MULXq	%r9, %r9, %rdx
	adoxq	%r9, %r8
	adcxq	%rax, %rdx
	adoxq	%rax, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rsi
	adcq	%rax, %rcx
	adcq	%rax, %rdi
	adcq	%rax, %r8
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rsi
	movq	%rsi, 280(%rsp)
	movq	%rcx, 288(%rsp)
	movq	%rdi, 296(%rsp)
	movq	%r8, 304(%rsp)
	movq	216(%rsp), %rdx
	movq	224(%rsp), %r11
	movq	232(%rsp), %r13
	movq	240(%rsp), %rbx
	xorq	%rax, %rax
	MULXq	%rdx, %rsi, %rcx
	MULXq	%r11, %r8, %rdi
	MULXq	%r13, %r10, %r9
	adcxq	%r10, %rdi
	MULXq	%rbx, %rdx, %r10
	adcxq	%rdx, %r9
	movq	%r11, %rdx
	MULXq	%r13, %rbp, %r11
	adoxq	%rbp, %r9
	adcxq	%r11, %r10
	MULXq	%rbx, %rbp, %r11
	adoxq	%rbp, %r10
	MULXq	%rdx, %r12, %rbp
	movq	%r13, %rdx
	MULXq	%rbx, %r14, %r13
	adcxq	%r14, %r11
	adoxq	%rax, %r11
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	MULXq	%rdx, %r15, %r14
	movq	%rbx, %rdx
	MULXq	%rdx, %rdx, %rbx
	adcxq	%r8, %r8
	adoxq	%rcx, %r8
	adcxq	%rdi, %rdi
	adoxq	%r12, %rdi
	adcxq	%r9, %r9
	adoxq	%rbp, %r9
	adcxq	%r10, %r10
	adoxq	%r15, %r10
	adcxq	%r11, %r11
	adoxq	%r14, %r11
	adcxq	%r13, %r13
	adoxq	%rdx, %r13
	adcxq	%rax, %rbx
	adoxq	%rax, %rbx
	movq	$38, %rdx
	MULXq	%r10, %r10, %rcx
	adoxq	%r10, %rsi
	adcxq	%rcx, %r8
	MULXq	%r11, %r10, %rcx
	adoxq	%r10, %r8
	adcxq	%rcx, %rdi
	MULXq	%r13, %r10, %rcx
	adoxq	%r10, %rdi
	adcxq	%rcx, %r9
	MULXq	%rbx, %rdx, %rcx
	adoxq	%rdx, %r9
	adcxq	%rax, %rcx
	adoxq	%rax, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rsi
	adcq	%rax, %r8
	adcq	%rax, %rdi
	adcq	%rax, %r9
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rsi
	movq	%rsi, 216(%rsp)
	movq	%r8, 224(%rsp)
	movq	%rdi, 232(%rsp)
	movq	%r9, 240(%rsp)
	movq	184(%rsp), %rdx
	movq	192(%rsp), %r11
	movq	200(%rsp), %r13
	movq	208(%rsp), %rbx
	xorq	%r8, %r8
	MULXq	%rdx, %rax, %r9
	MULXq	%r11, %rsi, %rcx
	MULXq	%r13, %r10, %rdi
	adcxq	%r10, %rcx
	MULXq	%rbx, %rdx, %r10
	adcxq	%rdx, %rdi
	movq	%r11, %rdx
	MULXq	%r13, %rbp, %r11
	adoxq	%rbp, %rdi
	adcxq	%r11, %r10
	MULXq	%rbx, %rbp, %r11
	adoxq	%rbp, %r10
	MULXq	%rdx, %r12, %rbp
	movq	%r13, %rdx
	MULXq	%rbx, %r14, %r13
	adcxq	%r14, %r11
	adoxq	%r8, %r11
	adcxq	%r8, %r13
	adoxq	%r8, %r13
	MULXq	%rdx, %r15, %r14
	movq	%rbx, %rdx
	MULXq	%rdx, %rdx, %rbx
	adcxq	%rsi, %rsi
	adoxq	%r9, %rsi
	adcxq	%rcx, %rcx
	adoxq	%r12, %rcx
	adcxq	%rdi, %rdi
	adoxq	%rbp, %rdi
	adcxq	%r10, %r10
	adoxq	%r15, %r10
	adcxq	%r11, %r11
	adoxq	%r14, %r11
	adcxq	%r13, %r13
	adoxq	%rdx, %r13
	adcxq	%r8, %rbx
	adoxq	%r8, %rbx
	movq	$38, %rdx
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rax
	adcxq	%r9, %rsi
	MULXq	%r11, %r10, %r9
	adoxq	%r10, %rsi
	adcxq	%r9, %rcx
	MULXq	%r13, %r10, %r9
	adoxq	%r10, %rcx
	adcxq	%r9, %rdi
	MULXq	%rbx, %r9, %rdx
	adoxq	%r9, %rdi
	adcxq	%r8, %rdx
	adoxq	%r8, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rax
	adcq	%r8, %rsi
	adcq	%r8, %rcx
	adcq	%r8, %rdi
	sbbq	%r8, %r8
	andq	$38, %r8
	addq	%r8, %rax
	movq	248(%rsp), %rdx
	movq	256(%rsp), %r8
	movq	264(%rsp), %r9
	movq	272(%rsp), %r10
	xorq	%r11, %r11
	addq	280(%rsp), %rdx
	adcq	288(%rsp), %r8
	adcq	296(%rsp), %r9
	adcq	304(%rsp), %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdx
	adcq	$0, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdx
	movq	%rdx, 184(%rsp)
	movq	%r8, 192(%rsp)
	movq	%r9, 200(%rsp)
	movq	%r10, 208(%rsp)
	movq	248(%rsp), %rdx
	movq	256(%rsp), %r8
	movq	264(%rsp), %r9
	movq	272(%rsp), %r10
	xorq	%r11, %r11
	subq	280(%rsp), %rdx
	sbbq	288(%rsp), %r8
	sbbq	296(%rsp), %r9
	sbbq	304(%rsp), %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	subq	%r11, %rdx
	sbbq	$0, %r8
	sbbq	$0, %r9
	sbbq	$0, %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	subq	%r11, %rdx
	movq	%rdx, 280(%rsp)
	movq	%r8, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r10, 304(%rsp)
	xorq	%rdx, %rdx
	movq	216(%rsp), %r8
	movq	224(%rsp), %r9
	movq	232(%rsp), %r10
	movq	240(%rsp), %r11
	subq	%rax, %r8
	sbbq	%rsi, %r9
	sbbq	%rcx, %r10
	sbbq	%rdi, %r11
	sbbq	%rdx, %rdx
	andq	$38, %rdx
	subq	%rdx, %r8
	sbbq	$0, %r9
	sbbq	$0, %r10
	sbbq	$0, %r11
	sbbq	%rdx, %rdx
	andq	$38, %rdx
	subq	%rdx, %r8
	movq	%r8, 248(%rsp)
	movq	%r9, 256(%rsp)
	movq	%r10, 264(%rsp)
	movq	%r11, 272(%rsp)
	xorq	%r8, %r8
	movq	216(%rsp), %rdx
	MULXq	%rax, %r10, %r9
	MULXq	%rsi, %rbx, %r11
	adcxq	%rbx, %r9
	MULXq	%rcx, %rbp, %rbx
	adcxq	%rbp, %r11
	MULXq	%rdi, %rdx, %rbp
	adcxq	%rdx, %rbx
	adcxq	%r8, %rbp
	movq	224(%rsp), %rdx
	MULXq	%rax, %r13, %r12
	adoxq	%r13, %r9
	adcxq	%r12, %r11
	MULXq	%rsi, %r13, %r12
	adoxq	%r13, %r11
	adcxq	%r12, %rbx
	MULXq	%rcx, %r13, %r12
	adoxq	%r13, %rbx
	adcxq	%r12, %rbp
	MULXq	%rdi, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%r8, %r12
	adoxq	%r8, %r12
	movq	232(%rsp), %rdx
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %r11
	adcxq	%r13, %rbx
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %rbx
	adcxq	%r13, %rbp
	MULXq	%rcx, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rdi, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%r8, %r13
	adoxq	%r8, %r13
	movq	240(%rsp), %rdx
	MULXq	%rax, %r14, %rax
	adoxq	%r14, %rbx
	adcxq	%rax, %rbp
	MULXq	%rsi, %rsi, %rax
	adoxq	%rsi, %rbp
	adcxq	%rax, %r12
	MULXq	%rcx, %rcx, %rax
	adoxq	%rcx, %r12
	adcxq	%rax, %r13
	MULXq	%rdi, %rcx, %rax
	adoxq	%rcx, %r13
	adcxq	%r8, %rax
	adoxq	%r8, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rsi, %rcx
	adoxq	%rsi, %r10
	adcxq	%rcx, %r9
	MULXq	%r12, %rsi, %rcx
	adoxq	%rsi, %r9
	adcxq	%rcx, %r11
	MULXq	%r13, %rsi, %rcx
	adoxq	%rsi, %r11
	adcxq	%rcx, %rbx
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %rbx
	adcxq	%r8, %rax
	adoxq	%r8, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r10
	adcq	%r8, %r9
	adcq	%r8, %r11
	adcq	%r8, %rbx
	sbbq	%r8, %r8
	andq	$38, %r8
	addq	%r8, %r10
	movq	%r10, 56(%rsp)
	movq	%r9, 64(%rsp)
	movq	%r11, 72(%rsp)
	movq	%rbx, 80(%rsp)
	movq	280(%rsp), %rdx
	movq	288(%rsp), %r11
	movq	296(%rsp), %r13
	movq	304(%rsp), %rbx
	xorq	%rax, %rax
	MULXq	%rdx, %rsi, %rcx
	MULXq	%r11, %r8, %rdi
	MULXq	%r13, %r10, %r9
	adcxq	%r10, %rdi
	MULXq	%rbx, %rdx, %r10
	adcxq	%rdx, %r9
	movq	%r11, %rdx
	MULXq	%r13, %rbp, %r11
	adoxq	%rbp, %r9
	adcxq	%r11, %r10
	MULXq	%rbx, %rbp, %r11
	adoxq	%rbp, %r10
	MULXq	%rdx, %r12, %rbp
	movq	%r13, %rdx
	MULXq	%rbx, %r14, %r13
	adcxq	%r14, %r11
	adoxq	%rax, %r11
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	MULXq	%rdx, %r15, %r14
	movq	%rbx, %rdx
	MULXq	%rdx, %rdx, %rbx
	adcxq	%r8, %r8
	adoxq	%rcx, %r8
	adcxq	%rdi, %rdi
	adoxq	%r12, %rdi
	adcxq	%r9, %r9
	adoxq	%rbp, %r9
	adcxq	%r10, %r10
	adoxq	%r15, %r10
	adcxq	%r11, %r11
	adoxq	%r14, %r11
	adcxq	%r13, %r13
	adoxq	%rdx, %r13
	adcxq	%rax, %rbx
	adoxq	%rax, %rbx
	movq	$38, %rdx
	MULXq	%r10, %r10, %rcx
	adoxq	%r10, %rsi
	adcxq	%rcx, %r8
	MULXq	%r11, %r10, %rcx
	adoxq	%r10, %r8
	adcxq	%rcx, %rdi
	MULXq	%r13, %r10, %rcx
	adoxq	%r10, %rdi
	adcxq	%rcx, %r9
	MULXq	%rbx, %rdx, %rcx
	adoxq	%rdx, %r9
	adcxq	%rax, %rcx
	adoxq	%rax, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rsi
	adcq	%rax, %r8
	adcq	%rax, %rdi
	adcq	%rax, %r9
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rsi
	movq	%rsi, 280(%rsp)
	movq	%r8, 288(%rsp)
	movq	%rdi, 296(%rsp)
	movq	%r9, 304(%rsp)
	movq	$121665, %rdx
	MULXq	248(%rsp), %rcx, %rax
	MULXq	256(%rsp), %rdi, %rsi
	addq	%rdi, %rax
	MULXq	264(%rsp), %r8, %rdi
	adcq	%r8, %rsi
	MULXq	272(%rsp), %r9, %r8
	adcq	%r9, %rdi
	adcq	$0, %r8
	imulq	$38, %r8, %r8
	addq	%r8, %rcx
	adcq	$0, %rax
	adcq	$0, %rsi
	adcq	$0, %rdi
	sbbq	%rdx, %rdx
	andq	$38, %rdx
	addq	%rdx, %rcx
	movq	%rcx, 312(%rsp)
	movq	%rax, 320(%rsp)
	movq	%rsi, 328(%rsp)
	movq	%rdi, 336(%rsp)
	movq	184(%rsp), %rdx
	movq	192(%rsp), %r11
	movq	200(%rsp), %r13
	movq	208(%rsp), %rbx
	xorq	%rax, %rax
	MULXq	%rdx, %rsi, %rcx
	MULXq	%r11, %r8, %rdi
	MULXq	%r13, %r10, %r9
	adcxq	%r10, %rdi
	MULXq	%rbx, %rdx, %r10
	adcxq	%rdx, %r9
	movq	%r11, %rdx
	MULXq	%r13, %rbp, %r11
	adoxq	%rbp, %r9
	adcxq	%r11, %r10
	MULXq	%rbx, %rbp, %r11
	adoxq	%rbp, %r10
	MULXq	%rdx, %r12, %rbp
	movq	%r13, %rdx
	MULXq	%rbx, %r14, %r13
	adcxq	%r14, %r11
	adoxq	%rax, %r11
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	MULXq	%rdx, %r15, %r14
	movq	%rbx, %rdx
	MULXq	%rdx, %rdx, %rbx
	adcxq	%r8, %r8
	adoxq	%rcx, %r8
	adcxq	%rdi, %rdi
	adoxq	%r12, %rdi
	adcxq	%r9, %r9
	adoxq	%rbp, %r9
	adcxq	%r10, %r10
	adoxq	%r15, %r10
	adcxq	%r11, %r11
	adoxq	%r14, %r11
	adcxq	%r13, %r13
	adoxq	%rdx, %r13
	adcxq	%rax, %rbx
	adoxq	%rax, %rbx
	movq	$38, %rdx
	MULXq	%r10, %r10, %rcx
	adoxq	%r10, %rsi
	adcxq	%rcx, %r8
	MULXq	%r11, %r10, %rcx
	adoxq	%r10, %r8
	adcxq	%rcx, %rdi
	MULXq	%r13, %r10, %rcx
	adoxq	%r10, %rdi
	adcxq	%rcx, %r9
	MULXq	%rbx, %rdx, %rcx
	adoxq	%rdx, %r9
	adcxq	%rax, %rcx
	adoxq	%rax, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rsi
	adcq	%rax, %r8
	adcq	%rax, %rdi
	adcq	%rax, %r9
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rsi
	movq	%rsi, 88(%rsp)
	movq	%r8, 96(%rsp)
	movq	%rdi, 104(%rsp)
	movq	%r9, 112(%rsp)
	movq	216(%rsp), %rax
	movq	224(%rsp), %rcx
	movq	232(%rsp), %rdx
	movq	240(%rsp), %rsi
	xorq	%rdi, %rdi
	addq	312(%rsp), %rax
	adcq	320(%rsp), %rcx
	adcq	328(%rsp), %rdx
	adcq	336(%rsp), %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %rax
	adcq	$0, %rcx
	adcq	$0, %rdx
	adcq	$0, %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %rax
	movq	%rax, 312(%rsp)
	movq	%rcx, 320(%rsp)
	movq	%rdx, 328(%rsp)
	movq	%rsi, 336(%rsp)
	movq	280(%rsp), %r9
	movq	288(%rsp), %r10
	movq	296(%rsp), %r11
	movq	304(%rsp), %rbx
	xorq	%rax, %rax
	movq	152(%rsp), %rdx
	MULXq	%r9, %rsi, %rcx
	MULXq	%r10, %r8, %rdi
	adcxq	%r8, %rcx
	MULXq	%r11, %rbp, %r8
	adcxq	%rbp, %rdi
	MULXq	%rbx, %rdx, %rbp
	adcxq	%rdx, %r8
	adcxq	%rax, %rbp
	movq	160(%rsp), %rdx
	MULXq	%r9, %r13, %r12
	adoxq	%r13, %rcx
	adcxq	%r12, %rdi
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %rdi
	adcxq	%r12, %r8
	MULXq	%r11, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %rbp
	MULXq	%rbx, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rax, %r12
	adoxq	%rax, %r12
	movq	168(%rsp), %rdx
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %rdi
	adcxq	%r13, %r8
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %rbp
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rbx, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	movq	176(%rsp), %rdx
	MULXq	%r9, %r14, %r9
	adoxq	%r14, %r8
	adcxq	%r9, %rbp
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rbp
	adcxq	%r9, %r12
	MULXq	%r11, %r10, %r9
	adoxq	%r10, %r12
	adcxq	%r9, %r13
	MULXq	%rbx, %rdx, %r9
	adoxq	%rdx, %r13
	adcxq	%rax, %r9
	adoxq	%rax, %r9
	movq	$38, %rdx
	MULXq	%rbp, %r11, %r10
	adoxq	%r11, %rsi
	adcxq	%r10, %rcx
	MULXq	%r12, %r11, %r10
	adoxq	%r11, %rcx
	adcxq	%r10, %rdi
	MULXq	%r13, %r11, %r10
	adoxq	%r11, %rdi
	adcxq	%r10, %r8
	MULXq	%r9, %r9, %rdx
	adoxq	%r9, %r8
	adcxq	%rax, %rdx
	adoxq	%rax, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rsi
	adcq	%rax, %rcx
	adcq	%rax, %rdi
	adcq	%rax, %r8
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rsi
	movq	%rsi, 120(%rsp)
	movq	%rcx, 128(%rsp)
	movq	%rdi, 136(%rsp)
	movq	%r8, 144(%rsp)
	movq	312(%rsp), %r9
	movq	320(%rsp), %r10
	movq	328(%rsp), %r11
	movq	336(%rsp), %rbx
	xorq	%rcx, %rcx
	movq	248(%rsp), %rdx
	MULXq	%r9, %rax, %r8
	MULXq	%r10, %rdi, %rsi
	adcxq	%rdi, %r8
	MULXq	%r11, %rbp, %rdi
	adcxq	%rbp, %rsi
	MULXq	%rbx, %rdx, %rbp
	adcxq	%rdx, %rdi
	adcxq	%rcx, %rbp
	movq	256(%rsp), %rdx
	MULXq	%r9, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %rsi
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %rsi
	adcxq	%r12, %rdi
	MULXq	%r11, %r13, %r12
	adoxq	%r13, %rdi
	adcxq	%r12, %rbp
	MULXq	%rbx, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rcx, %r12
	adoxq	%rcx, %r12
	movq	264(%rsp), %rdx
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %rsi
	adcxq	%r13, %rdi
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %rdi
	adcxq	%r13, %rbp
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rbx, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rcx, %r13
	adoxq	%rcx, %r13
	movq	272(%rsp), %rdx
	MULXq	%r9, %r14, %r9
	adoxq	%r14, %rdi
	adcxq	%r9, %rbp
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rbp
	adcxq	%r9, %r12
	MULXq	%r11, %r10, %r9
	adoxq	%r10, %r12
	adcxq	%r9, %r13
	MULXq	%rbx, %rdx, %r9
	adoxq	%rdx, %r13
	adcxq	%rcx, %r9
	adoxq	%rcx, %r9
	movq	$38, %rdx
	MULXq	%rbp, %r11, %r10
	adoxq	%r11, %rax
	adcxq	%r10, %r8
	MULXq	%r12, %r11, %r10
	adoxq	%r11, %r8
	adcxq	%r10, %rsi
	MULXq	%r13, %r11, %r10
	adoxq	%r11, %rsi
	adcxq	%r10, %rdi
	MULXq	%r9, %r9, %rdx
	adoxq	%r9, %rdi
	adcxq	%rcx, %rdx
	adoxq	%rcx, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rax
	adcq	%rcx, %r8
	adcq	%rcx, %rsi
	adcq	%rcx, %rdi
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	addq	%rcx, %rax
	movq	16(%rsp), %rcx
	cmpq	$0, %rcx
	jnbe	Ljade_scalarmult_curve25519_amd64_mulx_base$9
	movq	%rax, 120(%rsp)
	movq	%r8, 128(%rsp)
	movq	%rsi, 136(%rsp)
	movq	%rdi, 144(%rsp)
	xorq	%r9, %r9
	movq	%rax, %rdx
	MULXq	%rdx, %r10, %rbx
	MULXq	%r8, %r11, %rcx
	MULXq	%rsi, %rbp, %rax
	adcxq	%rbp, %rcx
	MULXq	%rdi, %rdx, %rbp
	adcxq	%rdx, %rax
	movq	%r8, %rdx
	MULXq	%rsi, %r12, %r8
	adoxq	%r12, %rax
	adcxq	%r8, %rbp
	MULXq	%rdi, %r12, %r8
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rsi, %rdx
	MULXq	%rdi, %r14, %rsi
	adcxq	%r14, %r8
	adoxq	%r9, %r8
	adcxq	%r9, %rsi
	adoxq	%r9, %rsi
	MULXq	%rdx, %r15, %r14
	movq	%rdi, %rdx
	MULXq	%rdx, %rdx, %rdi
	adcxq	%r11, %r11
	adoxq	%rbx, %r11
	adcxq	%rcx, %rcx
	adoxq	%r13, %rcx
	adcxq	%rax, %rax
	adoxq	%r12, %rax
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r8, %r8
	adoxq	%r14, %r8
	adcxq	%rsi, %rsi
	adoxq	%rdx, %rsi
	adcxq	%r9, %rdi
	adoxq	%r9, %rdi
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r10
	adcxq	%rbx, %r11
	MULXq	%r8, %rbx, %r8
	adoxq	%rbx, %r11
	adcxq	%r8, %rcx
	MULXq	%rsi, %r8, %rsi
	adoxq	%r8, %rcx
	adcxq	%rsi, %rax
	MULXq	%rdi, %rsi, %rdx
	adoxq	%rsi, %rax
	adcxq	%r9, %rdx
	adoxq	%r9, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %r10
	adcq	%r9, %r11
	adcq	%r9, %rcx
	adcq	%r9, %rax
	sbbq	%r9, %r9
	andq	$38, %r9
	addq	%r9, %r10
	movq	%r10, 88(%rsp)
	movq	%r11, 96(%rsp)
	movq	%rcx, 104(%rsp)
	movq	%rax, 112(%rsp)
	xorq	%rsi, %rsi
	movq	%r10, %rdx
	MULXq	%rdx, %rdi, %rbx
	MULXq	%r11, %r10, %r9
	MULXq	%rcx, %rbp, %r8
	adcxq	%rbp, %r9
	MULXq	%rax, %rdx, %rbp
	adcxq	%rdx, %r8
	movq	%r11, %rdx
	MULXq	%rcx, %r12, %r11
	adoxq	%r12, %r8
	adcxq	%r11, %rbp
	MULXq	%rax, %r12, %r11
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rcx, %rdx
	MULXq	%rax, %r14, %rcx
	adcxq	%r14, %r11
	adoxq	%rsi, %r11
	adcxq	%rsi, %rcx
	adoxq	%rsi, %rcx
	MULXq	%rdx, %r15, %r14
	movq	%rax, %rdx
	MULXq	%rdx, %rdx, %rax
	adcxq	%r10, %r10
	adoxq	%rbx, %r10
	adcxq	%r9, %r9
	adoxq	%r13, %r9
	adcxq	%r8, %r8
	adoxq	%r12, %r8
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r11, %r11
	adoxq	%r14, %r11
	adcxq	%rcx, %rcx
	adoxq	%rdx, %rcx
	adcxq	%rsi, %rax
	adoxq	%rsi, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rdi
	adcxq	%rbx, %r10
	MULXq	%r11, %rbx, %r11
	adoxq	%rbx, %r10
	adcxq	%r11, %r9
	MULXq	%rcx, %r11, %rcx
	adoxq	%r11, %r9
	adcxq	%rcx, %r8
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r8
	adcxq	%rsi, %rax
	adoxq	%rsi, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rdi
	adcq	%rsi, %r10
	adcq	%rsi, %r9
	adcq	%rsi, %r8
	sbbq	%rsi, %rsi
	andq	$38, %rsi
	addq	%rsi, %rdi
	xorq	%r11, %r11
	movq	%rdi, %rdx
	MULXq	%rdx, %rax, %rbx
	MULXq	%r10, %rsi, %rcx
	MULXq	%r9, %rbp, %rdi
	adcxq	%rbp, %rcx
	MULXq	%r8, %rdx, %rbp
	adcxq	%rdx, %rdi
	movq	%r10, %rdx
	MULXq	%r9, %r12, %r10
	adoxq	%r12, %rdi
	adcxq	%r10, %rbp
	MULXq	%r8, %r12, %r10
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r9, %rdx
	MULXq	%r8, %r14, %r9
	adcxq	%r14, %r10
	adoxq	%r11, %r10
	adcxq	%r11, %r9
	adoxq	%r11, %r9
	MULXq	%rdx, %r15, %r14
	movq	%r8, %rdx
	MULXq	%rdx, %rdx, %r8
	adcxq	%rsi, %rsi
	adoxq	%rbx, %rsi
	adcxq	%rcx, %rcx
	adoxq	%r13, %rcx
	adcxq	%rdi, %rdi
	adoxq	%r12, %rdi
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r10, %r10
	adoxq	%r14, %r10
	adcxq	%r9, %r9
	adoxq	%rdx, %r9
	adcxq	%r11, %r8
	adoxq	%r11, %r8
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rax
	adcxq	%rbx, %rsi
	MULXq	%r10, %rbx, %r10
	adoxq	%rbx, %rsi
	adcxq	%r10, %rcx
	MULXq	%r9, %r10, %r9
	adoxq	%r10, %rcx
	adcxq	%r9, %rdi
	MULXq	%r8, %r8, %rdx
	adoxq	%r8, %rdi
	adcxq	%r11, %rdx
	adoxq	%r11, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rax
	adcq	%r11, %rsi
	adcq	%r11, %rcx
	adcq	%r11, %rdi
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rax
	xorq	%r11, %r11
	movq	120(%rsp), %rdx
	MULXq	%rax, %rbx, %r8
	MULXq	%rsi, %r10, %r9
	adcxq	%r10, %r8
	MULXq	%rcx, %rbp, %r10
	adcxq	%rbp, %r9
	MULXq	%rdi, %rdx, %rbp
	adcxq	%rdx, %r10
	adcxq	%r11, %rbp
	movq	128(%rsp), %rdx
	MULXq	%rax, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %r9
	MULXq	%rsi, %r13, %r12
	adoxq	%r13, %r9
	adcxq	%r12, %r10
	MULXq	%rcx, %r13, %r12
	adoxq	%r13, %r10
	adcxq	%r12, %rbp
	MULXq	%rdi, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%r11, %r12
	adoxq	%r11, %r12
	movq	136(%rsp), %rdx
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %r9
	adcxq	%r13, %r10
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %r10
	adcxq	%r13, %rbp
	MULXq	%rcx, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rdi, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%r11, %r13
	adoxq	%r11, %r13
	movq	144(%rsp), %rdx
	MULXq	%rax, %r14, %rax
	adoxq	%r14, %r10
	adcxq	%rax, %rbp
	MULXq	%rsi, %rsi, %rax
	adoxq	%rsi, %rbp
	adcxq	%rax, %r12
	MULXq	%rcx, %rcx, %rax
	adoxq	%rcx, %r12
	adcxq	%rax, %r13
	MULXq	%rdi, %rcx, %rax
	adoxq	%rcx, %r13
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rsi, %rcx
	adoxq	%rsi, %rbx
	adcxq	%rcx, %r8
	MULXq	%r12, %rsi, %rcx
	adoxq	%rsi, %r8
	adcxq	%rcx, %r9
	MULXq	%r13, %rsi, %rcx
	adoxq	%rsi, %r9
	adcxq	%rcx, %r10
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r10
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rbx
	adcq	%r11, %r8
	adcq	%r11, %r9
	adcq	%r11, %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rbx
	movq	%rbx, 120(%rsp)
	movq	%r8, 128(%rsp)
	movq	%r9, 136(%rsp)
	movq	%r10, 144(%rsp)
	xorq	%rcx, %rcx
	movq	88(%rsp), %rdx
	MULXq	%rbx, %rsi, %r11
	MULXq	%r8, %rax, %rbp
	adcxq	%rax, %r11
	MULXq	%r9, %rdi, %rax
	adcxq	%rdi, %rbp
	MULXq	%r10, %rdx, %rdi
	adcxq	%rdx, %rax
	adcxq	%rcx, %rdi
	movq	96(%rsp), %rdx
	MULXq	%rbx, %r13, %r12
	adoxq	%r13, %r11
	adcxq	%r12, %rbp
	MULXq	%r8, %r13, %r12
	adoxq	%r13, %rbp
	adcxq	%r12, %rax
	MULXq	%r9, %r13, %r12
	adoxq	%r13, %rax
	adcxq	%r12, %rdi
	MULXq	%r10, %rdx, %r12
	adoxq	%rdx, %rdi
	adcxq	%rcx, %r12
	adoxq	%rcx, %r12
	movq	104(%rsp), %rdx
	MULXq	%rbx, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %rax
	MULXq	%r8, %r14, %r13
	adoxq	%r14, %rax
	adcxq	%r13, %rdi
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %rdi
	adcxq	%r13, %r12
	MULXq	%r10, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rcx, %r13
	adoxq	%rcx, %r13
	movq	112(%rsp), %rdx
	MULXq	%rbx, %r14, %rbx
	adoxq	%r14, %rax
	adcxq	%rbx, %rdi
	MULXq	%r8, %rbx, %r8
	adoxq	%rbx, %rdi
	adcxq	%r8, %r12
	MULXq	%r9, %r9, %r8
	adoxq	%r9, %r12
	adcxq	%r8, %r13
	MULXq	%r10, %rdx, %r8
	adoxq	%rdx, %r13
	adcxq	%rcx, %r8
	adoxq	%rcx, %r8
	movq	$38, %rdx
	MULXq	%rdi, %r9, %rdi
	adoxq	%r9, %rsi
	adcxq	%rdi, %r11
	MULXq	%r12, %r9, %rdi
	adoxq	%r9, %r11
	adcxq	%rdi, %rbp
	MULXq	%r13, %r9, %rdi
	adoxq	%r9, %rbp
	adcxq	%rdi, %rax
	MULXq	%r8, %rdi, %rdx
	adoxq	%rdi, %rax
	adcxq	%rcx, %rdx
	adoxq	%rcx, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rsi
	adcq	%rcx, %r11
	adcq	%rcx, %rbp
	adcq	%rcx, %rax
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	addq	%rcx, %rsi
	movq	%rsi, 88(%rsp)
	movq	%r11, 96(%rsp)
	movq	%rbp, 104(%rsp)
	movq	%rax, 112(%rsp)
	xorq	%r8, %r8
	movq	%rsi, %rdx
	MULXq	%rdx, %rcx, %r10
	MULXq	%r11, %rdi, %rsi
	MULXq	%rbp, %rbx, %r9
	adcxq	%rbx, %rsi
	MULXq	%rax, %rdx, %rbx
	adcxq	%rdx, %r9
	movq	%r11, %rdx
	MULXq	%rbp, %r12, %r11
	adoxq	%r12, %r9
	adcxq	%r11, %rbx
	MULXq	%rax, %r12, %r11
	adoxq	%r12, %rbx
	MULXq	%rdx, %r13, %r12
	movq	%rbp, %rdx
	MULXq	%rax, %r14, %rbp
	adcxq	%r14, %r11
	adoxq	%r8, %r11
	adcxq	%r8, %rbp
	adoxq	%r8, %rbp
	MULXq	%rdx, %r15, %r14
	movq	%rax, %rdx
	MULXq	%rdx, %rdx, %rax
	adcxq	%rdi, %rdi
	adoxq	%r10, %rdi
	adcxq	%rsi, %rsi
	adoxq	%r13, %rsi
	adcxq	%r9, %r9
	adoxq	%r12, %r9
	adcxq	%rbx, %rbx
	adoxq	%r15, %rbx
	adcxq	%r11, %r11
	adoxq	%r14, %r11
	adcxq	%rbp, %rbp
	adoxq	%rdx, %rbp
	adcxq	%r8, %rax
	adoxq	%r8, %rax
	movq	$38, %rdx
	MULXq	%rbx, %rbx, %r10
	adoxq	%rbx, %rcx
	adcxq	%r10, %rdi
	MULXq	%r11, %r11, %r10
	adoxq	%r11, %rdi
	adcxq	%r10, %rsi
	MULXq	%rbp, %r11, %r10
	adoxq	%r11, %rsi
	adcxq	%r10, %r9
	MULXq	%rax, %rdx, %rax
	adoxq	%rdx, %r9
	adcxq	%r8, %rax
	adoxq	%r8, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rcx
	adcq	%r8, %rdi
	adcq	%r8, %rsi
	adcq	%r8, %r9
	sbbq	%r8, %r8
	andq	$38, %r8
	addq	%r8, %rcx
	xorq	%rax, %rax
	movq	120(%rsp), %rdx
	MULXq	%rcx, %rbx, %r10
	MULXq	%rdi, %r8, %r11
	adcxq	%r8, %r10
	MULXq	%rsi, %rbp, %r8
	adcxq	%rbp, %r11
	MULXq	%r9, %rdx, %rbp
	adcxq	%rdx, %r8
	adcxq	%rax, %rbp
	movq	128(%rsp), %rdx
	MULXq	%rcx, %r13, %r12
	adoxq	%r13, %r10
	adcxq	%r12, %r11
	MULXq	%rdi, %r13, %r12
	adoxq	%r13, %r11
	adcxq	%r12, %r8
	MULXq	%rsi, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %rbp
	MULXq	%r9, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rax, %r12
	adoxq	%rax, %r12
	movq	136(%rsp), %rdx
	MULXq	%rcx, %r14, %r13
	adoxq	%r14, %r11
	adcxq	%r13, %r8
	MULXq	%rdi, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %rbp
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%r9, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	movq	144(%rsp), %rdx
	MULXq	%rcx, %r14, %rcx
	adoxq	%r14, %r8
	adcxq	%rcx, %rbp
	MULXq	%rdi, %rdi, %rcx
	adoxq	%rdi, %rbp
	adcxq	%rcx, %r12
	MULXq	%rsi, %rsi, %rcx
	adoxq	%rsi, %r12
	adcxq	%rcx, %r13
	MULXq	%r9, %rdx, %rcx
	adoxq	%rdx, %r13
	adcxq	%rax, %rcx
	adoxq	%rax, %rcx
	movq	$38, %rdx
	MULXq	%rbp, %rdi, %rsi
	adoxq	%rdi, %rbx
	adcxq	%rsi, %r10
	MULXq	%r12, %rdi, %rsi
	adoxq	%rdi, %r10
	adcxq	%rsi, %r11
	MULXq	%r13, %rdi, %rsi
	adoxq	%rdi, %r11
	adcxq	%rsi, %r8
	MULXq	%rcx, %rdx, %rcx
	adoxq	%rdx, %r8
	adcxq	%rax, %rcx
	adoxq	%rax, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rbx
	adcq	%rax, %r10
	adcq	%rax, %r11
	adcq	%rax, %r8
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rbx
	movq	%rbx, 120(%rsp)
	movq	%r10, 128(%rsp)
	movq	%r11, 136(%rsp)
	movq	%r8, 144(%rsp)
	xorq	%r9, %r9
	movq	%rbx, %rdx
	MULXq	%rdx, %rdi, %rbx
	MULXq	%r10, %rsi, %rax
	MULXq	%r11, %rbp, %rcx
	adcxq	%rbp, %rax
	MULXq	%r8, %rdx, %rbp
	adcxq	%rdx, %rcx
	movq	%r10, %rdx
	MULXq	%r11, %r12, %r10
	adoxq	%r12, %rcx
	adcxq	%r10, %rbp
	MULXq	%r8, %r12, %r10
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r11, %rdx
	MULXq	%r8, %r14, %r11
	adcxq	%r14, %r10
	adoxq	%r9, %r10
	adcxq	%r9, %r11
	adoxq	%r9, %r11
	MULXq	%rdx, %r15, %r14
	movq	%r8, %rdx
	MULXq	%rdx, %rdx, %r8
	adcxq	%rsi, %rsi
	adoxq	%rbx, %rsi
	adcxq	%rax, %rax
	adoxq	%r13, %rax
	adcxq	%rcx, %rcx
	adoxq	%r12, %rcx
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r10, %r10
	adoxq	%r14, %r10
	adcxq	%r11, %r11
	adoxq	%rdx, %r11
	adcxq	%r9, %r8
	adoxq	%r9, %r8
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rdi
	adcxq	%rbx, %rsi
	MULXq	%r10, %rbx, %r10
	adoxq	%rbx, %rsi
	adcxq	%r10, %rax
	MULXq	%r11, %r11, %r10
	adoxq	%r11, %rax
	adcxq	%r10, %rcx
	MULXq	%r8, %r8, %rdx
	adoxq	%r8, %rcx
	adcxq	%r9, %rdx
	adoxq	%r9, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rdi
	adcq	%r9, %rsi
	adcq	%r9, %rax
	adcq	%r9, %rcx
	sbbq	%r9, %r9
	andq	$38, %r9
	addq	%r9, %rdi
	movl	$2, %edx
Ljade_scalarmult_curve25519_amd64_mulx_base$8:
	movl	%edx, 344(%rsp)
	xorq	%r11, %r11
	movq	%rdi, %rdx
	MULXq	%rdx, %rdi, %rbx
	MULXq	%rsi, %r9, %r8
	MULXq	%rax, %rbp, %r10
	adcxq	%rbp, %r8
	MULXq	%rcx, %rdx, %rbp
	adcxq	%rdx, %r10
	movq	%rsi, %rdx
	MULXq	%rax, %r12, %rsi
	adoxq	%r12, %r10
	adcxq	%rsi, %rbp
	MULXq	%rcx, %r12, %rsi
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rax, %rdx
	MULXq	%rcx, %r14, %rax
	adcxq	%r14, %rsi
	adoxq	%r11, %rsi
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	MULXq	%rdx, %r15, %r14
	movq	%rcx, %rdx
	MULXq	%rdx, %rdx, %rcx
	adcxq	%r9, %r9
	adoxq	%rbx, %r9
	adcxq	%r8, %r8
	adoxq	%r13, %r8
	adcxq	%r10, %r10
	adoxq	%r12, %r10
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rsi, %rsi
	adoxq	%r14, %rsi
	adcxq	%rax, %rax
	adoxq	%rdx, %rax
	adcxq	%r11, %rcx
	adoxq	%r11, %rcx
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rdi
	adcxq	%rbx, %r9
	MULXq	%rsi, %rbx, %rsi
	adoxq	%rbx, %r9
	adcxq	%rsi, %r8
	MULXq	%rax, %rsi, %rax
	adoxq	%rsi, %r8
	adcxq	%rax, %r10
	MULXq	%rcx, %rcx, %rax
	adoxq	%rcx, %r10
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rdi
	adcq	%r11, %r9
	adcq	%r11, %r8
	adcq	%r11, %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdi
	xorq	%r11, %r11
	movq	%rdi, %rdx
	MULXq	%rdx, %rdi, %rbx
	MULXq	%r9, %rsi, %rax
	MULXq	%r8, %rbp, %rcx
	adcxq	%rbp, %rax
	MULXq	%r10, %rdx, %rbp
	adcxq	%rdx, %rcx
	movq	%r9, %rdx
	MULXq	%r8, %r12, %r9
	adoxq	%r12, %rcx
	adcxq	%r9, %rbp
	MULXq	%r10, %r12, %r9
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r8, %rdx
	MULXq	%r10, %r14, %r8
	adcxq	%r14, %r9
	adoxq	%r11, %r9
	adcxq	%r11, %r8
	adoxq	%r11, %r8
	MULXq	%rdx, %r15, %r14
	movq	%r10, %rdx
	MULXq	%rdx, %rdx, %r10
	adcxq	%rsi, %rsi
	adoxq	%rbx, %rsi
	adcxq	%rax, %rax
	adoxq	%r13, %rax
	adcxq	%rcx, %rcx
	adoxq	%r12, %rcx
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r9, %r9
	adoxq	%r14, %r9
	adcxq	%r8, %r8
	adoxq	%rdx, %r8
	adcxq	%r11, %r10
	adoxq	%r11, %r10
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rdi
	adcxq	%rbx, %rsi
	MULXq	%r9, %rbx, %r9
	adoxq	%rbx, %rsi
	adcxq	%r9, %rax
	MULXq	%r8, %r9, %r8
	adoxq	%r9, %rax
	adcxq	%r8, %rcx
	MULXq	%r10, %r8, %rdx
	adoxq	%r8, %rcx
	adcxq	%r11, %rdx
	adoxq	%r11, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rdi
	adcq	%r11, %rsi
	adcq	%r11, %rax
	adcq	%r11, %rcx
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdi
	movl	344(%rsp), %edx
	decl	%edx
	jne 	Ljade_scalarmult_curve25519_amd64_mulx_base$8
	xorq	%r10, %r10
	movq	120(%rsp), %rdx
	MULXq	%rdi, %r12, %r8
	MULXq	%rsi, %r9, %r11
	adcxq	%r9, %r8
	MULXq	%rax, %rbx, %r9
	adcxq	%rbx, %r11
	MULXq	%rcx, %rdx, %rbx
	adcxq	%rdx, %r9
	adcxq	%r10, %rbx
	movq	128(%rsp), %rdx
	MULXq	%rdi, %r13, %rbp
	adoxq	%r13, %r8
	adcxq	%rbp, %r11
	MULXq	%rsi, %r13, %rbp
	adoxq	%r13, %r11
	adcxq	%rbp, %r9
	MULXq	%rax, %r13, %rbp
	adoxq	%r13, %r9
	adcxq	%rbp, %rbx
	MULXq	%rcx, %rdx, %rbp
	adoxq	%rdx, %rbx
	adcxq	%r10, %rbp
	adoxq	%r10, %rbp
	movq	136(%rsp), %rdx
	MULXq	%rdi, %r14, %r13
	adoxq	%r14, %r11
	adcxq	%r13, %r9
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %r9
	adcxq	%r13, %rbx
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %rbx
	adcxq	%r13, %rbp
	MULXq	%rcx, %rdx, %r13
	adoxq	%rdx, %rbp
	adcxq	%r10, %r13
	adoxq	%r10, %r13
	movq	144(%rsp), %rdx
	MULXq	%rdi, %r14, %rdi
	adoxq	%r14, %r9
	adcxq	%rdi, %rbx
	MULXq	%rsi, %rdi, %rsi
	adoxq	%rdi, %rbx
	adcxq	%rsi, %rbp
	MULXq	%rax, %rsi, %rax
	adoxq	%rsi, %rbp
	adcxq	%rax, %r13
	MULXq	%rcx, %rcx, %rax
	adoxq	%rcx, %r13
	adcxq	%r10, %rax
	adoxq	%r10, %rax
	movq	$38, %rdx
	MULXq	%rbx, %rsi, %rcx
	adoxq	%rsi, %r12
	adcxq	%rcx, %r8
	MULXq	%rbp, %rsi, %rcx
	adoxq	%rsi, %r8
	adcxq	%rcx, %r11
	MULXq	%r13, %rsi, %rcx
	adoxq	%rsi, %r11
	adcxq	%rcx, %r9
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r9
	adcxq	%r10, %rax
	adoxq	%r10, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	adcq	%r10, %r8
	adcq	%r10, %r11
	adcq	%r10, %r9
	sbbq	%r10, %r10
	andq	$38, %r10
	addq	%r10, %r12
	movq	%r12, 120(%rsp)
	movq	%r8, 128(%rsp)
	movq	%r11, 136(%rsp)
	movq	%r9, 144(%rsp)
	movl	$5, %eax
Ljade_scalarmult_curve25519_amd64_mulx_base$7:
	movl	%eax, 344(%rsp)
	xorq	%rdi, %rdi
	movq	%r12, %rdx
	MULXq	%rdx, %r10, %rbx
	MULXq	%r8, %rcx, %rax
	MULXq	%r11, %rbp, %rsi
	adcxq	%rbp, %rax
	MULXq	%r9, %rdx, %rbp
	adcxq	%rdx, %rsi
	movq	%r8, %rdx
	MULXq	%r11, %r12, %r8
	adoxq	%r12, %rsi
	adcxq	%r8, %rbp
	MULXq	%r9, %r12, %r8
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r11, %rdx
	MULXq	%r9, %r14, %r11
	adcxq	%r14, %r8
	adoxq	%rdi, %r8
	adcxq	%rdi, %r11
	adoxq	%rdi, %r11
	MULXq	%rdx, %r15, %r14
	movq	%r9, %rdx
	MULXq	%rdx, %rdx, %r9
	adcxq	%rcx, %rcx
	adoxq	%rbx, %rcx
	adcxq	%rax, %rax
	adoxq	%r13, %rax
	adcxq	%rsi, %rsi
	adoxq	%r12, %rsi
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r8, %r8
	adoxq	%r14, %r8
	adcxq	%r11, %r11
	adoxq	%rdx, %r11
	adcxq	%rdi, %r9
	adoxq	%rdi, %r9
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r10
	adcxq	%rbx, %rcx
	MULXq	%r8, %rbx, %r8
	adoxq	%rbx, %rcx
	adcxq	%r8, %rax
	MULXq	%r11, %r11, %r8
	adoxq	%r11, %rax
	adcxq	%r8, %rsi
	MULXq	%r9, %r8, %rdx
	adoxq	%r8, %rsi
	adcxq	%rdi, %rdx
	adoxq	%rdi, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %r10
	adcq	%rdi, %rcx
	adcq	%rdi, %rax
	adcq	%rdi, %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %r10
	xorq	%rdi, %rdi
	movq	%r10, %rdx
	MULXq	%rdx, %r12, %r10
	MULXq	%rcx, %r8, %r11
	MULXq	%rax, %rbx, %r9
	adcxq	%rbx, %r11
	MULXq	%rsi, %rdx, %rbx
	adcxq	%rdx, %r9
	movq	%rcx, %rdx
	MULXq	%rax, %rbp, %rcx
	adoxq	%rbp, %r9
	adcxq	%rcx, %rbx
	MULXq	%rsi, %rbp, %rcx
	adoxq	%rbp, %rbx
	MULXq	%rdx, %r13, %rbp
	movq	%rax, %rdx
	MULXq	%rsi, %r14, %rax
	adcxq	%r14, %rcx
	adoxq	%rdi, %rcx
	adcxq	%rdi, %rax
	adoxq	%rdi, %rax
	MULXq	%rdx, %r15, %r14
	movq	%rsi, %rdx
	MULXq	%rdx, %rdx, %rsi
	adcxq	%r8, %r8
	adoxq	%r10, %r8
	adcxq	%r11, %r11
	adoxq	%r13, %r11
	adcxq	%r9, %r9
	adoxq	%rbp, %r9
	adcxq	%rbx, %rbx
	adoxq	%r15, %rbx
	adcxq	%rcx, %rcx
	adoxq	%r14, %rcx
	adcxq	%rax, %rax
	adoxq	%rdx, %rax
	adcxq	%rdi, %rsi
	adoxq	%rdi, %rsi
	movq	$38, %rdx
	MULXq	%rbx, %rbx, %r10
	adoxq	%rbx, %r12
	adcxq	%r10, %r8
	MULXq	%rcx, %r10, %rcx
	adoxq	%r10, %r8
	adcxq	%rcx, %r11
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r11
	adcxq	%rax, %r9
	MULXq	%rsi, %rcx, %rax
	adoxq	%rcx, %r9
	adcxq	%rdi, %rax
	adoxq	%rdi, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r12
	adcq	%rdi, %r8
	adcq	%rdi, %r11
	adcq	%rdi, %r9
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %r12
	movl	344(%rsp), %eax
	decl	%eax
	jne 	Ljade_scalarmult_curve25519_amd64_mulx_base$7
	xorq	%rax, %rax
	movq	120(%rsp), %rdx
	MULXq	%r12, %rbp, %rbx
	MULXq	%r8, %rcx, %r10
	adcxq	%rcx, %rbx
	MULXq	%r11, %rsi, %rcx
	adcxq	%rsi, %r10
	MULXq	%r9, %rdx, %rsi
	adcxq	%rdx, %rcx
	adcxq	%rax, %rsi
	movq	128(%rsp), %rdx
	MULXq	%r12, %r13, %rdi
	adoxq	%r13, %rbx
	adcxq	%rdi, %r10
	MULXq	%r8, %r13, %rdi
	adoxq	%r13, %r10
	adcxq	%rdi, %rcx
	MULXq	%r11, %r13, %rdi
	adoxq	%r13, %rcx
	adcxq	%rdi, %rsi
	MULXq	%r9, %rdx, %rdi
	adoxq	%rdx, %rsi
	adcxq	%rax, %rdi
	adoxq	%rax, %rdi
	movq	136(%rsp), %rdx
	MULXq	%r12, %r14, %r13
	adoxq	%r14, %r10
	adcxq	%r13, %rcx
	MULXq	%r8, %r14, %r13
	adoxq	%r14, %rcx
	adcxq	%r13, %rsi
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %rsi
	adcxq	%r13, %rdi
	MULXq	%r9, %rdx, %r13
	adoxq	%rdx, %rdi
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	movq	144(%rsp), %rdx
	MULXq	%r12, %r14, %r12
	adoxq	%r14, %rcx
	adcxq	%r12, %rsi
	MULXq	%r8, %r12, %r8
	adoxq	%r12, %rsi
	adcxq	%r8, %rdi
	MULXq	%r11, %r11, %r8
	adoxq	%r11, %rdi
	adcxq	%r8, %r13
	MULXq	%r9, %rdx, %r8
	adoxq	%rdx, %r13
	adcxq	%rax, %r8
	adoxq	%rax, %r8
	movq	$38, %rdx
	MULXq	%rsi, %r9, %rsi
	adoxq	%r9, %rbp
	adcxq	%rsi, %rbx
	MULXq	%rdi, %rdi, %rsi
	adoxq	%rdi, %rbx
	adcxq	%rsi, %r10
	MULXq	%r13, %rdi, %rsi
	adoxq	%rdi, %r10
	adcxq	%rsi, %rcx
	MULXq	%r8, %rsi, %rdx
	adoxq	%rsi, %rcx
	adcxq	%rax, %rdx
	adoxq	%rax, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rbp
	adcq	%rax, %rbx
	adcq	%rax, %r10
	adcq	%rax, %rcx
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rbp
	movq	%rbp, 152(%rsp)
	movq	%rbx, 160(%rsp)
	movq	%r10, 168(%rsp)
	movq	%rcx, 176(%rsp)
	movl	$10, %eax
Ljade_scalarmult_curve25519_amd64_mulx_base$6:
	movl	%eax, 344(%rsp)
	xorq	%r8, %r8
	movq	%rbp, %rdx
	MULXq	%rdx, %r9, %r11
	MULXq	%rbx, %rsi, %rax
	MULXq	%r10, %rbp, %rdi
	adcxq	%rbp, %rax
	MULXq	%rcx, %rdx, %rbp
	adcxq	%rdx, %rdi
	movq	%rbx, %rdx
	MULXq	%r10, %r12, %rbx
	adoxq	%r12, %rdi
	adcxq	%rbx, %rbp
	MULXq	%rcx, %r12, %rbx
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r10, %rdx
	MULXq	%rcx, %r14, %r10
	adcxq	%r14, %rbx
	adoxq	%r8, %rbx
	adcxq	%r8, %r10
	adoxq	%r8, %r10
	MULXq	%rdx, %r15, %r14
	movq	%rcx, %rdx
	MULXq	%rdx, %rdx, %rcx
	adcxq	%rsi, %rsi
	adoxq	%r11, %rsi
	adcxq	%rax, %rax
	adoxq	%r13, %rax
	adcxq	%rdi, %rdi
	adoxq	%r12, %rdi
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rbx, %rbx
	adoxq	%r14, %rbx
	adcxq	%r10, %r10
	adoxq	%rdx, %r10
	adcxq	%r8, %rcx
	adoxq	%r8, %rcx
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %r11
	adoxq	%rbp, %r9
	adcxq	%r11, %rsi
	MULXq	%rbx, %rbx, %r11
	adoxq	%rbx, %rsi
	adcxq	%r11, %rax
	MULXq	%r10, %r11, %r10
	adoxq	%r11, %rax
	adcxq	%r10, %rdi
	MULXq	%rcx, %rdx, %rcx
	adoxq	%rdx, %rdi
	adcxq	%r8, %rcx
	adoxq	%r8, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %r9
	adcq	%r8, %rsi
	adcq	%r8, %rax
	adcq	%r8, %rdi
	sbbq	%r8, %r8
	andq	$38, %r8
	addq	%r8, %r9
	xorq	%r8, %r8
	movq	%r9, %rdx
	MULXq	%rdx, %rbp, %r9
	MULXq	%rsi, %rbx, %r10
	MULXq	%rax, %r11, %rcx
	adcxq	%r11, %r10
	MULXq	%rdi, %rdx, %r11
	adcxq	%rdx, %rcx
	movq	%rsi, %rdx
	MULXq	%rax, %r12, %rsi
	adoxq	%r12, %rcx
	adcxq	%rsi, %r11
	MULXq	%rdi, %r12, %rsi
	adoxq	%r12, %r11
	MULXq	%rdx, %r13, %r12
	movq	%rax, %rdx
	MULXq	%rdi, %r14, %rax
	adcxq	%r14, %rsi
	adoxq	%r8, %rsi
	adcxq	%r8, %rax
	adoxq	%r8, %rax
	MULXq	%rdx, %r15, %r14
	movq	%rdi, %rdx
	MULXq	%rdx, %rdx, %rdi
	adcxq	%rbx, %rbx
	adoxq	%r9, %rbx
	adcxq	%r10, %r10
	adoxq	%r13, %r10
	adcxq	%rcx, %rcx
	adoxq	%r12, %rcx
	adcxq	%r11, %r11
	adoxq	%r15, %r11
	adcxq	%rsi, %rsi
	adoxq	%r14, %rsi
	adcxq	%rax, %rax
	adoxq	%rdx, %rax
	adcxq	%r8, %rdi
	adoxq	%r8, %rdi
	movq	$38, %rdx
	MULXq	%r11, %r11, %r9
	adoxq	%r11, %rbp
	adcxq	%r9, %rbx
	MULXq	%rsi, %r9, %rsi
	adoxq	%r9, %rbx
	adcxq	%rsi, %r10
	MULXq	%rax, %rsi, %rax
	adoxq	%rsi, %r10
	adcxq	%rax, %rcx
	MULXq	%rdi, %rdx, %rax
	adoxq	%rdx, %rcx
	adcxq	%r8, %rax
	adoxq	%r8, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rbp
	adcq	%r8, %rbx
	adcq	%r8, %r10
	adcq	%r8, %rcx
	sbbq	%r8, %r8
	andq	$38, %r8
	addq	%r8, %rbp
	movl	344(%rsp), %eax
	decl	%eax
	jne 	Ljade_scalarmult_curve25519_amd64_mulx_base$6
	xorq	%r9, %r9
	movq	152(%rsp), %rdx
	MULXq	%rbp, %rdi, %rax
	MULXq	%rbx, %r8, %rsi
	adcxq	%r8, %rax
	MULXq	%r10, %r11, %r8
	adcxq	%r11, %rsi
	MULXq	%rcx, %rdx, %r11
	adcxq	%rdx, %r8
	adcxq	%r9, %r11
	movq	160(%rsp), %rdx
	MULXq	%rbp, %r13, %r12
	adoxq	%r13, %rax
	adcxq	%r12, %rsi
	MULXq	%rbx, %r13, %r12
	adoxq	%r13, %rsi
	adcxq	%r12, %r8
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %r11
	MULXq	%rcx, %rdx, %r12
	adoxq	%rdx, %r11
	adcxq	%r9, %r12
	adoxq	%r9, %r12
	movq	168(%rsp), %rdx
	MULXq	%rbp, %r14, %r13
	adoxq	%r14, %rsi
	adcxq	%r13, %r8
	MULXq	%rbx, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %r11
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %r11
	adcxq	%r13, %r12
	MULXq	%rcx, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%r9, %r13
	adoxq	%r9, %r13
	movq	176(%rsp), %rdx
	MULXq	%rbp, %r14, %rbp
	adoxq	%r14, %r8
	adcxq	%rbp, %r11
	MULXq	%rbx, %rbp, %rbx
	adoxq	%rbp, %r11
	adcxq	%rbx, %r12
	MULXq	%r10, %rbx, %r10
	adoxq	%rbx, %r12
	adcxq	%r10, %r13
	MULXq	%rcx, %rdx, %rcx
	adoxq	%rdx, %r13
	adcxq	%r9, %rcx
	adoxq	%r9, %rcx
	movq	$38, %rdx
	MULXq	%r11, %r11, %r10
	adoxq	%r11, %rdi
	adcxq	%r10, %rax
	MULXq	%r12, %r11, %r10
	adoxq	%r11, %rax
	adcxq	%r10, %rsi
	MULXq	%r13, %r11, %r10
	adoxq	%r11, %rsi
	adcxq	%r10, %r8
	MULXq	%rcx, %rdx, %rcx
	adoxq	%rdx, %r8
	adcxq	%r9, %rcx
	adoxq	%r9, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rdi
	adcq	%r9, %rax
	adcq	%r9, %rsi
	adcq	%r9, %r8
	sbbq	%r9, %r9
	andq	$38, %r9
	addq	%r9, %rdi
	movl	$5, %ecx
Ljade_scalarmult_curve25519_amd64_mulx_base$5:
	movl	%ecx, 344(%rsp)
	xorq	%r11, %r11
	movq	%rdi, %rdx
	MULXq	%rdx, %rdi, %rbx
	MULXq	%rax, %r9, %rcx
	MULXq	%rsi, %rbp, %r10
	adcxq	%rbp, %rcx
	MULXq	%r8, %rdx, %rbp
	adcxq	%rdx, %r10
	movq	%rax, %rdx
	MULXq	%rsi, %r12, %rax
	adoxq	%r12, %r10
	adcxq	%rax, %rbp
	MULXq	%r8, %r12, %rax
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rsi, %rdx
	MULXq	%r8, %r14, %rsi
	adcxq	%r14, %rax
	adoxq	%r11, %rax
	adcxq	%r11, %rsi
	adoxq	%r11, %rsi
	MULXq	%rdx, %r15, %r14
	movq	%r8, %rdx
	MULXq	%rdx, %rdx, %r8
	adcxq	%r9, %r9
	adoxq	%rbx, %r9
	adcxq	%rcx, %rcx
	adoxq	%r13, %rcx
	adcxq	%r10, %r10
	adoxq	%r12, %r10
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rax, %rax
	adoxq	%r14, %rax
	adcxq	%rsi, %rsi
	adoxq	%rdx, %rsi
	adcxq	%r11, %r8
	adoxq	%r11, %r8
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rdi
	adcxq	%rbx, %r9
	MULXq	%rax, %rbx, %rax
	adoxq	%rbx, %r9
	adcxq	%rax, %rcx
	MULXq	%rsi, %rsi, %rax
	adoxq	%rsi, %rcx
	adcxq	%rax, %r10
	MULXq	%r8, %rdx, %rax
	adoxq	%rdx, %r10
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rdi
	adcq	%r11, %r9
	adcq	%r11, %rcx
	adcq	%r11, %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdi
	xorq	%r11, %r11
	movq	%rdi, %rdx
	MULXq	%rdx, %rdi, %rbx
	MULXq	%r9, %rax, %rsi
	MULXq	%rcx, %rbp, %r8
	adcxq	%rbp, %rsi
	MULXq	%r10, %rdx, %rbp
	adcxq	%rdx, %r8
	movq	%r9, %rdx
	MULXq	%rcx, %r12, %r9
	adoxq	%r12, %r8
	adcxq	%r9, %rbp
	MULXq	%r10, %r12, %r9
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rcx, %rdx
	MULXq	%r10, %r14, %rcx
	adcxq	%r14, %r9
	adoxq	%r11, %r9
	adcxq	%r11, %rcx
	adoxq	%r11, %rcx
	MULXq	%rdx, %r15, %r14
	movq	%r10, %rdx
	MULXq	%rdx, %rdx, %r10
	adcxq	%rax, %rax
	adoxq	%rbx, %rax
	adcxq	%rsi, %rsi
	adoxq	%r13, %rsi
	adcxq	%r8, %r8
	adoxq	%r12, %r8
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r9, %r9
	adoxq	%r14, %r9
	adcxq	%rcx, %rcx
	adoxq	%rdx, %rcx
	adcxq	%r11, %r10
	adoxq	%r11, %r10
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rdi
	adcxq	%rbx, %rax
	MULXq	%r9, %rbx, %r9
	adoxq	%rbx, %rax
	adcxq	%r9, %rsi
	MULXq	%rcx, %r9, %rcx
	adoxq	%r9, %rsi
	adcxq	%rcx, %r8
	MULXq	%r10, %rdx, %rcx
	adoxq	%rdx, %r8
	adcxq	%r11, %rcx
	adoxq	%r11, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rdi
	adcq	%r11, %rax
	adcq	%r11, %rsi
	adcq	%r11, %r8
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdi
	movl	344(%rsp), %ecx
	decl	%ecx
	jne 	Ljade_scalarmult_curve25519_amd64_mulx_base$5
	xorq	%rcx, %rcx
	movq	120(%rsp), %rdx
	MULXq	%rdi, %rbx, %r9
	MULXq	%rax, %r11, %r10
	adcxq	%r11, %r9
	MULXq	%rsi, %rbp, %r11
	adcxq	%rbp, %r10
	MULXq	%r8, %rdx, %rbp
	adcxq	%rdx, %r11
	adcxq	%rcx, %rbp
	movq	128(%rsp), %rdx
	MULXq	%rdi, %r13, %r12
	adoxq	%r13, %r9
	adcxq	%r12, %r10
	MULXq	%rax, %r13, %r12
	adoxq	%r13, %r10
	adcxq	%r12, %r11
	MULXq	%rsi, %r13, %r12
	adoxq	%r13, %r11
	adcxq	%r12, %rbp
	MULXq	%r8, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rcx, %r12
	adoxq	%rcx, %r12
	movq	136(%rsp), %rdx
	MULXq	%rdi, %r14, %r13
	adoxq	%r14, %r10
	adcxq	%r13, %r11
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %r11
	adcxq	%r13, %rbp
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%r8, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rcx, %r13
	adoxq	%rcx, %r13
	movq	144(%rsp), %rdx
	MULXq	%rdi, %r14, %rdi
	adoxq	%r14, %r11
	adcxq	%rdi, %rbp
	MULXq	%rax, %rdi, %rax
	adoxq	%rdi, %rbp
	adcxq	%rax, %r12
	MULXq	%rsi, %rsi, %rax
	adoxq	%rsi, %r12
	adcxq	%rax, %r13
	MULXq	%r8, %rdx, %rax
	adoxq	%rdx, %r13
	adcxq	%rcx, %rax
	adoxq	%rcx, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rdi, %rsi
	adoxq	%rdi, %rbx
	adcxq	%rsi, %r9
	MULXq	%r12, %rdi, %rsi
	adoxq	%rdi, %r9
	adcxq	%rsi, %r10
	MULXq	%r13, %rdi, %rsi
	adoxq	%rdi, %r10
	adcxq	%rsi, %r11
	MULXq	%rax, %rdx, %rax
	adoxq	%rdx, %r11
	adcxq	%rcx, %rax
	adoxq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rbx
	adcq	%rcx, %r9
	adcq	%rcx, %r10
	adcq	%rcx, %r11
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	addq	%rcx, %rbx
	movq	%rbx, 120(%rsp)
	movq	%r9, 128(%rsp)
	movq	%r10, 136(%rsp)
	movq	%r11, 144(%rsp)
	movl	$25, %eax
Ljade_scalarmult_curve25519_amd64_mulx_base$4:
	movl	%eax, 344(%rsp)
	xorq	%rdi, %rdi
	movq	%rbx, %rdx
	MULXq	%rdx, %r8, %rbx
	MULXq	%r9, %rcx, %rax
	MULXq	%r10, %rbp, %rsi
	adcxq	%rbp, %rax
	MULXq	%r11, %rdx, %rbp
	adcxq	%rdx, %rsi
	movq	%r9, %rdx
	MULXq	%r10, %r12, %r9
	adoxq	%r12, %rsi
	adcxq	%r9, %rbp
	MULXq	%r11, %r12, %r9
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r10, %rdx
	MULXq	%r11, %r14, %r10
	adcxq	%r14, %r9
	adoxq	%rdi, %r9
	adcxq	%rdi, %r10
	adoxq	%rdi, %r10
	MULXq	%rdx, %r15, %r14
	movq	%r11, %rdx
	MULXq	%rdx, %rdx, %r11
	adcxq	%rcx, %rcx
	adoxq	%rbx, %rcx
	adcxq	%rax, %rax
	adoxq	%r13, %rax
	adcxq	%rsi, %rsi
	adoxq	%r12, %rsi
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r9, %r9
	adoxq	%r14, %r9
	adcxq	%r10, %r10
	adoxq	%rdx, %r10
	adcxq	%rdi, %r11
	adoxq	%rdi, %r11
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r8
	adcxq	%rbx, %rcx
	MULXq	%r9, %rbx, %r9
	adoxq	%rbx, %rcx
	adcxq	%r9, %rax
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rax
	adcxq	%r9, %rsi
	MULXq	%r11, %r9, %rdx
	adoxq	%r9, %rsi
	adcxq	%rdi, %rdx
	adoxq	%rdi, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %r8
	adcq	%rdi, %rcx
	adcq	%rdi, %rax
	adcq	%rdi, %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %r8
	xorq	%rdi, %rdi
	movq	%r8, %rdx
	MULXq	%rdx, %rbx, %r8
	MULXq	%rcx, %r9, %r10
	MULXq	%rax, %rbp, %r11
	adcxq	%rbp, %r10
	MULXq	%rsi, %rdx, %rbp
	adcxq	%rdx, %r11
	movq	%rcx, %rdx
	MULXq	%rax, %r12, %rcx
	adoxq	%r12, %r11
	adcxq	%rcx, %rbp
	MULXq	%rsi, %r12, %rcx
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rax, %rdx
	MULXq	%rsi, %r14, %rax
	adcxq	%r14, %rcx
	adoxq	%rdi, %rcx
	adcxq	%rdi, %rax
	adoxq	%rdi, %rax
	MULXq	%rdx, %r15, %r14
	movq	%rsi, %rdx
	MULXq	%rdx, %rdx, %rsi
	adcxq	%r9, %r9
	adoxq	%r8, %r9
	adcxq	%r10, %r10
	adoxq	%r13, %r10
	adcxq	%r11, %r11
	adoxq	%r12, %r11
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rcx, %rcx
	adoxq	%r14, %rcx
	adcxq	%rax, %rax
	adoxq	%rdx, %rax
	adcxq	%rdi, %rsi
	adoxq	%rdi, %rsi
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %r8
	adoxq	%rbp, %rbx
	adcxq	%r8, %r9
	MULXq	%rcx, %r8, %rcx
	adoxq	%r8, %r9
	adcxq	%rcx, %r10
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r10
	adcxq	%rax, %r11
	MULXq	%rsi, %rcx, %rax
	adoxq	%rcx, %r11
	adcxq	%rdi, %rax
	adoxq	%rdi, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rbx
	adcq	%rdi, %r9
	adcq	%rdi, %r10
	adcq	%rdi, %r11
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %rbx
	movl	344(%rsp), %eax
	decl	%eax
	jne 	Ljade_scalarmult_curve25519_amd64_mulx_base$4
	xorq	%r8, %r8
	movq	120(%rsp), %rdx
	MULXq	%rbx, %rdi, %rsi
	MULXq	%r9, %rax, %rcx
	adcxq	%rax, %rsi
	MULXq	%r10, %rbp, %rax
	adcxq	%rbp, %rcx
	MULXq	%r11, %rdx, %rbp
	adcxq	%rdx, %rax
	adcxq	%r8, %rbp
	movq	128(%rsp), %rdx
	MULXq	%rbx, %r13, %r12
	adoxq	%r13, %rsi
	adcxq	%r12, %rcx
	MULXq	%r9, %r13, %r12
	adoxq	%r13, %rcx
	adcxq	%r12, %rax
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %rax
	adcxq	%r12, %rbp
	MULXq	%r11, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%r8, %r12
	adoxq	%r8, %r12
	movq	136(%rsp), %rdx
	MULXq	%rbx, %r14, %r13
	adoxq	%r14, %rcx
	adcxq	%r13, %rax
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %rax
	adcxq	%r13, %rbp
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%r11, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%r8, %r13
	adoxq	%r8, %r13
	movq	144(%rsp), %rdx
	MULXq	%rbx, %r14, %rbx
	adoxq	%r14, %rax
	adcxq	%rbx, %rbp
	MULXq	%r9, %rbx, %r9
	adoxq	%rbx, %rbp
	adcxq	%r9, %r12
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %r12
	adcxq	%r9, %r13
	MULXq	%r11, %rdx, %r9
	adoxq	%rdx, %r13
	adcxq	%r8, %r9
	adoxq	%r8, %r9
	movq	$38, %rdx
	MULXq	%rbp, %r11, %r10
	adoxq	%r11, %rdi
	adcxq	%r10, %rsi
	MULXq	%r12, %r11, %r10
	adoxq	%r11, %rsi
	adcxq	%r10, %rcx
	MULXq	%r13, %r11, %r10
	adoxq	%r11, %rcx
	adcxq	%r10, %rax
	MULXq	%r9, %r9, %rdx
	adoxq	%r9, %rax
	adcxq	%r8, %rdx
	adoxq	%r8, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rdi
	adcq	%r8, %rsi
	adcq	%r8, %rcx
	adcq	%r8, %rax
	sbbq	%r8, %r8
	andq	$38, %r8
	addq	%r8, %rdi
	movq	%rdi, 152(%rsp)
	movq	%rsi, 160(%rsp)
	movq	%rcx, 168(%rsp)
	movq	%rax, 176(%rsp)
	movl	$50, %edx
Ljade_scalarmult_curve25519_amd64_mulx_base$3:
	movl	%edx, 344(%rsp)
	xorq	%r11, %r11
	movq	%rdi, %rdx
	MULXq	%rdx, %rdi, %rbx
	MULXq	%rsi, %r9, %r8
	MULXq	%rcx, %rbp, %r10
	adcxq	%rbp, %r8
	MULXq	%rax, %rdx, %rbp
	adcxq	%rdx, %r10
	movq	%rsi, %rdx
	MULXq	%rcx, %r12, %rsi
	adoxq	%r12, %r10
	adcxq	%rsi, %rbp
	MULXq	%rax, %r12, %rsi
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rcx, %rdx
	MULXq	%rax, %r14, %rcx
	adcxq	%r14, %rsi
	adoxq	%r11, %rsi
	adcxq	%r11, %rcx
	adoxq	%r11, %rcx
	MULXq	%rdx, %r15, %r14
	movq	%rax, %rdx
	MULXq	%rdx, %rdx, %rax
	adcxq	%r9, %r9
	adoxq	%rbx, %r9
	adcxq	%r8, %r8
	adoxq	%r13, %r8
	adcxq	%r10, %r10
	adoxq	%r12, %r10
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rsi, %rsi
	adoxq	%r14, %rsi
	adcxq	%rcx, %rcx
	adoxq	%rdx, %rcx
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rdi
	adcxq	%rbx, %r9
	MULXq	%rsi, %rbx, %rsi
	adoxq	%rbx, %r9
	adcxq	%rsi, %r8
	MULXq	%rcx, %rsi, %rcx
	adoxq	%rsi, %r8
	adcxq	%rcx, %r10
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r10
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rdi
	adcq	%r11, %r9
	adcq	%r11, %r8
	adcq	%r11, %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdi
	xorq	%r11, %r11
	movq	%rdi, %rdx
	MULXq	%rdx, %rdi, %rbx
	MULXq	%r9, %rsi, %rcx
	MULXq	%r8, %rbp, %rax
	adcxq	%rbp, %rcx
	MULXq	%r10, %rdx, %rbp
	adcxq	%rdx, %rax
	movq	%r9, %rdx
	MULXq	%r8, %r12, %r9
	adoxq	%r12, %rax
	adcxq	%r9, %rbp
	MULXq	%r10, %r12, %r9
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r8, %rdx
	MULXq	%r10, %r14, %r8
	adcxq	%r14, %r9
	adoxq	%r11, %r9
	adcxq	%r11, %r8
	adoxq	%r11, %r8
	MULXq	%rdx, %r15, %r14
	movq	%r10, %rdx
	MULXq	%rdx, %rdx, %r10
	adcxq	%rsi, %rsi
	adoxq	%rbx, %rsi
	adcxq	%rcx, %rcx
	adoxq	%r13, %rcx
	adcxq	%rax, %rax
	adoxq	%r12, %rax
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r9, %r9
	adoxq	%r14, %r9
	adcxq	%r8, %r8
	adoxq	%rdx, %r8
	adcxq	%r11, %r10
	adoxq	%r11, %r10
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rdi
	adcxq	%rbx, %rsi
	MULXq	%r9, %rbx, %r9
	adoxq	%rbx, %rsi
	adcxq	%r9, %rcx
	MULXq	%r8, %r9, %r8
	adoxq	%r9, %rcx
	adcxq	%r8, %rax
	MULXq	%r10, %r8, %rdx
	adoxq	%r8, %rax
	adcxq	%r11, %rdx
	adoxq	%r11, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rdi
	adcq	%r11, %rsi
	adcq	%r11, %rcx
	adcq	%r11, %rax
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdi
	movl	344(%rsp), %edx
	decl	%edx
	jne 	Ljade_scalarmult_curve25519_amd64_mulx_base$3
	xorq	%rbx, %rbx
	movq	152(%rsp), %rdx
	MULXq	%rdi, %r9, %r8
	MULXq	%rsi, %r11, %r10
	adcxq	%r11, %r8
	MULXq	%rcx, %rbp, %r11
	adcxq	%rbp, %r10
	MULXq	%rax, %rdx, %rbp
	adcxq	%rdx, %r11
	adcxq	%rbx, %rbp
	movq	160(%rsp), %rdx
	MULXq	%rdi, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %r10
	MULXq	%rsi, %r13, %r12
	adoxq	%r13, %r10
	adcxq	%r12, %r11
	MULXq	%rcx, %r13, %r12
	adoxq	%r13, %r11
	adcxq	%r12, %rbp
	MULXq	%rax, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rbx, %r12
	adoxq	%rbx, %r12
	movq	168(%rsp), %rdx
	MULXq	%rdi, %r14, %r13
	adoxq	%r14, %r10
	adcxq	%r13, %r11
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %r11
	adcxq	%r13, %rbp
	MULXq	%rcx, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rax, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rbx, %r13
	adoxq	%rbx, %r13
	movq	176(%rsp), %rdx
	MULXq	%rdi, %r14, %rdi
	adoxq	%r14, %r11
	adcxq	%rdi, %rbp
	MULXq	%rsi, %rdi, %rsi
	adoxq	%rdi, %rbp
	adcxq	%rsi, %r12
	MULXq	%rcx, %rsi, %rcx
	adoxq	%rsi, %r12
	adcxq	%rcx, %r13
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r13
	adcxq	%rbx, %rax
	adoxq	%rbx, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rsi, %rcx
	adoxq	%rsi, %r9
	adcxq	%rcx, %r8
	MULXq	%r12, %rsi, %rcx
	adoxq	%rsi, %r8
	adcxq	%rcx, %r10
	MULXq	%r13, %rsi, %rcx
	adoxq	%rsi, %r10
	adcxq	%rcx, %r11
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r11
	adcxq	%rbx, %rax
	adoxq	%rbx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r9
	adcq	%rbx, %r8
	adcq	%rbx, %r10
	adcq	%rbx, %r11
	sbbq	%rbx, %rbx
	andq	$38, %rbx
	addq	%rbx, %r9
	movl	$25, %eax
Ljade_scalarmult_curve25519_amd64_mulx_base$2:
	movl	%eax, 344(%rsp)
	xorq	%rdi, %rdi
	movq	%r9, %rdx
	MULXq	%rdx, %r9, %rbx
	MULXq	%r8, %rcx, %rax
	MULXq	%r10, %rbp, %rsi
	adcxq	%rbp, %rax
	MULXq	%r11, %rdx, %rbp
	adcxq	%rdx, %rsi
	movq	%r8, %rdx
	MULXq	%r10, %r12, %r8
	adoxq	%r12, %rsi
	adcxq	%r8, %rbp
	MULXq	%r11, %r12, %r8
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r10, %rdx
	MULXq	%r11, %r14, %r10
	adcxq	%r14, %r8
	adoxq	%rdi, %r8
	adcxq	%rdi, %r10
	adoxq	%rdi, %r10
	MULXq	%rdx, %r15, %r14
	movq	%r11, %rdx
	MULXq	%rdx, %rdx, %r11
	adcxq	%rcx, %rcx
	adoxq	%rbx, %rcx
	adcxq	%rax, %rax
	adoxq	%r13, %rax
	adcxq	%rsi, %rsi
	adoxq	%r12, %rsi
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r8, %r8
	adoxq	%r14, %r8
	adcxq	%r10, %r10
	adoxq	%rdx, %r10
	adcxq	%rdi, %r11
	adoxq	%rdi, %r11
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r9
	adcxq	%rbx, %rcx
	MULXq	%r8, %rbx, %r8
	adoxq	%rbx, %rcx
	adcxq	%r8, %rax
	MULXq	%r10, %r10, %r8
	adoxq	%r10, %rax
	adcxq	%r8, %rsi
	MULXq	%r11, %r8, %rdx
	adoxq	%r8, %rsi
	adcxq	%rdi, %rdx
	adoxq	%rdi, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %r9
	adcq	%rdi, %rcx
	adcq	%rdi, %rax
	adcq	%rdi, %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %r9
	xorq	%rdi, %rdi
	movq	%r9, %rdx
	MULXq	%rdx, %r9, %rbx
	MULXq	%rcx, %r8, %r10
	MULXq	%rax, %rbp, %r11
	adcxq	%rbp, %r10
	MULXq	%rsi, %rdx, %rbp
	adcxq	%rdx, %r11
	movq	%rcx, %rdx
	MULXq	%rax, %r12, %rcx
	adoxq	%r12, %r11
	adcxq	%rcx, %rbp
	MULXq	%rsi, %r12, %rcx
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rax, %rdx
	MULXq	%rsi, %r14, %rax
	adcxq	%r14, %rcx
	adoxq	%rdi, %rcx
	adcxq	%rdi, %rax
	adoxq	%rdi, %rax
	MULXq	%rdx, %r15, %r14
	movq	%rsi, %rdx
	MULXq	%rdx, %rdx, %rsi
	adcxq	%r8, %r8
	adoxq	%rbx, %r8
	adcxq	%r10, %r10
	adoxq	%r13, %r10
	adcxq	%r11, %r11
	adoxq	%r12, %r11
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rcx, %rcx
	adoxq	%r14, %rcx
	adcxq	%rax, %rax
	adoxq	%rdx, %rax
	adcxq	%rdi, %rsi
	adoxq	%rdi, %rsi
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r9
	adcxq	%rbx, %r8
	MULXq	%rcx, %rbx, %rcx
	adoxq	%rbx, %r8
	adcxq	%rcx, %r10
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r10
	adcxq	%rax, %r11
	MULXq	%rsi, %rcx, %rax
	adoxq	%rcx, %r11
	adcxq	%rdi, %rax
	adoxq	%rdi, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r9
	adcq	%rdi, %r8
	adcq	%rdi, %r10
	adcq	%rdi, %r11
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %r9
	movl	344(%rsp), %eax
	decl	%eax
	jne 	Ljade_scalarmult_curve25519_amd64_mulx_base$2
	xorq	%rdi, %rdi
	movq	120(%rsp), %rdx
	MULXq	%r9, %rsi, %rcx
	MULXq	%r8, %rax, %rbx
	adcxq	%rax, %rcx
	MULXq	%r10, %rbp, %rax
	adcxq	%rbp, %rbx
	MULXq	%r11, %rdx, %rbp
	adcxq	%rdx, %rax
	adcxq	%rdi, %rbp
	movq	128(%rsp), %rdx
	MULXq	%r9, %r13, %r12
	adoxq	%r13, %rcx
	adcxq	%r12, %rbx
	MULXq	%r8, %r13, %r12
	adoxq	%r13, %rbx
	adcxq	%r12, %rax
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %rax
	adcxq	%r12, %rbp
	MULXq	%r11, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rdi, %r12
	adoxq	%rdi, %r12
	movq	136(%rsp), %rdx
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %rbx
	adcxq	%r13, %rax
	MULXq	%r8, %r14, %r13
	adoxq	%r14, %rax
	adcxq	%r13, %rbp
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%r11, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rdi, %r13
	adoxq	%rdi, %r13
	movq	144(%rsp), %rdx
	MULXq	%r9, %r14, %r9
	adoxq	%r14, %rax
	adcxq	%r9, %rbp
	MULXq	%r8, %r9, %r8
	adoxq	%r9, %rbp
	adcxq	%r8, %r12
	MULXq	%r10, %r9, %r8
	adoxq	%r9, %r12
	adcxq	%r8, %r13
	MULXq	%r11, %rdx, %r8
	adoxq	%rdx, %r13
	adcxq	%rdi, %r8
	adoxq	%rdi, %r8
	movq	$38, %rdx
	MULXq	%rbp, %r10, %r9
	adoxq	%r10, %rsi
	adcxq	%r9, %rcx
	MULXq	%r12, %r10, %r9
	adoxq	%r10, %rcx
	adcxq	%r9, %rbx
	MULXq	%r13, %r10, %r9
	adoxq	%r10, %rbx
	adcxq	%r9, %rax
	MULXq	%r8, %r8, %rdx
	adoxq	%r8, %rax
	adcxq	%rdi, %rdx
	adoxq	%rdi, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rsi
	adcq	%rdi, %rcx
	adcq	%rdi, %rbx
	adcq	%rdi, %rax
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %rsi
	movl	$2, %edx
Ljade_scalarmult_curve25519_amd64_mulx_base$1:
	movl	%edx, 344(%rsp)
	xorq	%r10, %r10
	movq	%rsi, %rdx
	MULXq	%rdx, %rsi, %r11
	MULXq	%rcx, %r8, %rdi
	MULXq	%rbx, %rbp, %r9
	adcxq	%rbp, %rdi
	MULXq	%rax, %rdx, %rbp
	adcxq	%rdx, %r9
	movq	%rcx, %rdx
	MULXq	%rbx, %r12, %rcx
	adoxq	%r12, %r9
	adcxq	%rcx, %rbp
	MULXq	%rax, %r12, %rcx
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rbx, %rdx
	MULXq	%rax, %r14, %rbx
	adcxq	%r14, %rcx
	adoxq	%r10, %rcx
	adcxq	%r10, %rbx
	adoxq	%r10, %rbx
	MULXq	%rdx, %r15, %r14
	movq	%rax, %rdx
	MULXq	%rdx, %rdx, %rax
	adcxq	%r8, %r8
	adoxq	%r11, %r8
	adcxq	%rdi, %rdi
	adoxq	%r13, %rdi
	adcxq	%r9, %r9
	adoxq	%r12, %r9
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rcx, %rcx
	adoxq	%r14, %rcx
	adcxq	%rbx, %rbx
	adoxq	%rdx, %rbx
	adcxq	%r10, %rax
	adoxq	%r10, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %r11
	adoxq	%rbp, %rsi
	adcxq	%r11, %r8
	MULXq	%rcx, %r11, %rcx
	adoxq	%r11, %r8
	adcxq	%rcx, %rdi
	MULXq	%rbx, %r11, %rcx
	adoxq	%r11, %rdi
	adcxq	%rcx, %r9
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r9
	adcxq	%r10, %rax
	adoxq	%r10, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rsi
	adcq	%r10, %r8
	adcq	%r10, %rdi
	adcq	%r10, %r9
	sbbq	%r10, %r10
	andq	$38, %r10
	addq	%r10, %rsi
	xorq	%r10, %r10
	movq	%rsi, %rdx
	MULXq	%rdx, %rsi, %r11
	MULXq	%r8, %rcx, %rbx
	MULXq	%rdi, %rbp, %rax
	adcxq	%rbp, %rbx
	MULXq	%r9, %rdx, %rbp
	adcxq	%rdx, %rax
	movq	%r8, %rdx
	MULXq	%rdi, %r12, %r8
	adoxq	%r12, %rax
	adcxq	%r8, %rbp
	MULXq	%r9, %r12, %r8
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rdi, %rdx
	MULXq	%r9, %r14, %rdi
	adcxq	%r14, %r8
	adoxq	%r10, %r8
	adcxq	%r10, %rdi
	adoxq	%r10, %rdi
	MULXq	%rdx, %r15, %r14
	movq	%r9, %rdx
	MULXq	%rdx, %rdx, %r9
	adcxq	%rcx, %rcx
	adoxq	%r11, %rcx
	adcxq	%rbx, %rbx
	adoxq	%r13, %rbx
	adcxq	%rax, %rax
	adoxq	%r12, %rax
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r8, %r8
	adoxq	%r14, %r8
	adcxq	%rdi, %rdi
	adoxq	%rdx, %rdi
	adcxq	%r10, %r9
	adoxq	%r10, %r9
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %r11
	adoxq	%rbp, %rsi
	adcxq	%r11, %rcx
	MULXq	%r8, %r11, %r8
	adoxq	%r11, %rcx
	adcxq	%r8, %rbx
	MULXq	%rdi, %r8, %rdi
	adoxq	%r8, %rbx
	adcxq	%rdi, %rax
	MULXq	%r9, %rdi, %rdx
	adoxq	%rdi, %rax
	adcxq	%r10, %rdx
	adoxq	%r10, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rsi
	adcq	%r10, %rcx
	adcq	%r10, %rbx
	adcq	%r10, %rax
	sbbq	%r10, %r10
	andq	$38, %r10
	addq	%r10, %rsi
	movl	344(%rsp), %edx
	decl	%edx
	jne 	Ljade_scalarmult_curve25519_amd64_mulx_base$1
	xorq	%r8, %r8
	movq	%rsi, %rdx
	MULXq	%rdx, %rsi, %r9
	MULXq	%rcx, %r10, %rdi
	MULXq	%rbx, %rbp, %r11
	adcxq	%rbp, %rdi
	MULXq	%rax, %rdx, %rbp
	adcxq	%rdx, %r11
	movq	%rcx, %rdx
	MULXq	%rbx, %r12, %rcx
	adoxq	%r12, %r11
	adcxq	%rcx, %rbp
	MULXq	%rax, %r12, %rcx
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rbx, %rdx
	MULXq	%rax, %r14, %rbx
	adcxq	%r14, %rcx
	adoxq	%r8, %rcx
	adcxq	%r8, %rbx
	adoxq	%r8, %rbx
	MULXq	%rdx, %r15, %r14
	movq	%rax, %rdx
	MULXq	%rdx, %rdx, %rax
	adcxq	%r10, %r10
	adoxq	%r9, %r10
	adcxq	%rdi, %rdi
	adoxq	%r13, %rdi
	adcxq	%r11, %r11
	adoxq	%r12, %r11
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rcx, %rcx
	adoxq	%r14, %rcx
	adcxq	%rbx, %rbx
	adoxq	%rdx, %rbx
	adcxq	%r8, %rax
	adoxq	%r8, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %r9
	adoxq	%rbp, %rsi
	adcxq	%r9, %r10
	MULXq	%rcx, %r9, %rcx
	adoxq	%r9, %r10
	adcxq	%rcx, %rdi
	MULXq	%rbx, %r9, %rcx
	adoxq	%r9, %rdi
	adcxq	%rcx, %r11
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r11
	adcxq	%r8, %rax
	adoxq	%r8, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rsi
	adcq	%r8, %r10
	adcq	%r8, %rdi
	adcq	%r8, %r11
	sbbq	%r8, %r8
	andq	$38, %r8
	addq	%r8, %rsi
	xorq	%rbx, %rbx
	movq	88(%rsp), %rdx
	MULXq	%rsi, %rcx, %rax
	MULXq	%r10, %r9, %r8
	adcxq	%r9, %rax
	MULXq	%rdi, %rbp, %r9
	adcxq	%rbp, %r8
	MULXq	%r11, %rdx, %rbp
	adcxq	%rdx, %r9
	adcxq	%rbx, %rbp
	movq	96(%rsp), %rdx
	MULXq	%rsi, %r13, %r12
	adoxq	%r13, %rax
	adcxq	%r12, %r8
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %r9
	MULXq	%rdi, %r13, %r12
	adoxq	%r13, %r9
	adcxq	%r12, %rbp
	MULXq	%r11, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rbx, %r12
	adoxq	%rbx, %r12
	movq	104(%rsp), %rdx
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %r9
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %r9
	adcxq	%r13, %rbp
	MULXq	%rdi, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%r11, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rbx, %r13
	adoxq	%rbx, %r13
	movq	112(%rsp), %rdx
	MULXq	%rsi, %r14, %rsi
	adoxq	%r14, %r9
	adcxq	%rsi, %rbp
	MULXq	%r10, %r10, %rsi
	adoxq	%r10, %rbp
	adcxq	%rsi, %r12
	MULXq	%rdi, %rdi, %rsi
	adoxq	%rdi, %r12
	adcxq	%rsi, %r13
	MULXq	%r11, %rdx, %rsi
	adoxq	%rdx, %r13
	adcxq	%rbx, %rsi
	adoxq	%rbx, %rsi
	movq	$38, %rdx
	MULXq	%rbp, %r10, %rdi
	adoxq	%r10, %rcx
	adcxq	%rdi, %rax
	MULXq	%r12, %r10, %rdi
	adoxq	%r10, %rax
	adcxq	%rdi, %r8
	MULXq	%r13, %r10, %rdi
	adoxq	%r10, %r8
	adcxq	%rdi, %r9
	MULXq	%rsi, %rsi, %rdx
	adoxq	%rsi, %r9
	adcxq	%rbx, %rdx
	adoxq	%rbx, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rcx
	adcq	%rbx, %rax
	adcq	%rbx, %r8
	adcq	%rbx, %r9
	sbbq	%rbx, %rbx
	andq	$38, %rbx
	addq	%rbx, %rcx
	xorq	%rsi, %rsi
	movq	56(%rsp), %rdx
	MULXq	%rcx, %r10, %rdi
	MULXq	%rax, %rbx, %r11
	adcxq	%rbx, %rdi
	MULXq	%r8, %rbp, %rbx
	adcxq	%rbp, %r11
	MULXq	%r9, %rdx, %rbp
	adcxq	%rdx, %rbx
	adcxq	%rsi, %rbp
	movq	64(%rsp), %rdx
	MULXq	%rcx, %r13, %r12
	adoxq	%r13, %rdi
	adcxq	%r12, %r11
	MULXq	%rax, %r13, %r12
	adoxq	%r13, %r11
	adcxq	%r12, %rbx
	MULXq	%r8, %r13, %r12
	adoxq	%r13, %rbx
	adcxq	%r12, %rbp
	MULXq	%r9, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rsi, %r12
	adoxq	%rsi, %r12
	movq	72(%rsp), %rdx
	MULXq	%rcx, %r14, %r13
	adoxq	%r14, %r11
	adcxq	%r13, %rbx
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %rbx
	adcxq	%r13, %rbp
	MULXq	%r8, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%r9, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rsi, %r13
	adoxq	%rsi, %r13
	movq	80(%rsp), %rdx
	MULXq	%rcx, %r14, %rcx
	adoxq	%r14, %rbx
	adcxq	%rcx, %rbp
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %rbp
	adcxq	%rax, %r12
	MULXq	%r8, %rcx, %rax
	adoxq	%rcx, %r12
	adcxq	%rax, %r13
	MULXq	%r9, %rcx, %rax
	adoxq	%rcx, %r13
	adcxq	%rsi, %rax
	adoxq	%rsi, %rax
	movq	$38, %rdx
	MULXq	%rbp, %r8, %rcx
	adoxq	%r8, %r10
	adcxq	%rcx, %rdi
	MULXq	%r12, %r8, %rcx
	adoxq	%r8, %rdi
	adcxq	%rcx, %r11
	MULXq	%r13, %r8, %rcx
	adoxq	%r8, %r11
	adcxq	%rcx, %rbx
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %rbx
	adcxq	%rsi, %rax
	adoxq	%rsi, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r10
	adcq	%rsi, %rdi
	adcq	%rsi, %r11
	adcq	%rsi, %rbx
	sbbq	%rsi, %rsi
	andq	$38, %rsi
	addq	%rsi, %r10
	leaq	(%rbx,%rbx), %rax
	sarq	$63, %rbx
	shrq	$1, %rax
	andq	$19, %rbx
	addq	$19, %rbx
	addq	%rbx, %r10
	adcq	$0, %rdi
	adcq	$0, %r11
	adcq	$0, %rax
	leaq	(%rax,%rax), %rcx
	sarq	$63, %rax
	shrq	$1, %rcx
	notq	%rax
	andq	$19, %rax
	subq	%rax, %r10
	sbbq	$0, %rdi
	sbbq	$0, %r11
	sbbq	$0, %rcx
	movq	(%rsp), %rax
	movq	%r10, (%rax)
	movq	%rdi, 8(%rax)
	movq	%r11, 16(%rax)
	movq	%rcx, 24(%rax)
	xorq	%rax, %rax
	movq	352(%rsp), %rbx
	movq	360(%rsp), %rbp
	movq	368(%rsp), %r12
	movq	376(%rsp), %r13
	movq	384(%rsp), %r14
	movq	392(%rsp), %r15
	movq	400(%rsp), %rsp
	ret 
_jade_scalarmult_curve25519_amd64_mulx:
jade_scalarmult_curve25519_amd64_mulx:
	movq	%rsp, %rax
	leaq	-408(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rax, 400(%rsp)
	movq	%rbx, 352(%rsp)
	movq	%rbp, 360(%rsp)
	movq	%r12, 368(%rsp)
	movq	%r13, 376(%rsp)
	movq	%r14, 384(%rsp)
	movq	%r15, 392(%rsp)
	movq	%rdi, (%rsp)
	movq	(%rsi), %rax
	movq	%rax, 24(%rsp)
	movq	8(%rsi), %rax
	movq	%rax, 32(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 40(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 48(%rsp)
	andb	$-8, 24(%rsp)
	andb	$127, 55(%rsp)
	orb 	$64, 55(%rsp)
	movq	(%rdx), %rcx
	movq	8(%rdx), %r8
	movq	16(%rdx), %r10
	movq	24(%rdx), %rdx
	movq	$9223372036854775807, %rax
	andq	%rax, %rdx
	xorq	%r11, %r11
	movq	$1, 56(%rsp)
	movq	$0, %rdi
	movq	%rcx, 88(%rsp)
	movq	%r8, 96(%rsp)
	movq	%r10, 104(%rsp)
	movq	%rdx, 112(%rsp)
	movq	$1, 120(%rsp)
	movq	%r11, 64(%rsp)
	movq	%r11, %r9
	movq	%r11, 128(%rsp)
	movq	%r11, 72(%rsp)
	movq	%r11, %rax
	movq	%r11, 136(%rsp)
	movq	%r11, 80(%rsp)
	movq	%r11, %rsi
	movq	%r11, 144(%rsp)
	movq	%rcx, 152(%rsp)
	movq	%r8, 160(%rsp)
	movq	%r10, 168(%rsp)
	movq	%rdx, 176(%rsp)
	movq	$255, %rcx
	movq	$0, 8(%rsp)
Ljade_scalarmult_curve25519_amd64_mulx$9:
	addq	$-1, %rcx
	movq	%rcx, 16(%rsp)
	movq	%rcx, %rdx
	shrq	$3, %rdx
	movzbq	24(%rsp,%rdx), %rdx
	andq	$7, %rcx
	shrq	%cl, %rdx
	andq	$1, %rdx
	movq	8(%rsp), %r8
	xorq	%rdx, %r8
	xorq	%rcx, %rcx
	subq	%r8, %rcx
	movq	120(%rsp), %r8
	movq	128(%rsp), %r10
	movq	136(%rsp), %r11
	movq	144(%rsp), %rbx
	movq	%rdi, %rbp
	movq	%r9, %r12
	movq	%rax, %r13
	movq	%rsi, %r14
	xorq	%r8, %rbp
	xorq	%r10, %r12
	xorq	%r11, %r13
	xorq	%rbx, %r14
	andq	%rcx, %rbp
	andq	%rcx, %r12
	andq	%rcx, %r13
	andq	%rcx, %r14
	xorq	%rbp, %rdi
	xorq	%rbp, %r8
	movq	%r8, 120(%rsp)
	xorq	%r12, %r9
	xorq	%r12, %r10
	movq	%r10, 128(%rsp)
	xorq	%r13, %rax
	xorq	%r13, %r11
	movq	%r11, 136(%rsp)
	xorq	%r14, %rsi
	xorq	%r14, %rbx
	movq	%rbx, 144(%rsp)
	movq	88(%rsp), %r11
	movq	96(%rsp), %rbx
	movq	104(%rsp), %r8
	movq	112(%rsp), %r10
	movq	56(%rsp), %rbp
	movq	%r11, %r12
	xorq	%rbp, %r12
	andq	%rcx, %r12
	xorq	%r12, %rbp
	xorq	%r12, %r11
	movq	%rbp, 56(%rsp)
	movq	%r11, 88(%rsp)
	movq	64(%rsp), %r11
	movq	%rbx, %rbp
	xorq	%r11, %rbp
	andq	%rcx, %rbp
	xorq	%rbp, %r11
	xorq	%rbp, %rbx
	movq	%r11, 64(%rsp)
	movq	%rbx, 96(%rsp)
	movq	72(%rsp), %r11
	movq	%r8, %rbx
	xorq	%r11, %rbx
	andq	%rcx, %rbx
	xorq	%rbx, %r11
	xorq	%rbx, %r8
	movq	%r11, 72(%rsp)
	movq	%r8, 104(%rsp)
	movq	80(%rsp), %r8
	movq	%r10, %r11
	xorq	%r8, %r11
	andq	%rcx, %r11
	xorq	%r11, %r8
	xorq	%r11, %r10
	movq	%r8, 80(%rsp)
	movq	%r10, 112(%rsp)
	movq	%rdx, 8(%rsp)
	xorq	%rcx, %rcx
	movq	56(%rsp), %rdx
	movq	64(%rsp), %r8
	movq	72(%rsp), %r10
	movq	80(%rsp), %r11
	subq	%rdi, %rdx
	sbbq	%r9, %r8
	sbbq	%rax, %r10
	sbbq	%rsi, %r11
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	subq	%rcx, %rdx
	sbbq	$0, %r8
	sbbq	$0, %r10
	sbbq	$0, %r11
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	subq	%rcx, %rdx
	movq	%rdx, 184(%rsp)
	movq	%r8, 192(%rsp)
	movq	%r10, 200(%rsp)
	movq	%r11, 208(%rsp)
	xorq	%rcx, %rcx
	addq	56(%rsp), %rdi
	adcq	64(%rsp), %r9
	adcq	72(%rsp), %rax
	adcq	80(%rsp), %rsi
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	addq	%rcx, %rdi
	adcq	$0, %r9
	adcq	$0, %rax
	adcq	$0, %rsi
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	addq	%rcx, %rdi
	movq	%rdi, 216(%rsp)
	movq	%r9, 224(%rsp)
	movq	%rax, 232(%rsp)
	movq	%rsi, 240(%rsp)
	movq	88(%rsp), %rax
	movq	96(%rsp), %rcx
	movq	104(%rsp), %rdx
	movq	112(%rsp), %rsi
	xorq	%rdi, %rdi
	subq	120(%rsp), %rax
	sbbq	128(%rsp), %rcx
	sbbq	136(%rsp), %rdx
	sbbq	144(%rsp), %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	subq	%rdi, %rax
	sbbq	$0, %rcx
	sbbq	$0, %rdx
	sbbq	$0, %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	subq	%rdi, %rax
	movq	%rax, 248(%rsp)
	movq	%rcx, 256(%rsp)
	movq	%rdx, 264(%rsp)
	movq	%rsi, 272(%rsp)
	movq	88(%rsp), %rax
	movq	96(%rsp), %rcx
	movq	104(%rsp), %rdx
	movq	112(%rsp), %rsi
	xorq	%rdi, %rdi
	addq	120(%rsp), %rax
	adcq	128(%rsp), %rcx
	adcq	136(%rsp), %rdx
	adcq	144(%rsp), %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %rax
	adcq	$0, %rcx
	adcq	$0, %rdx
	adcq	$0, %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %rax
	movq	%rax, 280(%rsp)
	movq	%rcx, 288(%rsp)
	movq	%rdx, 296(%rsp)
	movq	%rsi, 304(%rsp)
	movq	248(%rsp), %r9
	movq	256(%rsp), %r10
	movq	264(%rsp), %r11
	movq	272(%rsp), %rbx
	xorq	%rax, %rax
	movq	216(%rsp), %rdx
	MULXq	%r9, %rsi, %rcx
	MULXq	%r10, %r8, %rdi
	adcxq	%r8, %rcx
	MULXq	%r11, %rbp, %r8
	adcxq	%rbp, %rdi
	MULXq	%rbx, %rdx, %rbp
	adcxq	%rdx, %r8
	adcxq	%rax, %rbp
	movq	224(%rsp), %rdx
	MULXq	%r9, %r13, %r12
	adoxq	%r13, %rcx
	adcxq	%r12, %rdi
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %rdi
	adcxq	%r12, %r8
	MULXq	%r11, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %rbp
	MULXq	%rbx, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rax, %r12
	adoxq	%rax, %r12
	movq	232(%rsp), %rdx
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %rdi
	adcxq	%r13, %r8
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %rbp
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rbx, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	movq	240(%rsp), %rdx
	MULXq	%r9, %r14, %r9
	adoxq	%r14, %r8
	adcxq	%r9, %rbp
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rbp
	adcxq	%r9, %r12
	MULXq	%r11, %r10, %r9
	adoxq	%r10, %r12
	adcxq	%r9, %r13
	MULXq	%rbx, %rdx, %r9
	adoxq	%rdx, %r13
	adcxq	%rax, %r9
	adoxq	%rax, %r9
	movq	$38, %rdx
	MULXq	%rbp, %r11, %r10
	adoxq	%r11, %rsi
	adcxq	%r10, %rcx
	MULXq	%r12, %r11, %r10
	adoxq	%r11, %rcx
	adcxq	%r10, %rdi
	MULXq	%r13, %r11, %r10
	adoxq	%r11, %rdi
	adcxq	%r10, %r8
	MULXq	%r9, %r9, %rdx
	adoxq	%r9, %r8
	adcxq	%rax, %rdx
	adoxq	%rax, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rsi
	adcq	%rax, %rcx
	adcq	%rax, %rdi
	adcq	%rax, %r8
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rsi
	movq	%rsi, 248(%rsp)
	movq	%rcx, 256(%rsp)
	movq	%rdi, 264(%rsp)
	movq	%r8, 272(%rsp)
	movq	184(%rsp), %r9
	movq	192(%rsp), %r10
	movq	200(%rsp), %r11
	movq	208(%rsp), %rbx
	xorq	%rax, %rax
	movq	280(%rsp), %rdx
	MULXq	%r9, %rsi, %rcx
	MULXq	%r10, %r8, %rdi
	adcxq	%r8, %rcx
	MULXq	%r11, %rbp, %r8
	adcxq	%rbp, %rdi
	MULXq	%rbx, %rdx, %rbp
	adcxq	%rdx, %r8
	adcxq	%rax, %rbp
	movq	288(%rsp), %rdx
	MULXq	%r9, %r13, %r12
	adoxq	%r13, %rcx
	adcxq	%r12, %rdi
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %rdi
	adcxq	%r12, %r8
	MULXq	%r11, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %rbp
	MULXq	%rbx, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rax, %r12
	adoxq	%rax, %r12
	movq	296(%rsp), %rdx
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %rdi
	adcxq	%r13, %r8
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %rbp
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rbx, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	movq	304(%rsp), %rdx
	MULXq	%r9, %r14, %r9
	adoxq	%r14, %r8
	adcxq	%r9, %rbp
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rbp
	adcxq	%r9, %r12
	MULXq	%r11, %r10, %r9
	adoxq	%r10, %r12
	adcxq	%r9, %r13
	MULXq	%rbx, %rdx, %r9
	adoxq	%rdx, %r13
	adcxq	%rax, %r9
	adoxq	%rax, %r9
	movq	$38, %rdx
	MULXq	%rbp, %r11, %r10
	adoxq	%r11, %rsi
	adcxq	%r10, %rcx
	MULXq	%r12, %r11, %r10
	adoxq	%r11, %rcx
	adcxq	%r10, %rdi
	MULXq	%r13, %r11, %r10
	adoxq	%r11, %rdi
	adcxq	%r10, %r8
	MULXq	%r9, %r9, %rdx
	adoxq	%r9, %r8
	adcxq	%rax, %rdx
	adoxq	%rax, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rsi
	adcq	%rax, %rcx
	adcq	%rax, %rdi
	adcq	%rax, %r8
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rsi
	movq	%rsi, 280(%rsp)
	movq	%rcx, 288(%rsp)
	movq	%rdi, 296(%rsp)
	movq	%r8, 304(%rsp)
	movq	216(%rsp), %rdx
	movq	224(%rsp), %r11
	movq	232(%rsp), %r13
	movq	240(%rsp), %rbx
	xorq	%rax, %rax
	MULXq	%rdx, %rsi, %rcx
	MULXq	%r11, %r8, %rdi
	MULXq	%r13, %r10, %r9
	adcxq	%r10, %rdi
	MULXq	%rbx, %rdx, %r10
	adcxq	%rdx, %r9
	movq	%r11, %rdx
	MULXq	%r13, %rbp, %r11
	adoxq	%rbp, %r9
	adcxq	%r11, %r10
	MULXq	%rbx, %rbp, %r11
	adoxq	%rbp, %r10
	MULXq	%rdx, %r12, %rbp
	movq	%r13, %rdx
	MULXq	%rbx, %r14, %r13
	adcxq	%r14, %r11
	adoxq	%rax, %r11
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	MULXq	%rdx, %r15, %r14
	movq	%rbx, %rdx
	MULXq	%rdx, %rdx, %rbx
	adcxq	%r8, %r8
	adoxq	%rcx, %r8
	adcxq	%rdi, %rdi
	adoxq	%r12, %rdi
	adcxq	%r9, %r9
	adoxq	%rbp, %r9
	adcxq	%r10, %r10
	adoxq	%r15, %r10
	adcxq	%r11, %r11
	adoxq	%r14, %r11
	adcxq	%r13, %r13
	adoxq	%rdx, %r13
	adcxq	%rax, %rbx
	adoxq	%rax, %rbx
	movq	$38, %rdx
	MULXq	%r10, %r10, %rcx
	adoxq	%r10, %rsi
	adcxq	%rcx, %r8
	MULXq	%r11, %r10, %rcx
	adoxq	%r10, %r8
	adcxq	%rcx, %rdi
	MULXq	%r13, %r10, %rcx
	adoxq	%r10, %rdi
	adcxq	%rcx, %r9
	MULXq	%rbx, %rdx, %rcx
	adoxq	%rdx, %r9
	adcxq	%rax, %rcx
	adoxq	%rax, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rsi
	adcq	%rax, %r8
	adcq	%rax, %rdi
	adcq	%rax, %r9
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rsi
	movq	%rsi, 216(%rsp)
	movq	%r8, 224(%rsp)
	movq	%rdi, 232(%rsp)
	movq	%r9, 240(%rsp)
	movq	184(%rsp), %rdx
	movq	192(%rsp), %r11
	movq	200(%rsp), %r13
	movq	208(%rsp), %rbx
	xorq	%r8, %r8
	MULXq	%rdx, %rax, %r9
	MULXq	%r11, %rsi, %rcx
	MULXq	%r13, %r10, %rdi
	adcxq	%r10, %rcx
	MULXq	%rbx, %rdx, %r10
	adcxq	%rdx, %rdi
	movq	%r11, %rdx
	MULXq	%r13, %rbp, %r11
	adoxq	%rbp, %rdi
	adcxq	%r11, %r10
	MULXq	%rbx, %rbp, %r11
	adoxq	%rbp, %r10
	MULXq	%rdx, %r12, %rbp
	movq	%r13, %rdx
	MULXq	%rbx, %r14, %r13
	adcxq	%r14, %r11
	adoxq	%r8, %r11
	adcxq	%r8, %r13
	adoxq	%r8, %r13
	MULXq	%rdx, %r15, %r14
	movq	%rbx, %rdx
	MULXq	%rdx, %rdx, %rbx
	adcxq	%rsi, %rsi
	adoxq	%r9, %rsi
	adcxq	%rcx, %rcx
	adoxq	%r12, %rcx
	adcxq	%rdi, %rdi
	adoxq	%rbp, %rdi
	adcxq	%r10, %r10
	adoxq	%r15, %r10
	adcxq	%r11, %r11
	adoxq	%r14, %r11
	adcxq	%r13, %r13
	adoxq	%rdx, %r13
	adcxq	%r8, %rbx
	adoxq	%r8, %rbx
	movq	$38, %rdx
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rax
	adcxq	%r9, %rsi
	MULXq	%r11, %r10, %r9
	adoxq	%r10, %rsi
	adcxq	%r9, %rcx
	MULXq	%r13, %r10, %r9
	adoxq	%r10, %rcx
	adcxq	%r9, %rdi
	MULXq	%rbx, %r9, %rdx
	adoxq	%r9, %rdi
	adcxq	%r8, %rdx
	adoxq	%r8, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rax
	adcq	%r8, %rsi
	adcq	%r8, %rcx
	adcq	%r8, %rdi
	sbbq	%r8, %r8
	andq	$38, %r8
	addq	%r8, %rax
	movq	248(%rsp), %rdx
	movq	256(%rsp), %r8
	movq	264(%rsp), %r9
	movq	272(%rsp), %r10
	xorq	%r11, %r11
	addq	280(%rsp), %rdx
	adcq	288(%rsp), %r8
	adcq	296(%rsp), %r9
	adcq	304(%rsp), %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdx
	adcq	$0, %r8
	adcq	$0, %r9
	adcq	$0, %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdx
	movq	%rdx, 184(%rsp)
	movq	%r8, 192(%rsp)
	movq	%r9, 200(%rsp)
	movq	%r10, 208(%rsp)
	movq	248(%rsp), %rdx
	movq	256(%rsp), %r8
	movq	264(%rsp), %r9
	movq	272(%rsp), %r10
	xorq	%r11, %r11
	subq	280(%rsp), %rdx
	sbbq	288(%rsp), %r8
	sbbq	296(%rsp), %r9
	sbbq	304(%rsp), %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	subq	%r11, %rdx
	sbbq	$0, %r8
	sbbq	$0, %r9
	sbbq	$0, %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	subq	%r11, %rdx
	movq	%rdx, 280(%rsp)
	movq	%r8, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r10, 304(%rsp)
	xorq	%rdx, %rdx
	movq	216(%rsp), %r8
	movq	224(%rsp), %r9
	movq	232(%rsp), %r10
	movq	240(%rsp), %r11
	subq	%rax, %r8
	sbbq	%rsi, %r9
	sbbq	%rcx, %r10
	sbbq	%rdi, %r11
	sbbq	%rdx, %rdx
	andq	$38, %rdx
	subq	%rdx, %r8
	sbbq	$0, %r9
	sbbq	$0, %r10
	sbbq	$0, %r11
	sbbq	%rdx, %rdx
	andq	$38, %rdx
	subq	%rdx, %r8
	movq	%r8, 248(%rsp)
	movq	%r9, 256(%rsp)
	movq	%r10, 264(%rsp)
	movq	%r11, 272(%rsp)
	xorq	%r8, %r8
	movq	216(%rsp), %rdx
	MULXq	%rax, %r10, %r9
	MULXq	%rsi, %rbx, %r11
	adcxq	%rbx, %r9
	MULXq	%rcx, %rbp, %rbx
	adcxq	%rbp, %r11
	MULXq	%rdi, %rdx, %rbp
	adcxq	%rdx, %rbx
	adcxq	%r8, %rbp
	movq	224(%rsp), %rdx
	MULXq	%rax, %r13, %r12
	adoxq	%r13, %r9
	adcxq	%r12, %r11
	MULXq	%rsi, %r13, %r12
	adoxq	%r13, %r11
	adcxq	%r12, %rbx
	MULXq	%rcx, %r13, %r12
	adoxq	%r13, %rbx
	adcxq	%r12, %rbp
	MULXq	%rdi, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%r8, %r12
	adoxq	%r8, %r12
	movq	232(%rsp), %rdx
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %r11
	adcxq	%r13, %rbx
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %rbx
	adcxq	%r13, %rbp
	MULXq	%rcx, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rdi, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%r8, %r13
	adoxq	%r8, %r13
	movq	240(%rsp), %rdx
	MULXq	%rax, %r14, %rax
	adoxq	%r14, %rbx
	adcxq	%rax, %rbp
	MULXq	%rsi, %rsi, %rax
	adoxq	%rsi, %rbp
	adcxq	%rax, %r12
	MULXq	%rcx, %rcx, %rax
	adoxq	%rcx, %r12
	adcxq	%rax, %r13
	MULXq	%rdi, %rcx, %rax
	adoxq	%rcx, %r13
	adcxq	%r8, %rax
	adoxq	%r8, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rsi, %rcx
	adoxq	%rsi, %r10
	adcxq	%rcx, %r9
	MULXq	%r12, %rsi, %rcx
	adoxq	%rsi, %r9
	adcxq	%rcx, %r11
	MULXq	%r13, %rsi, %rcx
	adoxq	%rsi, %r11
	adcxq	%rcx, %rbx
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %rbx
	adcxq	%r8, %rax
	adoxq	%r8, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r10
	adcq	%r8, %r9
	adcq	%r8, %r11
	adcq	%r8, %rbx
	sbbq	%r8, %r8
	andq	$38, %r8
	addq	%r8, %r10
	movq	%r10, 56(%rsp)
	movq	%r9, 64(%rsp)
	movq	%r11, 72(%rsp)
	movq	%rbx, 80(%rsp)
	movq	280(%rsp), %rdx
	movq	288(%rsp), %r11
	movq	296(%rsp), %r13
	movq	304(%rsp), %rbx
	xorq	%rax, %rax
	MULXq	%rdx, %rsi, %rcx
	MULXq	%r11, %r8, %rdi
	MULXq	%r13, %r10, %r9
	adcxq	%r10, %rdi
	MULXq	%rbx, %rdx, %r10
	adcxq	%rdx, %r9
	movq	%r11, %rdx
	MULXq	%r13, %rbp, %r11
	adoxq	%rbp, %r9
	adcxq	%r11, %r10
	MULXq	%rbx, %rbp, %r11
	adoxq	%rbp, %r10
	MULXq	%rdx, %r12, %rbp
	movq	%r13, %rdx
	MULXq	%rbx, %r14, %r13
	adcxq	%r14, %r11
	adoxq	%rax, %r11
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	MULXq	%rdx, %r15, %r14
	movq	%rbx, %rdx
	MULXq	%rdx, %rdx, %rbx
	adcxq	%r8, %r8
	adoxq	%rcx, %r8
	adcxq	%rdi, %rdi
	adoxq	%r12, %rdi
	adcxq	%r9, %r9
	adoxq	%rbp, %r9
	adcxq	%r10, %r10
	adoxq	%r15, %r10
	adcxq	%r11, %r11
	adoxq	%r14, %r11
	adcxq	%r13, %r13
	adoxq	%rdx, %r13
	adcxq	%rax, %rbx
	adoxq	%rax, %rbx
	movq	$38, %rdx
	MULXq	%r10, %r10, %rcx
	adoxq	%r10, %rsi
	adcxq	%rcx, %r8
	MULXq	%r11, %r10, %rcx
	adoxq	%r10, %r8
	adcxq	%rcx, %rdi
	MULXq	%r13, %r10, %rcx
	adoxq	%r10, %rdi
	adcxq	%rcx, %r9
	MULXq	%rbx, %rdx, %rcx
	adoxq	%rdx, %r9
	adcxq	%rax, %rcx
	adoxq	%rax, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rsi
	adcq	%rax, %r8
	adcq	%rax, %rdi
	adcq	%rax, %r9
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rsi
	movq	%rsi, 280(%rsp)
	movq	%r8, 288(%rsp)
	movq	%rdi, 296(%rsp)
	movq	%r9, 304(%rsp)
	movq	$121665, %rdx
	MULXq	248(%rsp), %rcx, %rax
	MULXq	256(%rsp), %rdi, %rsi
	addq	%rdi, %rax
	MULXq	264(%rsp), %r8, %rdi
	adcq	%r8, %rsi
	MULXq	272(%rsp), %r9, %r8
	adcq	%r9, %rdi
	adcq	$0, %r8
	imulq	$38, %r8, %r8
	addq	%r8, %rcx
	adcq	$0, %rax
	adcq	$0, %rsi
	adcq	$0, %rdi
	sbbq	%rdx, %rdx
	andq	$38, %rdx
	addq	%rdx, %rcx
	movq	%rcx, 312(%rsp)
	movq	%rax, 320(%rsp)
	movq	%rsi, 328(%rsp)
	movq	%rdi, 336(%rsp)
	movq	184(%rsp), %rdx
	movq	192(%rsp), %r11
	movq	200(%rsp), %r13
	movq	208(%rsp), %rbx
	xorq	%rax, %rax
	MULXq	%rdx, %rsi, %rcx
	MULXq	%r11, %r8, %rdi
	MULXq	%r13, %r10, %r9
	adcxq	%r10, %rdi
	MULXq	%rbx, %rdx, %r10
	adcxq	%rdx, %r9
	movq	%r11, %rdx
	MULXq	%r13, %rbp, %r11
	adoxq	%rbp, %r9
	adcxq	%r11, %r10
	MULXq	%rbx, %rbp, %r11
	adoxq	%rbp, %r10
	MULXq	%rdx, %r12, %rbp
	movq	%r13, %rdx
	MULXq	%rbx, %r14, %r13
	adcxq	%r14, %r11
	adoxq	%rax, %r11
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	MULXq	%rdx, %r15, %r14
	movq	%rbx, %rdx
	MULXq	%rdx, %rdx, %rbx
	adcxq	%r8, %r8
	adoxq	%rcx, %r8
	adcxq	%rdi, %rdi
	adoxq	%r12, %rdi
	adcxq	%r9, %r9
	adoxq	%rbp, %r9
	adcxq	%r10, %r10
	adoxq	%r15, %r10
	adcxq	%r11, %r11
	adoxq	%r14, %r11
	adcxq	%r13, %r13
	adoxq	%rdx, %r13
	adcxq	%rax, %rbx
	adoxq	%rax, %rbx
	movq	$38, %rdx
	MULXq	%r10, %r10, %rcx
	adoxq	%r10, %rsi
	adcxq	%rcx, %r8
	MULXq	%r11, %r10, %rcx
	adoxq	%r10, %r8
	adcxq	%rcx, %rdi
	MULXq	%r13, %r10, %rcx
	adoxq	%r10, %rdi
	adcxq	%rcx, %r9
	MULXq	%rbx, %rdx, %rcx
	adoxq	%rdx, %r9
	adcxq	%rax, %rcx
	adoxq	%rax, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rsi
	adcq	%rax, %r8
	adcq	%rax, %rdi
	adcq	%rax, %r9
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rsi
	movq	%rsi, 88(%rsp)
	movq	%r8, 96(%rsp)
	movq	%rdi, 104(%rsp)
	movq	%r9, 112(%rsp)
	movq	216(%rsp), %rax
	movq	224(%rsp), %rcx
	movq	232(%rsp), %rdx
	movq	240(%rsp), %rsi
	xorq	%rdi, %rdi
	addq	312(%rsp), %rax
	adcq	320(%rsp), %rcx
	adcq	328(%rsp), %rdx
	adcq	336(%rsp), %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %rax
	adcq	$0, %rcx
	adcq	$0, %rdx
	adcq	$0, %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %rax
	movq	%rax, 312(%rsp)
	movq	%rcx, 320(%rsp)
	movq	%rdx, 328(%rsp)
	movq	%rsi, 336(%rsp)
	movq	280(%rsp), %r9
	movq	288(%rsp), %r10
	movq	296(%rsp), %r11
	movq	304(%rsp), %rbx
	xorq	%rax, %rax
	movq	152(%rsp), %rdx
	MULXq	%r9, %rsi, %rcx
	MULXq	%r10, %r8, %rdi
	adcxq	%r8, %rcx
	MULXq	%r11, %rbp, %r8
	adcxq	%rbp, %rdi
	MULXq	%rbx, %rdx, %rbp
	adcxq	%rdx, %r8
	adcxq	%rax, %rbp
	movq	160(%rsp), %rdx
	MULXq	%r9, %r13, %r12
	adoxq	%r13, %rcx
	adcxq	%r12, %rdi
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %rdi
	adcxq	%r12, %r8
	MULXq	%r11, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %rbp
	MULXq	%rbx, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rax, %r12
	adoxq	%rax, %r12
	movq	168(%rsp), %rdx
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %rdi
	adcxq	%r13, %r8
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %rbp
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rbx, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	movq	176(%rsp), %rdx
	MULXq	%r9, %r14, %r9
	adoxq	%r14, %r8
	adcxq	%r9, %rbp
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rbp
	adcxq	%r9, %r12
	MULXq	%r11, %r10, %r9
	adoxq	%r10, %r12
	adcxq	%r9, %r13
	MULXq	%rbx, %rdx, %r9
	adoxq	%rdx, %r13
	adcxq	%rax, %r9
	adoxq	%rax, %r9
	movq	$38, %rdx
	MULXq	%rbp, %r11, %r10
	adoxq	%r11, %rsi
	adcxq	%r10, %rcx
	MULXq	%r12, %r11, %r10
	adoxq	%r11, %rcx
	adcxq	%r10, %rdi
	MULXq	%r13, %r11, %r10
	adoxq	%r11, %rdi
	adcxq	%r10, %r8
	MULXq	%r9, %r9, %rdx
	adoxq	%r9, %r8
	adcxq	%rax, %rdx
	adoxq	%rax, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rsi
	adcq	%rax, %rcx
	adcq	%rax, %rdi
	adcq	%rax, %r8
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %rsi
	movq	%rsi, 120(%rsp)
	movq	%rcx, 128(%rsp)
	movq	%rdi, 136(%rsp)
	movq	%r8, 144(%rsp)
	movq	312(%rsp), %r8
	movq	320(%rsp), %r10
	movq	328(%rsp), %r11
	movq	336(%rsp), %rbx
	xorq	%rcx, %rcx
	movq	248(%rsp), %rdx
	MULXq	%r8, %rdi, %r9
	MULXq	%r10, %rsi, %rax
	adcxq	%rsi, %r9
	MULXq	%r11, %rbp, %rsi
	adcxq	%rbp, %rax
	MULXq	%rbx, %rdx, %rbp
	adcxq	%rdx, %rsi
	adcxq	%rcx, %rbp
	movq	256(%rsp), %rdx
	MULXq	%r8, %r13, %r12
	adoxq	%r13, %r9
	adcxq	%r12, %rax
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %rax
	adcxq	%r12, %rsi
	MULXq	%r11, %r13, %r12
	adoxq	%r13, %rsi
	adcxq	%r12, %rbp
	MULXq	%rbx, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rcx, %r12
	adoxq	%rcx, %r12
	movq	264(%rsp), %rdx
	MULXq	%r8, %r14, %r13
	adoxq	%r14, %rax
	adcxq	%r13, %rsi
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %rsi
	adcxq	%r13, %rbp
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rbx, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rcx, %r13
	adoxq	%rcx, %r13
	movq	272(%rsp), %rdx
	MULXq	%r8, %r14, %r8
	adoxq	%r14, %rsi
	adcxq	%r8, %rbp
	MULXq	%r10, %r10, %r8
	adoxq	%r10, %rbp
	adcxq	%r8, %r12
	MULXq	%r11, %r10, %r8
	adoxq	%r10, %r12
	adcxq	%r8, %r13
	MULXq	%rbx, %rdx, %r8
	adoxq	%rdx, %r13
	adcxq	%rcx, %r8
	adoxq	%rcx, %r8
	movq	$38, %rdx
	MULXq	%rbp, %r11, %r10
	adoxq	%r11, %rdi
	adcxq	%r10, %r9
	MULXq	%r12, %r11, %r10
	adoxq	%r11, %r9
	adcxq	%r10, %rax
	MULXq	%r13, %r11, %r10
	adoxq	%r11, %rax
	adcxq	%r10, %rsi
	MULXq	%r8, %r8, %rdx
	adoxq	%r8, %rsi
	adcxq	%rcx, %rdx
	adoxq	%rcx, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rdi
	adcq	%rcx, %r9
	adcq	%rcx, %rax
	adcq	%rcx, %rsi
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	addq	%rcx, %rdi
	movq	16(%rsp), %rcx
	cmpq	$0, %rcx
	jnbe	Ljade_scalarmult_curve25519_amd64_mulx$9
	movq	%rdi, 120(%rsp)
	movq	%r9, 128(%rsp)
	movq	%rax, 136(%rsp)
	movq	%rsi, 144(%rsp)
	xorq	%r10, %r10
	movq	%rdi, %rdx
	MULXq	%rdx, %r11, %rbx
	MULXq	%r9, %r8, %rdi
	MULXq	%rax, %rbp, %rcx
	adcxq	%rbp, %rdi
	MULXq	%rsi, %rdx, %rbp
	adcxq	%rdx, %rcx
	movq	%r9, %rdx
	MULXq	%rax, %r12, %r9
	adoxq	%r12, %rcx
	adcxq	%r9, %rbp
	MULXq	%rsi, %r12, %r9
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rax, %rdx
	MULXq	%rsi, %r14, %rax
	adcxq	%r14, %r9
	adoxq	%r10, %r9
	adcxq	%r10, %rax
	adoxq	%r10, %rax
	MULXq	%rdx, %r15, %r14
	movq	%rsi, %rdx
	MULXq	%rdx, %rdx, %rsi
	adcxq	%r8, %r8
	adoxq	%rbx, %r8
	adcxq	%rdi, %rdi
	adoxq	%r13, %rdi
	adcxq	%rcx, %rcx
	adoxq	%r12, %rcx
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r9, %r9
	adoxq	%r14, %r9
	adcxq	%rax, %rax
	adoxq	%rdx, %rax
	adcxq	%r10, %rsi
	adoxq	%r10, %rsi
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r11
	adcxq	%rbx, %r8
	MULXq	%r9, %rbx, %r9
	adoxq	%rbx, %r8
	adcxq	%r9, %rdi
	MULXq	%rax, %r9, %rax
	adoxq	%r9, %rdi
	adcxq	%rax, %rcx
	MULXq	%rsi, %rdx, %rax
	adoxq	%rdx, %rcx
	adcxq	%r10, %rax
	adoxq	%r10, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r11
	adcq	%r10, %r8
	adcq	%r10, %rdi
	adcq	%r10, %rcx
	sbbq	%r10, %r10
	andq	$38, %r10
	addq	%r10, %r11
	movq	%r11, 88(%rsp)
	movq	%r8, 96(%rsp)
	movq	%rdi, 104(%rsp)
	movq	%rcx, 112(%rsp)
	xorq	%rsi, %rsi
	movq	%r11, %rdx
	MULXq	%rdx, %r9, %rbx
	MULXq	%r8, %r11, %r10
	MULXq	%rdi, %rbp, %rax
	adcxq	%rbp, %r10
	MULXq	%rcx, %rdx, %rbp
	adcxq	%rdx, %rax
	movq	%r8, %rdx
	MULXq	%rdi, %r12, %r8
	adoxq	%r12, %rax
	adcxq	%r8, %rbp
	MULXq	%rcx, %r12, %r8
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rdi, %rdx
	MULXq	%rcx, %r14, %rdi
	adcxq	%r14, %r8
	adoxq	%rsi, %r8
	adcxq	%rsi, %rdi
	adoxq	%rsi, %rdi
	MULXq	%rdx, %r15, %r14
	movq	%rcx, %rdx
	MULXq	%rdx, %rdx, %rcx
	adcxq	%r11, %r11
	adoxq	%rbx, %r11
	adcxq	%r10, %r10
	adoxq	%r13, %r10
	adcxq	%rax, %rax
	adoxq	%r12, %rax
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r8, %r8
	adoxq	%r14, %r8
	adcxq	%rdi, %rdi
	adoxq	%rdx, %rdi
	adcxq	%rsi, %rcx
	adoxq	%rsi, %rcx
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r9
	adcxq	%rbx, %r11
	MULXq	%r8, %rbx, %r8
	adoxq	%rbx, %r11
	adcxq	%r8, %r10
	MULXq	%rdi, %r8, %rdi
	adoxq	%r8, %r10
	adcxq	%rdi, %rax
	MULXq	%rcx, %rdx, %rcx
	adoxq	%rdx, %rax
	adcxq	%rsi, %rcx
	adoxq	%rsi, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %r9
	adcq	%rsi, %r11
	adcq	%rsi, %r10
	adcq	%rsi, %rax
	sbbq	%rsi, %rsi
	andq	$38, %rsi
	addq	%rsi, %r9
	xorq	%rcx, %rcx
	movq	%r9, %rdx
	MULXq	%rdx, %rsi, %rbx
	MULXq	%r11, %r8, %rdi
	MULXq	%r10, %rbp, %r9
	adcxq	%rbp, %rdi
	MULXq	%rax, %rdx, %rbp
	adcxq	%rdx, %r9
	movq	%r11, %rdx
	MULXq	%r10, %r12, %r11
	adoxq	%r12, %r9
	adcxq	%r11, %rbp
	MULXq	%rax, %r12, %r11
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r10, %rdx
	MULXq	%rax, %r14, %r10
	adcxq	%r14, %r11
	adoxq	%rcx, %r11
	adcxq	%rcx, %r10
	adoxq	%rcx, %r10
	MULXq	%rdx, %r15, %r14
	movq	%rax, %rdx
	MULXq	%rdx, %rdx, %rax
	adcxq	%r8, %r8
	adoxq	%rbx, %r8
	adcxq	%rdi, %rdi
	adoxq	%r13, %rdi
	adcxq	%r9, %r9
	adoxq	%r12, %r9
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r11, %r11
	adoxq	%r14, %r11
	adcxq	%r10, %r10
	adoxq	%rdx, %r10
	adcxq	%rcx, %rax
	adoxq	%rcx, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rsi
	adcxq	%rbx, %r8
	MULXq	%r11, %rbx, %r11
	adoxq	%rbx, %r8
	adcxq	%r11, %rdi
	MULXq	%r10, %r11, %r10
	adoxq	%r11, %rdi
	adcxq	%r10, %r9
	MULXq	%rax, %rdx, %rax
	adoxq	%rdx, %r9
	adcxq	%rcx, %rax
	adoxq	%rcx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rsi
	adcq	%rcx, %r8
	adcq	%rcx, %rdi
	adcq	%rcx, %r9
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	addq	%rcx, %rsi
	xorq	%r10, %r10
	movq	120(%rsp), %rdx
	MULXq	%rsi, %rbx, %r11
	MULXq	%r8, %rcx, %rax
	adcxq	%rcx, %r11
	MULXq	%rdi, %rbp, %rcx
	adcxq	%rbp, %rax
	MULXq	%r9, %rdx, %rbp
	adcxq	%rdx, %rcx
	adcxq	%r10, %rbp
	movq	128(%rsp), %rdx
	MULXq	%rsi, %r13, %r12
	adoxq	%r13, %r11
	adcxq	%r12, %rax
	MULXq	%r8, %r13, %r12
	adoxq	%r13, %rax
	adcxq	%r12, %rcx
	MULXq	%rdi, %r13, %r12
	adoxq	%r13, %rcx
	adcxq	%r12, %rbp
	MULXq	%r9, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%r10, %r12
	adoxq	%r10, %r12
	movq	136(%rsp), %rdx
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %rax
	adcxq	%r13, %rcx
	MULXq	%r8, %r14, %r13
	adoxq	%r14, %rcx
	adcxq	%r13, %rbp
	MULXq	%rdi, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%r9, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%r10, %r13
	adoxq	%r10, %r13
	movq	144(%rsp), %rdx
	MULXq	%rsi, %r14, %rsi
	adoxq	%r14, %rcx
	adcxq	%rsi, %rbp
	MULXq	%r8, %r8, %rsi
	adoxq	%r8, %rbp
	adcxq	%rsi, %r12
	MULXq	%rdi, %rdi, %rsi
	adoxq	%rdi, %r12
	adcxq	%rsi, %r13
	MULXq	%r9, %rdx, %rsi
	adoxq	%rdx, %r13
	adcxq	%r10, %rsi
	adoxq	%r10, %rsi
	movq	$38, %rdx
	MULXq	%rbp, %r8, %rdi
	adoxq	%r8, %rbx
	adcxq	%rdi, %r11
	MULXq	%r12, %r8, %rdi
	adoxq	%r8, %r11
	adcxq	%rdi, %rax
	MULXq	%r13, %r8, %rdi
	adoxq	%r8, %rax
	adcxq	%rdi, %rcx
	MULXq	%rsi, %rsi, %rdx
	adoxq	%rsi, %rcx
	adcxq	%r10, %rdx
	adoxq	%r10, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rbx
	adcq	%r10, %r11
	adcq	%r10, %rax
	adcq	%r10, %rcx
	sbbq	%r10, %r10
	andq	$38, %r10
	addq	%r10, %rbx
	movq	%rbx, 120(%rsp)
	movq	%r11, 128(%rsp)
	movq	%rax, 136(%rsp)
	movq	%rcx, 144(%rsp)
	xorq	%rsi, %rsi
	movq	88(%rsp), %rdx
	MULXq	%rbx, %rdi, %r10
	MULXq	%r11, %r8, %r9
	adcxq	%r8, %r10
	MULXq	%rax, %rbp, %r8
	adcxq	%rbp, %r9
	MULXq	%rcx, %rdx, %rbp
	adcxq	%rdx, %r8
	adcxq	%rsi, %rbp
	movq	96(%rsp), %rdx
	MULXq	%rbx, %r13, %r12
	adoxq	%r13, %r10
	adcxq	%r12, %r9
	MULXq	%r11, %r13, %r12
	adoxq	%r13, %r9
	adcxq	%r12, %r8
	MULXq	%rax, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %rbp
	MULXq	%rcx, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rsi, %r12
	adoxq	%rsi, %r12
	movq	104(%rsp), %rdx
	MULXq	%rbx, %r14, %r13
	adoxq	%r14, %r9
	adcxq	%r13, %r8
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %rbp
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rcx, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rsi, %r13
	adoxq	%rsi, %r13
	movq	112(%rsp), %rdx
	MULXq	%rbx, %r14, %rbx
	adoxq	%r14, %r8
	adcxq	%rbx, %rbp
	MULXq	%r11, %rbx, %r11
	adoxq	%rbx, %rbp
	adcxq	%r11, %r12
	MULXq	%rax, %r11, %rax
	adoxq	%r11, %r12
	adcxq	%rax, %r13
	MULXq	%rcx, %rcx, %rax
	adoxq	%rcx, %r13
	adcxq	%rsi, %rax
	adoxq	%rsi, %rax
	movq	$38, %rdx
	MULXq	%rbp, %r11, %rcx
	adoxq	%r11, %rdi
	adcxq	%rcx, %r10
	MULXq	%r12, %r11, %rcx
	adoxq	%r11, %r10
	adcxq	%rcx, %r9
	MULXq	%r13, %r11, %rcx
	adoxq	%r11, %r9
	adcxq	%rcx, %r8
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r8
	adcxq	%rsi, %rax
	adoxq	%rsi, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rdi
	adcq	%rsi, %r10
	adcq	%rsi, %r9
	adcq	%rsi, %r8
	sbbq	%rsi, %rsi
	andq	$38, %rsi
	addq	%rsi, %rdi
	movq	%rdi, 88(%rsp)
	movq	%r10, 96(%rsp)
	movq	%r9, 104(%rsp)
	movq	%r8, 112(%rsp)
	xorq	%r11, %r11
	movq	%rdi, %rdx
	MULXq	%rdx, %rax, %rbx
	MULXq	%r10, %rsi, %rcx
	MULXq	%r9, %rbp, %rdi
	adcxq	%rbp, %rcx
	MULXq	%r8, %rdx, %rbp
	adcxq	%rdx, %rdi
	movq	%r10, %rdx
	MULXq	%r9, %r12, %r10
	adoxq	%r12, %rdi
	adcxq	%r10, %rbp
	MULXq	%r8, %r12, %r10
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r9, %rdx
	MULXq	%r8, %r14, %r9
	adcxq	%r14, %r10
	adoxq	%r11, %r10
	adcxq	%r11, %r9
	adoxq	%r11, %r9
	MULXq	%rdx, %r15, %r14
	movq	%r8, %rdx
	MULXq	%rdx, %rdx, %r8
	adcxq	%rsi, %rsi
	adoxq	%rbx, %rsi
	adcxq	%rcx, %rcx
	adoxq	%r13, %rcx
	adcxq	%rdi, %rdi
	adoxq	%r12, %rdi
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r10, %r10
	adoxq	%r14, %r10
	adcxq	%r9, %r9
	adoxq	%rdx, %r9
	adcxq	%r11, %r8
	adoxq	%r11, %r8
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rax
	adcxq	%rbx, %rsi
	MULXq	%r10, %rbx, %r10
	adoxq	%rbx, %rsi
	adcxq	%r10, %rcx
	MULXq	%r9, %r10, %r9
	adoxq	%r10, %rcx
	adcxq	%r9, %rdi
	MULXq	%r8, %r8, %rdx
	adoxq	%r8, %rdi
	adcxq	%r11, %rdx
	adoxq	%r11, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rax
	adcq	%r11, %rsi
	adcq	%r11, %rcx
	adcq	%r11, %rdi
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rax
	xorq	%r11, %r11
	movq	120(%rsp), %rdx
	MULXq	%rax, %rbx, %r10
	MULXq	%rsi, %r9, %r8
	adcxq	%r9, %r10
	MULXq	%rcx, %rbp, %r9
	adcxq	%rbp, %r8
	MULXq	%rdi, %rdx, %rbp
	adcxq	%rdx, %r9
	adcxq	%r11, %rbp
	movq	128(%rsp), %rdx
	MULXq	%rax, %r13, %r12
	adoxq	%r13, %r10
	adcxq	%r12, %r8
	MULXq	%rsi, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %r9
	MULXq	%rcx, %r13, %r12
	adoxq	%r13, %r9
	adcxq	%r12, %rbp
	MULXq	%rdi, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%r11, %r12
	adoxq	%r11, %r12
	movq	136(%rsp), %rdx
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %r9
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %r9
	adcxq	%r13, %rbp
	MULXq	%rcx, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rdi, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%r11, %r13
	adoxq	%r11, %r13
	movq	144(%rsp), %rdx
	MULXq	%rax, %r14, %rax
	adoxq	%r14, %r9
	adcxq	%rax, %rbp
	MULXq	%rsi, %rsi, %rax
	adoxq	%rsi, %rbp
	adcxq	%rax, %r12
	MULXq	%rcx, %rcx, %rax
	adoxq	%rcx, %r12
	adcxq	%rax, %r13
	MULXq	%rdi, %rcx, %rax
	adoxq	%rcx, %r13
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rsi, %rcx
	adoxq	%rsi, %rbx
	adcxq	%rcx, %r10
	MULXq	%r12, %rsi, %rcx
	adoxq	%rsi, %r10
	adcxq	%rcx, %r8
	MULXq	%r13, %rsi, %rcx
	adoxq	%rsi, %r8
	adcxq	%rcx, %r9
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r9
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rbx
	adcq	%r11, %r10
	adcq	%r11, %r8
	adcq	%r11, %r9
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rbx
	movq	%rbx, 120(%rsp)
	movq	%r10, 128(%rsp)
	movq	%r8, 136(%rsp)
	movq	%r9, 144(%rsp)
	xorq	%r11, %r11
	movq	%rbx, %rdx
	MULXq	%rdx, %rdi, %rbx
	MULXq	%r10, %rax, %rsi
	MULXq	%r8, %rbp, %rcx
	adcxq	%rbp, %rsi
	MULXq	%r9, %rdx, %rbp
	adcxq	%rdx, %rcx
	movq	%r10, %rdx
	MULXq	%r8, %r12, %r10
	adoxq	%r12, %rcx
	adcxq	%r10, %rbp
	MULXq	%r9, %r12, %r10
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r8, %rdx
	MULXq	%r9, %r14, %r8
	adcxq	%r14, %r10
	adoxq	%r11, %r10
	adcxq	%r11, %r8
	adoxq	%r11, %r8
	MULXq	%rdx, %r15, %r14
	movq	%r9, %rdx
	MULXq	%rdx, %rdx, %r9
	adcxq	%rax, %rax
	adoxq	%rbx, %rax
	adcxq	%rsi, %rsi
	adoxq	%r13, %rsi
	adcxq	%rcx, %rcx
	adoxq	%r12, %rcx
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r10, %r10
	adoxq	%r14, %r10
	adcxq	%r8, %r8
	adoxq	%rdx, %r8
	adcxq	%r11, %r9
	adoxq	%r11, %r9
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rdi
	adcxq	%rbx, %rax
	MULXq	%r10, %rbx, %r10
	adoxq	%rbx, %rax
	adcxq	%r10, %rsi
	MULXq	%r8, %r10, %r8
	adoxq	%r10, %rsi
	adcxq	%r8, %rcx
	MULXq	%r9, %r8, %rdx
	adoxq	%r8, %rcx
	adcxq	%r11, %rdx
	adoxq	%r11, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rdi
	adcq	%r11, %rax
	adcq	%r11, %rsi
	adcq	%r11, %rcx
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdi
	movl	$2, %edx
Ljade_scalarmult_curve25519_amd64_mulx$8:
	movl	%edx, 344(%rsp)
	xorq	%r11, %r11
	movq	%rdi, %rdx
	MULXq	%rdx, %rdi, %rbx
	MULXq	%rax, %r9, %r8
	MULXq	%rsi, %rbp, %r10
	adcxq	%rbp, %r8
	MULXq	%rcx, %rdx, %rbp
	adcxq	%rdx, %r10
	movq	%rax, %rdx
	MULXq	%rsi, %r12, %rax
	adoxq	%r12, %r10
	adcxq	%rax, %rbp
	MULXq	%rcx, %r12, %rax
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rsi, %rdx
	MULXq	%rcx, %r14, %rsi
	adcxq	%r14, %rax
	adoxq	%r11, %rax
	adcxq	%r11, %rsi
	adoxq	%r11, %rsi
	MULXq	%rdx, %r15, %r14
	movq	%rcx, %rdx
	MULXq	%rdx, %rdx, %rcx
	adcxq	%r9, %r9
	adoxq	%rbx, %r9
	adcxq	%r8, %r8
	adoxq	%r13, %r8
	adcxq	%r10, %r10
	adoxq	%r12, %r10
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rax, %rax
	adoxq	%r14, %rax
	adcxq	%rsi, %rsi
	adoxq	%rdx, %rsi
	adcxq	%r11, %rcx
	adoxq	%r11, %rcx
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rdi
	adcxq	%rbx, %r9
	MULXq	%rax, %rbx, %rax
	adoxq	%rbx, %r9
	adcxq	%rax, %r8
	MULXq	%rsi, %rsi, %rax
	adoxq	%rsi, %r8
	adcxq	%rax, %r10
	MULXq	%rcx, %rcx, %rax
	adoxq	%rcx, %r10
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rdi
	adcq	%r11, %r9
	adcq	%r11, %r8
	adcq	%r11, %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdi
	xorq	%r11, %r11
	movq	%rdi, %rdx
	MULXq	%rdx, %rdi, %rbx
	MULXq	%r9, %rax, %rsi
	MULXq	%r8, %rbp, %rcx
	adcxq	%rbp, %rsi
	MULXq	%r10, %rdx, %rbp
	adcxq	%rdx, %rcx
	movq	%r9, %rdx
	MULXq	%r8, %r12, %r9
	adoxq	%r12, %rcx
	adcxq	%r9, %rbp
	MULXq	%r10, %r12, %r9
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r8, %rdx
	MULXq	%r10, %r14, %r8
	adcxq	%r14, %r9
	adoxq	%r11, %r9
	adcxq	%r11, %r8
	adoxq	%r11, %r8
	MULXq	%rdx, %r15, %r14
	movq	%r10, %rdx
	MULXq	%rdx, %rdx, %r10
	adcxq	%rax, %rax
	adoxq	%rbx, %rax
	adcxq	%rsi, %rsi
	adoxq	%r13, %rsi
	adcxq	%rcx, %rcx
	adoxq	%r12, %rcx
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r9, %r9
	adoxq	%r14, %r9
	adcxq	%r8, %r8
	adoxq	%rdx, %r8
	adcxq	%r11, %r10
	adoxq	%r11, %r10
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rdi
	adcxq	%rbx, %rax
	MULXq	%r9, %rbx, %r9
	adoxq	%rbx, %rax
	adcxq	%r9, %rsi
	MULXq	%r8, %r9, %r8
	adoxq	%r9, %rsi
	adcxq	%r8, %rcx
	MULXq	%r10, %r8, %rdx
	adoxq	%r8, %rcx
	adcxq	%r11, %rdx
	adoxq	%r11, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rdi
	adcq	%r11, %rax
	adcq	%r11, %rsi
	adcq	%r11, %rcx
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rdi
	movl	344(%rsp), %edx
	decl	%edx
	jne 	Ljade_scalarmult_curve25519_amd64_mulx$8
	xorq	%rbx, %rbx
	movq	120(%rsp), %rdx
	MULXq	%rdi, %r8, %r11
	MULXq	%rax, %r10, %r9
	adcxq	%r10, %r11
	MULXq	%rsi, %rbp, %r10
	adcxq	%rbp, %r9
	MULXq	%rcx, %rdx, %rbp
	adcxq	%rdx, %r10
	adcxq	%rbx, %rbp
	movq	128(%rsp), %rdx
	MULXq	%rdi, %r13, %r12
	adoxq	%r13, %r11
	adcxq	%r12, %r9
	MULXq	%rax, %r13, %r12
	adoxq	%r13, %r9
	adcxq	%r12, %r10
	MULXq	%rsi, %r13, %r12
	adoxq	%r13, %r10
	adcxq	%r12, %rbp
	MULXq	%rcx, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rbx, %r12
	adoxq	%rbx, %r12
	movq	136(%rsp), %rdx
	MULXq	%rdi, %r14, %r13
	adoxq	%r14, %r9
	adcxq	%r13, %r10
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %r10
	adcxq	%r13, %rbp
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rcx, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rbx, %r13
	adoxq	%rbx, %r13
	movq	144(%rsp), %rdx
	MULXq	%rdi, %r14, %rdi
	adoxq	%r14, %r10
	adcxq	%rdi, %rbp
	MULXq	%rax, %rdi, %rax
	adoxq	%rdi, %rbp
	adcxq	%rax, %r12
	MULXq	%rsi, %rsi, %rax
	adoxq	%rsi, %r12
	adcxq	%rax, %r13
	MULXq	%rcx, %rcx, %rax
	adoxq	%rcx, %r13
	adcxq	%rbx, %rax
	adoxq	%rbx, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rsi, %rcx
	adoxq	%rsi, %r8
	adcxq	%rcx, %r11
	MULXq	%r12, %rsi, %rcx
	adoxq	%rsi, %r11
	adcxq	%rcx, %r9
	MULXq	%r13, %rsi, %rcx
	adoxq	%rsi, %r9
	adcxq	%rcx, %r10
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r10
	adcxq	%rbx, %rax
	adoxq	%rbx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r8
	adcq	%rbx, %r11
	adcq	%rbx, %r9
	adcq	%rbx, %r10
	sbbq	%rbx, %rbx
	andq	$38, %rbx
	addq	%rbx, %r8
	movq	%r8, 120(%rsp)
	movq	%r11, 128(%rsp)
	movq	%r9, 136(%rsp)
	movq	%r10, 144(%rsp)
	movl	$5, %eax
Ljade_scalarmult_curve25519_amd64_mulx$7:
	movl	%eax, 344(%rsp)
	xorq	%rdi, %rdi
	movq	%r8, %rdx
	MULXq	%rdx, %r8, %rbx
	MULXq	%r11, %rcx, %rax
	MULXq	%r9, %rbp, %rsi
	adcxq	%rbp, %rax
	MULXq	%r10, %rdx, %rbp
	adcxq	%rdx, %rsi
	movq	%r11, %rdx
	MULXq	%r9, %r12, %r11
	adoxq	%r12, %rsi
	adcxq	%r11, %rbp
	MULXq	%r10, %r12, %r11
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r9, %rdx
	MULXq	%r10, %r14, %r9
	adcxq	%r14, %r11
	adoxq	%rdi, %r11
	adcxq	%rdi, %r9
	adoxq	%rdi, %r9
	MULXq	%rdx, %r15, %r14
	movq	%r10, %rdx
	MULXq	%rdx, %rdx, %r10
	adcxq	%rcx, %rcx
	adoxq	%rbx, %rcx
	adcxq	%rax, %rax
	adoxq	%r13, %rax
	adcxq	%rsi, %rsi
	adoxq	%r12, %rsi
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r11, %r11
	adoxq	%r14, %r11
	adcxq	%r9, %r9
	adoxq	%rdx, %r9
	adcxq	%rdi, %r10
	adoxq	%rdi, %r10
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r8
	adcxq	%rbx, %rcx
	MULXq	%r11, %rbx, %r11
	adoxq	%rbx, %rcx
	adcxq	%r11, %rax
	MULXq	%r9, %r11, %r9
	adoxq	%r11, %rax
	adcxq	%r9, %rsi
	MULXq	%r10, %r9, %rdx
	adoxq	%r9, %rsi
	adcxq	%rdi, %rdx
	adoxq	%rdi, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %r8
	adcq	%rdi, %rcx
	adcq	%rdi, %rax
	adcq	%rdi, %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %r8
	xorq	%rdi, %rdi
	movq	%r8, %rdx
	MULXq	%rdx, %r8, %rbx
	MULXq	%rcx, %r11, %r9
	MULXq	%rax, %rbp, %r10
	adcxq	%rbp, %r9
	MULXq	%rsi, %rdx, %rbp
	adcxq	%rdx, %r10
	movq	%rcx, %rdx
	MULXq	%rax, %r12, %rcx
	adoxq	%r12, %r10
	adcxq	%rcx, %rbp
	MULXq	%rsi, %r12, %rcx
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rax, %rdx
	MULXq	%rsi, %r14, %rax
	adcxq	%r14, %rcx
	adoxq	%rdi, %rcx
	adcxq	%rdi, %rax
	adoxq	%rdi, %rax
	MULXq	%rdx, %r15, %r14
	movq	%rsi, %rdx
	MULXq	%rdx, %rdx, %rsi
	adcxq	%r11, %r11
	adoxq	%rbx, %r11
	adcxq	%r9, %r9
	adoxq	%r13, %r9
	adcxq	%r10, %r10
	adoxq	%r12, %r10
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rcx, %rcx
	adoxq	%r14, %rcx
	adcxq	%rax, %rax
	adoxq	%rdx, %rax
	adcxq	%rdi, %rsi
	adoxq	%rdi, %rsi
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r8
	adcxq	%rbx, %r11
	MULXq	%rcx, %rbx, %rcx
	adoxq	%rbx, %r11
	adcxq	%rcx, %r9
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r9
	adcxq	%rax, %r10
	MULXq	%rsi, %rcx, %rax
	adoxq	%rcx, %r10
	adcxq	%rdi, %rax
	adoxq	%rdi, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r8
	adcq	%rdi, %r11
	adcq	%rdi, %r9
	adcq	%rdi, %r10
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %r8
	movl	344(%rsp), %eax
	decl	%eax
	jne 	Ljade_scalarmult_curve25519_amd64_mulx$7
	xorq	%rbx, %rbx
	movq	120(%rsp), %rdx
	MULXq	%r8, %rax, %rcx
	MULXq	%r11, %rsi, %rdi
	adcxq	%rsi, %rcx
	MULXq	%r9, %rbp, %rsi
	adcxq	%rbp, %rdi
	MULXq	%r10, %rdx, %rbp
	adcxq	%rdx, %rsi
	adcxq	%rbx, %rbp
	movq	128(%rsp), %rdx
	MULXq	%r8, %r13, %r12
	adoxq	%r13, %rcx
	adcxq	%r12, %rdi
	MULXq	%r11, %r13, %r12
	adoxq	%r13, %rdi
	adcxq	%r12, %rsi
	MULXq	%r9, %r13, %r12
	adoxq	%r13, %rsi
	adcxq	%r12, %rbp
	MULXq	%r10, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rbx, %r12
	adoxq	%rbx, %r12
	movq	136(%rsp), %rdx
	MULXq	%r8, %r14, %r13
	adoxq	%r14, %rdi
	adcxq	%r13, %rsi
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %rsi
	adcxq	%r13, %rbp
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%r10, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rbx, %r13
	adoxq	%rbx, %r13
	movq	144(%rsp), %rdx
	MULXq	%r8, %r14, %r8
	adoxq	%r14, %rsi
	adcxq	%r8, %rbp
	MULXq	%r11, %r11, %r8
	adoxq	%r11, %rbp
	adcxq	%r8, %r12
	MULXq	%r9, %r9, %r8
	adoxq	%r9, %r12
	adcxq	%r8, %r13
	MULXq	%r10, %rdx, %r8
	adoxq	%rdx, %r13
	adcxq	%rbx, %r8
	adoxq	%rbx, %r8
	movq	$38, %rdx
	MULXq	%rbp, %r10, %r9
	adoxq	%r10, %rax
	adcxq	%r9, %rcx
	MULXq	%r12, %r10, %r9
	adoxq	%r10, %rcx
	adcxq	%r9, %rdi
	MULXq	%r13, %r10, %r9
	adoxq	%r10, %rdi
	adcxq	%r9, %rsi
	MULXq	%r8, %r8, %rdx
	adoxq	%r8, %rsi
	adcxq	%rbx, %rdx
	adoxq	%rbx, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rax
	adcq	%rbx, %rcx
	adcq	%rbx, %rdi
	adcq	%rbx, %rsi
	sbbq	%rbx, %rbx
	andq	$38, %rbx
	addq	%rbx, %rax
	movq	%rax, 152(%rsp)
	movq	%rcx, 160(%rsp)
	movq	%rdi, 168(%rsp)
	movq	%rsi, 176(%rsp)
	movl	$10, %edx
Ljade_scalarmult_curve25519_amd64_mulx$6:
	movl	%edx, 344(%rsp)
	xorq	%r11, %r11
	movq	%rax, %rdx
	MULXq	%rdx, %rax, %rbx
	MULXq	%rcx, %r9, %r8
	MULXq	%rdi, %rbp, %r10
	adcxq	%rbp, %r8
	MULXq	%rsi, %rdx, %rbp
	adcxq	%rdx, %r10
	movq	%rcx, %rdx
	MULXq	%rdi, %r12, %rcx
	adoxq	%r12, %r10
	adcxq	%rcx, %rbp
	MULXq	%rsi, %r12, %rcx
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rdi, %rdx
	MULXq	%rsi, %r14, %rdi
	adcxq	%r14, %rcx
	adoxq	%r11, %rcx
	adcxq	%r11, %rdi
	adoxq	%r11, %rdi
	MULXq	%rdx, %r15, %r14
	movq	%rsi, %rdx
	MULXq	%rdx, %rdx, %rsi
	adcxq	%r9, %r9
	adoxq	%rbx, %r9
	adcxq	%r8, %r8
	adoxq	%r13, %r8
	adcxq	%r10, %r10
	adoxq	%r12, %r10
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rcx, %rcx
	adoxq	%r14, %rcx
	adcxq	%rdi, %rdi
	adoxq	%rdx, %rdi
	adcxq	%r11, %rsi
	adoxq	%r11, %rsi
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rax
	adcxq	%rbx, %r9
	MULXq	%rcx, %rbx, %rcx
	adoxq	%rbx, %r9
	adcxq	%rcx, %r8
	MULXq	%rdi, %rdi, %rcx
	adoxq	%rdi, %r8
	adcxq	%rcx, %r10
	MULXq	%rsi, %rdx, %rcx
	adoxq	%rdx, %r10
	adcxq	%r11, %rcx
	adoxq	%r11, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rax
	adcq	%r11, %r9
	adcq	%r11, %r8
	adcq	%r11, %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rax
	xorq	%r11, %r11
	movq	%rax, %rdx
	MULXq	%rdx, %rax, %rbx
	MULXq	%r9, %rcx, %rdi
	MULXq	%r8, %rbp, %rsi
	adcxq	%rbp, %rdi
	MULXq	%r10, %rdx, %rbp
	adcxq	%rdx, %rsi
	movq	%r9, %rdx
	MULXq	%r8, %r12, %r9
	adoxq	%r12, %rsi
	adcxq	%r9, %rbp
	MULXq	%r10, %r12, %r9
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r8, %rdx
	MULXq	%r10, %r14, %r8
	adcxq	%r14, %r9
	adoxq	%r11, %r9
	adcxq	%r11, %r8
	adoxq	%r11, %r8
	MULXq	%rdx, %r15, %r14
	movq	%r10, %rdx
	MULXq	%rdx, %rdx, %r10
	adcxq	%rcx, %rcx
	adoxq	%rbx, %rcx
	adcxq	%rdi, %rdi
	adoxq	%r13, %rdi
	adcxq	%rsi, %rsi
	adoxq	%r12, %rsi
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r9, %r9
	adoxq	%r14, %r9
	adcxq	%r8, %r8
	adoxq	%rdx, %r8
	adcxq	%r11, %r10
	adoxq	%r11, %r10
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rax
	adcxq	%rbx, %rcx
	MULXq	%r9, %rbx, %r9
	adoxq	%rbx, %rcx
	adcxq	%r9, %rdi
	MULXq	%r8, %r9, %r8
	adoxq	%r9, %rdi
	adcxq	%r8, %rsi
	MULXq	%r10, %r8, %rdx
	adoxq	%r8, %rsi
	adcxq	%r11, %rdx
	adoxq	%r11, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rax
	adcq	%r11, %rcx
	adcq	%r11, %rdi
	adcq	%r11, %rsi
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rax
	movl	344(%rsp), %edx
	decl	%edx
	jne 	Ljade_scalarmult_curve25519_amd64_mulx$6
	xorq	%rbx, %rbx
	movq	152(%rsp), %rdx
	MULXq	%rax, %r11, %r9
	MULXq	%rcx, %r10, %r8
	adcxq	%r10, %r9
	MULXq	%rdi, %rbp, %r10
	adcxq	%rbp, %r8
	MULXq	%rsi, %rdx, %rbp
	adcxq	%rdx, %r10
	adcxq	%rbx, %rbp
	movq	160(%rsp), %rdx
	MULXq	%rax, %r13, %r12
	adoxq	%r13, %r9
	adcxq	%r12, %r8
	MULXq	%rcx, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %r10
	MULXq	%rdi, %r13, %r12
	adoxq	%r13, %r10
	adcxq	%r12, %rbp
	MULXq	%rsi, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rbx, %r12
	adoxq	%rbx, %r12
	movq	168(%rsp), %rdx
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %r10
	MULXq	%rcx, %r14, %r13
	adoxq	%r14, %r10
	adcxq	%r13, %rbp
	MULXq	%rdi, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%rsi, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rbx, %r13
	adoxq	%rbx, %r13
	movq	176(%rsp), %rdx
	MULXq	%rax, %r14, %rax
	adoxq	%r14, %r10
	adcxq	%rax, %rbp
	MULXq	%rcx, %rcx, %rax
	adoxq	%rcx, %rbp
	adcxq	%rax, %r12
	MULXq	%rdi, %rcx, %rax
	adoxq	%rcx, %r12
	adcxq	%rax, %r13
	MULXq	%rsi, %rcx, %rax
	adoxq	%rcx, %r13
	adcxq	%rbx, %rax
	adoxq	%rbx, %rax
	movq	$38, %rdx
	MULXq	%rbp, %rsi, %rcx
	adoxq	%rsi, %r11
	adcxq	%rcx, %r9
	MULXq	%r12, %rsi, %rcx
	adoxq	%rsi, %r9
	adcxq	%rcx, %r8
	MULXq	%r13, %rsi, %rcx
	adoxq	%rsi, %r8
	adcxq	%rcx, %r10
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r10
	adcxq	%rbx, %rax
	adoxq	%rbx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r11
	adcq	%rbx, %r9
	adcq	%rbx, %r8
	adcq	%rbx, %r10
	sbbq	%rbx, %rbx
	andq	$38, %rbx
	addq	%rbx, %r11
	movl	$5, %eax
Ljade_scalarmult_curve25519_amd64_mulx$5:
	movl	%eax, 344(%rsp)
	xorq	%rdi, %rdi
	movq	%r11, %rdx
	MULXq	%rdx, %r11, %rbx
	MULXq	%r9, %rcx, %rax
	MULXq	%r8, %rbp, %rsi
	adcxq	%rbp, %rax
	MULXq	%r10, %rdx, %rbp
	adcxq	%rdx, %rsi
	movq	%r9, %rdx
	MULXq	%r8, %r12, %r9
	adoxq	%r12, %rsi
	adcxq	%r9, %rbp
	MULXq	%r10, %r12, %r9
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r8, %rdx
	MULXq	%r10, %r14, %r8
	adcxq	%r14, %r9
	adoxq	%rdi, %r9
	adcxq	%rdi, %r8
	adoxq	%rdi, %r8
	MULXq	%rdx, %r15, %r14
	movq	%r10, %rdx
	MULXq	%rdx, %rdx, %r10
	adcxq	%rcx, %rcx
	adoxq	%rbx, %rcx
	adcxq	%rax, %rax
	adoxq	%r13, %rax
	adcxq	%rsi, %rsi
	adoxq	%r12, %rsi
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r9, %r9
	adoxq	%r14, %r9
	adcxq	%r8, %r8
	adoxq	%rdx, %r8
	adcxq	%rdi, %r10
	adoxq	%rdi, %r10
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r11
	adcxq	%rbx, %rcx
	MULXq	%r9, %rbx, %r9
	adoxq	%rbx, %rcx
	adcxq	%r9, %rax
	MULXq	%r8, %r9, %r8
	adoxq	%r9, %rax
	adcxq	%r8, %rsi
	MULXq	%r10, %r8, %rdx
	adoxq	%r8, %rsi
	adcxq	%rdi, %rdx
	adoxq	%rdi, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %r11
	adcq	%rdi, %rcx
	adcq	%rdi, %rax
	adcq	%rdi, %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %r11
	xorq	%rdi, %rdi
	movq	%r11, %rdx
	MULXq	%rdx, %r11, %rbx
	MULXq	%rcx, %r9, %r8
	MULXq	%rax, %rbp, %r10
	adcxq	%rbp, %r8
	MULXq	%rsi, %rdx, %rbp
	adcxq	%rdx, %r10
	movq	%rcx, %rdx
	MULXq	%rax, %r12, %rcx
	adoxq	%r12, %r10
	adcxq	%rcx, %rbp
	MULXq	%rsi, %r12, %rcx
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rax, %rdx
	MULXq	%rsi, %r14, %rax
	adcxq	%r14, %rcx
	adoxq	%rdi, %rcx
	adcxq	%rdi, %rax
	adoxq	%rdi, %rax
	MULXq	%rdx, %r15, %r14
	movq	%rsi, %rdx
	MULXq	%rdx, %rdx, %rsi
	adcxq	%r9, %r9
	adoxq	%rbx, %r9
	adcxq	%r8, %r8
	adoxq	%r13, %r8
	adcxq	%r10, %r10
	adoxq	%r12, %r10
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rcx, %rcx
	adoxq	%r14, %rcx
	adcxq	%rax, %rax
	adoxq	%rdx, %rax
	adcxq	%rdi, %rsi
	adoxq	%rdi, %rsi
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r11
	adcxq	%rbx, %r9
	MULXq	%rcx, %rbx, %rcx
	adoxq	%rbx, %r9
	adcxq	%rcx, %r8
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r8
	adcxq	%rax, %r10
	MULXq	%rsi, %rcx, %rax
	adoxq	%rcx, %r10
	adcxq	%rdi, %rax
	adoxq	%rdi, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r11
	adcq	%rdi, %r9
	adcq	%rdi, %r8
	adcq	%rdi, %r10
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %r11
	movl	344(%rsp), %eax
	decl	%eax
	jne 	Ljade_scalarmult_curve25519_amd64_mulx$5
	xorq	%rbx, %rbx
	movq	120(%rsp), %rdx
	MULXq	%r11, %rsi, %rax
	MULXq	%r9, %rcx, %rdi
	adcxq	%rcx, %rax
	MULXq	%r8, %rbp, %rcx
	adcxq	%rbp, %rdi
	MULXq	%r10, %rdx, %rbp
	adcxq	%rdx, %rcx
	adcxq	%rbx, %rbp
	movq	128(%rsp), %rdx
	MULXq	%r11, %r13, %r12
	adoxq	%r13, %rax
	adcxq	%r12, %rdi
	MULXq	%r9, %r13, %r12
	adoxq	%r13, %rdi
	adcxq	%r12, %rcx
	MULXq	%r8, %r13, %r12
	adoxq	%r13, %rcx
	adcxq	%r12, %rbp
	MULXq	%r10, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rbx, %r12
	adoxq	%rbx, %r12
	movq	136(%rsp), %rdx
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %rdi
	adcxq	%r13, %rcx
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %rcx
	adcxq	%r13, %rbp
	MULXq	%r8, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%r10, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rbx, %r13
	adoxq	%rbx, %r13
	movq	144(%rsp), %rdx
	MULXq	%r11, %r14, %r11
	adoxq	%r14, %rcx
	adcxq	%r11, %rbp
	MULXq	%r9, %r11, %r9
	adoxq	%r11, %rbp
	adcxq	%r9, %r12
	MULXq	%r8, %r9, %r8
	adoxq	%r9, %r12
	adcxq	%r8, %r13
	MULXq	%r10, %rdx, %r8
	adoxq	%rdx, %r13
	adcxq	%rbx, %r8
	adoxq	%rbx, %r8
	movq	$38, %rdx
	MULXq	%rbp, %r10, %r9
	adoxq	%r10, %rsi
	adcxq	%r9, %rax
	MULXq	%r12, %r10, %r9
	adoxq	%r10, %rax
	adcxq	%r9, %rdi
	MULXq	%r13, %r10, %r9
	adoxq	%r10, %rdi
	adcxq	%r9, %rcx
	MULXq	%r8, %r8, %rdx
	adoxq	%r8, %rcx
	adcxq	%rbx, %rdx
	adoxq	%rbx, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rsi
	adcq	%rbx, %rax
	adcq	%rbx, %rdi
	adcq	%rbx, %rcx
	sbbq	%rbx, %rbx
	andq	$38, %rbx
	addq	%rbx, %rsi
	movq	%rsi, 120(%rsp)
	movq	%rax, 128(%rsp)
	movq	%rdi, 136(%rsp)
	movq	%rcx, 144(%rsp)
	movl	$25, %edx
Ljade_scalarmult_curve25519_amd64_mulx$4:
	movl	%edx, 344(%rsp)
	xorq	%r11, %r11
	movq	%rsi, %rdx
	MULXq	%rdx, %rsi, %rbx
	MULXq	%rax, %r9, %r8
	MULXq	%rdi, %rbp, %r10
	adcxq	%rbp, %r8
	MULXq	%rcx, %rdx, %rbp
	adcxq	%rdx, %r10
	movq	%rax, %rdx
	MULXq	%rdi, %r12, %rax
	adoxq	%r12, %r10
	adcxq	%rax, %rbp
	MULXq	%rcx, %r12, %rax
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rdi, %rdx
	MULXq	%rcx, %r14, %rdi
	adcxq	%r14, %rax
	adoxq	%r11, %rax
	adcxq	%r11, %rdi
	adoxq	%r11, %rdi
	MULXq	%rdx, %r15, %r14
	movq	%rcx, %rdx
	MULXq	%rdx, %rdx, %rcx
	adcxq	%r9, %r9
	adoxq	%rbx, %r9
	adcxq	%r8, %r8
	adoxq	%r13, %r8
	adcxq	%r10, %r10
	adoxq	%r12, %r10
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rax, %rax
	adoxq	%r14, %rax
	adcxq	%rdi, %rdi
	adoxq	%rdx, %rdi
	adcxq	%r11, %rcx
	adoxq	%r11, %rcx
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rsi
	adcxq	%rbx, %r9
	MULXq	%rax, %rbx, %rax
	adoxq	%rbx, %r9
	adcxq	%rax, %r8
	MULXq	%rdi, %rdi, %rax
	adoxq	%rdi, %r8
	adcxq	%rax, %r10
	MULXq	%rcx, %rcx, %rax
	adoxq	%rcx, %r10
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rsi
	adcq	%r11, %r9
	adcq	%r11, %r8
	adcq	%r11, %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rsi
	xorq	%r11, %r11
	movq	%rsi, %rdx
	MULXq	%rdx, %rsi, %rbx
	MULXq	%r9, %rax, %rdi
	MULXq	%r8, %rbp, %rcx
	adcxq	%rbp, %rdi
	MULXq	%r10, %rdx, %rbp
	adcxq	%rdx, %rcx
	movq	%r9, %rdx
	MULXq	%r8, %r12, %r9
	adoxq	%r12, %rcx
	adcxq	%r9, %rbp
	MULXq	%r10, %r12, %r9
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r8, %rdx
	MULXq	%r10, %r14, %r8
	adcxq	%r14, %r9
	adoxq	%r11, %r9
	adcxq	%r11, %r8
	adoxq	%r11, %r8
	MULXq	%rdx, %r15, %r14
	movq	%r10, %rdx
	MULXq	%rdx, %rdx, %r10
	adcxq	%rax, %rax
	adoxq	%rbx, %rax
	adcxq	%rdi, %rdi
	adoxq	%r13, %rdi
	adcxq	%rcx, %rcx
	adoxq	%r12, %rcx
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r9, %r9
	adoxq	%r14, %r9
	adcxq	%r8, %r8
	adoxq	%rdx, %r8
	adcxq	%r11, %r10
	adoxq	%r11, %r10
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rsi
	adcxq	%rbx, %rax
	MULXq	%r9, %rbx, %r9
	adoxq	%rbx, %rax
	adcxq	%r9, %rdi
	MULXq	%r8, %r9, %r8
	adoxq	%r9, %rdi
	adcxq	%r8, %rcx
	MULXq	%r10, %r8, %rdx
	adoxq	%r8, %rcx
	adcxq	%r11, %rdx
	adoxq	%r11, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rsi
	adcq	%r11, %rax
	adcq	%r11, %rdi
	adcq	%r11, %rcx
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rsi
	movl	344(%rsp), %edx
	decl	%edx
	jne 	Ljade_scalarmult_curve25519_amd64_mulx$4
	xorq	%r11, %r11
	movq	120(%rsp), %rdx
	MULXq	%rsi, %rbp, %r9
	MULXq	%rax, %r8, %r10
	adcxq	%r8, %r9
	MULXq	%rdi, %rbx, %r8
	adcxq	%rbx, %r10
	MULXq	%rcx, %rdx, %rbx
	adcxq	%rdx, %r8
	adcxq	%r11, %rbx
	movq	128(%rsp), %rdx
	MULXq	%rsi, %r13, %r12
	adoxq	%r13, %r9
	adcxq	%r12, %r10
	MULXq	%rax, %r13, %r12
	adoxq	%r13, %r10
	adcxq	%r12, %r8
	MULXq	%rdi, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %rbx
	MULXq	%rcx, %rdx, %r12
	adoxq	%rdx, %rbx
	adcxq	%r11, %r12
	adoxq	%r11, %r12
	movq	136(%rsp), %rdx
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %r10
	adcxq	%r13, %r8
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %r8
	adcxq	%r13, %rbx
	MULXq	%rdi, %r14, %r13
	adoxq	%r14, %rbx
	adcxq	%r13, %r12
	MULXq	%rcx, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%r11, %r13
	adoxq	%r11, %r13
	movq	144(%rsp), %rdx
	MULXq	%rsi, %r14, %rsi
	adoxq	%r14, %r8
	adcxq	%rsi, %rbx
	MULXq	%rax, %rsi, %rax
	adoxq	%rsi, %rbx
	adcxq	%rax, %r12
	MULXq	%rdi, %rsi, %rax
	adoxq	%rsi, %r12
	adcxq	%rax, %r13
	MULXq	%rcx, %rcx, %rax
	adoxq	%rcx, %r13
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	movq	$38, %rdx
	MULXq	%rbx, %rsi, %rcx
	adoxq	%rsi, %rbp
	adcxq	%rcx, %r9
	MULXq	%r12, %rsi, %rcx
	adoxq	%rsi, %r9
	adcxq	%rcx, %r10
	MULXq	%r13, %rsi, %rcx
	adoxq	%rsi, %r10
	adcxq	%rcx, %r8
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r8
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rbp
	adcq	%r11, %r9
	adcq	%r11, %r10
	adcq	%r11, %r8
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %rbp
	movq	%rbp, 152(%rsp)
	movq	%r9, 160(%rsp)
	movq	%r10, 168(%rsp)
	movq	%r8, 176(%rsp)
	movl	$50, %eax
Ljade_scalarmult_curve25519_amd64_mulx$3:
	movl	%eax, 344(%rsp)
	xorq	%rdi, %rdi
	movq	%rbp, %rdx
	MULXq	%rdx, %r11, %rbx
	MULXq	%r9, %rcx, %rax
	MULXq	%r10, %rbp, %rsi
	adcxq	%rbp, %rax
	MULXq	%r8, %rdx, %rbp
	adcxq	%rdx, %rsi
	movq	%r9, %rdx
	MULXq	%r10, %r12, %r9
	adoxq	%r12, %rsi
	adcxq	%r9, %rbp
	MULXq	%r8, %r12, %r9
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%r10, %rdx
	MULXq	%r8, %r14, %r10
	adcxq	%r14, %r9
	adoxq	%rdi, %r9
	adcxq	%rdi, %r10
	adoxq	%rdi, %r10
	MULXq	%rdx, %r15, %r14
	movq	%r8, %rdx
	MULXq	%rdx, %rdx, %r8
	adcxq	%rcx, %rcx
	adoxq	%rbx, %rcx
	adcxq	%rax, %rax
	adoxq	%r13, %rax
	adcxq	%rsi, %rsi
	adoxq	%r12, %rsi
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r9, %r9
	adoxq	%r14, %r9
	adcxq	%r10, %r10
	adoxq	%rdx, %r10
	adcxq	%rdi, %r8
	adoxq	%rdi, %r8
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r11
	adcxq	%rbx, %rcx
	MULXq	%r9, %rbx, %r9
	adoxq	%rbx, %rcx
	adcxq	%r9, %rax
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rax
	adcxq	%r9, %rsi
	MULXq	%r8, %r8, %rdx
	adoxq	%r8, %rsi
	adcxq	%rdi, %rdx
	adoxq	%rdi, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %r11
	adcq	%rdi, %rcx
	adcq	%rdi, %rax
	adcq	%rdi, %rsi
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %r11
	xorq	%rdi, %rdi
	movq	%r11, %rdx
	MULXq	%rdx, %rbp, %r11
	MULXq	%rcx, %r9, %r10
	MULXq	%rax, %rbx, %r8
	adcxq	%rbx, %r10
	MULXq	%rsi, %rdx, %rbx
	adcxq	%rdx, %r8
	movq	%rcx, %rdx
	MULXq	%rax, %r12, %rcx
	adoxq	%r12, %r8
	adcxq	%rcx, %rbx
	MULXq	%rsi, %r12, %rcx
	adoxq	%r12, %rbx
	MULXq	%rdx, %r13, %r12
	movq	%rax, %rdx
	MULXq	%rsi, %r14, %rax
	adcxq	%r14, %rcx
	adoxq	%rdi, %rcx
	adcxq	%rdi, %rax
	adoxq	%rdi, %rax
	MULXq	%rdx, %r15, %r14
	movq	%rsi, %rdx
	MULXq	%rdx, %rdx, %rsi
	adcxq	%r9, %r9
	adoxq	%r11, %r9
	adcxq	%r10, %r10
	adoxq	%r13, %r10
	adcxq	%r8, %r8
	adoxq	%r12, %r8
	adcxq	%rbx, %rbx
	adoxq	%r15, %rbx
	adcxq	%rcx, %rcx
	adoxq	%r14, %rcx
	adcxq	%rax, %rax
	adoxq	%rdx, %rax
	adcxq	%rdi, %rsi
	adoxq	%rdi, %rsi
	movq	$38, %rdx
	MULXq	%rbx, %rbx, %r11
	adoxq	%rbx, %rbp
	adcxq	%r11, %r9
	MULXq	%rcx, %r11, %rcx
	adoxq	%r11, %r9
	adcxq	%rcx, %r10
	MULXq	%rax, %rcx, %rax
	adoxq	%rcx, %r10
	adcxq	%rax, %r8
	MULXq	%rsi, %rcx, %rax
	adoxq	%rcx, %r8
	adcxq	%rdi, %rax
	adoxq	%rdi, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rbp
	adcq	%rdi, %r9
	adcq	%rdi, %r10
	adcq	%rdi, %r8
	sbbq	%rdi, %rdi
	andq	$38, %rdi
	addq	%rdi, %rbp
	movl	344(%rsp), %eax
	decl	%eax
	jne 	Ljade_scalarmult_curve25519_amd64_mulx$3
	xorq	%rcx, %rcx
	movq	152(%rsp), %rdx
	MULXq	%rbp, %rbx, %r12
	MULXq	%r9, %rsi, %rax
	adcxq	%rsi, %r12
	MULXq	%r10, %rsi, %r11
	adcxq	%rsi, %rax
	MULXq	%r8, %rdx, %rsi
	adcxq	%rdx, %r11
	adcxq	%rcx, %rsi
	movq	160(%rsp), %rdx
	MULXq	%rbp, %r13, %rdi
	adoxq	%r13, %r12
	adcxq	%rdi, %rax
	MULXq	%r9, %r13, %rdi
	adoxq	%r13, %rax
	adcxq	%rdi, %r11
	MULXq	%r10, %r13, %rdi
	adoxq	%r13, %r11
	adcxq	%rdi, %rsi
	MULXq	%r8, %rdx, %rdi
	adoxq	%rdx, %rsi
	adcxq	%rcx, %rdi
	adoxq	%rcx, %rdi
	movq	168(%rsp), %rdx
	MULXq	%rbp, %r14, %r13
	adoxq	%r14, %rax
	adcxq	%r13, %r11
	MULXq	%r9, %r14, %r13
	adoxq	%r14, %r11
	adcxq	%r13, %rsi
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %rsi
	adcxq	%r13, %rdi
	MULXq	%r8, %rdx, %r13
	adoxq	%rdx, %rdi
	adcxq	%rcx, %r13
	adoxq	%rcx, %r13
	movq	176(%rsp), %rdx
	MULXq	%rbp, %r14, %rbp
	adoxq	%r14, %r11
	adcxq	%rbp, %rsi
	MULXq	%r9, %rbp, %r9
	adoxq	%rbp, %rsi
	adcxq	%r9, %rdi
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rdi
	adcxq	%r9, %r13
	MULXq	%r8, %rdx, %r8
	adoxq	%rdx, %r13
	adcxq	%rcx, %r8
	adoxq	%rcx, %r8
	movq	$38, %rdx
	MULXq	%rsi, %r9, %rsi
	adoxq	%r9, %rbx
	adcxq	%rsi, %r12
	MULXq	%rdi, %rdi, %rsi
	adoxq	%rdi, %r12
	adcxq	%rsi, %rax
	MULXq	%r13, %rdi, %rsi
	adoxq	%rdi, %rax
	adcxq	%rsi, %r11
	MULXq	%r8, %rsi, %rdx
	adoxq	%rsi, %r11
	adcxq	%rcx, %rdx
	adoxq	%rcx, %rdx
	imulq	$38, %rdx, %rdx
	addq	%rdx, %rbx
	adcq	%rcx, %r12
	adcq	%rcx, %rax
	adcq	%rcx, %r11
	sbbq	%rcx, %rcx
	andq	$38, %rcx
	addq	%rcx, %rbx
	movl	$25, %ecx
Ljade_scalarmult_curve25519_amd64_mulx$2:
	movl	%ecx, 344(%rsp)
	xorq	%r8, %r8
	movq	%rbx, %rdx
	MULXq	%rdx, %r9, %r10
	MULXq	%r12, %rsi, %rcx
	MULXq	%rax, %rbx, %rdi
	adcxq	%rbx, %rcx
	MULXq	%r11, %rdx, %rbx
	adcxq	%rdx, %rdi
	movq	%r12, %rdx
	MULXq	%rax, %r12, %rbp
	adoxq	%r12, %rdi
	adcxq	%rbp, %rbx
	MULXq	%r11, %r12, %rbp
	adoxq	%r12, %rbx
	MULXq	%rdx, %r13, %r12
	movq	%rax, %rdx
	MULXq	%r11, %r14, %rax
	adcxq	%r14, %rbp
	adoxq	%r8, %rbp
	adcxq	%r8, %rax
	adoxq	%r8, %rax
	MULXq	%rdx, %r15, %r14
	movq	%r11, %rdx
	MULXq	%rdx, %rdx, %r11
	adcxq	%rsi, %rsi
	adoxq	%r10, %rsi
	adcxq	%rcx, %rcx
	adoxq	%r13, %rcx
	adcxq	%rdi, %rdi
	adoxq	%r12, %rdi
	adcxq	%rbx, %rbx
	adoxq	%r15, %rbx
	adcxq	%rbp, %rbp
	adoxq	%r14, %rbp
	adcxq	%rax, %rax
	adoxq	%rdx, %rax
	adcxq	%r8, %r11
	adoxq	%r8, %r11
	movq	$38, %rdx
	MULXq	%rbx, %rbx, %r10
	adoxq	%rbx, %r9
	adcxq	%r10, %rsi
	MULXq	%rbp, %rbx, %r10
	adoxq	%rbx, %rsi
	adcxq	%r10, %rcx
	MULXq	%rax, %r10, %rax
	adoxq	%r10, %rcx
	adcxq	%rax, %rdi
	MULXq	%r11, %rdx, %rax
	adoxq	%rdx, %rdi
	adcxq	%r8, %rax
	adoxq	%r8, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r9
	adcq	%r8, %rsi
	adcq	%r8, %rcx
	adcq	%r8, %rdi
	sbbq	%r8, %r8
	andq	$38, %r8
	addq	%r8, %r9
	xorq	%r8, %r8
	movq	%r9, %rdx
	MULXq	%rdx, %rbx, %r9
	MULXq	%rsi, %r12, %rax
	MULXq	%rcx, %r10, %r11
	adcxq	%r10, %rax
	MULXq	%rdi, %rdx, %r10
	adcxq	%rdx, %r11
	movq	%rsi, %rdx
	MULXq	%rcx, %rbp, %rsi
	adoxq	%rbp, %r11
	adcxq	%rsi, %r10
	MULXq	%rdi, %rbp, %rsi
	adoxq	%rbp, %r10
	MULXq	%rdx, %r13, %rbp
	movq	%rcx, %rdx
	MULXq	%rdi, %r14, %rcx
	adcxq	%r14, %rsi
	adoxq	%r8, %rsi
	adcxq	%r8, %rcx
	adoxq	%r8, %rcx
	MULXq	%rdx, %r15, %r14
	movq	%rdi, %rdx
	MULXq	%rdx, %rdx, %rdi
	adcxq	%r12, %r12
	adoxq	%r9, %r12
	adcxq	%rax, %rax
	adoxq	%r13, %rax
	adcxq	%r11, %r11
	adoxq	%rbp, %r11
	adcxq	%r10, %r10
	adoxq	%r15, %r10
	adcxq	%rsi, %rsi
	adoxq	%r14, %rsi
	adcxq	%rcx, %rcx
	adoxq	%rdx, %rcx
	adcxq	%r8, %rdi
	adoxq	%r8, %rdi
	movq	$38, %rdx
	MULXq	%r10, %r10, %r9
	adoxq	%r10, %rbx
	adcxq	%r9, %r12
	MULXq	%rsi, %r9, %rsi
	adoxq	%r9, %r12
	adcxq	%rsi, %rax
	MULXq	%rcx, %rsi, %rcx
	adoxq	%rsi, %rax
	adcxq	%rcx, %r11
	MULXq	%rdi, %rdx, %rcx
	adoxq	%rdx, %r11
	adcxq	%r8, %rcx
	adoxq	%r8, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rbx
	adcq	%r8, %r12
	adcq	%r8, %rax
	adcq	%r8, %r11
	sbbq	%r8, %r8
	andq	$38, %r8
	addq	%r8, %rbx
	movl	344(%rsp), %ecx
	decl	%ecx
	jne 	Ljade_scalarmult_curve25519_amd64_mulx$2
	xorq	%r9, %r9
	movq	120(%rsp), %rdx
	MULXq	%rbx, %r8, %rsi
	MULXq	%r12, %rdi, %rcx
	adcxq	%rdi, %rsi
	MULXq	%rax, %r10, %rdi
	adcxq	%r10, %rcx
	MULXq	%r11, %rdx, %r10
	adcxq	%rdx, %rdi
	adcxq	%r9, %r10
	movq	128(%rsp), %rdx
	MULXq	%rbx, %r13, %rbp
	adoxq	%r13, %rsi
	adcxq	%rbp, %rcx
	MULXq	%r12, %r13, %rbp
	adoxq	%r13, %rcx
	adcxq	%rbp, %rdi
	MULXq	%rax, %r13, %rbp
	adoxq	%r13, %rdi
	adcxq	%rbp, %r10
	MULXq	%r11, %rdx, %rbp
	adoxq	%rdx, %r10
	adcxq	%r9, %rbp
	adoxq	%r9, %rbp
	movq	136(%rsp), %rdx
	MULXq	%rbx, %r14, %r13
	adoxq	%r14, %rcx
	adcxq	%r13, %rdi
	MULXq	%r12, %r14, %r13
	adoxq	%r14, %rdi
	adcxq	%r13, %r10
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %r10
	adcxq	%r13, %rbp
	MULXq	%r11, %rdx, %r13
	adoxq	%rdx, %rbp
	adcxq	%r9, %r13
	adoxq	%r9, %r13
	movq	144(%rsp), %rdx
	MULXq	%rbx, %r14, %rbx
	adoxq	%r14, %rdi
	adcxq	%rbx, %r10
	MULXq	%r12, %r12, %rbx
	adoxq	%r12, %r10
	adcxq	%rbx, %rbp
	MULXq	%rax, %rbx, %rax
	adoxq	%rbx, %rbp
	adcxq	%rax, %r13
	MULXq	%r11, %rdx, %rax
	adoxq	%rdx, %r13
	adcxq	%r9, %rax
	adoxq	%r9, %rax
	movq	$38, %rdx
	MULXq	%r10, %r11, %r10
	adoxq	%r11, %r8
	adcxq	%r10, %rsi
	MULXq	%rbp, %r11, %r10
	adoxq	%r11, %rsi
	adcxq	%r10, %rcx
	MULXq	%r13, %r11, %r10
	adoxq	%r11, %rcx
	adcxq	%r10, %rdi
	MULXq	%rax, %rdx, %rax
	adoxq	%rdx, %rdi
	adcxq	%r9, %rax
	adoxq	%r9, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r8
	adcq	%r9, %rsi
	adcq	%r9, %rcx
	adcq	%r9, %rdi
	sbbq	%r9, %r9
	andq	$38, %r9
	addq	%r9, %r8
	movl	$2, %eax
Ljade_scalarmult_curve25519_amd64_mulx$1:
	movl	%eax, 344(%rsp)
	xorq	%r11, %r11
	movq	%r8, %rdx
	MULXq	%rdx, %r8, %rbx
	MULXq	%rsi, %r9, %rax
	MULXq	%rcx, %rbp, %r10
	adcxq	%rbp, %rax
	MULXq	%rdi, %rdx, %rbp
	adcxq	%rdx, %r10
	movq	%rsi, %rdx
	MULXq	%rcx, %r12, %rsi
	adoxq	%r12, %r10
	adcxq	%rsi, %rbp
	MULXq	%rdi, %r12, %rsi
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rcx, %rdx
	MULXq	%rdi, %r14, %rcx
	adcxq	%r14, %rsi
	adoxq	%r11, %rsi
	adcxq	%r11, %rcx
	adoxq	%r11, %rcx
	MULXq	%rdx, %r15, %r14
	movq	%rdi, %rdx
	MULXq	%rdx, %rdx, %rdi
	adcxq	%r9, %r9
	adoxq	%rbx, %r9
	adcxq	%rax, %rax
	adoxq	%r13, %rax
	adcxq	%r10, %r10
	adoxq	%r12, %r10
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rsi, %rsi
	adoxq	%r14, %rsi
	adcxq	%rcx, %rcx
	adoxq	%rdx, %rcx
	adcxq	%r11, %rdi
	adoxq	%r11, %rdi
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r8
	adcxq	%rbx, %r9
	MULXq	%rsi, %rbx, %rsi
	adoxq	%rbx, %r9
	adcxq	%rsi, %rax
	MULXq	%rcx, %rsi, %rcx
	adoxq	%rsi, %rax
	adcxq	%rcx, %r10
	MULXq	%rdi, %rdx, %rcx
	adoxq	%rdx, %r10
	adcxq	%r11, %rcx
	adoxq	%r11, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %r8
	adcq	%r11, %r9
	adcq	%r11, %rax
	adcq	%r11, %r10
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %r8
	xorq	%r11, %r11
	movq	%r8, %rdx
	MULXq	%rdx, %r8, %rbx
	MULXq	%r9, %rsi, %rcx
	MULXq	%rax, %rbp, %rdi
	adcxq	%rbp, %rcx
	MULXq	%r10, %rdx, %rbp
	adcxq	%rdx, %rdi
	movq	%r9, %rdx
	MULXq	%rax, %r12, %r9
	adoxq	%r12, %rdi
	adcxq	%r9, %rbp
	MULXq	%r10, %r12, %r9
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rax, %rdx
	MULXq	%r10, %r14, %rax
	adcxq	%r14, %r9
	adoxq	%r11, %r9
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	MULXq	%rdx, %r15, %r14
	movq	%r10, %rdx
	MULXq	%rdx, %rdx, %r10
	adcxq	%rsi, %rsi
	adoxq	%rbx, %rsi
	adcxq	%rcx, %rcx
	adoxq	%r13, %rcx
	adcxq	%rdi, %rdi
	adoxq	%r12, %rdi
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%r9, %r9
	adoxq	%r14, %r9
	adcxq	%rax, %rax
	adoxq	%rdx, %rax
	adcxq	%r11, %r10
	adoxq	%r11, %r10
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %r8
	adcxq	%rbx, %rsi
	MULXq	%r9, %rbx, %r9
	adoxq	%rbx, %rsi
	adcxq	%r9, %rcx
	MULXq	%rax, %r9, %rax
	adoxq	%r9, %rcx
	adcxq	%rax, %rdi
	MULXq	%r10, %rdx, %rax
	adoxq	%rdx, %rdi
	adcxq	%r11, %rax
	adoxq	%r11, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %r8
	adcq	%r11, %rsi
	adcq	%r11, %rcx
	adcq	%r11, %rdi
	sbbq	%r11, %r11
	andq	$38, %r11
	addq	%r11, %r8
	movl	344(%rsp), %eax
	decl	%eax
	jne 	Ljade_scalarmult_curve25519_amd64_mulx$1
	xorq	%r9, %r9
	movq	%r8, %rdx
	MULXq	%rdx, %rax, %rbx
	MULXq	%rsi, %r10, %r11
	MULXq	%rcx, %rbp, %r8
	adcxq	%rbp, %r11
	MULXq	%rdi, %rdx, %rbp
	adcxq	%rdx, %r8
	movq	%rsi, %rdx
	MULXq	%rcx, %r12, %rsi
	adoxq	%r12, %r8
	adcxq	%rsi, %rbp
	MULXq	%rdi, %r12, %rsi
	adoxq	%r12, %rbp
	MULXq	%rdx, %r13, %r12
	movq	%rcx, %rdx
	MULXq	%rdi, %r14, %rcx
	adcxq	%r14, %rsi
	adoxq	%r9, %rsi
	adcxq	%r9, %rcx
	adoxq	%r9, %rcx
	MULXq	%rdx, %r15, %r14
	movq	%rdi, %rdx
	MULXq	%rdx, %rdx, %rdi
	adcxq	%r10, %r10
	adoxq	%rbx, %r10
	adcxq	%r11, %r11
	adoxq	%r13, %r11
	adcxq	%r8, %r8
	adoxq	%r12, %r8
	adcxq	%rbp, %rbp
	adoxq	%r15, %rbp
	adcxq	%rsi, %rsi
	adoxq	%r14, %rsi
	adcxq	%rcx, %rcx
	adoxq	%rdx, %rcx
	adcxq	%r9, %rdi
	adoxq	%r9, %rdi
	movq	$38, %rdx
	MULXq	%rbp, %rbp, %rbx
	adoxq	%rbp, %rax
	adcxq	%rbx, %r10
	MULXq	%rsi, %rbx, %rsi
	adoxq	%rbx, %r10
	adcxq	%rsi, %r11
	MULXq	%rcx, %rsi, %rcx
	adoxq	%rsi, %r11
	adcxq	%rcx, %r8
	MULXq	%rdi, %rdx, %rcx
	adoxq	%rdx, %r8
	adcxq	%r9, %rcx
	adoxq	%r9, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %rax
	adcq	%r9, %r10
	adcq	%r9, %r11
	adcq	%r9, %r8
	sbbq	%r9, %r9
	andq	$38, %r9
	addq	%r9, %rax
	xorq	%rbx, %rbx
	movq	88(%rsp), %rdx
	MULXq	%rax, %rsi, %rcx
	MULXq	%r10, %r9, %rdi
	adcxq	%r9, %rcx
	MULXq	%r11, %rbp, %r9
	adcxq	%rbp, %rdi
	MULXq	%r8, %rdx, %rbp
	adcxq	%rdx, %r9
	adcxq	%rbx, %rbp
	movq	96(%rsp), %rdx
	MULXq	%rax, %r13, %r12
	adoxq	%r13, %rcx
	adcxq	%r12, %rdi
	MULXq	%r10, %r13, %r12
	adoxq	%r13, %rdi
	adcxq	%r12, %r9
	MULXq	%r11, %r13, %r12
	adoxq	%r13, %r9
	adcxq	%r12, %rbp
	MULXq	%r8, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rbx, %r12
	adoxq	%rbx, %r12
	movq	104(%rsp), %rdx
	MULXq	%rax, %r14, %r13
	adoxq	%r14, %rdi
	adcxq	%r13, %r9
	MULXq	%r10, %r14, %r13
	adoxq	%r14, %r9
	adcxq	%r13, %rbp
	MULXq	%r11, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%r8, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rbx, %r13
	adoxq	%rbx, %r13
	movq	112(%rsp), %rdx
	MULXq	%rax, %r14, %rax
	adoxq	%r14, %r9
	adcxq	%rax, %rbp
	MULXq	%r10, %r10, %rax
	adoxq	%r10, %rbp
	adcxq	%rax, %r12
	MULXq	%r11, %r10, %rax
	adoxq	%r10, %r12
	adcxq	%rax, %r13
	MULXq	%r8, %rdx, %rax
	adoxq	%rdx, %r13
	adcxq	%rbx, %rax
	adoxq	%rbx, %rax
	movq	$38, %rdx
	MULXq	%rbp, %r10, %r8
	adoxq	%r10, %rsi
	adcxq	%r8, %rcx
	MULXq	%r12, %r10, %r8
	adoxq	%r10, %rcx
	adcxq	%r8, %rdi
	MULXq	%r13, %r10, %r8
	adoxq	%r10, %rdi
	adcxq	%r8, %r9
	MULXq	%rax, %rdx, %rax
	adoxq	%rdx, %r9
	adcxq	%rbx, %rax
	adoxq	%rbx, %rax
	imulq	$38, %rax, %rax
	addq	%rax, %rsi
	adcq	%rbx, %rcx
	adcq	%rbx, %rdi
	adcq	%rbx, %r9
	sbbq	%rbx, %rbx
	andq	$38, %rbx
	addq	%rbx, %rsi
	xorq	%rax, %rax
	movq	56(%rsp), %rdx
	MULXq	%rsi, %r10, %r8
	MULXq	%rcx, %rbx, %r11
	adcxq	%rbx, %r8
	MULXq	%rdi, %rbp, %rbx
	adcxq	%rbp, %r11
	MULXq	%r9, %rdx, %rbp
	adcxq	%rdx, %rbx
	adcxq	%rax, %rbp
	movq	64(%rsp), %rdx
	MULXq	%rsi, %r13, %r12
	adoxq	%r13, %r8
	adcxq	%r12, %r11
	MULXq	%rcx, %r13, %r12
	adoxq	%r13, %r11
	adcxq	%r12, %rbx
	MULXq	%rdi, %r13, %r12
	adoxq	%r13, %rbx
	adcxq	%r12, %rbp
	MULXq	%r9, %rdx, %r12
	adoxq	%rdx, %rbp
	adcxq	%rax, %r12
	adoxq	%rax, %r12
	movq	72(%rsp), %rdx
	MULXq	%rsi, %r14, %r13
	adoxq	%r14, %r11
	adcxq	%r13, %rbx
	MULXq	%rcx, %r14, %r13
	adoxq	%r14, %rbx
	adcxq	%r13, %rbp
	MULXq	%rdi, %r14, %r13
	adoxq	%r14, %rbp
	adcxq	%r13, %r12
	MULXq	%r9, %rdx, %r13
	adoxq	%rdx, %r12
	adcxq	%rax, %r13
	adoxq	%rax, %r13
	movq	80(%rsp), %rdx
	MULXq	%rsi, %r14, %rsi
	adoxq	%r14, %rbx
	adcxq	%rsi, %rbp
	MULXq	%rcx, %rsi, %rcx
	adoxq	%rsi, %rbp
	adcxq	%rcx, %r12
	MULXq	%rdi, %rsi, %rcx
	adoxq	%rsi, %r12
	adcxq	%rcx, %r13
	MULXq	%r9, %rdx, %rcx
	adoxq	%rdx, %r13
	adcxq	%rax, %rcx
	adoxq	%rax, %rcx
	movq	$38, %rdx
	MULXq	%rbp, %rdi, %rsi
	adoxq	%rdi, %r10
	adcxq	%rsi, %r8
	MULXq	%r12, %rdi, %rsi
	adoxq	%rdi, %r8
	adcxq	%rsi, %r11
	MULXq	%r13, %rdi, %rsi
	adoxq	%rdi, %r11
	adcxq	%rsi, %rbx
	MULXq	%rcx, %rdx, %rcx
	adoxq	%rdx, %rbx
	adcxq	%rax, %rcx
	adoxq	%rax, %rcx
	imulq	$38, %rcx, %rcx
	addq	%rcx, %r10
	adcq	%rax, %r8
	adcq	%rax, %r11
	adcq	%rax, %rbx
	sbbq	%rax, %rax
	andq	$38, %rax
	addq	%rax, %r10
	leaq	(%rbx,%rbx), %rax
	sarq	$63, %rbx
	shrq	$1, %rax
	andq	$19, %rbx
	addq	$19, %rbx
	addq	%rbx, %r10
	adcq	$0, %r8
	adcq	$0, %r11
	adcq	$0, %rax
	leaq	(%rax,%rax), %rcx
	sarq	$63, %rax
	shrq	$1, %rcx
	notq	%rax
	andq	$19, %rax
	subq	%rax, %r10
	sbbq	$0, %r8
	sbbq	$0, %r11
	sbbq	$0, %rcx
	movq	(%rsp), %rax
	movq	%r10, (%rax)
	movq	%r8, 8(%rax)
	movq	%r11, 16(%rax)
	movq	%rcx, 24(%rax)
	xorq	%rax, %rax
	movq	352(%rsp), %rbx
	movq	360(%rsp), %rbp
	movq	368(%rsp), %r12
	movq	376(%rsp), %r13
	movq	384(%rsp), %r14
	movq	392(%rsp), %r15
	movq	400(%rsp), %rsp
	ret 
