	.att_syntax
	.text
	.p2align	5
	.globl	_jade_scalarmult_curve25519_amd64_ref5_base
	.globl	jade_scalarmult_curve25519_amd64_ref5_base
	.globl	_jade_scalarmult_curve25519_amd64_ref5
	.globl	jade_scalarmult_curve25519_amd64_ref5
_jade_scalarmult_curve25519_amd64_ref5_base:
jade_scalarmult_curve25519_amd64_ref5_base:
	movq	%rsp, %rax
	leaq	-480(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rax, 472(%rsp)
	movq	%rbx, 432(%rsp)
	movq	%rbp, 440(%rsp)
	movq	%r12, 448(%rsp)
	movq	%r13, 456(%rsp)
	movq	%r14, 464(%rsp)
	movq	%rdi, (%rsp)
	movq	(%rsi), %rax
	movq	%rax, 40(%rsp)
	movq	8(%rsi), %rax
	movq	%rax, 48(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 56(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 64(%rsp)
	andb	$-8, 40(%rsp)
	andb	$127, 71(%rsp)
	orb 	$64, 71(%rsp)
	movq	$9, %rcx
	movq	$0, %r8
	movq	$0, %r9
	movq	$0, %r10
	movq	$0, %r11
	xorq	%rbx, %rbx
	movq	$1, 72(%rsp)
	movq	$0, %rbp
	movq	%rcx, 112(%rsp)
	movq	%r8, 120(%rsp)
	movq	%r9, 128(%rsp)
	movq	%r10, 136(%rsp)
	movq	%r11, 144(%rsp)
	movq	$1, 152(%rsp)
	movq	%rbx, 80(%rsp)
	movq	%rbx, %rax
	movq	%rbx, 160(%rsp)
	movq	%rbx, 88(%rsp)
	movq	%rbx, %rdx
	movq	%rbx, 168(%rsp)
	movq	%rbx, 96(%rsp)
	movq	%rbx, %rsi
	movq	%rbx, 176(%rsp)
	movq	%rbx, 104(%rsp)
	movq	%rbx, %rdi
	movq	%rbx, 184(%rsp)
	movq	%rcx, 192(%rsp)
	movq	%r8, 200(%rsp)
	movq	%r9, 208(%rsp)
	movq	%r10, 216(%rsp)
	movq	%r11, 224(%rsp)
	movq	$255, %rcx
	movq	$0, 8(%rsp)
Ljade_scalarmult_curve25519_amd64_ref5_base$28:
	addq	$-1, %rcx
	movq	%rcx, 16(%rsp)
	movq	%rcx, %r8
	shrq	$3, %r8
	movzbq	40(%rsp,%r8), %r8
	andq	$7, %rcx
	shrq	%cl, %r8
	andq	$1, %r8
	movq	8(%rsp), %r9
	xorq	%r8, %r9
	xorq	%rcx, %rcx
	subq	%r9, %rcx
	movq	%rbp, %r11
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	%rsi, %r9
	movq	%rdi, %r10
	xorq	152(%rsp), %r11
	andq	%rcx, %r11
	xorq	160(%rsp), %rbx
	andq	%rcx, %rbx
	xorq	168(%rsp), %r12
	andq	%rcx, %r12
	xorq	176(%rsp), %r9
	andq	%rcx, %r9
	xorq	184(%rsp), %r10
	andq	%rcx, %r10
	xorq	%r11, %rbp
	movq	152(%rsp), %r13
	xorq	%r11, %r13
	movq	%r13, 152(%rsp)
	xorq	%rbx, %rax
	movq	160(%rsp), %r11
	xorq	%rbx, %r11
	movq	%r11, 160(%rsp)
	xorq	%r12, %rdx
	movq	168(%rsp), %r11
	xorq	%r12, %r11
	movq	%r11, 168(%rsp)
	xorq	%r9, %rsi
	movq	176(%rsp), %r11
	xorq	%r9, %r11
	movq	%r11, 176(%rsp)
	xorq	%r10, %rdi
	movq	184(%rsp), %r9
	xorq	%r10, %r9
	movq	%r9, 184(%rsp)
	movq	112(%rsp), %r12
	movq	120(%rsp), %r9
	movq	128(%rsp), %r10
	movq	136(%rsp), %r11
	movq	144(%rsp), %rbx
	movq	72(%rsp), %r13
	movq	%r12, %r14
	xorq	%r13, %r14
	andq	%rcx, %r14
	xorq	%r14, %r13
	xorq	%r14, %r12
	movq	%r13, 72(%rsp)
	movq	%r12, 112(%rsp)
	movq	80(%rsp), %r12
	movq	%r9, %r13
	xorq	%r12, %r13
	andq	%rcx, %r13
	xorq	%r13, %r12
	xorq	%r13, %r9
	movq	%r12, 80(%rsp)
	movq	%r9, 120(%rsp)
	movq	88(%rsp), %r9
	movq	%r10, %r12
	xorq	%r9, %r12
	andq	%rcx, %r12
	xorq	%r12, %r9
	xorq	%r12, %r10
	movq	%r9, 88(%rsp)
	movq	%r10, 128(%rsp)
	movq	96(%rsp), %r9
	movq	%r11, %r10
	xorq	%r9, %r10
	andq	%rcx, %r10
	xorq	%r10, %r9
	xorq	%r10, %r11
	movq	%r9, 96(%rsp)
	movq	%r11, 136(%rsp)
	movq	104(%rsp), %r9
	movq	%rbx, %r10
	xorq	%r9, %r10
	andq	%rcx, %r10
	xorq	%r10, %r9
	xorq	%r10, %rbx
	movq	%r9, 104(%rsp)
	movq	%rbx, 144(%rsp)
	movq	%r8, 8(%rsp)
	movq	$4503599627370458, %rcx
	movq	$4503599627370494, %r8
	movq	72(%rsp), %r9
	movq	80(%rsp), %r10
	movq	88(%rsp), %r11
	movq	96(%rsp), %rbx
	movq	104(%rsp), %r12
	addq	%rcx, %r9
	addq	%r8, %r10
	addq	%r8, %r11
	addq	%r8, %rbx
	addq	%r8, %r12
	subq	%rbp, %r9
	subq	%rax, %r10
	subq	%rdx, %r11
	subq	%rsi, %rbx
	subq	%rdi, %r12
	movq	%r9, 232(%rsp)
	movq	%r10, 240(%rsp)
	movq	%r11, 248(%rsp)
	movq	%rbx, 256(%rsp)
	movq	%r12, 264(%rsp)
	addq	72(%rsp), %rbp
	addq	80(%rsp), %rax
	addq	88(%rsp), %rdx
	addq	96(%rsp), %rsi
	addq	104(%rsp), %rdi
	movq	%rbp, 272(%rsp)
	movq	%rax, 280(%rsp)
	movq	%rdx, 288(%rsp)
	movq	%rsi, 296(%rsp)
	movq	%rdi, 304(%rsp)
	movq	112(%rsp), %rax
	movq	120(%rsp), %rcx
	movq	128(%rsp), %rdx
	movq	136(%rsp), %rsi
	movq	144(%rsp), %rdi
	movq	$4503599627370458, %r8
	movq	$4503599627370494, %r9
	addq	%r8, %rax
	addq	%r9, %rcx
	addq	%r9, %rdx
	addq	%r9, %rsi
	addq	%r9, %rdi
	subq	152(%rsp), %rax
	subq	160(%rsp), %rcx
	subq	168(%rsp), %rdx
	subq	176(%rsp), %rsi
	subq	184(%rsp), %rdi
	movq	%rax, 312(%rsp)
	movq	%rcx, 320(%rsp)
	movq	%rdx, 328(%rsp)
	movq	%rsi, 336(%rsp)
	movq	%rdi, 344(%rsp)
	movq	112(%rsp), %rax
	movq	120(%rsp), %rcx
	movq	128(%rsp), %rdx
	movq	136(%rsp), %rsi
	movq	144(%rsp), %rdi
	addq	152(%rsp), %rax
	addq	160(%rsp), %rcx
	addq	168(%rsp), %rdx
	addq	176(%rsp), %rsi
	addq	184(%rsp), %rdi
	movq	%rax, 352(%rsp)
	movq	%rcx, 360(%rsp)
	movq	%rdx, 368(%rsp)
	movq	%rsi, 376(%rsp)
	movq	%rdi, 384(%rsp)
	movq	296(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 24(%rsp)
	mulq	328(%rsp)
	movq	%rax, %r12
	movq	%rdx, %rdi
	movq	304(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 32(%rsp)
	mulq	320(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rdi
	movq	272(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rdi
	movq	272(%rsp), %rax
	mulq	320(%rsp)
	movq	%rax, %r10
	movq	%rdx, %rbx
	movq	272(%rsp), %rax
	mulq	328(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	272(%rsp), %rax
	mulq	336(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %r11
	movq	272(%rsp), %rax
	mulq	344(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rsi
	movq	280(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	280(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	280(%rsp), %rax
	mulq	328(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r11
	movq	280(%rsp), %rax
	mulq	336(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rsi
	movq	280(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	344(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rdi
	movq	288(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	288(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r11
	movq	288(%rsp), %rax
	mulq	328(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rsi
	movq	288(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	336(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rdi
	movq	288(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	344(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	296(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r11
	movq	296(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rsi
	movq	24(%rsp), %rax
	mulq	336(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	24(%rsp), %rax
	mulq	344(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	304(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rsi
	movq	32(%rsp), %rax
	mulq	328(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	32(%rsp), %rax
	mulq	336(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	32(%rsp), %rax
	mulq	344(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r11
	movq	$2251799813685247, %rax
	shldq	$13, %r12, %rdi
	andq	%rax, %r12
	shldq	$13, %r10, %rbx
	andq	%rax, %r10
	addq	%rdi, %r10
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	addq	%rbx, %r8
	shldq	$13, %rcx, %r11
	andq	%rax, %rcx
	addq	%r9, %rcx
	shldq	$13, %rbp, %rsi
	andq	%rax, %rbp
	addq	%r11, %rbp
	imulq	$19, %rsi, %rdx
	addq	%rdx, %r12
	movq	%r12, %rdx
	shrq	$51, %rdx
	addq	%r10, %rdx
	movq	%rdx, %rsi
	shrq	$51, %rdx
	andq	%rax, %r12
	addq	%r8, %rdx
	movq	%rdx, %rdi
	shrq	$51, %rdx
	andq	%rax, %rsi
	addq	%rcx, %rdx
	movq	%rdx, %rcx
	shrq	$51, %rdx
	andq	%rax, %rdi
	addq	%rbp, %rdx
	movq	%rdx, %r8
	shrq	$51, %rdx
	andq	%rax, %rcx
	imulq	$19, %rdx, %rdx
	addq	%rdx, %r12
	andq	%rax, %r8
	movq	%r12, 312(%rsp)
	movq	%rsi, 320(%rsp)
	movq	%rdi, 328(%rsp)
	movq	%rcx, 336(%rsp)
	movq	%r8, 344(%rsp)
	movq	376(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 32(%rsp)
	mulq	248(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %rbx
	movq	384(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 24(%rsp)
	mulq	240(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %rbx
	movq	352(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %rbx
	movq	352(%rsp), %rax
	mulq	240(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r11
	movq	352(%rsp), %rax
	mulq	248(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %rdi
	movq	352(%rsp), %rax
	mulq	256(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %r8
	movq	352(%rsp), %rax
	mulq	264(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r12
	movq	360(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	360(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rdi
	movq	360(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r8
	movq	360(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r12
	movq	360(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %rbx
	movq	368(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rdi
	movq	368(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r8
	movq	368(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r12
	movq	368(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	256(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %rbx
	movq	368(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	376(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r8
	movq	376(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r12
	movq	32(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	32(%rsp), %rax
	mulq	264(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rdi
	movq	384(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r12
	movq	24(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r11
	movq	24(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rdi
	movq	24(%rsp), %rax
	mulq	264(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r8
	movq	$2251799813685247, %rax
	shldq	$13, %rsi, %rbx
	andq	%rax, %rsi
	shldq	$13, %r10, %r11
	andq	%rax, %r10
	addq	%rbx, %r10
	shldq	$13, %rcx, %rdi
	andq	%rax, %rcx
	addq	%r11, %rcx
	shldq	$13, %rbp, %r8
	andq	%rax, %rbp
	addq	%rdi, %rbp
	shldq	$13, %r9, %r12
	andq	%rax, %r9
	addq	%r8, %r9
	imulq	$19, %r12, %rdx
	addq	%rdx, %rsi
	movq	%rsi, %rdx
	shrq	$51, %rdx
	addq	%r10, %rdx
	movq	%rdx, %rdi
	shrq	$51, %rdx
	andq	%rax, %rsi
	addq	%rcx, %rdx
	movq	%rdx, %rcx
	shrq	$51, %rdx
	andq	%rax, %rdi
	addq	%rbp, %rdx
	movq	%rdx, %r8
	shrq	$51, %rdx
	andq	%rax, %rcx
	addq	%r9, %rdx
	movq	%rdx, %r9
	shrq	$51, %rdx
	andq	%rax, %r8
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rsi
	andq	%rax, %r9
	movq	%rsi, 352(%rsp)
	movq	%rdi, 360(%rsp)
	movq	%rcx, 368(%rsp)
	movq	%r8, 376(%rsp)
	movq	%r9, 384(%rsp)
	movq	272(%rsp), %rax
	mulq	272(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	272(%rsp), %rax
	shlq	$1, %rax
	mulq	280(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %r8
	movq	272(%rsp), %rax
	shlq	$1, %rax
	mulq	288(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r9
	movq	272(%rsp), %rax
	shlq	$1, %rax
	mulq	296(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %r11
	movq	272(%rsp), %rax
	shlq	$1, %rax
	mulq	304(%rsp)
	movq	%rax, %r10
	movq	%rdx, %rbp
	movq	280(%rsp), %rax
	mulq	280(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r9
	movq	280(%rsp), %rax
	shlq	$1, %rax
	mulq	288(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %r11
	movq	280(%rsp), %rax
	shlq	$1, %rax
	mulq	296(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbp
	movq	280(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	304(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	288(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbp
	movq	288(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	296(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	288(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	304(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r8
	movq	296(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	296(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r8
	movq	296(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	304(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r9
	movq	304(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	304(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %r11
	movq	$2251799813685247, %rax
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	shldq	$13, %rbx, %r8
	andq	%rax, %rbx
	addq	%rsi, %rbx
	shldq	$13, %r12, %r9
	andq	%rax, %r12
	addq	%r8, %r12
	shldq	$13, %rdi, %r11
	andq	%rax, %rdi
	addq	%r9, %rdi
	shldq	$13, %r10, %rbp
	andq	%rax, %r10
	addq	%r11, %r10
	imulq	$19, %rbp, %rdx
	addq	%rdx, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rdx
	addq	%rbx, %rdx
	andq	%rax, %rcx
	movq	%rdx, %rsi
	shrq	$51, %rdx
	addq	%r12, %rdx
	andq	%rax, %rsi
	movq	%rdx, %r8
	shrq	$51, %rdx
	addq	%rdi, %rdx
	andq	%rax, %r8
	movq	%rdx, %rdi
	shrq	$51, %rdx
	addq	%r10, %rdx
	andq	%rax, %rdi
	movq	%rdx, %r9
	shrq	$51, %rdx
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rcx
	andq	%rax, %r9
	movq	%rcx, 272(%rsp)
	movq	%rsi, 280(%rsp)
	movq	%r8, 288(%rsp)
	movq	%rdi, 296(%rsp)
	movq	%r9, 304(%rsp)
	movq	232(%rsp), %rax
	mulq	232(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r11
	movq	232(%rsp), %rax
	shlq	$1, %rax
	mulq	240(%rsp)
	movq	%rax, %r9
	movq	%rdx, %rbp
	movq	232(%rsp), %rax
	shlq	$1, %rax
	mulq	248(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %rbx
	movq	232(%rsp), %rax
	shlq	$1, %rax
	mulq	256(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %r10
	movq	232(%rsp), %rax
	shlq	$1, %rax
	mulq	264(%rsp)
	movq	%rax, %r12
	movq	%rdx, %rsi
	movq	240(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbx
	movq	240(%rsp), %rax
	shlq	$1, %rax
	mulq	248(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r10
	movq	240(%rsp), %rax
	shlq	$1, %rax
	mulq	256(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rsi
	movq	240(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r11
	movq	248(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rsi
	movq	248(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	256(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r11
	movq	248(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %rbp
	movq	256(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	256(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %rbp
	movq	256(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbx
	movq	264(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r10
	movq	$2251799813685247, %rax
	shldq	$13, %r8, %r11
	andq	%rax, %r8
	shldq	$13, %r9, %rbp
	andq	%rax, %r9
	addq	%r11, %r9
	shldq	$13, %rdi, %rbx
	andq	%rax, %rdi
	addq	%rbp, %rdi
	shldq	$13, %rcx, %r10
	andq	%rax, %rcx
	addq	%rbx, %rcx
	shldq	$13, %r12, %rsi
	andq	%rax, %r12
	addq	%r10, %r12
	imulq	$19, %rsi, %rdx
	addq	%rdx, %r8
	movq	%r8, %rdx
	shrq	$51, %rdx
	addq	%r9, %rdx
	andq	%rax, %r8
	movq	%rdx, %rsi
	shrq	$51, %rdx
	addq	%rdi, %rdx
	andq	%rax, %rsi
	movq	%rdx, %rdi
	shrq	$51, %rdx
	addq	%rcx, %rdx
	andq	%rax, %rdi
	movq	%rdx, %rcx
	shrq	$51, %rdx
	addq	%r12, %rdx
	andq	%rax, %rcx
	movq	%rdx, %r9
	shrq	$51, %rdx
	imulq	$19, %rdx, %rdx
	addq	%rdx, %r8
	andq	%rax, %r9
	movq	%r8, 232(%rsp)
	movq	%rsi, 240(%rsp)
	movq	%rdi, 248(%rsp)
	movq	%rcx, 256(%rsp)
	movq	%r9, 264(%rsp)
	movq	312(%rsp), %rax
	movq	320(%rsp), %rcx
	movq	328(%rsp), %rdx
	movq	336(%rsp), %rsi
	movq	344(%rsp), %rdi
	addq	352(%rsp), %rax
	addq	360(%rsp), %rcx
	addq	368(%rsp), %rdx
	addq	376(%rsp), %rsi
	addq	384(%rsp), %rdi
	movq	%rax, 392(%rsp)
	movq	%rcx, 400(%rsp)
	movq	%rdx, 408(%rsp)
	movq	%rsi, 416(%rsp)
	movq	%rdi, 424(%rsp)
	movq	312(%rsp), %rax
	movq	320(%rsp), %rcx
	movq	328(%rsp), %rdx
	movq	336(%rsp), %rsi
	movq	344(%rsp), %rdi
	movq	$4503599627370458, %r8
	movq	$4503599627370494, %r9
	addq	%r8, %rax
	addq	%r9, %rcx
	addq	%r9, %rdx
	addq	%r9, %rsi
	addq	%r9, %rdi
	subq	352(%rsp), %rax
	subq	360(%rsp), %rcx
	subq	368(%rsp), %rdx
	subq	376(%rsp), %rsi
	subq	384(%rsp), %rdi
	movq	%rax, 352(%rsp)
	movq	%rcx, 360(%rsp)
	movq	%rdx, 368(%rsp)
	movq	%rsi, 376(%rsp)
	movq	%rdi, 384(%rsp)
	movq	296(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 24(%rsp)
	mulq	248(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r12
	movq	304(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 32(%rsp)
	mulq	240(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r12
	movq	272(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r12
	movq	272(%rsp), %rax
	mulq	240(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %rbx
	movq	272(%rsp), %rax
	mulq	248(%rsp)
	movq	%rax, %r8
	movq	%rdx, %rdi
	movq	272(%rsp), %rax
	mulq	256(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rsi
	movq	272(%rsp), %rax
	mulq	264(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %r10
	movq	280(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rbx
	movq	280(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %rdi
	movq	280(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rsi
	movq	280(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r10
	movq	280(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r12
	movq	288(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %rdi
	movq	288(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rsi
	movq	288(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r10
	movq	288(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	256(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r12
	movq	288(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rbx
	movq	296(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rsi
	movq	296(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r10
	movq	24(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rbx
	movq	24(%rsp), %rax
	mulq	264(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %rdi
	movq	304(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r10
	movq	32(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rbx
	movq	32(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %rdi
	movq	32(%rsp), %rax
	mulq	264(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rsi
	movq	$2251799813685247, %rax
	shldq	$13, %r9, %r12
	andq	%rax, %r9
	shldq	$13, %rcx, %rbx
	andq	%rax, %rcx
	addq	%r12, %rcx
	shldq	$13, %r8, %rdi
	andq	%rax, %r8
	addq	%rbx, %r8
	shldq	$13, %r11, %rsi
	andq	%rax, %r11
	addq	%rdi, %r11
	shldq	$13, %rbp, %r10
	andq	%rax, %rbp
	addq	%rsi, %rbp
	imulq	$19, %r10, %rdx
	addq	%rdx, %r9
	movq	%r9, %rdx
	shrq	$51, %rdx
	addq	%rcx, %rdx
	movq	%rdx, %rcx
	shrq	$51, %rdx
	andq	%rax, %r9
	addq	%r8, %rdx
	movq	%rdx, %rsi
	shrq	$51, %rdx
	andq	%rax, %rcx
	addq	%r11, %rdx
	movq	%rdx, %rdi
	shrq	$51, %rdx
	andq	%rax, %rsi
	addq	%rbp, %rdx
	movq	%rdx, %r8
	shrq	$51, %rdx
	andq	%rax, %rdi
	imulq	$19, %rdx, %rdx
	addq	%rdx, %r9
	andq	%rax, %r8
	movq	%r9, 72(%rsp)
	movq	%rcx, 80(%rsp)
	movq	%rsi, 88(%rsp)
	movq	%rdi, 96(%rsp)
	movq	%r8, 104(%rsp)
	movq	272(%rsp), %rax
	movq	280(%rsp), %rcx
	movq	288(%rsp), %rdx
	movq	296(%rsp), %rsi
	movq	304(%rsp), %rdi
	movq	$4503599627370458, %r8
	movq	$4503599627370494, %r9
	addq	%r8, %rax
	addq	%r9, %rcx
	addq	%r9, %rdx
	addq	%r9, %rsi
	addq	%r9, %rdi
	subq	232(%rsp), %rax
	subq	240(%rsp), %rcx
	subq	248(%rsp), %rdx
	subq	256(%rsp), %rsi
	subq	264(%rsp), %rdi
	movq	%rax, 232(%rsp)
	movq	%rcx, 240(%rsp)
	movq	%rdx, 248(%rsp)
	movq	%rsi, 256(%rsp)
	movq	%rdi, 264(%rsp)
	movq	352(%rsp), %rax
	mulq	352(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rbx
	movq	352(%rsp), %rax
	shlq	$1, %rax
	mulq	360(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %r10
	movq	352(%rsp), %rax
	shlq	$1, %rax
	mulq	368(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r12
	movq	352(%rsp), %rax
	shlq	$1, %rax
	mulq	376(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	352(%rsp), %rax
	shlq	$1, %rax
	mulq	384(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %r9
	movq	360(%rsp), %rax
	mulq	360(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r12
	movq	360(%rsp), %rax
	shlq	$1, %rax
	mulq	368(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	360(%rsp), %rax
	shlq	$1, %rax
	mulq	376(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %r9
	movq	360(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	384(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbx
	movq	368(%rsp), %rax
	mulq	368(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %r9
	movq	368(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	376(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbx
	movq	368(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	384(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r10
	movq	376(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	376(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r10
	movq	376(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	384(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r12
	movq	384(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	384(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	$2251799813685247, %rax
	shldq	$13, %r11, %rbx
	andq	%rax, %r11
	shldq	$13, %rbp, %r10
	andq	%rax, %rbp
	addq	%rbx, %rbp
	shldq	$13, %r8, %r12
	andq	%rax, %r8
	addq	%r10, %r8
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	addq	%r12, %rcx
	shldq	$13, %rdi, %r9
	andq	%rax, %rdi
	addq	%rsi, %rdi
	imulq	$19, %r9, %rdx
	addq	%rdx, %r11
	movq	%r11, %rdx
	shrq	$51, %rdx
	addq	%rbp, %rdx
	andq	%rax, %r11
	movq	%rdx, %rsi
	shrq	$51, %rdx
	addq	%r8, %rdx
	andq	%rax, %rsi
	movq	%rdx, %r8
	shrq	$51, %rdx
	addq	%rcx, %rdx
	andq	%rax, %r8
	movq	%rdx, %rcx
	shrq	$51, %rdx
	addq	%rdi, %rdx
	andq	%rax, %rcx
	movq	%rdx, %rdi
	shrq	$51, %rdx
	imulq	$19, %rdx, %rdx
	addq	%rdx, %r11
	andq	%rax, %rdi
	movq	%r11, 352(%rsp)
	movq	%rsi, 360(%rsp)
	movq	%r8, 368(%rsp)
	movq	%rcx, 376(%rsp)
	movq	%rdi, 384(%rsp)
	movq	$996679680, %rcx
	movq	232(%rsp), %rax
	mulq	%rcx
	shrq	$13, %rax
	movq	%rax, %rsi
	movq	%rdx, %rdi
	movq	240(%rsp), %rax
	mulq	%rcx
	shrq	$13, %rax
	addq	%rax, %rdi
	movq	%rdx, %r8
	movq	248(%rsp), %rax
	mulq	%rcx
	shrq	$13, %rax
	addq	%rax, %r8
	movq	%rdx, %r9
	movq	256(%rsp), %rax
	mulq	%rcx
	shrq	$13, %rax
	addq	%rax, %r9
	movq	%rdx, %r10
	movq	264(%rsp), %rax
	mulq	%rcx
	shrq	$13, %rax
	addq	%rax, %r10
	imulq	$19, %rdx, %rax
	addq	%rax, %rsi
	addq	272(%rsp), %rsi
	addq	280(%rsp), %rdi
	addq	288(%rsp), %r8
	addq	296(%rsp), %r9
	addq	304(%rsp), %r10
	movq	%rsi, 272(%rsp)
	movq	%rdi, 280(%rsp)
	movq	%r8, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r10, 304(%rsp)
	movq	392(%rsp), %rax
	mulq	392(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %r8
	movq	392(%rsp), %rax
	shlq	$1, %rax
	mulq	400(%rsp)
	movq	%rax, %r12
	movq	%rdx, %rsi
	movq	392(%rsp), %rax
	shlq	$1, %rax
	mulq	408(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %rcx
	movq	392(%rsp), %rax
	shlq	$1, %rax
	mulq	416(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %r11
	movq	392(%rsp), %rax
	shlq	$1, %rax
	mulq	424(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r9
	movq	400(%rsp), %rax
	mulq	400(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rcx
	movq	400(%rsp), %rax
	shlq	$1, %rax
	mulq	408(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r11
	movq	400(%rsp), %rax
	shlq	$1, %rax
	mulq	416(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r9
	movq	400(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	424(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r8
	movq	408(%rsp), %rax
	mulq	408(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r9
	movq	408(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	416(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r8
	movq	408(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	424(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rsi
	movq	416(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	416(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rsi
	movq	416(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	424(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rcx
	movq	424(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	424(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r11
	movq	$2251799813685247, %rax
	shldq	$13, %rbx, %r8
	andq	%rax, %rbx
	shldq	$13, %r12, %rsi
	andq	%rax, %r12
	addq	%r8, %r12
	shldq	$13, %rdi, %rcx
	andq	%rax, %rdi
	addq	%rsi, %rdi
	shldq	$13, %rbp, %r11
	andq	%rax, %rbp
	addq	%rcx, %rbp
	shldq	$13, %r10, %r9
	andq	%rax, %r10
	addq	%r11, %r10
	imulq	$19, %r9, %rcx
	addq	%rcx, %rbx
	movq	%rbx, %rcx
	shrq	$51, %rcx
	addq	%r12, %rcx
	andq	%rax, %rbx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	addq	%rdi, %rcx
	andq	%rax, %rdx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	addq	%rbp, %rcx
	andq	%rax, %rsi
	movq	%rcx, %rdi
	shrq	$51, %rcx
	addq	%r10, %rcx
	andq	%rax, %rdi
	movq	%rcx, %r8
	shrq	$51, %rcx
	imulq	$19, %rcx, %rcx
	addq	%rcx, %rbx
	andq	%rax, %r8
	movq	%rbx, 112(%rsp)
	movq	%rdx, 120(%rsp)
	movq	%rsi, 128(%rsp)
	movq	%rdi, 136(%rsp)
	movq	%r8, 144(%rsp)
	movq	216(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 32(%rsp)
	mulq	368(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	224(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 24(%rsp)
	mulq	360(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rsi
	movq	192(%rsp), %rax
	mulq	352(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rsi
	movq	192(%rsp), %rax
	mulq	360(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rbx
	movq	192(%rsp), %rax
	mulq	368(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	192(%rsp), %rax
	mulq	376(%rsp)
	movq	%rax, %r12
	movq	%rdx, %rcx
	movq	192(%rsp), %rax
	mulq	384(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %r10
	movq	200(%rsp), %rax
	mulq	352(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbx
	movq	200(%rsp), %rax
	mulq	360(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	200(%rsp), %rax
	mulq	368(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	200(%rsp), %rax
	mulq	376(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r10
	movq	200(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	384(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rsi
	movq	208(%rsp), %rax
	mulq	352(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	208(%rsp), %rax
	mulq	360(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	208(%rsp), %rax
	mulq	368(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r10
	movq	208(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	376(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rsi
	movq	208(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	384(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbx
	movq	216(%rsp), %rax
	mulq	352(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	216(%rsp), %rax
	mulq	360(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r10
	movq	32(%rsp), %rax
	mulq	376(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbx
	movq	32(%rsp), %rax
	mulq	384(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	224(%rsp), %rax
	mulq	352(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r10
	movq	24(%rsp), %rax
	mulq	368(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbx
	movq	24(%rsp), %rax
	mulq	376(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	24(%rsp), %rax
	mulq	384(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rcx
	movq	$2251799813685247, %rax
	shldq	$13, %rdi, %rsi
	andq	%rax, %rdi
	shldq	$13, %r11, %rbx
	andq	%rax, %r11
	addq	%rsi, %r11
	shldq	$13, %r8, %r9
	andq	%rax, %r8
	addq	%rbx, %r8
	shldq	$13, %r12, %rcx
	andq	%rax, %r12
	addq	%r9, %r12
	shldq	$13, %rbp, %r10
	andq	%rax, %rbp
	addq	%rcx, %rbp
	imulq	$19, %r10, %rcx
	addq	%rcx, %rdi
	movq	%rdi, %rcx
	shrq	$51, %rcx
	addq	%r11, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	andq	%rax, %rdi
	addq	%r8, %rcx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	andq	%rax, %rdx
	addq	%r12, %rcx
	movq	%rcx, %r8
	shrq	$51, %rcx
	andq	%rax, %rsi
	addq	%rbp, %rcx
	movq	%rcx, %r9
	shrq	$51, %rcx
	andq	%rax, %r8
	imulq	$19, %rcx, %rcx
	addq	%rcx, %rdi
	andq	%rax, %r9
	movq	%rdi, 152(%rsp)
	movq	%rdx, 160(%rsp)
	movq	%rsi, 168(%rsp)
	movq	%r8, 176(%rsp)
	movq	%r9, 184(%rsp)
	movq	256(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 24(%rsp)
	mulq	288(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rdi
	movq	264(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 32(%rsp)
	mulq	280(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rdi
	movq	232(%rsp), %rax
	mulq	272(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rdi
	movq	232(%rsp), %rax
	mulq	280(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	232(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r10
	movq	232(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %r11
	movq	%rdx, %r8
	movq	232(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %r9
	movq	240(%rsp), %rax
	mulq	272(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	240(%rsp), %rax
	mulq	280(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r10
	movq	240(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %r8
	movq	240(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r9
	movq	240(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	304(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rdi
	movq	248(%rsp), %rax
	mulq	272(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r10
	movq	248(%rsp), %rax
	mulq	280(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %r8
	movq	248(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r9
	movq	248(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	296(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rdi
	movq	248(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	304(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	256(%rsp), %rax
	mulq	272(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %r8
	movq	256(%rsp), %rax
	mulq	280(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r9
	movq	24(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	24(%rsp), %rax
	mulq	304(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r10
	movq	264(%rsp), %rax
	mulq	272(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r9
	movq	32(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	32(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r10
	movq	32(%rsp), %rax
	mulq	304(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %r8
	movq	$2251799813685247, %r13
	shldq	$13, %rbp, %rdi
	andq	%r13, %rbp
	shldq	$13, %rbx, %r12
	andq	%r13, %rbx
	addq	%rdi, %rbx
	shldq	$13, %rsi, %r10
	andq	%r13, %rsi
	addq	%r12, %rsi
	shldq	$13, %r11, %r8
	andq	%r13, %r11
	addq	%r10, %r11
	shldq	$13, %rcx, %r9
	andq	%r13, %rcx
	addq	%r8, %rcx
	imulq	$19, %r9, %rax
	addq	%rax, %rbp
	movq	%rbp, %r8
	shrq	$51, %r8
	addq	%rbx, %r8
	movq	%r8, %rax
	shrq	$51, %r8
	andq	%r13, %rbp
	addq	%rsi, %r8
	movq	%r8, %rdx
	shrq	$51, %r8
	andq	%r13, %rax
	addq	%r11, %r8
	movq	%r8, %rsi
	shrq	$51, %r8
	andq	%r13, %rdx
	addq	%rcx, %r8
	movq	%r8, %rdi
	shrq	$51, %r8
	andq	%r13, %rsi
	imulq	$19, %r8, %rcx
	addq	%rcx, %rbp
	andq	%r13, %rdi
	movq	16(%rsp), %rcx
	cmpq	$0, %rcx
	jnbe	Ljade_scalarmult_curve25519_amd64_ref5_base$28
	movq	%rbp, 152(%rsp)
	movq	%rax, 160(%rsp)
	movq	%rdx, 168(%rsp)
	movq	%rsi, 176(%rsp)
	movq	%rdi, 184(%rsp)
	movq	152(%rsp), %rax
	movq	%rax, 112(%rsp)
	movq	160(%rsp), %rax
	movq	%rax, 120(%rsp)
	movq	168(%rsp), %rax
	movq	%rax, 128(%rsp)
	movq	176(%rsp), %rax
	movq	%rax, 136(%rsp)
	movq	184(%rsp), %rax
	movq	%rax, 144(%rsp)
	leaq	112(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$27(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$27:
	leaq	8(%rsp), %rsp
	movq	112(%rsp), %rax
	movq	%rax, 192(%rsp)
	movq	120(%rsp), %rax
	movq	%rax, 200(%rsp)
	movq	128(%rsp), %rax
	movq	%rax, 208(%rsp)
	movq	136(%rsp), %rax
	movq	%rax, 216(%rsp)
	movq	144(%rsp), %rax
	movq	%rax, 224(%rsp)
	leaq	192(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$26(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$26:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$25(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$25:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %r9
	leaq	152(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$24(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5_base$24:
	leaq	24(%rsp), %rsp
	leaq	112(%rsp), %r9
	leaq	192(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$23(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5_base$23:
	leaq	24(%rsp), %rsp
	movq	112(%rsp), %rax
	movq	%rax, 152(%rsp)
	movq	120(%rsp), %rax
	movq	%rax, 160(%rsp)
	movq	128(%rsp), %rax
	movq	%rax, 168(%rsp)
	movq	136(%rsp), %rax
	movq	%rax, 176(%rsp)
	movq	144(%rsp), %rax
	movq	%rax, 184(%rsp)
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$22(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$22:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %r9
	leaq	152(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$21(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5_base$21:
	leaq	24(%rsp), %rsp
	movq	192(%rsp), %rax
	movq	%rax, 152(%rsp)
	movq	200(%rsp), %rax
	movq	%rax, 160(%rsp)
	movq	208(%rsp), %rax
	movq	%rax, 168(%rsp)
	movq	216(%rsp), %rax
	movq	%rax, 176(%rsp)
	movq	224(%rsp), %rax
	movq	%rax, 184(%rsp)
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$20(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$20:
	leaq	8(%rsp), %rsp
	movl	$4, %r13d
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$19(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$19:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %r9
	leaq	152(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$18(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5_base$18:
	leaq	24(%rsp), %rsp
	movl	$10, %r13d
	movq	192(%rsp), %rax
	movq	%rax, 152(%rsp)
	movq	200(%rsp), %rax
	movq	%rax, 160(%rsp)
	movq	208(%rsp), %rax
	movq	%rax, 168(%rsp)
	movq	216(%rsp), %rax
	movq	%rax, 176(%rsp)
	movq	224(%rsp), %rax
	movq	%rax, 184(%rsp)
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$17(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$17:
	leaq	8(%rsp), %rsp
	leaq	152(%rsp), %r9
	leaq	192(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$16(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5_base$16:
	leaq	24(%rsp), %rsp
	movl	$20, %r13d
	movq	152(%rsp), %rax
	movq	%rax, 272(%rsp)
	movq	160(%rsp), %rax
	movq	%rax, 280(%rsp)
	movq	168(%rsp), %rax
	movq	%rax, 288(%rsp)
	movq	176(%rsp), %rax
	movq	%rax, 296(%rsp)
	movq	184(%rsp), %rax
	movq	%rax, 304(%rsp)
	leaq	272(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$15(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$15:
	leaq	8(%rsp), %rsp
	leaq	152(%rsp), %r9
	leaq	272(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$14(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5_base$14:
	leaq	24(%rsp), %rsp
	movl	$10, %r13d
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$13(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$13:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %r9
	leaq	152(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$12(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5_base$12:
	leaq	24(%rsp), %rsp
	movl	$50, %r13d
	movq	192(%rsp), %rax
	movq	%rax, 152(%rsp)
	movq	200(%rsp), %rax
	movq	%rax, 160(%rsp)
	movq	208(%rsp), %rax
	movq	%rax, 168(%rsp)
	movq	216(%rsp), %rax
	movq	%rax, 176(%rsp)
	movq	224(%rsp), %rax
	movq	%rax, 184(%rsp)
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$11(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$11:
	leaq	8(%rsp), %rsp
	leaq	152(%rsp), %r9
	leaq	192(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$10(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5_base$10:
	leaq	24(%rsp), %rsp
	movl	$100, %r13d
	movq	152(%rsp), %rax
	movq	%rax, 272(%rsp)
	movq	160(%rsp), %rax
	movq	%rax, 280(%rsp)
	movq	168(%rsp), %rax
	movq	%rax, 288(%rsp)
	movq	176(%rsp), %rax
	movq	%rax, 296(%rsp)
	movq	184(%rsp), %rax
	movq	%rax, 304(%rsp)
	leaq	272(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$9(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$9:
	leaq	8(%rsp), %rsp
	leaq	152(%rsp), %r9
	leaq	272(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$8(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5_base$8:
	leaq	24(%rsp), %rsp
	movl	$50, %r13d
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$7(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$7:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %r9
	leaq	152(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$6(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5_base$6:
	leaq	24(%rsp), %rsp
	movl	$4, %r13d
	leaq	192(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$5(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$5:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$4(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5_base$4:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %r9
	leaq	112(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5_base$3(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5_base$3:
	leaq	24(%rsp), %rsp
	movq	96(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 8(%rsp)
	mulq	208(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r12
	movq	104(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 16(%rsp)
	mulq	200(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r12
	movq	72(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r12
	movq	72(%rsp), %rax
	mulq	200(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rdi
	movq	72(%rsp), %rax
	mulq	208(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r10
	movq	72(%rsp), %rax
	mulq	216(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %r8
	movq	72(%rsp), %rax
	mulq	224(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rbp
	movq	80(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rdi
	movq	80(%rsp), %rax
	mulq	200(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r10
	movq	80(%rsp), %rax
	mulq	208(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	80(%rsp), %rax
	mulq	216(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rbp
	movq	80(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	224(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r12
	movq	88(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r10
	movq	88(%rsp), %rax
	mulq	200(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	88(%rsp), %rax
	mulq	208(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rbp
	movq	88(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	216(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r12
	movq	88(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	224(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rdi
	movq	96(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	96(%rsp), %rax
	mulq	200(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rbp
	movq	8(%rsp), %rax
	mulq	216(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rdi
	movq	8(%rsp), %rax
	mulq	224(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r10
	movq	104(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rbp
	movq	16(%rsp), %rax
	mulq	208(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rdi
	movq	16(%rsp), %rax
	mulq	216(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r10
	movq	16(%rsp), %rax
	mulq	224(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	$2251799813685247, %rax
	shldq	$13, %r9, %r12
	andq	%rax, %r9
	shldq	$13, %r11, %rdi
	andq	%rax, %r11
	addq	%r12, %r11
	shldq	$13, %rsi, %r10
	andq	%rax, %rsi
	addq	%rdi, %rsi
	shldq	$13, %rcx, %r8
	andq	%rax, %rcx
	addq	%r10, %rcx
	shldq	$13, %rbx, %rbp
	andq	%rax, %rbx
	addq	%r8, %rbx
	imulq	$19, %rbp, %rdx
	addq	%rdx, %r9
	movq	%r9, %r8
	shrq	$51, %r8
	addq	%r11, %r8
	movq	%r8, %rdx
	shrq	$51, %r8
	andq	%rax, %r9
	addq	%rsi, %r8
	movq	%r8, %rsi
	shrq	$51, %r8
	andq	%rax, %rdx
	addq	%rcx, %r8
	movq	%r8, %rcx
	shrq	$51, %r8
	andq	%rax, %rsi
	addq	%rbx, %r8
	movq	%r8, %rdi
	shrq	$51, %r8
	andq	%rax, %rcx
	imulq	$19, %r8, %r8
	addq	%r8, %r9
	andq	%rax, %rdi
	movq	$2251799813685247, %rax
	movq	%rax, %r8
	addq	$-18, %r8
	movq	$3, %r10
	jmp 	Ljade_scalarmult_curve25519_amd64_ref5_base$1
Ljade_scalarmult_curve25519_amd64_ref5_base$2:
	movq	%r9, %r11
	shrq	$51, %r11
	andq	%rax, %r9
	addq	%r11, %rdx
	movq	%rdx, %r11
	shrq	$51, %r11
	andq	%rax, %rdx
	addq	%r11, %rsi
	movq	%rsi, %r11
	shrq	$51, %r11
	andq	%rax, %rsi
	addq	%r11, %rcx
	movq	%rcx, %r11
	shrq	$51, %r11
	andq	%rax, %rcx
	addq	%r11, %rdi
	movq	%rdi, %r11
	shrq	$51, %r11
	andq	%rax, %rdi
	imulq	$19, %r11, %r11
	addq	%r11, %r9
	addq	$-1, %r10
Ljade_scalarmult_curve25519_amd64_ref5_base$1:
	cmpq	$0, %r10
	jnbe	Ljade_scalarmult_curve25519_amd64_ref5_base$2
	movq	$1, %r11
	cmpq	%r8, %r9
	cmovl	%r10, %r11
	cmpq	%rax, %rdx
	cmovne	%r10, %r11
	cmpq	%rax, %rsi
	cmovne	%r10, %r11
	cmpq	%rax, %rcx
	cmovne	%r10, %r11
	cmpq	%rax, %rdi
	cmovne	%r10, %r11
	negq	%r11
	andq	%r11, %rax
	andq	%r11, %r8
	subq	%r8, %r9
	subq	%rax, %rdx
	subq	%rax, %rsi
	subq	%rax, %rcx
	subq	%rax, %rdi
	movq	%rdx, %rax
	shlq	$51, %rax
	orq 	%r9, %rax
	movq	%rsi, %r8
	shlq	$38, %r8
	shrq	$13, %rdx
	orq 	%rdx, %r8
	movq	%rcx, %rdx
	shlq	$25, %rdx
	shrq	$26, %rsi
	orq 	%rsi, %rdx
	shlq	$12, %rdi
	shrq	$39, %rcx
	orq 	%rcx, %rdi
	movq	(%rsp), %rcx
	movq	%rax, (%rcx)
	movq	%r8, 8(%rcx)
	movq	%rdx, 16(%rcx)
	movq	%rdi, 24(%rcx)
	xorq	%rax, %rax
	movq	432(%rsp), %rbx
	movq	440(%rsp), %rbp
	movq	448(%rsp), %r12
	movq	456(%rsp), %r13
	movq	464(%rsp), %r14
	movq	472(%rsp), %rsp
	ret 
_jade_scalarmult_curve25519_amd64_ref5:
jade_scalarmult_curve25519_amd64_ref5:
	movq	%rsp, %rax
	leaq	-480(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rax, 472(%rsp)
	movq	%rbx, 432(%rsp)
	movq	%rbp, 440(%rsp)
	movq	%r12, 448(%rsp)
	movq	%r13, 456(%rsp)
	movq	%r14, 464(%rsp)
	movq	%rdi, (%rsp)
	movq	(%rsi), %rax
	movq	%rax, 40(%rsp)
	movq	8(%rsi), %rax
	movq	%rax, 48(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 56(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 64(%rsp)
	andb	$-8, 40(%rsp)
	andb	$127, 71(%rsp)
	orb 	$64, 71(%rsp)
	movq	(%rdx), %rax
	movq	8(%rdx), %rsi
	movq	16(%rdx), %rdi
	movq	24(%rdx), %rdx
	movq	$2251799813685247, %r9
	movq	%rax, %rcx
	andq	%r9, %rcx
	movq	%rsi, %r8
	shlq	$13, %r8
	shrq	$51, %rax
	orq 	%rax, %r8
	andq	%r9, %r8
	movq	%rdi, %r10
	shlq	$26, %r10
	shrq	$38, %rsi
	orq 	%rsi, %r10
	andq	%r9, %r10
	movq	%rdx, %r11
	shlq	$39, %r11
	shrq	$25, %rdi
	orq 	%rdi, %r11
	andq	%r9, %r11
	movq	%rdx, %rbp
	shrq	$12, %rbp
	andq	%r9, %rbp
	xorq	%r9, %r9
	movq	$1, 72(%rsp)
	movq	$0, %rbx
	movq	%rcx, 112(%rsp)
	movq	%r8, 120(%rsp)
	movq	%r10, 128(%rsp)
	movq	%r11, 136(%rsp)
	movq	%rbp, 144(%rsp)
	movq	$1, 152(%rsp)
	movq	%r9, 80(%rsp)
	movq	%r9, %rax
	movq	%r9, 160(%rsp)
	movq	%r9, 88(%rsp)
	movq	%r9, %rdx
	movq	%r9, 168(%rsp)
	movq	%r9, 96(%rsp)
	movq	%r9, %rsi
	movq	%r9, 176(%rsp)
	movq	%r9, 104(%rsp)
	movq	%r9, %rdi
	movq	%r9, 184(%rsp)
	movq	%rcx, 192(%rsp)
	movq	%r8, 200(%rsp)
	movq	%r10, 208(%rsp)
	movq	%r11, 216(%rsp)
	movq	%rbp, 224(%rsp)
	movq	$255, %rcx
	movq	$0, 8(%rsp)
Ljade_scalarmult_curve25519_amd64_ref5$28:
	addq	$-1, %rcx
	movq	%rcx, 16(%rsp)
	movq	%rcx, %r8
	shrq	$3, %r8
	movzbq	40(%rsp,%r8), %r8
	andq	$7, %rcx
	shrq	%cl, %r8
	andq	$1, %r8
	movq	8(%rsp), %r9
	xorq	%r8, %r9
	xorq	%rcx, %rcx
	subq	%r9, %rcx
	movq	%rbx, %r11
	movq	%rax, %rbp
	movq	%rdx, %r12
	movq	%rsi, %r9
	movq	%rdi, %r10
	xorq	152(%rsp), %r11
	andq	%rcx, %r11
	xorq	160(%rsp), %rbp
	andq	%rcx, %rbp
	xorq	168(%rsp), %r12
	andq	%rcx, %r12
	xorq	176(%rsp), %r9
	andq	%rcx, %r9
	xorq	184(%rsp), %r10
	andq	%rcx, %r10
	xorq	%r11, %rbx
	movq	152(%rsp), %r13
	xorq	%r11, %r13
	movq	%r13, 152(%rsp)
	xorq	%rbp, %rax
	movq	160(%rsp), %r11
	xorq	%rbp, %r11
	movq	%r11, 160(%rsp)
	xorq	%r12, %rdx
	movq	168(%rsp), %r11
	xorq	%r12, %r11
	movq	%r11, 168(%rsp)
	xorq	%r9, %rsi
	movq	176(%rsp), %r11
	xorq	%r9, %r11
	movq	%r11, 176(%rsp)
	xorq	%r10, %rdi
	movq	184(%rsp), %r9
	xorq	%r10, %r9
	movq	%r9, 184(%rsp)
	movq	112(%rsp), %r12
	movq	120(%rsp), %r9
	movq	128(%rsp), %r10
	movq	136(%rsp), %r11
	movq	144(%rsp), %rbp
	movq	72(%rsp), %r13
	movq	%r12, %r14
	xorq	%r13, %r14
	andq	%rcx, %r14
	xorq	%r14, %r13
	xorq	%r14, %r12
	movq	%r13, 72(%rsp)
	movq	%r12, 112(%rsp)
	movq	80(%rsp), %r12
	movq	%r9, %r13
	xorq	%r12, %r13
	andq	%rcx, %r13
	xorq	%r13, %r12
	xorq	%r13, %r9
	movq	%r12, 80(%rsp)
	movq	%r9, 120(%rsp)
	movq	88(%rsp), %r9
	movq	%r10, %r12
	xorq	%r9, %r12
	andq	%rcx, %r12
	xorq	%r12, %r9
	xorq	%r12, %r10
	movq	%r9, 88(%rsp)
	movq	%r10, 128(%rsp)
	movq	96(%rsp), %r9
	movq	%r11, %r10
	xorq	%r9, %r10
	andq	%rcx, %r10
	xorq	%r10, %r9
	xorq	%r10, %r11
	movq	%r9, 96(%rsp)
	movq	%r11, 136(%rsp)
	movq	104(%rsp), %r9
	movq	%rbp, %r10
	xorq	%r9, %r10
	andq	%rcx, %r10
	xorq	%r10, %r9
	xorq	%r10, %rbp
	movq	%r9, 104(%rsp)
	movq	%rbp, 144(%rsp)
	movq	%r8, 8(%rsp)
	movq	$4503599627370458, %rcx
	movq	$4503599627370494, %r8
	movq	72(%rsp), %r9
	movq	80(%rsp), %r10
	movq	88(%rsp), %r11
	movq	96(%rsp), %rbp
	movq	104(%rsp), %r12
	addq	%rcx, %r9
	addq	%r8, %r10
	addq	%r8, %r11
	addq	%r8, %rbp
	addq	%r8, %r12
	subq	%rbx, %r9
	subq	%rax, %r10
	subq	%rdx, %r11
	subq	%rsi, %rbp
	subq	%rdi, %r12
	movq	%r9, 232(%rsp)
	movq	%r10, 240(%rsp)
	movq	%r11, 248(%rsp)
	movq	%rbp, 256(%rsp)
	movq	%r12, 264(%rsp)
	addq	72(%rsp), %rbx
	addq	80(%rsp), %rax
	addq	88(%rsp), %rdx
	addq	96(%rsp), %rsi
	addq	104(%rsp), %rdi
	movq	%rbx, 272(%rsp)
	movq	%rax, 280(%rsp)
	movq	%rdx, 288(%rsp)
	movq	%rsi, 296(%rsp)
	movq	%rdi, 304(%rsp)
	movq	112(%rsp), %rax
	movq	120(%rsp), %rcx
	movq	128(%rsp), %rdx
	movq	136(%rsp), %rsi
	movq	144(%rsp), %rdi
	movq	$4503599627370458, %r8
	movq	$4503599627370494, %r9
	addq	%r8, %rax
	addq	%r9, %rcx
	addq	%r9, %rdx
	addq	%r9, %rsi
	addq	%r9, %rdi
	subq	152(%rsp), %rax
	subq	160(%rsp), %rcx
	subq	168(%rsp), %rdx
	subq	176(%rsp), %rsi
	subq	184(%rsp), %rdi
	movq	%rax, 312(%rsp)
	movq	%rcx, 320(%rsp)
	movq	%rdx, 328(%rsp)
	movq	%rsi, 336(%rsp)
	movq	%rdi, 344(%rsp)
	movq	112(%rsp), %rax
	movq	120(%rsp), %rcx
	movq	128(%rsp), %rdx
	movq	136(%rsp), %rsi
	movq	144(%rsp), %rdi
	addq	152(%rsp), %rax
	addq	160(%rsp), %rcx
	addq	168(%rsp), %rdx
	addq	176(%rsp), %rsi
	addq	184(%rsp), %rdi
	movq	%rax, 352(%rsp)
	movq	%rcx, 360(%rsp)
	movq	%rdx, 368(%rsp)
	movq	%rsi, 376(%rsp)
	movq	%rdi, 384(%rsp)
	movq	296(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 24(%rsp)
	mulq	328(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r9
	movq	304(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 32(%rsp)
	mulq	320(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r9
	movq	272(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r9
	movq	272(%rsp), %rax
	mulq	320(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %rbx
	movq	272(%rsp), %rax
	mulq	328(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r8
	movq	272(%rsp), %rax
	mulq	336(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %rbp
	movq	272(%rsp), %rax
	mulq	344(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rcx
	movq	280(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %rbx
	movq	280(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r8
	movq	280(%rsp), %rax
	mulq	328(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbp
	movq	280(%rsp), %rax
	mulq	336(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rcx
	movq	280(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	344(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r9
	movq	288(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r8
	movq	288(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbp
	movq	288(%rsp), %rax
	mulq	328(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rcx
	movq	288(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	336(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r9
	movq	288(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	344(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %rbx
	movq	296(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbp
	movq	296(%rsp), %rax
	mulq	320(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rcx
	movq	24(%rsp), %rax
	mulq	336(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %rbx
	movq	24(%rsp), %rax
	mulq	344(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r8
	movq	304(%rsp), %rax
	mulq	312(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rcx
	movq	32(%rsp), %rax
	mulq	328(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %rbx
	movq	32(%rsp), %rax
	mulq	336(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r8
	movq	32(%rsp), %rax
	mulq	344(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbp
	movq	$2251799813685247, %rax
	shldq	$13, %r12, %r9
	andq	%rax, %r12
	shldq	$13, %rsi, %rbx
	andq	%rax, %rsi
	addq	%r9, %rsi
	shldq	$13, %r10, %r8
	andq	%rax, %r10
	addq	%rbx, %r10
	shldq	$13, %rdi, %rbp
	andq	%rax, %rdi
	addq	%r8, %rdi
	shldq	$13, %r11, %rcx
	andq	%rax, %r11
	addq	%rbp, %r11
	imulq	$19, %rcx, %rcx
	addq	%rcx, %r12
	movq	%r12, %rcx
	shrq	$51, %rcx
	addq	%rsi, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	andq	%rax, %r12
	addq	%r10, %rcx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	andq	%rax, %rdx
	addq	%rdi, %rcx
	movq	%rcx, %rdi
	shrq	$51, %rcx
	andq	%rax, %rsi
	addq	%r11, %rcx
	movq	%rcx, %r8
	shrq	$51, %rcx
	andq	%rax, %rdi
	imulq	$19, %rcx, %rcx
	addq	%rcx, %r12
	andq	%rax, %r8
	movq	%r12, 312(%rsp)
	movq	%rdx, 320(%rsp)
	movq	%rsi, 328(%rsp)
	movq	%rdi, 336(%rsp)
	movq	%r8, 344(%rsp)
	movq	376(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 32(%rsp)
	mulq	248(%rsp)
	movq	%rax, %r10
	movq	%rdx, %r9
	movq	384(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 24(%rsp)
	mulq	240(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r9
	movq	352(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r9
	movq	352(%rsp), %rax
	mulq	240(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %rbx
	movq	352(%rsp), %rax
	mulq	248(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %rcx
	movq	352(%rsp), %rax
	mulq	256(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r8
	movq	352(%rsp), %rax
	mulq	264(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	360(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbx
	movq	360(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %rcx
	movq	360(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r8
	movq	360(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	360(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r9
	movq	368(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %rcx
	movq	368(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r8
	movq	368(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	368(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	256(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %r9
	movq	368(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbx
	movq	376(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r8
	movq	376(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	32(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbx
	movq	32(%rsp), %rax
	mulq	264(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %rcx
	movq	384(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	24(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbx
	movq	24(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %rcx
	movq	24(%rsp), %rax
	mulq	264(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r8
	movq	$2251799813685247, %rax
	shldq	$13, %r10, %r9
	andq	%rax, %r10
	shldq	$13, %rdi, %rbx
	andq	%rax, %rdi
	addq	%r9, %rdi
	shldq	$13, %rsi, %rcx
	andq	%rax, %rsi
	addq	%rbx, %rsi
	shldq	$13, %r12, %r8
	andq	%rax, %r12
	addq	%rcx, %r12
	shldq	$13, %r11, %rbp
	andq	%rax, %r11
	addq	%r8, %r11
	imulq	$19, %rbp, %rcx
	addq	%rcx, %r10
	movq	%r10, %rcx
	shrq	$51, %rcx
	addq	%rdi, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	andq	%rax, %r10
	addq	%rsi, %rcx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	andq	%rax, %rdx
	addq	%r12, %rcx
	movq	%rcx, %rdi
	shrq	$51, %rcx
	andq	%rax, %rsi
	addq	%r11, %rcx
	movq	%rcx, %r8
	shrq	$51, %rcx
	andq	%rax, %rdi
	imulq	$19, %rcx, %rcx
	addq	%rcx, %r10
	andq	%rax, %r8
	movq	%r10, 352(%rsp)
	movq	%rdx, 360(%rsp)
	movq	%rsi, 368(%rsp)
	movq	%rdi, 376(%rsp)
	movq	%r8, 384(%rsp)
	movq	272(%rsp), %rax
	mulq	272(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rbx
	movq	272(%rsp), %rax
	shlq	$1, %rax
	mulq	280(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r9
	movq	272(%rsp), %rax
	shlq	$1, %rax
	mulq	288(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %rcx
	movq	272(%rsp), %rax
	shlq	$1, %rax
	mulq	296(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r10
	movq	272(%rsp), %rax
	shlq	$1, %rax
	mulq	304(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %r8
	movq	280(%rsp), %rax
	mulq	280(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rcx
	movq	280(%rsp), %rax
	shlq	$1, %rax
	mulq	288(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r10
	movq	280(%rsp), %rax
	shlq	$1, %rax
	mulq	296(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r8
	movq	280(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	304(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbx
	movq	288(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r8
	movq	288(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	296(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbx
	movq	288(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	304(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r9
	movq	296(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	296(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r9
	movq	296(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	304(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rcx
	movq	304(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	304(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r10
	movq	$2251799813685247, %rax
	shldq	$13, %r11, %rbx
	andq	%rax, %r11
	shldq	$13, %r12, %r9
	andq	%rax, %r12
	addq	%rbx, %r12
	shldq	$13, %rdi, %rcx
	andq	%rax, %rdi
	addq	%r9, %rdi
	shldq	$13, %rsi, %r10
	andq	%rax, %rsi
	addq	%rcx, %rsi
	shldq	$13, %rbp, %r8
	andq	%rax, %rbp
	addq	%r10, %rbp
	imulq	$19, %r8, %rcx
	addq	%rcx, %r11
	movq	%r11, %rcx
	shrq	$51, %rcx
	addq	%r12, %rcx
	andq	%rax, %r11
	movq	%rcx, %rdx
	shrq	$51, %rcx
	addq	%rdi, %rcx
	andq	%rax, %rdx
	movq	%rcx, %rdi
	shrq	$51, %rcx
	addq	%rsi, %rcx
	andq	%rax, %rdi
	movq	%rcx, %rsi
	shrq	$51, %rcx
	addq	%rbp, %rcx
	andq	%rax, %rsi
	movq	%rcx, %r8
	shrq	$51, %rcx
	imulq	$19, %rcx, %rcx
	addq	%rcx, %r11
	andq	%rax, %r8
	movq	%r11, 272(%rsp)
	movq	%rdx, 280(%rsp)
	movq	%rdi, 288(%rsp)
	movq	%rsi, 296(%rsp)
	movq	%r8, 304(%rsp)
	movq	232(%rsp), %rax
	mulq	232(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %rsi
	movq	232(%rsp), %rax
	shlq	$1, %rax
	mulq	240(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %r10
	movq	232(%rsp), %rax
	shlq	$1, %rax
	mulq	248(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %r11
	movq	232(%rsp), %rax
	shlq	$1, %rax
	mulq	256(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r8
	movq	232(%rsp), %rax
	shlq	$1, %rax
	mulq	264(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %r9
	movq	240(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %r11
	movq	240(%rsp), %rax
	shlq	$1, %rax
	mulq	248(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r8
	movq	240(%rsp), %rax
	shlq	$1, %rax
	mulq	256(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r9
	movq	240(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	248(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r9
	movq	248(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	256(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rsi
	movq	248(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r10
	movq	256(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	256(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r10
	movq	256(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %r11
	movq	264(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r8
	movq	$2251799813685247, %rax
	shldq	$13, %rcx, %rsi
	andq	%rax, %rcx
	shldq	$13, %rbp, %r10
	andq	%rax, %rbp
	addq	%rsi, %rbp
	shldq	$13, %rdi, %r11
	andq	%rax, %rdi
	addq	%r10, %rdi
	shldq	$13, %r12, %r8
	andq	%rax, %r12
	addq	%r11, %r12
	shldq	$13, %rbx, %r9
	andq	%rax, %rbx
	addq	%r8, %rbx
	imulq	$19, %r9, %rdx
	addq	%rdx, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rdx
	addq	%rbp, %rdx
	andq	%rax, %rcx
	movq	%rdx, %rsi
	shrq	$51, %rdx
	addq	%rdi, %rdx
	andq	%rax, %rsi
	movq	%rdx, %rdi
	shrq	$51, %rdx
	addq	%r12, %rdx
	andq	%rax, %rdi
	movq	%rdx, %r8
	shrq	$51, %rdx
	addq	%rbx, %rdx
	andq	%rax, %r8
	movq	%rdx, %r9
	shrq	$51, %rdx
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rcx
	andq	%rax, %r9
	movq	%rcx, 232(%rsp)
	movq	%rsi, 240(%rsp)
	movq	%rdi, 248(%rsp)
	movq	%r8, 256(%rsp)
	movq	%r9, 264(%rsp)
	movq	312(%rsp), %rax
	movq	320(%rsp), %rcx
	movq	328(%rsp), %rdx
	movq	336(%rsp), %rsi
	movq	344(%rsp), %rdi
	addq	352(%rsp), %rax
	addq	360(%rsp), %rcx
	addq	368(%rsp), %rdx
	addq	376(%rsp), %rsi
	addq	384(%rsp), %rdi
	movq	%rax, 392(%rsp)
	movq	%rcx, 400(%rsp)
	movq	%rdx, 408(%rsp)
	movq	%rsi, 416(%rsp)
	movq	%rdi, 424(%rsp)
	movq	312(%rsp), %rax
	movq	320(%rsp), %rcx
	movq	328(%rsp), %rdx
	movq	336(%rsp), %rsi
	movq	344(%rsp), %rdi
	movq	$4503599627370458, %r8
	movq	$4503599627370494, %r9
	addq	%r8, %rax
	addq	%r9, %rcx
	addq	%r9, %rdx
	addq	%r9, %rsi
	addq	%r9, %rdi
	subq	352(%rsp), %rax
	subq	360(%rsp), %rcx
	subq	368(%rsp), %rdx
	subq	376(%rsp), %rsi
	subq	384(%rsp), %rdi
	movq	%rax, 352(%rsp)
	movq	%rcx, 360(%rsp)
	movq	%rdx, 368(%rsp)
	movq	%rsi, 376(%rsp)
	movq	%rdi, 384(%rsp)
	movq	296(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 24(%rsp)
	mulq	248(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r11
	movq	304(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 32(%rsp)
	mulq	240(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r11
	movq	272(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r11
	movq	272(%rsp), %rax
	mulq	240(%rsp)
	movq	%rax, %r10
	movq	%rdx, %rbx
	movq	272(%rsp), %rax
	mulq	248(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %rcx
	movq	272(%rsp), %rax
	mulq	256(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r12
	movq	272(%rsp), %rax
	mulq	264(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %r9
	movq	280(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	280(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rcx
	movq	280(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r12
	movq	280(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r9
	movq	280(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r11
	movq	288(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rcx
	movq	288(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r12
	movq	288(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r9
	movq	288(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	256(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r11
	movq	288(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	264(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	296(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r12
	movq	296(%rsp), %rax
	mulq	240(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r9
	movq	24(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	24(%rsp), %rax
	mulq	264(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rcx
	movq	304(%rsp), %rax
	mulq	232(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %r9
	movq	32(%rsp), %rax
	mulq	248(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbx
	movq	32(%rsp), %rax
	mulq	256(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rcx
	movq	32(%rsp), %rax
	mulq	264(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r12
	movq	$2251799813685247, %rax
	shldq	$13, %r8, %r11
	andq	%rax, %r8
	shldq	$13, %r10, %rbx
	andq	%rax, %r10
	addq	%r11, %r10
	shldq	$13, %rdi, %rcx
	andq	%rax, %rdi
	addq	%rbx, %rdi
	shldq	$13, %rsi, %r12
	andq	%rax, %rsi
	addq	%rcx, %rsi
	shldq	$13, %rbp, %r9
	andq	%rax, %rbp
	addq	%r12, %rbp
	imulq	$19, %r9, %rcx
	addq	%rcx, %r8
	movq	%r8, %rcx
	shrq	$51, %rcx
	addq	%r10, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	andq	%rax, %r8
	addq	%rdi, %rcx
	movq	%rcx, %rdi
	shrq	$51, %rcx
	andq	%rax, %rdx
	addq	%rsi, %rcx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	andq	%rax, %rdi
	addq	%rbp, %rcx
	movq	%rcx, %r9
	shrq	$51, %rcx
	andq	%rax, %rsi
	imulq	$19, %rcx, %rcx
	addq	%rcx, %r8
	andq	%rax, %r9
	movq	%r8, 72(%rsp)
	movq	%rdx, 80(%rsp)
	movq	%rdi, 88(%rsp)
	movq	%rsi, 96(%rsp)
	movq	%r9, 104(%rsp)
	movq	272(%rsp), %rax
	movq	280(%rsp), %rcx
	movq	288(%rsp), %rdx
	movq	296(%rsp), %rsi
	movq	304(%rsp), %rdi
	movq	$4503599627370458, %r8
	movq	$4503599627370494, %r9
	addq	%r8, %rax
	addq	%r9, %rcx
	addq	%r9, %rdx
	addq	%r9, %rsi
	addq	%r9, %rdi
	subq	232(%rsp), %rax
	subq	240(%rsp), %rcx
	subq	248(%rsp), %rdx
	subq	256(%rsp), %rsi
	subq	264(%rsp), %rdi
	movq	%rax, 232(%rsp)
	movq	%rcx, 240(%rsp)
	movq	%rdx, 248(%rsp)
	movq	%rsi, 256(%rsp)
	movq	%rdi, 264(%rsp)
	movq	352(%rsp), %rax
	mulq	352(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %r8
	movq	352(%rsp), %rax
	shlq	$1, %rax
	mulq	360(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r11
	movq	352(%rsp), %rax
	shlq	$1, %rax
	mulq	368(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %r10
	movq	352(%rsp), %rax
	shlq	$1, %rax
	mulq	376(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rbp
	movq	352(%rsp), %rax
	shlq	$1, %rax
	mulq	384(%rsp)
	movq	%rax, %r12
	movq	%rdx, %rsi
	movq	360(%rsp), %rax
	mulq	360(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %r10
	movq	360(%rsp), %rax
	shlq	$1, %rax
	mulq	368(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rbp
	movq	360(%rsp), %rax
	shlq	$1, %rax
	mulq	376(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rsi
	movq	360(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	384(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	368(%rsp), %rax
	mulq	368(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %rsi
	movq	368(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	376(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r8
	movq	368(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	384(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r11
	movq	376(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	376(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r11
	movq	376(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	384(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %r10
	movq	384(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	384(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rbp
	movq	$2251799813685247, %rax
	shldq	$13, %rcx, %r8
	andq	%rax, %rcx
	shldq	$13, %r9, %r11
	andq	%rax, %r9
	addq	%r8, %r9
	shldq	$13, %rdi, %r10
	andq	%rax, %rdi
	addq	%r11, %rdi
	shldq	$13, %rbx, %rbp
	andq	%rax, %rbx
	addq	%r10, %rbx
	shldq	$13, %r12, %rsi
	andq	%rax, %r12
	addq	%rbp, %r12
	imulq	$19, %rsi, %rdx
	addq	%rdx, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rdx
	addq	%r9, %rdx
	andq	%rax, %rcx
	movq	%rdx, %rsi
	shrq	$51, %rdx
	addq	%rdi, %rdx
	andq	%rax, %rsi
	movq	%rdx, %rdi
	shrq	$51, %rdx
	addq	%rbx, %rdx
	andq	%rax, %rdi
	movq	%rdx, %r8
	shrq	$51, %rdx
	addq	%r12, %rdx
	andq	%rax, %r8
	movq	%rdx, %r9
	shrq	$51, %rdx
	imulq	$19, %rdx, %rdx
	addq	%rdx, %rcx
	andq	%rax, %r9
	movq	%rcx, 352(%rsp)
	movq	%rsi, 360(%rsp)
	movq	%rdi, 368(%rsp)
	movq	%r8, 376(%rsp)
	movq	%r9, 384(%rsp)
	movq	$996679680, %rcx
	movq	232(%rsp), %rax
	mulq	%rcx
	shrq	$13, %rax
	movq	%rax, %rsi
	movq	%rdx, %rdi
	movq	240(%rsp), %rax
	mulq	%rcx
	shrq	$13, %rax
	addq	%rax, %rdi
	movq	%rdx, %r8
	movq	248(%rsp), %rax
	mulq	%rcx
	shrq	$13, %rax
	addq	%rax, %r8
	movq	%rdx, %r9
	movq	256(%rsp), %rax
	mulq	%rcx
	shrq	$13, %rax
	addq	%rax, %r9
	movq	%rdx, %r10
	movq	264(%rsp), %rax
	mulq	%rcx
	shrq	$13, %rax
	addq	%rax, %r10
	imulq	$19, %rdx, %rax
	addq	%rax, %rsi
	addq	272(%rsp), %rsi
	addq	280(%rsp), %rdi
	addq	288(%rsp), %r8
	addq	296(%rsp), %r9
	addq	304(%rsp), %r10
	movq	%rsi, 272(%rsp)
	movq	%rdi, 280(%rsp)
	movq	%r8, 288(%rsp)
	movq	%r9, 296(%rsp)
	movq	%r10, 304(%rsp)
	movq	392(%rsp), %rax
	mulq	392(%rsp)
	movq	%rax, %rsi
	movq	%rdx, %r10
	movq	392(%rsp), %rax
	shlq	$1, %rax
	mulq	400(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %rcx
	movq	392(%rsp), %rax
	shlq	$1, %rax
	mulq	408(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rbp
	movq	392(%rsp), %rax
	shlq	$1, %rax
	mulq	416(%rsp)
	movq	%rax, %r12
	movq	%rdx, %r9
	movq	392(%rsp), %rax
	shlq	$1, %rax
	mulq	424(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %r8
	movq	400(%rsp), %rax
	mulq	400(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	400(%rsp), %rax
	shlq	$1, %rax
	mulq	408(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r9
	movq	400(%rsp), %rax
	shlq	$1, %rax
	mulq	416(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %r8
	movq	400(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	424(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r10
	movq	408(%rsp), %rax
	mulq	408(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %r8
	movq	408(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	416(%rsp)
	addq	%rax, %rsi
	adcq	%rdx, %r10
	movq	408(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	424(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	416(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	416(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %rcx
	movq	416(%rsp), %rax
	imulq	$38, %rax, %rax
	mulq	424(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rbp
	movq	424(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	424(%rsp)
	addq	%rax, %r12
	adcq	%rdx, %r9
	movq	$2251799813685247, %rax
	shldq	$13, %rsi, %r10
	andq	%rax, %rsi
	shldq	$13, %rbx, %rcx
	andq	%rax, %rbx
	addq	%r10, %rbx
	shldq	$13, %r11, %rbp
	andq	%rax, %r11
	addq	%rcx, %r11
	shldq	$13, %r12, %r9
	andq	%rax, %r12
	addq	%rbp, %r12
	shldq	$13, %rdi, %r8
	andq	%rax, %rdi
	addq	%r9, %rdi
	imulq	$19, %r8, %rcx
	addq	%rcx, %rsi
	movq	%rsi, %rcx
	shrq	$51, %rcx
	addq	%rbx, %rcx
	andq	%rax, %rsi
	movq	%rcx, %rdx
	shrq	$51, %rcx
	addq	%r11, %rcx
	andq	%rax, %rdx
	movq	%rcx, %r8
	shrq	$51, %rcx
	addq	%r12, %rcx
	andq	%rax, %r8
	movq	%rcx, %r9
	shrq	$51, %rcx
	addq	%rdi, %rcx
	andq	%rax, %r9
	movq	%rcx, %rdi
	shrq	$51, %rcx
	imulq	$19, %rcx, %rcx
	addq	%rcx, %rsi
	andq	%rax, %rdi
	movq	%rsi, 112(%rsp)
	movq	%rdx, 120(%rsp)
	movq	%r8, 128(%rsp)
	movq	%r9, 136(%rsp)
	movq	%rdi, 144(%rsp)
	movq	216(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 32(%rsp)
	mulq	368(%rsp)
	movq	%rax, %r9
	movq	%rdx, %rsi
	movq	224(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 24(%rsp)
	mulq	360(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %rsi
	movq	192(%rsp), %rax
	mulq	352(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %rsi
	movq	192(%rsp), %rax
	mulq	360(%rsp)
	movq	%rax, %r10
	movq	%rdx, %rcx
	movq	192(%rsp), %rax
	mulq	368(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	192(%rsp), %rax
	mulq	376(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %rbp
	movq	192(%rsp), %rax
	mulq	384(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r11
	movq	200(%rsp), %rax
	mulq	352(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rcx
	movq	200(%rsp), %rax
	mulq	360(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	200(%rsp), %rax
	mulq	368(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbp
	movq	200(%rsp), %rax
	mulq	376(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r11
	movq	200(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	384(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %rsi
	movq	208(%rsp), %rax
	mulq	352(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	208(%rsp), %rax
	mulq	360(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbp
	movq	208(%rsp), %rax
	mulq	368(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r11
	movq	208(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	376(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %rsi
	movq	208(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	384(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rcx
	movq	216(%rsp), %rax
	mulq	352(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbp
	movq	216(%rsp), %rax
	mulq	360(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r11
	movq	32(%rsp), %rax
	mulq	376(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rcx
	movq	32(%rsp), %rax
	mulq	384(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	224(%rsp), %rax
	mulq	352(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r11
	movq	24(%rsp), %rax
	mulq	368(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rcx
	movq	24(%rsp), %rax
	mulq	376(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	24(%rsp), %rax
	mulq	384(%rsp)
	addq	%rax, %rdi
	adcq	%rdx, %rbp
	movq	$2251799813685247, %rax
	shldq	$13, %r9, %rsi
	andq	%rax, %r9
	shldq	$13, %r10, %rcx
	andq	%rax, %r10
	addq	%rsi, %r10
	shldq	$13, %rbx, %r12
	andq	%rax, %rbx
	addq	%rcx, %rbx
	shldq	$13, %rdi, %rbp
	andq	%rax, %rdi
	addq	%r12, %rdi
	shldq	$13, %r8, %r11
	andq	%rax, %r8
	addq	%rbp, %r8
	imulq	$19, %r11, %rcx
	addq	%rcx, %r9
	movq	%r9, %rcx
	shrq	$51, %rcx
	addq	%r10, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	andq	%rax, %r9
	addq	%rbx, %rcx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	andq	%rax, %rdx
	addq	%rdi, %rcx
	movq	%rcx, %rdi
	shrq	$51, %rcx
	andq	%rax, %rsi
	addq	%r8, %rcx
	movq	%rcx, %r8
	shrq	$51, %rcx
	andq	%rax, %rdi
	imulq	$19, %rcx, %rcx
	addq	%rcx, %r9
	andq	%rax, %r8
	movq	%r9, 152(%rsp)
	movq	%rdx, 160(%rsp)
	movq	%rsi, 168(%rsp)
	movq	%rdi, 176(%rsp)
	movq	%r8, 184(%rsp)
	movq	256(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 24(%rsp)
	mulq	288(%rsp)
	movq	%rax, %rbx
	movq	%rdx, %r12
	movq	264(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 32(%rsp)
	mulq	280(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	232(%rsp), %rax
	mulq	272(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	232(%rsp), %rax
	mulq	280(%rsp)
	movq	%rax, %r11
	movq	%rdx, %rsi
	movq	232(%rsp), %rax
	mulq	288(%rsp)
	movq	%rax, %r8
	movq	%rdx, %r9
	movq	232(%rsp), %rax
	mulq	296(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %rdi
	movq	232(%rsp), %rax
	mulq	304(%rsp)
	movq	%rax, %r10
	movq	%rdx, %rbp
	movq	240(%rsp), %rax
	mulq	272(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rsi
	movq	240(%rsp), %rax
	mulq	280(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	240(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rdi
	movq	240(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbp
	movq	240(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	304(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	248(%rsp), %rax
	mulq	272(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	248(%rsp), %rax
	mulq	280(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rdi
	movq	248(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbp
	movq	248(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	296(%rsp)
	addq	%rax, %rbx
	adcq	%rdx, %r12
	movq	248(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	304(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rsi
	movq	256(%rsp), %rax
	mulq	272(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rdi
	movq	256(%rsp), %rax
	mulq	280(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbp
	movq	24(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rsi
	movq	24(%rsp), %rax
	mulq	304(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	264(%rsp), %rax
	mulq	272(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rbp
	movq	32(%rsp), %rax
	mulq	288(%rsp)
	addq	%rax, %r11
	adcq	%rdx, %rsi
	movq	32(%rsp), %rax
	mulq	296(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %r9
	movq	32(%rsp), %rax
	mulq	304(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %rdi
	movq	$2251799813685247, %r13
	shldq	$13, %rbx, %r12
	andq	%r13, %rbx
	shldq	$13, %r11, %rsi
	andq	%r13, %r11
	addq	%r12, %r11
	shldq	$13, %r8, %r9
	andq	%r13, %r8
	addq	%rsi, %r8
	shldq	$13, %rcx, %rdi
	andq	%r13, %rcx
	addq	%r9, %rcx
	shldq	$13, %r10, %rbp
	andq	%r13, %r10
	addq	%rdi, %r10
	imulq	$19, %rbp, %rax
	addq	%rax, %rbx
	movq	%rbx, %r9
	shrq	$51, %r9
	addq	%r11, %r9
	movq	%r9, %rax
	shrq	$51, %r9
	andq	%r13, %rbx
	addq	%r8, %r9
	movq	%r9, %rdx
	shrq	$51, %r9
	andq	%r13, %rax
	addq	%rcx, %r9
	movq	%r9, %rsi
	shrq	$51, %r9
	andq	%r13, %rdx
	addq	%r10, %r9
	movq	%r9, %rdi
	shrq	$51, %r9
	andq	%r13, %rsi
	imulq	$19, %r9, %rcx
	addq	%rcx, %rbx
	andq	%r13, %rdi
	movq	16(%rsp), %rcx
	cmpq	$0, %rcx
	jnbe	Ljade_scalarmult_curve25519_amd64_ref5$28
	movq	%rbx, 152(%rsp)
	movq	%rax, 160(%rsp)
	movq	%rdx, 168(%rsp)
	movq	%rsi, 176(%rsp)
	movq	%rdi, 184(%rsp)
	movq	152(%rsp), %rax
	movq	%rax, 112(%rsp)
	movq	160(%rsp), %rax
	movq	%rax, 120(%rsp)
	movq	168(%rsp), %rax
	movq	%rax, 128(%rsp)
	movq	176(%rsp), %rax
	movq	%rax, 136(%rsp)
	movq	184(%rsp), %rax
	movq	%rax, 144(%rsp)
	leaq	112(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$27(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$27:
	leaq	8(%rsp), %rsp
	movq	112(%rsp), %rax
	movq	%rax, 192(%rsp)
	movq	120(%rsp), %rax
	movq	%rax, 200(%rsp)
	movq	128(%rsp), %rax
	movq	%rax, 208(%rsp)
	movq	136(%rsp), %rax
	movq	%rax, 216(%rsp)
	movq	144(%rsp), %rax
	movq	%rax, 224(%rsp)
	leaq	192(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$26(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$26:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$25(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$25:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %r9
	leaq	152(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$24(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5$24:
	leaq	24(%rsp), %rsp
	leaq	112(%rsp), %r9
	leaq	192(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$23(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5$23:
	leaq	24(%rsp), %rsp
	movq	112(%rsp), %rax
	movq	%rax, 152(%rsp)
	movq	120(%rsp), %rax
	movq	%rax, 160(%rsp)
	movq	128(%rsp), %rax
	movq	%rax, 168(%rsp)
	movq	136(%rsp), %rax
	movq	%rax, 176(%rsp)
	movq	144(%rsp), %rax
	movq	%rax, 184(%rsp)
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$22(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$22:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %r9
	leaq	152(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$21(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5$21:
	leaq	24(%rsp), %rsp
	movq	192(%rsp), %rax
	movq	%rax, 152(%rsp)
	movq	200(%rsp), %rax
	movq	%rax, 160(%rsp)
	movq	208(%rsp), %rax
	movq	%rax, 168(%rsp)
	movq	216(%rsp), %rax
	movq	%rax, 176(%rsp)
	movq	224(%rsp), %rax
	movq	%rax, 184(%rsp)
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$20(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$20:
	leaq	8(%rsp), %rsp
	movl	$4, %r13d
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$19(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$19:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %r9
	leaq	152(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$18(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5$18:
	leaq	24(%rsp), %rsp
	movl	$10, %r13d
	movq	192(%rsp), %rax
	movq	%rax, 152(%rsp)
	movq	200(%rsp), %rax
	movq	%rax, 160(%rsp)
	movq	208(%rsp), %rax
	movq	%rax, 168(%rsp)
	movq	216(%rsp), %rax
	movq	%rax, 176(%rsp)
	movq	224(%rsp), %rax
	movq	%rax, 184(%rsp)
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$17(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$17:
	leaq	8(%rsp), %rsp
	leaq	152(%rsp), %r9
	leaq	192(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$16(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5$16:
	leaq	24(%rsp), %rsp
	movl	$20, %r13d
	movq	152(%rsp), %rax
	movq	%rax, 272(%rsp)
	movq	160(%rsp), %rax
	movq	%rax, 280(%rsp)
	movq	168(%rsp), %rax
	movq	%rax, 288(%rsp)
	movq	176(%rsp), %rax
	movq	%rax, 296(%rsp)
	movq	184(%rsp), %rax
	movq	%rax, 304(%rsp)
	leaq	272(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$15(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$15:
	leaq	8(%rsp), %rsp
	leaq	152(%rsp), %r9
	leaq	272(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$14(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5$14:
	leaq	24(%rsp), %rsp
	movl	$10, %r13d
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$13(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$13:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %r9
	leaq	152(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$12(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5$12:
	leaq	24(%rsp), %rsp
	movl	$50, %r13d
	movq	192(%rsp), %rax
	movq	%rax, 152(%rsp)
	movq	200(%rsp), %rax
	movq	%rax, 160(%rsp)
	movq	208(%rsp), %rax
	movq	%rax, 168(%rsp)
	movq	216(%rsp), %rax
	movq	%rax, 176(%rsp)
	movq	224(%rsp), %rax
	movq	%rax, 184(%rsp)
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$11(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$11:
	leaq	8(%rsp), %rsp
	leaq	152(%rsp), %r9
	leaq	192(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$10(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5$10:
	leaq	24(%rsp), %rsp
	movl	$100, %r13d
	movq	152(%rsp), %rax
	movq	%rax, 272(%rsp)
	movq	160(%rsp), %rax
	movq	%rax, 280(%rsp)
	movq	168(%rsp), %rax
	movq	%rax, 288(%rsp)
	movq	176(%rsp), %rax
	movq	%rax, 296(%rsp)
	movq	184(%rsp), %rax
	movq	%rax, 304(%rsp)
	leaq	272(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$9(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$9:
	leaq	8(%rsp), %rsp
	leaq	152(%rsp), %r9
	leaq	272(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$8(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5$8:
	leaq	24(%rsp), %rsp
	movl	$50, %r13d
	leaq	152(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$7(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$7:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %r9
	leaq	152(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$6(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5$6:
	leaq	24(%rsp), %rsp
	movl	$4, %r13d
	leaq	192(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$5(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_it_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$5:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %rdi
	leaq	-8(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$4(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
Ljade_scalarmult_curve25519_amd64_ref5$4:
	leaq	8(%rsp), %rsp
	leaq	192(%rsp), %r9
	leaq	112(%rsp), %rbp
	leaq	-24(%rsp), %rsp
	leaq	Ljade_scalarmult_curve25519_amd64_ref5$3(%rip), %rax
	movq	%rax, 16(%rsp)
	jmp 	L_mul5_pp$1
Ljade_scalarmult_curve25519_amd64_ref5$3:
	leaq	24(%rsp), %rsp
	movq	96(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 8(%rsp)
	mulq	208(%rsp)
	movq	%rax, %r10
	movq	%rdx, %rsi
	movq	104(%rsp), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 16(%rsp)
	mulq	200(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rsi
	movq	72(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rsi
	movq	72(%rsp), %rax
	mulq	200(%rsp)
	movq	%rax, %rbp
	movq	%rdx, %rdi
	movq	72(%rsp), %rax
	mulq	208(%rsp)
	movq	%rax, %rcx
	movq	%rdx, %r12
	movq	72(%rsp), %rax
	mulq	216(%rsp)
	movq	%rax, %r9
	movq	%rdx, %r11
	movq	72(%rsp), %rax
	mulq	224(%rsp)
	movq	%rax, %r8
	movq	%rdx, %rbx
	movq	80(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rdi
	movq	80(%rsp), %rax
	mulq	200(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r12
	movq	80(%rsp), %rax
	mulq	208(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r11
	movq	80(%rsp), %rax
	mulq	216(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %rbx
	movq	80(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	224(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rsi
	movq	88(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r12
	movq	88(%rsp), %rax
	mulq	200(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r11
	movq	88(%rsp), %rax
	mulq	208(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %rbx
	movq	88(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	216(%rsp)
	addq	%rax, %r10
	adcq	%rdx, %rsi
	movq	88(%rsp), %rax
	imulq	$19, %rax, %rax
	mulq	224(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rdi
	movq	96(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r11
	movq	96(%rsp), %rax
	mulq	200(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %rbx
	movq	8(%rsp), %rax
	mulq	216(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rdi
	movq	8(%rsp), %rax
	mulq	224(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r12
	movq	104(%rsp), %rax
	mulq	192(%rsp)
	addq	%rax, %r8
	adcq	%rdx, %rbx
	movq	16(%rsp), %rax
	mulq	208(%rsp)
	addq	%rax, %rbp
	adcq	%rdx, %rdi
	movq	16(%rsp), %rax
	mulq	216(%rsp)
	addq	%rax, %rcx
	adcq	%rdx, %r12
	movq	16(%rsp), %rax
	mulq	224(%rsp)
	addq	%rax, %r9
	adcq	%rdx, %r11
	movq	$2251799813685247, %rax
	shldq	$13, %r10, %rsi
	andq	%rax, %r10
	shldq	$13, %rbp, %rdi
	andq	%rax, %rbp
	addq	%rsi, %rbp
	shldq	$13, %rcx, %r12
	andq	%rax, %rcx
	addq	%rdi, %rcx
	shldq	$13, %r9, %r11
	andq	%rax, %r9
	addq	%r12, %r9
	shldq	$13, %r8, %rbx
	andq	%rax, %r8
	addq	%r11, %r8
	imulq	$19, %rbx, %rdx
	addq	%rdx, %r10
	movq	%r10, %r11
	shrq	$51, %r11
	addq	%rbp, %r11
	movq	%r11, %rdx
	shrq	$51, %r11
	andq	%rax, %r10
	addq	%rcx, %r11
	movq	%r11, %rcx
	shrq	$51, %r11
	andq	%rax, %rdx
	addq	%r9, %r11
	movq	%r11, %rsi
	shrq	$51, %r11
	andq	%rax, %rcx
	addq	%r8, %r11
	movq	%r11, %rdi
	shrq	$51, %r11
	andq	%rax, %rsi
	imulq	$19, %r11, %r8
	addq	%r8, %r10
	andq	%rax, %rdi
	movq	$2251799813685247, %rax
	movq	%rax, %r8
	addq	$-18, %r8
	movq	$3, %r9
	jmp 	Ljade_scalarmult_curve25519_amd64_ref5$1
Ljade_scalarmult_curve25519_amd64_ref5$2:
	movq	%r10, %r11
	shrq	$51, %r11
	andq	%rax, %r10
	addq	%r11, %rdx
	movq	%rdx, %r11
	shrq	$51, %r11
	andq	%rax, %rdx
	addq	%r11, %rcx
	movq	%rcx, %r11
	shrq	$51, %r11
	andq	%rax, %rcx
	addq	%r11, %rsi
	movq	%rsi, %r11
	shrq	$51, %r11
	andq	%rax, %rsi
	addq	%r11, %rdi
	movq	%rdi, %r11
	shrq	$51, %r11
	andq	%rax, %rdi
	imulq	$19, %r11, %r11
	addq	%r11, %r10
	addq	$-1, %r9
Ljade_scalarmult_curve25519_amd64_ref5$1:
	cmpq	$0, %r9
	jnbe	Ljade_scalarmult_curve25519_amd64_ref5$2
	movq	$1, %r11
	cmpq	%r8, %r10
	cmovl	%r9, %r11
	cmpq	%rax, %rdx
	cmovne	%r9, %r11
	cmpq	%rax, %rcx
	cmovne	%r9, %r11
	cmpq	%rax, %rsi
	cmovne	%r9, %r11
	cmpq	%rax, %rdi
	cmovne	%r9, %r11
	negq	%r11
	andq	%r11, %rax
	andq	%r11, %r8
	subq	%r8, %r10
	subq	%rax, %rdx
	subq	%rax, %rcx
	subq	%rax, %rsi
	subq	%rax, %rdi
	movq	%rdx, %rax
	shlq	$51, %rax
	orq 	%r10, %rax
	movq	%rcx, %r8
	shlq	$38, %r8
	shrq	$13, %rdx
	orq 	%rdx, %r8
	movq	%rsi, %rdx
	shlq	$25, %rdx
	shrq	$26, %rcx
	orq 	%rcx, %rdx
	shlq	$12, %rdi
	shrq	$39, %rsi
	orq 	%rsi, %rdi
	movq	(%rsp), %rcx
	movq	%rax, (%rcx)
	movq	%r8, 8(%rcx)
	movq	%rdx, 16(%rcx)
	movq	%rdi, 24(%rcx)
	xorq	%rax, %rax
	movq	432(%rsp), %rbx
	movq	440(%rsp), %rbp
	movq	448(%rsp), %r12
	movq	456(%rsp), %r13
	movq	464(%rsp), %r14
	movq	472(%rsp), %rsp
	ret 
L_it_sqr5_p$1:
L_it_sqr5_p$2:
	leaq	-8(%rsp), %rsp
	leaq	L_it_sqr5_p$3(%rip), %rax
	movq	%rax, (%rsp)
	jmp 	L_sqr5_p$1
L_it_sqr5_p$3:
	leaq	8(%rsp), %rsp
	decl	%r13d
	jne 	L_it_sqr5_p$2
	jmp 	*(%rsp)
L_sqr5_p$1:
	movq	(%rdi), %rax
	mulq	(%rdi)
	movq	%rax, %r8
	movq	%rdx, %rsi
	movq	(%rdi), %rax
	shlq	$1, %rax
	mulq	8(%rdi)
	movq	%rax, %rbx
	movq	%rdx, %r11
	movq	(%rdi), %rax
	shlq	$1, %rax
	mulq	16(%rdi)
	movq	%rax, %r10
	movq	%rdx, %r14
	movq	(%rdi), %rax
	shlq	$1, %rax
	mulq	24(%rdi)
	movq	%rax, %rbp
	movq	%rdx, %r12
	movq	(%rdi), %rax
	shlq	$1, %rax
	mulq	32(%rdi)
	movq	%rax, %rcx
	movq	%rdx, %r9
	movq	8(%rdi), %rax
	mulq	8(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r14
	movq	8(%rdi), %rax
	shlq	$1, %rax
	mulq	16(%rdi)
	addq	%rax, %rbp
	adcq	%rdx, %r12
	movq	8(%rdi), %rax
	shlq	$1, %rax
	mulq	24(%rdi)
	addq	%rax, %rcx
	adcq	%rdx, %r9
	movq	8(%rdi), %rax
	imulq	$38, %rax, %rax
	mulq	32(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %rsi
	movq	16(%rdi), %rax
	mulq	16(%rdi)
	addq	%rax, %rcx
	adcq	%rdx, %r9
	movq	16(%rdi), %rax
	imulq	$38, %rax, %rax
	mulq	24(%rdi)
	addq	%rax, %r8
	adcq	%rdx, %rsi
	movq	16(%rdi), %rax
	imulq	$38, %rax, %rax
	mulq	32(%rdi)
	addq	%rax, %rbx
	adcq	%rdx, %r11
	movq	24(%rdi), %rax
	imulq	$19, %rax, %rax
	mulq	24(%rdi)
	addq	%rax, %rbx
	adcq	%rdx, %r11
	movq	24(%rdi), %rax
	imulq	$38, %rax, %rax
	mulq	32(%rdi)
	addq	%rax, %r10
	adcq	%rdx, %r14
	movq	32(%rdi), %rax
	imulq	$19, %rax, %rax
	mulq	32(%rdi)
	addq	%rax, %rbp
	adcq	%rdx, %r12
	movq	$2251799813685247, %rax
	shldq	$13, %r8, %rsi
	andq	%rax, %r8
	shldq	$13, %rbx, %r11
	andq	%rax, %rbx
	addq	%rsi, %rbx
	shldq	$13, %r10, %r14
	andq	%rax, %r10
	addq	%r11, %r10
	shldq	$13, %rbp, %r12
	andq	%rax, %rbp
	addq	%r14, %rbp
	shldq	$13, %rcx, %r9
	andq	%rax, %rcx
	addq	%r12, %rcx
	imulq	$19, %r9, %rdx
	addq	%rdx, %r8
	movq	%r8, %rdx
	shrq	$51, %rdx
	addq	%rbx, %rdx
	andq	%rax, %r8
	movq	%rdx, %rsi
	shrq	$51, %rdx
	addq	%r10, %rdx
	andq	%rax, %rsi
	movq	%rdx, %r9
	shrq	$51, %rdx
	addq	%rbp, %rdx
	andq	%rax, %r9
	movq	%rdx, %r10
	shrq	$51, %rdx
	addq	%rcx, %rdx
	andq	%rax, %r10
	movq	%rdx, %rcx
	shrq	$51, %rdx
	imulq	$19, %rdx, %rdx
	addq	%rdx, %r8
	andq	%rax, %rcx
	movq	%r8, (%rdi)
	movq	%rsi, 8(%rdi)
	movq	%r9, 16(%rdi)
	movq	%r10, 24(%rdi)
	movq	%rcx, 32(%rdi)
	jmp 	*(%rsp)
L_mul5_pp$1:
	movq	24(%r9), %rax
	imulq	$19, %rax, %rax
	movq	%rax, (%rsp)
	mulq	16(%rbp)
	movq	%rax, %rdi
	movq	%rdx, %r8
	movq	32(%r9), %rax
	imulq	$19, %rax, %rax
	movq	%rax, 8(%rsp)
	mulq	8(%rbp)
	addq	%rax, %rdi
	adcq	%rdx, %r8
	movq	(%r9), %rax
	mulq	(%rbp)
	addq	%rax, %rdi
	adcq	%rdx, %r8
	movq	(%r9), %rax
	mulq	8(%rbp)
	movq	%rax, %rbx
	movq	%rdx, %r14
	movq	(%r9), %rax
	mulq	16(%rbp)
	movq	%rax, %r11
	movq	%rdx, %rcx
	movq	(%r9), %rax
	mulq	24(%rbp)
	movq	%rax, %r10
	movq	%rdx, %r12
	movq	(%r9), %rax
	mulq	32(%rbp)
	movq	%rax, %rsi
	movq	%rdx, %r13
	movq	8(%r9), %rax
	mulq	(%rbp)
	addq	%rax, %rbx
	adcq	%rdx, %r14
	movq	8(%r9), %rax
	mulq	8(%rbp)
	addq	%rax, %r11
	adcq	%rdx, %rcx
	movq	8(%r9), %rax
	mulq	16(%rbp)
	addq	%rax, %r10
	adcq	%rdx, %r12
	movq	8(%r9), %rax
	mulq	24(%rbp)
	addq	%rax, %rsi
	adcq	%rdx, %r13
	movq	8(%r9), %rax
	imulq	$19, %rax, %rax
	mulq	32(%rbp)
	addq	%rax, %rdi
	adcq	%rdx, %r8
	movq	16(%r9), %rax
	mulq	(%rbp)
	addq	%rax, %r11
	adcq	%rdx, %rcx
	movq	16(%r9), %rax
	mulq	8(%rbp)
	addq	%rax, %r10
	adcq	%rdx, %r12
	movq	16(%r9), %rax
	mulq	16(%rbp)
	addq	%rax, %rsi
	adcq	%rdx, %r13
	movq	16(%r9), %rax
	imulq	$19, %rax, %rax
	mulq	24(%rbp)
	addq	%rax, %rdi
	adcq	%rdx, %r8
	movq	16(%r9), %rax
	imulq	$19, %rax, %rax
	mulq	32(%rbp)
	addq	%rax, %rbx
	adcq	%rdx, %r14
	movq	24(%r9), %rax
	mulq	(%rbp)
	addq	%rax, %r10
	adcq	%rdx, %r12
	movq	24(%r9), %rax
	mulq	8(%rbp)
	addq	%rax, %rsi
	adcq	%rdx, %r13
	movq	(%rsp), %rax
	mulq	24(%rbp)
	addq	%rax, %rbx
	adcq	%rdx, %r14
	movq	(%rsp), %rax
	mulq	32(%rbp)
	addq	%rax, %r11
	adcq	%rdx, %rcx
	movq	32(%r9), %rax
	mulq	(%rbp)
	addq	%rax, %rsi
	adcq	%rdx, %r13
	movq	8(%rsp), %rax
	mulq	16(%rbp)
	addq	%rax, %rbx
	adcq	%rdx, %r14
	movq	8(%rsp), %rax
	mulq	24(%rbp)
	addq	%rax, %r11
	adcq	%rdx, %rcx
	movq	8(%rsp), %rax
	mulq	32(%rbp)
	addq	%rax, %r10
	adcq	%rdx, %r12
	movq	$2251799813685247, %rax
	shldq	$13, %rdi, %r8
	andq	%rax, %rdi
	shldq	$13, %rbx, %r14
	andq	%rax, %rbx
	addq	%r8, %rbx
	shldq	$13, %r11, %rcx
	andq	%rax, %r11
	addq	%r14, %r11
	shldq	$13, %r10, %r12
	andq	%rax, %r10
	addq	%rcx, %r10
	shldq	$13, %rsi, %r13
	andq	%rax, %rsi
	addq	%r12, %rsi
	imulq	$19, %r13, %rcx
	addq	%rcx, %rdi
	movq	%rdi, %rcx
	shrq	$51, %rcx
	addq	%rbx, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rcx
	andq	%rax, %rdi
	addq	%r11, %rcx
	movq	%rcx, %r8
	shrq	$51, %rcx
	andq	%rax, %rdx
	addq	%r10, %rcx
	movq	%rcx, %r10
	shrq	$51, %rcx
	andq	%rax, %r8
	addq	%rsi, %rcx
	movq	%rcx, %rsi
	shrq	$51, %rcx
	andq	%rax, %r10
	imulq	$19, %rcx, %rcx
	addq	%rcx, %rdi
	andq	%rax, %rsi
	movq	%rdi, (%r9)
	movq	%rdx, 8(%r9)
	movq	%r8, 16(%r9)
	movq	%r10, 24(%r9)
	movq	%rsi, 32(%r9)
	jmp 	*16(%rsp)
