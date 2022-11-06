	.att_syntax
	.text
	.p2align	5
	.globl	_jade_hash_sha3_384_amd64_ref
	.globl	jade_hash_sha3_384_amd64_ref
_jade_hash_sha3_384_amd64_ref:
jade_hash_sha3_384_amd64_ref:
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
	movq	$48, %r8
	movb	$6, %r9b
	movq	$104, %rcx
	leaq	-448(%rsp), %rsp
	leaq	Ljade_hash_sha3_384_amd64_ref$1(%rip), %rax
	jmp 	L_keccak1600_ref$1
Ljade_hash_sha3_384_amd64_ref$1:
	leaq	448(%rsp), %rsp
	xorq	%rax, %rax
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %r15
	movq	48(%rsp), %rsp
	ret 
L_keccak1600_ref$1:
	movq	%rdi, (%rsp)
	movq	%r8, 8(%rsp)
	movb	%r9b, 440(%rsp)
	xorq	%rdi, %rdi
	movq	$0, %r8
	jmp 	L_keccak1600_ref$21
L_keccak1600_ref$22:
	movq	%rdi, 40(%rsp,%r8,8)
	incq	%r8
L_keccak1600_ref$21:
	cmpq	$25, %r8
	jb  	L_keccak1600_ref$22
	jmp 	L_keccak1600_ref$16
L_keccak1600_ref$17:
	movq	%rcx, %rdi
	shrq	$3, %rdi
	movq	$0, %r8
	jmp 	L_keccak1600_ref$19
L_keccak1600_ref$20:
	movq	(%rsi,%r8,8), %r9
	xorq	%r9, 40(%rsp,%r8,8)
	incq	%r8
L_keccak1600_ref$19:
	cmpq	%rdi, %r8
	jb  	L_keccak1600_ref$20
	addq	%rcx, %rsi
	subq	%rcx, %rdx
	movq	%rsi, 16(%rsp)
	movq	%rdx, 24(%rsp)
	movq	%rcx, 32(%rsp)
	leaq	glob_data + 0(%rip), %rcx
	movq	$0, %rdx
L_keccak1600_ref$18:
	movq	(%rcx,%rdx,8), %r11
	movq	40(%rsp), %r10
	movq	48(%rsp), %r9
	movq	56(%rsp), %rbx
	movq	64(%rsp), %rbp
	movq	72(%rsp), %r12
	xorq	80(%rsp), %r10
	xorq	88(%rsp), %r9
	xorq	96(%rsp), %rbx
	xorq	104(%rsp), %rbp
	xorq	112(%rsp), %r12
	xorq	120(%rsp), %r10
	xorq	128(%rsp), %r9
	xorq	136(%rsp), %rbx
	xorq	144(%rsp), %rbp
	xorq	152(%rsp), %r12
	xorq	160(%rsp), %r10
	xorq	168(%rsp), %r9
	xorq	176(%rsp), %rbx
	xorq	184(%rsp), %rbp
	xorq	192(%rsp), %r12
	xorq	200(%rsp), %r10
	xorq	208(%rsp), %r9
	xorq	216(%rsp), %rbx
	xorq	224(%rsp), %rbp
	xorq	232(%rsp), %r12
	movq	%r9, %rsi
	rolq	$1, %rsi
	xorq	%r12, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r10, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r9, %r8
	movq	%r12, %r9
	rolq	$1, %r9
	xorq	%rbx, %r9
	rolq	$1, %r10
	xorq	%rbp, %r10
	movq	40(%rsp), %rbx
	xorq	%rsi, %rbx
	movq	88(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$44, %rbp
	movq	136(%rsp), %r12
	xorq	%r8, %r12
	rolq	$43, %r12
	movq	184(%rsp), %r13
	xorq	%r9, %r13
	rolq	$21, %r13
	movq	232(%rsp), %r14
	xorq	%r10, %r14
	rolq	$14, %r14
	andnq	%r12, %rbp, %r15
	xorq	%rbx, %r15
	xorq	%r11, %r15
	movq	%r15, 240(%rsp)
	andnq	%r13, %r12, %r11
	xorq	%rbp, %r11
	movq	%r11, 248(%rsp)
	andnq	%r14, %r13, %r11
	xorq	%r12, %r11
	movq	%r11, 256(%rsp)
	andnq	%rbx, %r14, %r11
	xorq	%r13, %r11
	movq	%r11, 264(%rsp)
	andnq	%rbp, %rbx, %r11
	xorq	%r14, %r11
	movq	%r11, 272(%rsp)
	movq	64(%rsp), %r11
	xorq	%r9, %r11
	rolq	$28, %r11
	movq	112(%rsp), %rbx
	xorq	%r10, %rbx
	rolq	$20, %rbx
	movq	120(%rsp), %rbp
	xorq	%rsi, %rbp
	rolq	$3, %rbp
	movq	168(%rsp), %r12
	xorq	%rdi, %r12
	rolq	$45, %r12
	movq	216(%rsp), %r13
	xorq	%r8, %r13
	rolq	$61, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 280(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 288(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 296(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 304(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 312(%rsp)
	movq	48(%rsp), %r11
	xorq	%rdi, %r11
	rolq	$1, %r11
	movq	96(%rsp), %rbx
	xorq	%r8, %rbx
	rolq	$6, %rbx
	movq	144(%rsp), %rbp
	xorq	%r9, %rbp
	rolq	$25, %rbp
	movq	192(%rsp), %r12
	xorq	%r10, %r12
	rolq	$8, %r12
	movq	200(%rsp), %r13
	xorq	%rsi, %r13
	rolq	$18, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 320(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 328(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 336(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 344(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 352(%rsp)
	movq	72(%rsp), %r11
	xorq	%r10, %r11
	rolq	$27, %r11
	movq	80(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$36, %rbx
	movq	128(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$10, %rbp
	movq	176(%rsp), %r12
	xorq	%r8, %r12
	rolq	$15, %r12
	movq	224(%rsp), %r13
	xorq	%r9, %r13
	rolq	$56, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 360(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 368(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 376(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 384(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 392(%rsp)
	movq	56(%rsp), %r11
	xorq	%r8, %r11
	rolq	$62, %r11
	movq	104(%rsp), %r8
	xorq	%r9, %r8
	rolq	$55, %r8
	movq	152(%rsp), %r9
	xorq	%r10, %r9
	rolq	$39, %r9
	movq	160(%rsp), %r10
	xorq	%rsi, %r10
	rolq	$41, %r10
	movq	208(%rsp), %rsi
	xorq	%rdi, %rsi
	rolq	$2, %rsi
	andnq	%r9, %r8, %rdi
	xorq	%r11, %rdi
	movq	%rdi, 400(%rsp)
	andnq	%r10, %r9, %rdi
	xorq	%r8, %rdi
	movq	%rdi, 408(%rsp)
	andnq	%rsi, %r10, %rdi
	xorq	%r9, %rdi
	movq	%rdi, 416(%rsp)
	andnq	%r11, %rsi, %rdi
	xorq	%r10, %rdi
	movq	%rdi, 424(%rsp)
	andnq	%r8, %r11, %rdi
	xorq	%rsi, %rdi
	movq	%rdi, 432(%rsp)
	movq	8(%rcx,%rdx,8), %r11
	movq	240(%rsp), %r10
	movq	248(%rsp), %r9
	movq	256(%rsp), %rbx
	movq	264(%rsp), %rbp
	movq	272(%rsp), %r12
	xorq	280(%rsp), %r10
	xorq	288(%rsp), %r9
	xorq	296(%rsp), %rbx
	xorq	304(%rsp), %rbp
	xorq	312(%rsp), %r12
	xorq	320(%rsp), %r10
	xorq	328(%rsp), %r9
	xorq	336(%rsp), %rbx
	xorq	344(%rsp), %rbp
	xorq	352(%rsp), %r12
	xorq	360(%rsp), %r10
	xorq	368(%rsp), %r9
	xorq	376(%rsp), %rbx
	xorq	384(%rsp), %rbp
	xorq	392(%rsp), %r12
	xorq	400(%rsp), %r10
	xorq	408(%rsp), %r9
	xorq	416(%rsp), %rbx
	xorq	424(%rsp), %rbp
	xorq	432(%rsp), %r12
	movq	%r9, %rsi
	rolq	$1, %rsi
	xorq	%r12, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r10, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r9, %r8
	movq	%r12, %r9
	rolq	$1, %r9
	xorq	%rbx, %r9
	rolq	$1, %r10
	xorq	%rbp, %r10
	movq	240(%rsp), %rbx
	xorq	%rsi, %rbx
	movq	288(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$44, %rbp
	movq	336(%rsp), %r12
	xorq	%r8, %r12
	rolq	$43, %r12
	movq	384(%rsp), %r13
	xorq	%r9, %r13
	rolq	$21, %r13
	movq	432(%rsp), %r14
	xorq	%r10, %r14
	rolq	$14, %r14
	andnq	%r12, %rbp, %r15
	xorq	%rbx, %r15
	xorq	%r11, %r15
	movq	%r15, 40(%rsp)
	andnq	%r13, %r12, %r11
	xorq	%rbp, %r11
	movq	%r11, 48(%rsp)
	andnq	%r14, %r13, %r11
	xorq	%r12, %r11
	movq	%r11, 56(%rsp)
	andnq	%rbx, %r14, %r11
	xorq	%r13, %r11
	movq	%r11, 64(%rsp)
	andnq	%rbp, %rbx, %r11
	xorq	%r14, %r11
	movq	%r11, 72(%rsp)
	movq	264(%rsp), %r11
	xorq	%r9, %r11
	rolq	$28, %r11
	movq	312(%rsp), %rbx
	xorq	%r10, %rbx
	rolq	$20, %rbx
	movq	320(%rsp), %rbp
	xorq	%rsi, %rbp
	rolq	$3, %rbp
	movq	368(%rsp), %r12
	xorq	%rdi, %r12
	rolq	$45, %r12
	movq	416(%rsp), %r13
	xorq	%r8, %r13
	rolq	$61, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 80(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 88(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 96(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 104(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 112(%rsp)
	movq	248(%rsp), %r11
	xorq	%rdi, %r11
	rolq	$1, %r11
	movq	296(%rsp), %rbx
	xorq	%r8, %rbx
	rolq	$6, %rbx
	movq	344(%rsp), %rbp
	xorq	%r9, %rbp
	rolq	$25, %rbp
	movq	392(%rsp), %r12
	xorq	%r10, %r12
	rolq	$8, %r12
	movq	400(%rsp), %r13
	xorq	%rsi, %r13
	rolq	$18, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 120(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 128(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 136(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 144(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 152(%rsp)
	movq	272(%rsp), %r11
	xorq	%r10, %r11
	rolq	$27, %r11
	movq	280(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$36, %rbx
	movq	328(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$10, %rbp
	movq	376(%rsp), %r12
	xorq	%r8, %r12
	rolq	$15, %r12
	movq	424(%rsp), %r13
	xorq	%r9, %r13
	rolq	$56, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 160(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 168(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 176(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 184(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 192(%rsp)
	movq	256(%rsp), %r11
	xorq	%r8, %r11
	rolq	$62, %r11
	movq	304(%rsp), %r8
	xorq	%r9, %r8
	rolq	$55, %r8
	movq	352(%rsp), %r9
	xorq	%r10, %r9
	rolq	$39, %r9
	movq	360(%rsp), %r10
	xorq	%rsi, %r10
	rolq	$41, %r10
	movq	408(%rsp), %rsi
	xorq	%rdi, %rsi
	rolq	$2, %rsi
	andnq	%r9, %r8, %rdi
	xorq	%r11, %rdi
	movq	%rdi, 200(%rsp)
	andnq	%r10, %r9, %rdi
	xorq	%r8, %rdi
	movq	%rdi, 208(%rsp)
	andnq	%rsi, %r10, %rdi
	xorq	%r9, %rdi
	movq	%rdi, 216(%rsp)
	andnq	%r11, %rsi, %rdi
	xorq	%r10, %rdi
	movq	%rdi, 224(%rsp)
	andnq	%r8, %r11, %rdi
	xorq	%rsi, %rdi
	movq	%rdi, 232(%rsp)
	addq	$2, %rdx
	cmpq	$24, %rdx
	jb  	L_keccak1600_ref$18
	movq	16(%rsp), %rsi
	movq	24(%rsp), %rdx
	movq	32(%rsp), %rcx
L_keccak1600_ref$16:
	cmpq	%rcx, %rdx
	jnb 	L_keccak1600_ref$17
	movb	440(%rsp), %dil
	movq	%rdx, %r8
	shrq	$3, %r8
	movq	$0, %r9
	jmp 	L_keccak1600_ref$14
L_keccak1600_ref$15:
	movq	(%rsi,%r9,8), %r10
	xorq	%r10, 40(%rsp,%r9,8)
	incq	%r9
L_keccak1600_ref$14:
	cmpq	%r8, %r9
	jb  	L_keccak1600_ref$15
	shlq	$3, %r9
	jmp 	L_keccak1600_ref$12
L_keccak1600_ref$13:
	movb	(%rsi,%r9), %r8b
	xorb	%r8b, 40(%rsp,%r9)
	incq	%r9
L_keccak1600_ref$12:
	cmpq	%rdx, %r9
	jb  	L_keccak1600_ref$13
	xorb	%dil, 40(%rsp,%r9)
	movq	%rcx, %rdx
	addq	$-1, %rdx
	xorb	$-128, 40(%rsp,%rdx)
	movq	8(%rsp), %rsi
	jmp 	L_keccak1600_ref$7
L_keccak1600_ref$8:
	movq	%rsi, 8(%rsp)
	movq	%rcx, 32(%rsp)
	leaq	glob_data + 0(%rip), %rcx
	movq	$0, %rdx
L_keccak1600_ref$11:
	movq	(%rcx,%rdx,8), %r11
	movq	40(%rsp), %r10
	movq	48(%rsp), %r9
	movq	56(%rsp), %rbx
	movq	64(%rsp), %rbp
	movq	72(%rsp), %r12
	xorq	80(%rsp), %r10
	xorq	88(%rsp), %r9
	xorq	96(%rsp), %rbx
	xorq	104(%rsp), %rbp
	xorq	112(%rsp), %r12
	xorq	120(%rsp), %r10
	xorq	128(%rsp), %r9
	xorq	136(%rsp), %rbx
	xorq	144(%rsp), %rbp
	xorq	152(%rsp), %r12
	xorq	160(%rsp), %r10
	xorq	168(%rsp), %r9
	xorq	176(%rsp), %rbx
	xorq	184(%rsp), %rbp
	xorq	192(%rsp), %r12
	xorq	200(%rsp), %r10
	xorq	208(%rsp), %r9
	xorq	216(%rsp), %rbx
	xorq	224(%rsp), %rbp
	xorq	232(%rsp), %r12
	movq	%r9, %rsi
	rolq	$1, %rsi
	xorq	%r12, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r10, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r9, %r8
	movq	%r12, %r9
	rolq	$1, %r9
	xorq	%rbx, %r9
	rolq	$1, %r10
	xorq	%rbp, %r10
	movq	40(%rsp), %rbx
	xorq	%rsi, %rbx
	movq	88(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$44, %rbp
	movq	136(%rsp), %r12
	xorq	%r8, %r12
	rolq	$43, %r12
	movq	184(%rsp), %r13
	xorq	%r9, %r13
	rolq	$21, %r13
	movq	232(%rsp), %r14
	xorq	%r10, %r14
	rolq	$14, %r14
	andnq	%r12, %rbp, %r15
	xorq	%rbx, %r15
	xorq	%r11, %r15
	movq	%r15, 240(%rsp)
	andnq	%r13, %r12, %r11
	xorq	%rbp, %r11
	movq	%r11, 248(%rsp)
	andnq	%r14, %r13, %r11
	xorq	%r12, %r11
	movq	%r11, 256(%rsp)
	andnq	%rbx, %r14, %r11
	xorq	%r13, %r11
	movq	%r11, 264(%rsp)
	andnq	%rbp, %rbx, %r11
	xorq	%r14, %r11
	movq	%r11, 272(%rsp)
	movq	64(%rsp), %r11
	xorq	%r9, %r11
	rolq	$28, %r11
	movq	112(%rsp), %rbx
	xorq	%r10, %rbx
	rolq	$20, %rbx
	movq	120(%rsp), %rbp
	xorq	%rsi, %rbp
	rolq	$3, %rbp
	movq	168(%rsp), %r12
	xorq	%rdi, %r12
	rolq	$45, %r12
	movq	216(%rsp), %r13
	xorq	%r8, %r13
	rolq	$61, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 280(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 288(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 296(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 304(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 312(%rsp)
	movq	48(%rsp), %r11
	xorq	%rdi, %r11
	rolq	$1, %r11
	movq	96(%rsp), %rbx
	xorq	%r8, %rbx
	rolq	$6, %rbx
	movq	144(%rsp), %rbp
	xorq	%r9, %rbp
	rolq	$25, %rbp
	movq	192(%rsp), %r12
	xorq	%r10, %r12
	rolq	$8, %r12
	movq	200(%rsp), %r13
	xorq	%rsi, %r13
	rolq	$18, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 320(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 328(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 336(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 344(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 352(%rsp)
	movq	72(%rsp), %r11
	xorq	%r10, %r11
	rolq	$27, %r11
	movq	80(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$36, %rbx
	movq	128(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$10, %rbp
	movq	176(%rsp), %r12
	xorq	%r8, %r12
	rolq	$15, %r12
	movq	224(%rsp), %r13
	xorq	%r9, %r13
	rolq	$56, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 360(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 368(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 376(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 384(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 392(%rsp)
	movq	56(%rsp), %r11
	xorq	%r8, %r11
	rolq	$62, %r11
	movq	104(%rsp), %r8
	xorq	%r9, %r8
	rolq	$55, %r8
	movq	152(%rsp), %r9
	xorq	%r10, %r9
	rolq	$39, %r9
	movq	160(%rsp), %r10
	xorq	%rsi, %r10
	rolq	$41, %r10
	movq	208(%rsp), %rsi
	xorq	%rdi, %rsi
	rolq	$2, %rsi
	andnq	%r9, %r8, %rdi
	xorq	%r11, %rdi
	movq	%rdi, 400(%rsp)
	andnq	%r10, %r9, %rdi
	xorq	%r8, %rdi
	movq	%rdi, 408(%rsp)
	andnq	%rsi, %r10, %rdi
	xorq	%r9, %rdi
	movq	%rdi, 416(%rsp)
	andnq	%r11, %rsi, %rdi
	xorq	%r10, %rdi
	movq	%rdi, 424(%rsp)
	andnq	%r8, %r11, %rdi
	xorq	%rsi, %rdi
	movq	%rdi, 432(%rsp)
	movq	8(%rcx,%rdx,8), %r11
	movq	240(%rsp), %r10
	movq	248(%rsp), %r9
	movq	256(%rsp), %rbx
	movq	264(%rsp), %rbp
	movq	272(%rsp), %r12
	xorq	280(%rsp), %r10
	xorq	288(%rsp), %r9
	xorq	296(%rsp), %rbx
	xorq	304(%rsp), %rbp
	xorq	312(%rsp), %r12
	xorq	320(%rsp), %r10
	xorq	328(%rsp), %r9
	xorq	336(%rsp), %rbx
	xorq	344(%rsp), %rbp
	xorq	352(%rsp), %r12
	xorq	360(%rsp), %r10
	xorq	368(%rsp), %r9
	xorq	376(%rsp), %rbx
	xorq	384(%rsp), %rbp
	xorq	392(%rsp), %r12
	xorq	400(%rsp), %r10
	xorq	408(%rsp), %r9
	xorq	416(%rsp), %rbx
	xorq	424(%rsp), %rbp
	xorq	432(%rsp), %r12
	movq	%r9, %rsi
	rolq	$1, %rsi
	xorq	%r12, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r10, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r9, %r8
	movq	%r12, %r9
	rolq	$1, %r9
	xorq	%rbx, %r9
	rolq	$1, %r10
	xorq	%rbp, %r10
	movq	240(%rsp), %rbx
	xorq	%rsi, %rbx
	movq	288(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$44, %rbp
	movq	336(%rsp), %r12
	xorq	%r8, %r12
	rolq	$43, %r12
	movq	384(%rsp), %r13
	xorq	%r9, %r13
	rolq	$21, %r13
	movq	432(%rsp), %r14
	xorq	%r10, %r14
	rolq	$14, %r14
	andnq	%r12, %rbp, %r15
	xorq	%rbx, %r15
	xorq	%r11, %r15
	movq	%r15, 40(%rsp)
	andnq	%r13, %r12, %r11
	xorq	%rbp, %r11
	movq	%r11, 48(%rsp)
	andnq	%r14, %r13, %r11
	xorq	%r12, %r11
	movq	%r11, 56(%rsp)
	andnq	%rbx, %r14, %r11
	xorq	%r13, %r11
	movq	%r11, 64(%rsp)
	andnq	%rbp, %rbx, %r11
	xorq	%r14, %r11
	movq	%r11, 72(%rsp)
	movq	264(%rsp), %r11
	xorq	%r9, %r11
	rolq	$28, %r11
	movq	312(%rsp), %rbx
	xorq	%r10, %rbx
	rolq	$20, %rbx
	movq	320(%rsp), %rbp
	xorq	%rsi, %rbp
	rolq	$3, %rbp
	movq	368(%rsp), %r12
	xorq	%rdi, %r12
	rolq	$45, %r12
	movq	416(%rsp), %r13
	xorq	%r8, %r13
	rolq	$61, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 80(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 88(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 96(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 104(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 112(%rsp)
	movq	248(%rsp), %r11
	xorq	%rdi, %r11
	rolq	$1, %r11
	movq	296(%rsp), %rbx
	xorq	%r8, %rbx
	rolq	$6, %rbx
	movq	344(%rsp), %rbp
	xorq	%r9, %rbp
	rolq	$25, %rbp
	movq	392(%rsp), %r12
	xorq	%r10, %r12
	rolq	$8, %r12
	movq	400(%rsp), %r13
	xorq	%rsi, %r13
	rolq	$18, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 120(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 128(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 136(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 144(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 152(%rsp)
	movq	272(%rsp), %r11
	xorq	%r10, %r11
	rolq	$27, %r11
	movq	280(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$36, %rbx
	movq	328(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$10, %rbp
	movq	376(%rsp), %r12
	xorq	%r8, %r12
	rolq	$15, %r12
	movq	424(%rsp), %r13
	xorq	%r9, %r13
	rolq	$56, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 160(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 168(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 176(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 184(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 192(%rsp)
	movq	256(%rsp), %r11
	xorq	%r8, %r11
	rolq	$62, %r11
	movq	304(%rsp), %r8
	xorq	%r9, %r8
	rolq	$55, %r8
	movq	352(%rsp), %r9
	xorq	%r10, %r9
	rolq	$39, %r9
	movq	360(%rsp), %r10
	xorq	%rsi, %r10
	rolq	$41, %r10
	movq	408(%rsp), %rsi
	xorq	%rdi, %rsi
	rolq	$2, %rsi
	andnq	%r9, %r8, %rdi
	xorq	%r11, %rdi
	movq	%rdi, 200(%rsp)
	andnq	%r10, %r9, %rdi
	xorq	%r8, %rdi
	movq	%rdi, 208(%rsp)
	andnq	%rsi, %r10, %rdi
	xorq	%r9, %rdi
	movq	%rdi, 216(%rsp)
	andnq	%r11, %rsi, %rdi
	xorq	%r10, %rdi
	movq	%rdi, 224(%rsp)
	andnq	%r8, %r11, %rdi
	xorq	%rsi, %rdi
	movq	%rdi, 232(%rsp)
	addq	$2, %rdx
	cmpq	$24, %rdx
	jb  	L_keccak1600_ref$11
	movq	(%rsp), %rdx
	movq	8(%rsp), %rsi
	movq	32(%rsp), %rcx
	movq	%rcx, %rdi
	shrq	$3, %rdi
	movq	$0, %r8
	jmp 	L_keccak1600_ref$9
L_keccak1600_ref$10:
	movq	40(%rsp,%r8,8), %r9
	movq	%r9, (%rdx,%r8,8)
	incq	%r8
L_keccak1600_ref$9:
	cmpq	%rdi, %r8
	jb  	L_keccak1600_ref$10
	addq	%rcx, %rdx
	subq	%rcx, %rsi
	movq	%rdx, (%rsp)
L_keccak1600_ref$7:
	cmpq	%rcx, %rsi
	jnbe	L_keccak1600_ref$8
	movq	%rsi, 32(%rsp)
	leaq	glob_data + 0(%rip), %rcx
	movq	$0, %rdx
L_keccak1600_ref$6:
	movq	(%rcx,%rdx,8), %r11
	movq	40(%rsp), %r10
	movq	48(%rsp), %r9
	movq	56(%rsp), %rbx
	movq	64(%rsp), %rbp
	movq	72(%rsp), %r12
	xorq	80(%rsp), %r10
	xorq	88(%rsp), %r9
	xorq	96(%rsp), %rbx
	xorq	104(%rsp), %rbp
	xorq	112(%rsp), %r12
	xorq	120(%rsp), %r10
	xorq	128(%rsp), %r9
	xorq	136(%rsp), %rbx
	xorq	144(%rsp), %rbp
	xorq	152(%rsp), %r12
	xorq	160(%rsp), %r10
	xorq	168(%rsp), %r9
	xorq	176(%rsp), %rbx
	xorq	184(%rsp), %rbp
	xorq	192(%rsp), %r12
	xorq	200(%rsp), %r10
	xorq	208(%rsp), %r9
	xorq	216(%rsp), %rbx
	xorq	224(%rsp), %rbp
	xorq	232(%rsp), %r12
	movq	%r9, %rsi
	rolq	$1, %rsi
	xorq	%r12, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r10, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r9, %r8
	movq	%r12, %r9
	rolq	$1, %r9
	xorq	%rbx, %r9
	rolq	$1, %r10
	xorq	%rbp, %r10
	movq	40(%rsp), %rbx
	xorq	%rsi, %rbx
	movq	88(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$44, %rbp
	movq	136(%rsp), %r12
	xorq	%r8, %r12
	rolq	$43, %r12
	movq	184(%rsp), %r13
	xorq	%r9, %r13
	rolq	$21, %r13
	movq	232(%rsp), %r14
	xorq	%r10, %r14
	rolq	$14, %r14
	andnq	%r12, %rbp, %r15
	xorq	%rbx, %r15
	xorq	%r11, %r15
	movq	%r15, 240(%rsp)
	andnq	%r13, %r12, %r11
	xorq	%rbp, %r11
	movq	%r11, 248(%rsp)
	andnq	%r14, %r13, %r11
	xorq	%r12, %r11
	movq	%r11, 256(%rsp)
	andnq	%rbx, %r14, %r11
	xorq	%r13, %r11
	movq	%r11, 264(%rsp)
	andnq	%rbp, %rbx, %r11
	xorq	%r14, %r11
	movq	%r11, 272(%rsp)
	movq	64(%rsp), %r11
	xorq	%r9, %r11
	rolq	$28, %r11
	movq	112(%rsp), %rbx
	xorq	%r10, %rbx
	rolq	$20, %rbx
	movq	120(%rsp), %rbp
	xorq	%rsi, %rbp
	rolq	$3, %rbp
	movq	168(%rsp), %r12
	xorq	%rdi, %r12
	rolq	$45, %r12
	movq	216(%rsp), %r13
	xorq	%r8, %r13
	rolq	$61, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 280(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 288(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 296(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 304(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 312(%rsp)
	movq	48(%rsp), %r11
	xorq	%rdi, %r11
	rolq	$1, %r11
	movq	96(%rsp), %rbx
	xorq	%r8, %rbx
	rolq	$6, %rbx
	movq	144(%rsp), %rbp
	xorq	%r9, %rbp
	rolq	$25, %rbp
	movq	192(%rsp), %r12
	xorq	%r10, %r12
	rolq	$8, %r12
	movq	200(%rsp), %r13
	xorq	%rsi, %r13
	rolq	$18, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 320(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 328(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 336(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 344(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 352(%rsp)
	movq	72(%rsp), %r11
	xorq	%r10, %r11
	rolq	$27, %r11
	movq	80(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$36, %rbx
	movq	128(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$10, %rbp
	movq	176(%rsp), %r12
	xorq	%r8, %r12
	rolq	$15, %r12
	movq	224(%rsp), %r13
	xorq	%r9, %r13
	rolq	$56, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 360(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 368(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 376(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 384(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 392(%rsp)
	movq	56(%rsp), %r11
	xorq	%r8, %r11
	rolq	$62, %r11
	movq	104(%rsp), %r8
	xorq	%r9, %r8
	rolq	$55, %r8
	movq	152(%rsp), %r9
	xorq	%r10, %r9
	rolq	$39, %r9
	movq	160(%rsp), %r10
	xorq	%rsi, %r10
	rolq	$41, %r10
	movq	208(%rsp), %rsi
	xorq	%rdi, %rsi
	rolq	$2, %rsi
	andnq	%r9, %r8, %rdi
	xorq	%r11, %rdi
	movq	%rdi, 400(%rsp)
	andnq	%r10, %r9, %rdi
	xorq	%r8, %rdi
	movq	%rdi, 408(%rsp)
	andnq	%rsi, %r10, %rdi
	xorq	%r9, %rdi
	movq	%rdi, 416(%rsp)
	andnq	%r11, %rsi, %rdi
	xorq	%r10, %rdi
	movq	%rdi, 424(%rsp)
	andnq	%r8, %r11, %rdi
	xorq	%rsi, %rdi
	movq	%rdi, 432(%rsp)
	movq	8(%rcx,%rdx,8), %r11
	movq	240(%rsp), %r10
	movq	248(%rsp), %r9
	movq	256(%rsp), %rbx
	movq	264(%rsp), %rbp
	movq	272(%rsp), %r12
	xorq	280(%rsp), %r10
	xorq	288(%rsp), %r9
	xorq	296(%rsp), %rbx
	xorq	304(%rsp), %rbp
	xorq	312(%rsp), %r12
	xorq	320(%rsp), %r10
	xorq	328(%rsp), %r9
	xorq	336(%rsp), %rbx
	xorq	344(%rsp), %rbp
	xorq	352(%rsp), %r12
	xorq	360(%rsp), %r10
	xorq	368(%rsp), %r9
	xorq	376(%rsp), %rbx
	xorq	384(%rsp), %rbp
	xorq	392(%rsp), %r12
	xorq	400(%rsp), %r10
	xorq	408(%rsp), %r9
	xorq	416(%rsp), %rbx
	xorq	424(%rsp), %rbp
	xorq	432(%rsp), %r12
	movq	%r9, %rsi
	rolq	$1, %rsi
	xorq	%r12, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r10, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r9, %r8
	movq	%r12, %r9
	rolq	$1, %r9
	xorq	%rbx, %r9
	rolq	$1, %r10
	xorq	%rbp, %r10
	movq	240(%rsp), %rbx
	xorq	%rsi, %rbx
	movq	288(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$44, %rbp
	movq	336(%rsp), %r12
	xorq	%r8, %r12
	rolq	$43, %r12
	movq	384(%rsp), %r13
	xorq	%r9, %r13
	rolq	$21, %r13
	movq	432(%rsp), %r14
	xorq	%r10, %r14
	rolq	$14, %r14
	andnq	%r12, %rbp, %r15
	xorq	%rbx, %r15
	xorq	%r11, %r15
	movq	%r15, 40(%rsp)
	andnq	%r13, %r12, %r11
	xorq	%rbp, %r11
	movq	%r11, 48(%rsp)
	andnq	%r14, %r13, %r11
	xorq	%r12, %r11
	movq	%r11, 56(%rsp)
	andnq	%rbx, %r14, %r11
	xorq	%r13, %r11
	movq	%r11, 64(%rsp)
	andnq	%rbp, %rbx, %r11
	xorq	%r14, %r11
	movq	%r11, 72(%rsp)
	movq	264(%rsp), %r11
	xorq	%r9, %r11
	rolq	$28, %r11
	movq	312(%rsp), %rbx
	xorq	%r10, %rbx
	rolq	$20, %rbx
	movq	320(%rsp), %rbp
	xorq	%rsi, %rbp
	rolq	$3, %rbp
	movq	368(%rsp), %r12
	xorq	%rdi, %r12
	rolq	$45, %r12
	movq	416(%rsp), %r13
	xorq	%r8, %r13
	rolq	$61, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 80(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 88(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 96(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 104(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 112(%rsp)
	movq	248(%rsp), %r11
	xorq	%rdi, %r11
	rolq	$1, %r11
	movq	296(%rsp), %rbx
	xorq	%r8, %rbx
	rolq	$6, %rbx
	movq	344(%rsp), %rbp
	xorq	%r9, %rbp
	rolq	$25, %rbp
	movq	392(%rsp), %r12
	xorq	%r10, %r12
	rolq	$8, %r12
	movq	400(%rsp), %r13
	xorq	%rsi, %r13
	rolq	$18, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 120(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 128(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 136(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 144(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 152(%rsp)
	movq	272(%rsp), %r11
	xorq	%r10, %r11
	rolq	$27, %r11
	movq	280(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$36, %rbx
	movq	328(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$10, %rbp
	movq	376(%rsp), %r12
	xorq	%r8, %r12
	rolq	$15, %r12
	movq	424(%rsp), %r13
	xorq	%r9, %r13
	rolq	$56, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 160(%rsp)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 168(%rsp)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 176(%rsp)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 184(%rsp)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 192(%rsp)
	movq	256(%rsp), %r11
	xorq	%r8, %r11
	rolq	$62, %r11
	movq	304(%rsp), %r8
	xorq	%r9, %r8
	rolq	$55, %r8
	movq	352(%rsp), %r9
	xorq	%r10, %r9
	rolq	$39, %r9
	movq	360(%rsp), %r10
	xorq	%rsi, %r10
	rolq	$41, %r10
	movq	408(%rsp), %rsi
	xorq	%rdi, %rsi
	rolq	$2, %rsi
	andnq	%r9, %r8, %rdi
	xorq	%r11, %rdi
	movq	%rdi, 200(%rsp)
	andnq	%r10, %r9, %rdi
	xorq	%r8, %rdi
	movq	%rdi, 208(%rsp)
	andnq	%rsi, %r10, %rdi
	xorq	%r9, %rdi
	movq	%rdi, 216(%rsp)
	andnq	%r11, %rsi, %rdi
	xorq	%r10, %rdi
	movq	%rdi, 224(%rsp)
	andnq	%r8, %r11, %rdi
	xorq	%rsi, %rdi
	movq	%rdi, 232(%rsp)
	addq	$2, %rdx
	cmpq	$24, %rdx
	jb  	L_keccak1600_ref$6
	movq	(%rsp), %rcx
	movq	32(%rsp), %rdx
	movq	%rdx, %rsi
	shrq	$3, %rsi
	movq	$0, %rdi
	jmp 	L_keccak1600_ref$4
L_keccak1600_ref$5:
	movq	40(%rsp,%rdi,8), %r8
	movq	%r8, (%rcx,%rdi,8)
	incq	%rdi
L_keccak1600_ref$4:
	cmpq	%rsi, %rdi
	jb  	L_keccak1600_ref$5
	shlq	$3, %rdi
	jmp 	L_keccak1600_ref$2
L_keccak1600_ref$3:
	movb	40(%rsp,%rdi), %sil
	movb	%sil, (%rcx,%rdi)
	incq	%rdi
L_keccak1600_ref$2:
	cmpq	%rdx, %rdi
	jb  	L_keccak1600_ref$3
	jmp 	*%rax
	.data
	.p2align	5
_glob_data:
glob_data:
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
