	.att_syntax
	.text
	.p2align	5
	.globl	_jade_hash_sha3_256_amd64_ref
	.globl	jade_hash_sha3_256_amd64_ref
_jade_hash_sha3_256_amd64_ref:
jade_hash_sha3_256_amd64_ref:
	movq	%rsp, %rax
	leaq	-48(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rax, 40(%rsp)
	movq	%rbx, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r13, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	$32, %rcx
	movb	$6, %r8b
	movq	$136, %rax
	leaq	-448(%rsp), %rsp
	call	L_keccak1600_ref$1
Ljade_hash_sha3_256_amd64_ref$1:
	leaq	448(%rsp), %rsp
	xorq	%rax, %rax
	movq	(%rsp), %rbx
	movq	8(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	movq	32(%rsp), %r14
	movq	40(%rsp), %rsp
	ret 
L_keccak1600_ref$1:
	movq	%rdi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movb	%r8b, 448(%rsp)
	xorq	%rcx, %rcx
	movq	%rcx, 48(%rsp)
	movq	%rcx, 56(%rsp)
	movq	%rcx, 64(%rsp)
	movq	%rcx, 72(%rsp)
	movq	%rcx, 80(%rsp)
	movq	%rcx, 88(%rsp)
	movq	%rcx, 96(%rsp)
	movq	%rcx, 104(%rsp)
	movq	%rcx, 112(%rsp)
	movq	%rcx, 120(%rsp)
	movq	%rcx, 128(%rsp)
	movq	%rcx, 136(%rsp)
	movq	%rcx, 144(%rsp)
	movq	%rcx, 152(%rsp)
	movq	%rcx, 160(%rsp)
	movq	%rcx, 168(%rsp)
	movq	%rcx, 176(%rsp)
	movq	%rcx, 184(%rsp)
	movq	%rcx, 192(%rsp)
	movq	%rcx, 200(%rsp)
	movq	%rcx, 208(%rsp)
	movq	%rcx, 216(%rsp)
	movq	%rcx, 224(%rsp)
	movq	%rcx, 232(%rsp)
	movq	%rcx, 240(%rsp)
	jmp 	L_keccak1600_ref$16
L_keccak1600_ref$17:
	movq	%rax, %rcx
	shrq	$3, %rcx
	movq	$0, %rdi
	jmp 	L_keccak1600_ref$19
L_keccak1600_ref$20:
	movq	(%rsi,%rdi,8), %r8
	xorq	%r8, 48(%rsp,%rdi,8)
	incq	%rdi
L_keccak1600_ref$19:
	cmpq	%rcx, %rdi
	jb  	L_keccak1600_ref$20
	addq	%rax, %rsi
	subq	%rax, %rdx
	movq	%rsi, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	%rax, 40(%rsp)
	leaq	glob_data + 0(%rip), %rax
	movq	$0, %rcx
L_keccak1600_ref$18:
	movq	(%rax,%rcx,8), %r10
	movq	48(%rsp), %r9
	movq	56(%rsp), %r8
	movq	64(%rsp), %r11
	movq	72(%rsp), %rbx
	movq	80(%rsp), %rbp
	xorq	88(%rsp), %r9
	xorq	96(%rsp), %r8
	xorq	104(%rsp), %r11
	xorq	112(%rsp), %rbx
	xorq	120(%rsp), %rbp
	xorq	128(%rsp), %r9
	xorq	136(%rsp), %r8
	xorq	144(%rsp), %r11
	xorq	152(%rsp), %rbx
	xorq	160(%rsp), %rbp
	xorq	168(%rsp), %r9
	xorq	176(%rsp), %r8
	xorq	184(%rsp), %r11
	xorq	192(%rsp), %rbx
	xorq	200(%rsp), %rbp
	xorq	208(%rsp), %r9
	xorq	216(%rsp), %r8
	xorq	224(%rsp), %r11
	xorq	232(%rsp), %rbx
	xorq	240(%rsp), %rbp
	movq	%r8, %rdx
	rolq	$1, %rdx
	xorq	%rbp, %rdx
	movq	%r11, %rsi
	rolq	$1, %rsi
	xorq	%r9, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r8, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r11, %r8
	rolq	$1, %r9
	xorq	%rbx, %r9
	movq	48(%rsp), %r11
	xorq	%rdx, %r11
	movq	96(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$44, %rbx
	movq	144(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$43, %rbp
	movq	192(%rsp), %r12
	xorq	%r8, %r12
	rolq	$21, %r12
	movq	240(%rsp), %r13
	xorq	%r9, %r13
	rolq	$14, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	xorq	%r10, %r14
	movq	%r14, 248(%rsp)
	movq	%rbp, %r10
	notq	%r10
	andq	%r12, %r10
	xorq	%rbx, %r10
	movq	%r10, 256(%rsp)
	movq	%r12, %r10
	notq	%r10
	andq	%r13, %r10
	xorq	%rbp, %r10
	movq	%r10, 264(%rsp)
	movq	%r13, %r10
	notq	%r10
	andq	%r11, %r10
	xorq	%r12, %r10
	movq	%r10, 272(%rsp)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 280(%rsp)
	movq	72(%rsp), %r10
	xorq	%r8, %r10
	rolq	$28, %r10
	movq	120(%rsp), %r11
	xorq	%r9, %r11
	rolq	$20, %r11
	movq	128(%rsp), %r12
	xorq	%rdx, %r12
	rolq	$3, %r12
	movq	176(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$45, %rbx
	movq	224(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$61, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 288(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 296(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 304(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 312(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 320(%rsp)
	movq	56(%rsp), %r10
	xorq	%rsi, %r10
	rolq	$1, %r10
	movq	104(%rsp), %r11
	xorq	%rdi, %r11
	rolq	$6, %r11
	movq	152(%rsp), %r12
	xorq	%r8, %r12
	rolq	$25, %r12
	movq	200(%rsp), %rbx
	xorq	%r9, %rbx
	rolq	$8, %rbx
	movq	208(%rsp), %rbp
	xorq	%rdx, %rbp
	rolq	$18, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 328(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 336(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 344(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 352(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 360(%rsp)
	movq	80(%rsp), %r10
	xorq	%r9, %r10
	rolq	$27, %r10
	movq	88(%rsp), %r11
	xorq	%rdx, %r11
	rolq	$36, %r11
	movq	136(%rsp), %r12
	xorq	%rsi, %r12
	rolq	$10, %r12
	movq	184(%rsp), %rbx
	xorq	%rdi, %rbx
	rolq	$15, %rbx
	movq	232(%rsp), %rbp
	xorq	%r8, %rbp
	rolq	$56, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 368(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 376(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 384(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 392(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 400(%rsp)
	movq	64(%rsp), %r10
	xorq	%rdi, %r10
	rolq	$62, %r10
	movq	112(%rsp), %rdi
	xorq	%r8, %rdi
	rolq	$55, %rdi
	movq	160(%rsp), %r8
	xorq	%r9, %r8
	rolq	$39, %r8
	movq	168(%rsp), %r9
	xorq	%rdx, %r9
	rolq	$41, %r9
	movq	216(%rsp), %rdx
	xorq	%rsi, %rdx
	rolq	$2, %rdx
	movq	%rdi, %rsi
	notq	%rsi
	andq	%r8, %rsi
	xorq	%r10, %rsi
	movq	%rsi, 408(%rsp)
	movq	%r8, %rsi
	notq	%rsi
	andq	%r9, %rsi
	xorq	%rdi, %rsi
	movq	%rsi, 416(%rsp)
	movq	%r9, %rsi
	notq	%rsi
	andq	%rdx, %rsi
	xorq	%r8, %rsi
	movq	%rsi, 424(%rsp)
	movq	%rdx, %rsi
	notq	%rsi
	andq	%r10, %rsi
	xorq	%r9, %rsi
	movq	%rsi, 432(%rsp)
	notq	%r10
	andq	%rdi, %r10
	xorq	%rdx, %r10
	movq	%r10, 440(%rsp)
	movq	8(%rax,%rcx,8), %r10
	movq	248(%rsp), %r9
	movq	256(%rsp), %r8
	movq	264(%rsp), %r11
	movq	272(%rsp), %rbx
	movq	280(%rsp), %rbp
	xorq	288(%rsp), %r9
	xorq	296(%rsp), %r8
	xorq	304(%rsp), %r11
	xorq	312(%rsp), %rbx
	xorq	320(%rsp), %rbp
	xorq	328(%rsp), %r9
	xorq	336(%rsp), %r8
	xorq	344(%rsp), %r11
	xorq	352(%rsp), %rbx
	xorq	360(%rsp), %rbp
	xorq	368(%rsp), %r9
	xorq	376(%rsp), %r8
	xorq	384(%rsp), %r11
	xorq	392(%rsp), %rbx
	xorq	400(%rsp), %rbp
	xorq	408(%rsp), %r9
	xorq	416(%rsp), %r8
	xorq	424(%rsp), %r11
	xorq	432(%rsp), %rbx
	xorq	440(%rsp), %rbp
	movq	%r8, %rdx
	rolq	$1, %rdx
	xorq	%rbp, %rdx
	movq	%r11, %rsi
	rolq	$1, %rsi
	xorq	%r9, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r8, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r11, %r8
	rolq	$1, %r9
	xorq	%rbx, %r9
	movq	248(%rsp), %r11
	xorq	%rdx, %r11
	movq	296(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$44, %rbx
	movq	344(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$43, %rbp
	movq	392(%rsp), %r12
	xorq	%r8, %r12
	rolq	$21, %r12
	movq	440(%rsp), %r13
	xorq	%r9, %r13
	rolq	$14, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	xorq	%r10, %r14
	movq	%r14, 48(%rsp)
	movq	%rbp, %r10
	notq	%r10
	andq	%r12, %r10
	xorq	%rbx, %r10
	movq	%r10, 56(%rsp)
	movq	%r12, %r10
	notq	%r10
	andq	%r13, %r10
	xorq	%rbp, %r10
	movq	%r10, 64(%rsp)
	movq	%r13, %r10
	notq	%r10
	andq	%r11, %r10
	xorq	%r12, %r10
	movq	%r10, 72(%rsp)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 80(%rsp)
	movq	272(%rsp), %r10
	xorq	%r8, %r10
	rolq	$28, %r10
	movq	320(%rsp), %r11
	xorq	%r9, %r11
	rolq	$20, %r11
	movq	328(%rsp), %r12
	xorq	%rdx, %r12
	rolq	$3, %r12
	movq	376(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$45, %rbx
	movq	424(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$61, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 88(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 96(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 104(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 112(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 120(%rsp)
	movq	256(%rsp), %r10
	xorq	%rsi, %r10
	rolq	$1, %r10
	movq	304(%rsp), %r11
	xorq	%rdi, %r11
	rolq	$6, %r11
	movq	352(%rsp), %r12
	xorq	%r8, %r12
	rolq	$25, %r12
	movq	400(%rsp), %rbx
	xorq	%r9, %rbx
	rolq	$8, %rbx
	movq	408(%rsp), %rbp
	xorq	%rdx, %rbp
	rolq	$18, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 128(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 136(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 144(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 152(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 160(%rsp)
	movq	280(%rsp), %r10
	xorq	%r9, %r10
	rolq	$27, %r10
	movq	288(%rsp), %r11
	xorq	%rdx, %r11
	rolq	$36, %r11
	movq	336(%rsp), %r12
	xorq	%rsi, %r12
	rolq	$10, %r12
	movq	384(%rsp), %rbx
	xorq	%rdi, %rbx
	rolq	$15, %rbx
	movq	432(%rsp), %rbp
	xorq	%r8, %rbp
	rolq	$56, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 168(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 176(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 184(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 192(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 200(%rsp)
	movq	264(%rsp), %r10
	xorq	%rdi, %r10
	rolq	$62, %r10
	movq	312(%rsp), %rdi
	xorq	%r8, %rdi
	rolq	$55, %rdi
	movq	360(%rsp), %r8
	xorq	%r9, %r8
	rolq	$39, %r8
	movq	368(%rsp), %r9
	xorq	%rdx, %r9
	rolq	$41, %r9
	movq	416(%rsp), %rdx
	xorq	%rsi, %rdx
	rolq	$2, %rdx
	movq	%rdi, %rsi
	notq	%rsi
	andq	%r8, %rsi
	xorq	%r10, %rsi
	movq	%rsi, 208(%rsp)
	movq	%r8, %rsi
	notq	%rsi
	andq	%r9, %rsi
	xorq	%rdi, %rsi
	movq	%rsi, 216(%rsp)
	movq	%r9, %rsi
	notq	%rsi
	andq	%rdx, %rsi
	xorq	%r8, %rsi
	movq	%rsi, 224(%rsp)
	movq	%rdx, %rsi
	notq	%rsi
	andq	%r10, %rsi
	xorq	%r9, %rsi
	movq	%rsi, 232(%rsp)
	notq	%r10
	andq	%rdi, %r10
	xorq	%rdx, %r10
	movq	%r10, 240(%rsp)
	addq	$2, %rcx
	cmpq	$23, %rcx
	jb  	L_keccak1600_ref$18
	movq	24(%rsp), %rsi
	movq	32(%rsp), %rdx
	movq	40(%rsp), %rax
L_keccak1600_ref$16:
	cmpq	%rax, %rdx
	jnb 	L_keccak1600_ref$17
	movb	448(%rsp), %cl
	movq	%rdx, %rdi
	shrq	$3, %rdi
	movq	$0, %r8
	jmp 	L_keccak1600_ref$14
L_keccak1600_ref$15:
	movq	(%rsi,%r8,8), %r9
	xorq	%r9, 48(%rsp,%r8,8)
	incq	%r8
L_keccak1600_ref$14:
	cmpq	%rdi, %r8
	jb  	L_keccak1600_ref$15
	shlq	$3, %r8
	jmp 	L_keccak1600_ref$12
L_keccak1600_ref$13:
	movb	(%rsi,%r8), %dil
	xorb	%dil, 48(%rsp,%r8)
	incq	%r8
L_keccak1600_ref$12:
	cmpq	%rdx, %r8
	jb  	L_keccak1600_ref$13
	xorb	%cl, 48(%rsp,%r8)
	movq	%rax, %rcx
	addq	$-1, %rcx
	xorb	$-128, 48(%rsp,%rcx)
	movq	16(%rsp), %rdx
	jmp 	L_keccak1600_ref$7
L_keccak1600_ref$8:
	movq	%rdx, 16(%rsp)
	movq	%rax, 40(%rsp)
	leaq	glob_data + 0(%rip), %rax
	movq	$0, %rcx
L_keccak1600_ref$11:
	movq	(%rax,%rcx,8), %r10
	movq	48(%rsp), %r9
	movq	56(%rsp), %r8
	movq	64(%rsp), %r11
	movq	72(%rsp), %rbx
	movq	80(%rsp), %rbp
	xorq	88(%rsp), %r9
	xorq	96(%rsp), %r8
	xorq	104(%rsp), %r11
	xorq	112(%rsp), %rbx
	xorq	120(%rsp), %rbp
	xorq	128(%rsp), %r9
	xorq	136(%rsp), %r8
	xorq	144(%rsp), %r11
	xorq	152(%rsp), %rbx
	xorq	160(%rsp), %rbp
	xorq	168(%rsp), %r9
	xorq	176(%rsp), %r8
	xorq	184(%rsp), %r11
	xorq	192(%rsp), %rbx
	xorq	200(%rsp), %rbp
	xorq	208(%rsp), %r9
	xorq	216(%rsp), %r8
	xorq	224(%rsp), %r11
	xorq	232(%rsp), %rbx
	xorq	240(%rsp), %rbp
	movq	%r8, %rdx
	rolq	$1, %rdx
	xorq	%rbp, %rdx
	movq	%r11, %rsi
	rolq	$1, %rsi
	xorq	%r9, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r8, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r11, %r8
	rolq	$1, %r9
	xorq	%rbx, %r9
	movq	48(%rsp), %r11
	xorq	%rdx, %r11
	movq	96(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$44, %rbx
	movq	144(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$43, %rbp
	movq	192(%rsp), %r12
	xorq	%r8, %r12
	rolq	$21, %r12
	movq	240(%rsp), %r13
	xorq	%r9, %r13
	rolq	$14, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	xorq	%r10, %r14
	movq	%r14, 248(%rsp)
	movq	%rbp, %r10
	notq	%r10
	andq	%r12, %r10
	xorq	%rbx, %r10
	movq	%r10, 256(%rsp)
	movq	%r12, %r10
	notq	%r10
	andq	%r13, %r10
	xorq	%rbp, %r10
	movq	%r10, 264(%rsp)
	movq	%r13, %r10
	notq	%r10
	andq	%r11, %r10
	xorq	%r12, %r10
	movq	%r10, 272(%rsp)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 280(%rsp)
	movq	72(%rsp), %r10
	xorq	%r8, %r10
	rolq	$28, %r10
	movq	120(%rsp), %r11
	xorq	%r9, %r11
	rolq	$20, %r11
	movq	128(%rsp), %r12
	xorq	%rdx, %r12
	rolq	$3, %r12
	movq	176(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$45, %rbx
	movq	224(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$61, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 288(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 296(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 304(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 312(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 320(%rsp)
	movq	56(%rsp), %r10
	xorq	%rsi, %r10
	rolq	$1, %r10
	movq	104(%rsp), %r11
	xorq	%rdi, %r11
	rolq	$6, %r11
	movq	152(%rsp), %r12
	xorq	%r8, %r12
	rolq	$25, %r12
	movq	200(%rsp), %rbx
	xorq	%r9, %rbx
	rolq	$8, %rbx
	movq	208(%rsp), %rbp
	xorq	%rdx, %rbp
	rolq	$18, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 328(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 336(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 344(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 352(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 360(%rsp)
	movq	80(%rsp), %r10
	xorq	%r9, %r10
	rolq	$27, %r10
	movq	88(%rsp), %r11
	xorq	%rdx, %r11
	rolq	$36, %r11
	movq	136(%rsp), %r12
	xorq	%rsi, %r12
	rolq	$10, %r12
	movq	184(%rsp), %rbx
	xorq	%rdi, %rbx
	rolq	$15, %rbx
	movq	232(%rsp), %rbp
	xorq	%r8, %rbp
	rolq	$56, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 368(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 376(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 384(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 392(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 400(%rsp)
	movq	64(%rsp), %r10
	xorq	%rdi, %r10
	rolq	$62, %r10
	movq	112(%rsp), %rdi
	xorq	%r8, %rdi
	rolq	$55, %rdi
	movq	160(%rsp), %r8
	xorq	%r9, %r8
	rolq	$39, %r8
	movq	168(%rsp), %r9
	xorq	%rdx, %r9
	rolq	$41, %r9
	movq	216(%rsp), %rdx
	xorq	%rsi, %rdx
	rolq	$2, %rdx
	movq	%rdi, %rsi
	notq	%rsi
	andq	%r8, %rsi
	xorq	%r10, %rsi
	movq	%rsi, 408(%rsp)
	movq	%r8, %rsi
	notq	%rsi
	andq	%r9, %rsi
	xorq	%rdi, %rsi
	movq	%rsi, 416(%rsp)
	movq	%r9, %rsi
	notq	%rsi
	andq	%rdx, %rsi
	xorq	%r8, %rsi
	movq	%rsi, 424(%rsp)
	movq	%rdx, %rsi
	notq	%rsi
	andq	%r10, %rsi
	xorq	%r9, %rsi
	movq	%rsi, 432(%rsp)
	notq	%r10
	andq	%rdi, %r10
	xorq	%rdx, %r10
	movq	%r10, 440(%rsp)
	movq	8(%rax,%rcx,8), %r10
	movq	248(%rsp), %r9
	movq	256(%rsp), %r8
	movq	264(%rsp), %r11
	movq	272(%rsp), %rbx
	movq	280(%rsp), %rbp
	xorq	288(%rsp), %r9
	xorq	296(%rsp), %r8
	xorq	304(%rsp), %r11
	xorq	312(%rsp), %rbx
	xorq	320(%rsp), %rbp
	xorq	328(%rsp), %r9
	xorq	336(%rsp), %r8
	xorq	344(%rsp), %r11
	xorq	352(%rsp), %rbx
	xorq	360(%rsp), %rbp
	xorq	368(%rsp), %r9
	xorq	376(%rsp), %r8
	xorq	384(%rsp), %r11
	xorq	392(%rsp), %rbx
	xorq	400(%rsp), %rbp
	xorq	408(%rsp), %r9
	xorq	416(%rsp), %r8
	xorq	424(%rsp), %r11
	xorq	432(%rsp), %rbx
	xorq	440(%rsp), %rbp
	movq	%r8, %rdx
	rolq	$1, %rdx
	xorq	%rbp, %rdx
	movq	%r11, %rsi
	rolq	$1, %rsi
	xorq	%r9, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r8, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r11, %r8
	rolq	$1, %r9
	xorq	%rbx, %r9
	movq	248(%rsp), %r11
	xorq	%rdx, %r11
	movq	296(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$44, %rbx
	movq	344(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$43, %rbp
	movq	392(%rsp), %r12
	xorq	%r8, %r12
	rolq	$21, %r12
	movq	440(%rsp), %r13
	xorq	%r9, %r13
	rolq	$14, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	xorq	%r10, %r14
	movq	%r14, 48(%rsp)
	movq	%rbp, %r10
	notq	%r10
	andq	%r12, %r10
	xorq	%rbx, %r10
	movq	%r10, 56(%rsp)
	movq	%r12, %r10
	notq	%r10
	andq	%r13, %r10
	xorq	%rbp, %r10
	movq	%r10, 64(%rsp)
	movq	%r13, %r10
	notq	%r10
	andq	%r11, %r10
	xorq	%r12, %r10
	movq	%r10, 72(%rsp)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 80(%rsp)
	movq	272(%rsp), %r10
	xorq	%r8, %r10
	rolq	$28, %r10
	movq	320(%rsp), %r11
	xorq	%r9, %r11
	rolq	$20, %r11
	movq	328(%rsp), %r12
	xorq	%rdx, %r12
	rolq	$3, %r12
	movq	376(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$45, %rbx
	movq	424(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$61, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 88(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 96(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 104(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 112(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 120(%rsp)
	movq	256(%rsp), %r10
	xorq	%rsi, %r10
	rolq	$1, %r10
	movq	304(%rsp), %r11
	xorq	%rdi, %r11
	rolq	$6, %r11
	movq	352(%rsp), %r12
	xorq	%r8, %r12
	rolq	$25, %r12
	movq	400(%rsp), %rbx
	xorq	%r9, %rbx
	rolq	$8, %rbx
	movq	408(%rsp), %rbp
	xorq	%rdx, %rbp
	rolq	$18, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 128(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 136(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 144(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 152(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 160(%rsp)
	movq	280(%rsp), %r10
	xorq	%r9, %r10
	rolq	$27, %r10
	movq	288(%rsp), %r11
	xorq	%rdx, %r11
	rolq	$36, %r11
	movq	336(%rsp), %r12
	xorq	%rsi, %r12
	rolq	$10, %r12
	movq	384(%rsp), %rbx
	xorq	%rdi, %rbx
	rolq	$15, %rbx
	movq	432(%rsp), %rbp
	xorq	%r8, %rbp
	rolq	$56, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 168(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 176(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 184(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 192(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 200(%rsp)
	movq	264(%rsp), %r10
	xorq	%rdi, %r10
	rolq	$62, %r10
	movq	312(%rsp), %rdi
	xorq	%r8, %rdi
	rolq	$55, %rdi
	movq	360(%rsp), %r8
	xorq	%r9, %r8
	rolq	$39, %r8
	movq	368(%rsp), %r9
	xorq	%rdx, %r9
	rolq	$41, %r9
	movq	416(%rsp), %rdx
	xorq	%rsi, %rdx
	rolq	$2, %rdx
	movq	%rdi, %rsi
	notq	%rsi
	andq	%r8, %rsi
	xorq	%r10, %rsi
	movq	%rsi, 208(%rsp)
	movq	%r8, %rsi
	notq	%rsi
	andq	%r9, %rsi
	xorq	%rdi, %rsi
	movq	%rsi, 216(%rsp)
	movq	%r9, %rsi
	notq	%rsi
	andq	%rdx, %rsi
	xorq	%r8, %rsi
	movq	%rsi, 224(%rsp)
	movq	%rdx, %rsi
	notq	%rsi
	andq	%r10, %rsi
	xorq	%r9, %rsi
	movq	%rsi, 232(%rsp)
	notq	%r10
	andq	%rdi, %r10
	xorq	%rdx, %r10
	movq	%r10, 240(%rsp)
	addq	$2, %rcx
	cmpq	$23, %rcx
	jb  	L_keccak1600_ref$11
	movq	8(%rsp), %rcx
	movq	16(%rsp), %rdx
	movq	40(%rsp), %rax
	movq	%rax, %rsi
	shrq	$3, %rsi
	movq	$0, %rdi
	jmp 	L_keccak1600_ref$9
L_keccak1600_ref$10:
	movq	48(%rsp,%rdi,8), %r8
	movq	%r8, (%rcx,%rdi,8)
	incq	%rdi
L_keccak1600_ref$9:
	cmpq	%rsi, %rdi
	jb  	L_keccak1600_ref$10
	addq	%rax, %rcx
	subq	%rax, %rdx
	movq	%rcx, 8(%rsp)
L_keccak1600_ref$7:
	cmpq	%rax, %rdx
	jnbe	L_keccak1600_ref$8
	movq	%rdx, 40(%rsp)
	leaq	glob_data + 0(%rip), %rax
	movq	$0, %rcx
L_keccak1600_ref$6:
	movq	(%rax,%rcx,8), %r10
	movq	48(%rsp), %r9
	movq	56(%rsp), %r8
	movq	64(%rsp), %r11
	movq	72(%rsp), %rbx
	movq	80(%rsp), %rbp
	xorq	88(%rsp), %r9
	xorq	96(%rsp), %r8
	xorq	104(%rsp), %r11
	xorq	112(%rsp), %rbx
	xorq	120(%rsp), %rbp
	xorq	128(%rsp), %r9
	xorq	136(%rsp), %r8
	xorq	144(%rsp), %r11
	xorq	152(%rsp), %rbx
	xorq	160(%rsp), %rbp
	xorq	168(%rsp), %r9
	xorq	176(%rsp), %r8
	xorq	184(%rsp), %r11
	xorq	192(%rsp), %rbx
	xorq	200(%rsp), %rbp
	xorq	208(%rsp), %r9
	xorq	216(%rsp), %r8
	xorq	224(%rsp), %r11
	xorq	232(%rsp), %rbx
	xorq	240(%rsp), %rbp
	movq	%r8, %rdx
	rolq	$1, %rdx
	xorq	%rbp, %rdx
	movq	%r11, %rsi
	rolq	$1, %rsi
	xorq	%r9, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r8, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r11, %r8
	rolq	$1, %r9
	xorq	%rbx, %r9
	movq	48(%rsp), %r11
	xorq	%rdx, %r11
	movq	96(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$44, %rbx
	movq	144(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$43, %rbp
	movq	192(%rsp), %r12
	xorq	%r8, %r12
	rolq	$21, %r12
	movq	240(%rsp), %r13
	xorq	%r9, %r13
	rolq	$14, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	xorq	%r10, %r14
	movq	%r14, 248(%rsp)
	movq	%rbp, %r10
	notq	%r10
	andq	%r12, %r10
	xorq	%rbx, %r10
	movq	%r10, 256(%rsp)
	movq	%r12, %r10
	notq	%r10
	andq	%r13, %r10
	xorq	%rbp, %r10
	movq	%r10, 264(%rsp)
	movq	%r13, %r10
	notq	%r10
	andq	%r11, %r10
	xorq	%r12, %r10
	movq	%r10, 272(%rsp)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 280(%rsp)
	movq	72(%rsp), %r10
	xorq	%r8, %r10
	rolq	$28, %r10
	movq	120(%rsp), %r11
	xorq	%r9, %r11
	rolq	$20, %r11
	movq	128(%rsp), %r12
	xorq	%rdx, %r12
	rolq	$3, %r12
	movq	176(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$45, %rbx
	movq	224(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$61, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 288(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 296(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 304(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 312(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 320(%rsp)
	movq	56(%rsp), %r10
	xorq	%rsi, %r10
	rolq	$1, %r10
	movq	104(%rsp), %r11
	xorq	%rdi, %r11
	rolq	$6, %r11
	movq	152(%rsp), %r12
	xorq	%r8, %r12
	rolq	$25, %r12
	movq	200(%rsp), %rbx
	xorq	%r9, %rbx
	rolq	$8, %rbx
	movq	208(%rsp), %rbp
	xorq	%rdx, %rbp
	rolq	$18, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 328(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 336(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 344(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 352(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 360(%rsp)
	movq	80(%rsp), %r10
	xorq	%r9, %r10
	rolq	$27, %r10
	movq	88(%rsp), %r11
	xorq	%rdx, %r11
	rolq	$36, %r11
	movq	136(%rsp), %r12
	xorq	%rsi, %r12
	rolq	$10, %r12
	movq	184(%rsp), %rbx
	xorq	%rdi, %rbx
	rolq	$15, %rbx
	movq	232(%rsp), %rbp
	xorq	%r8, %rbp
	rolq	$56, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 368(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 376(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 384(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 392(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 400(%rsp)
	movq	64(%rsp), %r10
	xorq	%rdi, %r10
	rolq	$62, %r10
	movq	112(%rsp), %rdi
	xorq	%r8, %rdi
	rolq	$55, %rdi
	movq	160(%rsp), %r8
	xorq	%r9, %r8
	rolq	$39, %r8
	movq	168(%rsp), %r9
	xorq	%rdx, %r9
	rolq	$41, %r9
	movq	216(%rsp), %rdx
	xorq	%rsi, %rdx
	rolq	$2, %rdx
	movq	%rdi, %rsi
	notq	%rsi
	andq	%r8, %rsi
	xorq	%r10, %rsi
	movq	%rsi, 408(%rsp)
	movq	%r8, %rsi
	notq	%rsi
	andq	%r9, %rsi
	xorq	%rdi, %rsi
	movq	%rsi, 416(%rsp)
	movq	%r9, %rsi
	notq	%rsi
	andq	%rdx, %rsi
	xorq	%r8, %rsi
	movq	%rsi, 424(%rsp)
	movq	%rdx, %rsi
	notq	%rsi
	andq	%r10, %rsi
	xorq	%r9, %rsi
	movq	%rsi, 432(%rsp)
	notq	%r10
	andq	%rdi, %r10
	xorq	%rdx, %r10
	movq	%r10, 440(%rsp)
	movq	8(%rax,%rcx,8), %r10
	movq	248(%rsp), %r9
	movq	256(%rsp), %r8
	movq	264(%rsp), %r11
	movq	272(%rsp), %rbx
	movq	280(%rsp), %rbp
	xorq	288(%rsp), %r9
	xorq	296(%rsp), %r8
	xorq	304(%rsp), %r11
	xorq	312(%rsp), %rbx
	xorq	320(%rsp), %rbp
	xorq	328(%rsp), %r9
	xorq	336(%rsp), %r8
	xorq	344(%rsp), %r11
	xorq	352(%rsp), %rbx
	xorq	360(%rsp), %rbp
	xorq	368(%rsp), %r9
	xorq	376(%rsp), %r8
	xorq	384(%rsp), %r11
	xorq	392(%rsp), %rbx
	xorq	400(%rsp), %rbp
	xorq	408(%rsp), %r9
	xorq	416(%rsp), %r8
	xorq	424(%rsp), %r11
	xorq	432(%rsp), %rbx
	xorq	440(%rsp), %rbp
	movq	%r8, %rdx
	rolq	$1, %rdx
	xorq	%rbp, %rdx
	movq	%r11, %rsi
	rolq	$1, %rsi
	xorq	%r9, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r8, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r11, %r8
	rolq	$1, %r9
	xorq	%rbx, %r9
	movq	248(%rsp), %r11
	xorq	%rdx, %r11
	movq	296(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$44, %rbx
	movq	344(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$43, %rbp
	movq	392(%rsp), %r12
	xorq	%r8, %r12
	rolq	$21, %r12
	movq	440(%rsp), %r13
	xorq	%r9, %r13
	rolq	$14, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	xorq	%r10, %r14
	movq	%r14, 48(%rsp)
	movq	%rbp, %r10
	notq	%r10
	andq	%r12, %r10
	xorq	%rbx, %r10
	movq	%r10, 56(%rsp)
	movq	%r12, %r10
	notq	%r10
	andq	%r13, %r10
	xorq	%rbp, %r10
	movq	%r10, 64(%rsp)
	movq	%r13, %r10
	notq	%r10
	andq	%r11, %r10
	xorq	%r12, %r10
	movq	%r10, 72(%rsp)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 80(%rsp)
	movq	272(%rsp), %r10
	xorq	%r8, %r10
	rolq	$28, %r10
	movq	320(%rsp), %r11
	xorq	%r9, %r11
	rolq	$20, %r11
	movq	328(%rsp), %r12
	xorq	%rdx, %r12
	rolq	$3, %r12
	movq	376(%rsp), %rbx
	xorq	%rsi, %rbx
	rolq	$45, %rbx
	movq	424(%rsp), %rbp
	xorq	%rdi, %rbp
	rolq	$61, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 88(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 96(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 104(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 112(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 120(%rsp)
	movq	256(%rsp), %r10
	xorq	%rsi, %r10
	rolq	$1, %r10
	movq	304(%rsp), %r11
	xorq	%rdi, %r11
	rolq	$6, %r11
	movq	352(%rsp), %r12
	xorq	%r8, %r12
	rolq	$25, %r12
	movq	400(%rsp), %rbx
	xorq	%r9, %rbx
	rolq	$8, %rbx
	movq	408(%rsp), %rbp
	xorq	%rdx, %rbp
	rolq	$18, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 128(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 136(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 144(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 152(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 160(%rsp)
	movq	280(%rsp), %r10
	xorq	%r9, %r10
	rolq	$27, %r10
	movq	288(%rsp), %r11
	xorq	%rdx, %r11
	rolq	$36, %r11
	movq	336(%rsp), %r12
	xorq	%rsi, %r12
	rolq	$10, %r12
	movq	384(%rsp), %rbx
	xorq	%rdi, %rbx
	rolq	$15, %rbx
	movq	432(%rsp), %rbp
	xorq	%r8, %rbp
	rolq	$56, %rbp
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	xorq	%r10, %r13
	movq	%r13, 168(%rsp)
	movq	%r12, %r13
	notq	%r13
	andq	%rbx, %r13
	xorq	%r11, %r13
	movq	%r13, 176(%rsp)
	movq	%rbx, %r13
	notq	%r13
	andq	%rbp, %r13
	xorq	%r12, %r13
	movq	%r13, 184(%rsp)
	movq	%rbp, %r12
	notq	%r12
	andq	%r10, %r12
	xorq	%rbx, %r12
	movq	%r12, 192(%rsp)
	notq	%r10
	andq	%r11, %r10
	xorq	%rbp, %r10
	movq	%r10, 200(%rsp)
	movq	264(%rsp), %r10
	xorq	%rdi, %r10
	rolq	$62, %r10
	movq	312(%rsp), %rdi
	xorq	%r8, %rdi
	rolq	$55, %rdi
	movq	360(%rsp), %r8
	xorq	%r9, %r8
	rolq	$39, %r8
	movq	368(%rsp), %r9
	xorq	%rdx, %r9
	rolq	$41, %r9
	movq	416(%rsp), %rdx
	xorq	%rsi, %rdx
	rolq	$2, %rdx
	movq	%rdi, %rsi
	notq	%rsi
	andq	%r8, %rsi
	xorq	%r10, %rsi
	movq	%rsi, 208(%rsp)
	movq	%r8, %rsi
	notq	%rsi
	andq	%r9, %rsi
	xorq	%rdi, %rsi
	movq	%rsi, 216(%rsp)
	movq	%r9, %rsi
	notq	%rsi
	andq	%rdx, %rsi
	xorq	%r8, %rsi
	movq	%rsi, 224(%rsp)
	movq	%rdx, %rsi
	notq	%rsi
	andq	%r10, %rsi
	xorq	%r9, %rsi
	movq	%rsi, 232(%rsp)
	notq	%r10
	andq	%rdi, %r10
	xorq	%rdx, %r10
	movq	%r10, 240(%rsp)
	addq	$2, %rcx
	cmpq	$23, %rcx
	jb  	L_keccak1600_ref$6
	movq	8(%rsp), %rax
	movq	40(%rsp), %rcx
	movq	%rcx, %rdx
	shrq	$3, %rdx
	movq	$0, %rsi
	jmp 	L_keccak1600_ref$4
L_keccak1600_ref$5:
	movq	48(%rsp,%rsi,8), %rdi
	movq	%rdi, (%rax,%rsi,8)
	incq	%rsi
L_keccak1600_ref$4:
	cmpq	%rdx, %rsi
	jb  	L_keccak1600_ref$5
	shlq	$3, %rsi
	jmp 	L_keccak1600_ref$2
L_keccak1600_ref$3:
	movb	48(%rsp,%rsi), %dl
	movb	%dl, (%rax,%rsi)
	incq	%rsi
L_keccak1600_ref$2:
	cmpq	%rcx, %rsi
	jb  	L_keccak1600_ref$3
	ret 
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
