	.att_syntax
	.text
	.p2align	5
	.globl	_jade_hash_sha256_amd64_ref
	.globl	jade_hash_sha256_amd64_ref
_jade_hash_sha256_amd64_ref:
jade_hash_sha256_amd64_ref:
	movq	%rsp, %rax
	leaq	-232(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rax, 224(%rsp)
	movq	%rbx, 176(%rsp)
	movq	%rbp, 184(%rsp)
	movq	%r12, 192(%rsp)
	movq	%r13, 200(%rsp)
	movq	%r14, 208(%rsp)
	movq	%r15, 216(%rsp)
	movq	%rdi, (%rsp)
	movq	%rdx, %rax
	shlq	$3, %rax
	movq	%rax, 8(%rsp)
	movl	$1779033703, 16(%rsp)
	movl	$-1150833019, 20(%rsp)
	movl	$1013904242, 24(%rsp)
	movl	$-1521486534, 28(%rsp)
	movl	$1359893119, 32(%rsp)
	movl	$-1694144372, 36(%rsp)
	movl	$528734635, 40(%rsp)
	movl	$1541459225, 44(%rsp)
	leaq	16(%rsp), %rdi
	leaq	-272(%rsp), %rsp
	leaq	Ljade_hash_sha256_amd64_ref$12(%rip), %rcx
	jmp 	L_blocks_0_ref$1
Ljade_hash_sha256_amd64_ref$12:
	leaq	272(%rsp), %rsp
	movq	8(%rsp), %rcx
	movq	$0, %rdi
	jmp 	Ljade_hash_sha256_amd64_ref$10
Ljade_hash_sha256_amd64_ref$11:
	movb	(%rsi,%rdi), %al
	movb	%al, 48(%rsp,%rdi)
	incq	%rdi
Ljade_hash_sha256_amd64_ref$10:
	cmpq	%rdx, %rdi
	jb  	Ljade_hash_sha256_amd64_ref$11
	movb	$-128, 48(%rsp,%rdi)
	incq	%rdi
	cmpq	$56, %rdx
	jb  	Ljade_hash_sha256_amd64_ref$8
	movq	$120, %rdx
	movq	$2, %rax
	jmp 	Ljade_hash_sha256_amd64_ref$9
Ljade_hash_sha256_amd64_ref$8:
	movq	$56, %rdx
	movq	$1, %rax
Ljade_hash_sha256_amd64_ref$9:
	movb	$0, %sil
	jmp 	Ljade_hash_sha256_amd64_ref$6
Ljade_hash_sha256_amd64_ref$7:
	movb	%sil, 48(%rsp,%rdi)
	incq	%rdi
Ljade_hash_sha256_amd64_ref$6:
	cmpq	%rdx, %rdi
	jb  	Ljade_hash_sha256_amd64_ref$7
	addq	$7, %rdi
	jmp 	Ljade_hash_sha256_amd64_ref$4
Ljade_hash_sha256_amd64_ref$5:
	movb	%cl, 48(%rsp,%rdi)
	shrq	$8, %rcx
	addq	$-1, %rdi
Ljade_hash_sha256_amd64_ref$4:
	cmpq	%rdx, %rdi
	jnb 	Ljade_hash_sha256_amd64_ref$5
	addq	$9, %rdi
	jmp 	Ljade_hash_sha256_amd64_ref$2
Ljade_hash_sha256_amd64_ref$3:
	movb	%sil, 48(%rsp,%rdi)
	incq	%rdi
Ljade_hash_sha256_amd64_ref$2:
	cmpq	$128, %rdi
	jb  	Ljade_hash_sha256_amd64_ref$3
	leaq	48(%rsp), %r8
	leaq	-280(%rsp), %rsp
	leaq	Ljade_hash_sha256_amd64_ref$1(%rip), %rdx
	jmp 	L_blocks_1_ref$1
Ljade_hash_sha256_amd64_ref$1:
	leaq	280(%rsp), %rsp
	movq	(%rsp), %rax
	movl	16(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, (%rax)
	movl	20(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 4(%rax)
	movl	24(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 8(%rax)
	movl	28(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 12(%rax)
	movl	32(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 16(%rax)
	movl	36(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 20(%rax)
	movl	40(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 24(%rax)
	movl	44(%rsp), %ecx
	bswapl	%ecx
	movl	%ecx, 28(%rax)
	xorq	%rax, %rax
	movq	176(%rsp), %rbx
	movq	184(%rsp), %rbp
	movq	192(%rsp), %r12
	movq	200(%rsp), %r13
	movq	208(%rsp), %r14
	movq	216(%rsp), %r15
	movq	224(%rsp), %rsp
	ret 
L_blocks_1_ref$1:
	leaq	glob_data + 0(%rip), %rcx
	movq	%r9, (%rsp)
	movq	$0, %rsi
	movq	(%rsp), %rdi
	jmp 	L_blocks_1_ref$2
L_blocks_1_ref$3:
	movl	(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 24(%rsp)
	movl	4(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 28(%rsp)
	movl	8(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 32(%rsp)
	movl	12(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 36(%rsp)
	movl	16(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 40(%rsp)
	movl	20(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 44(%rsp)
	movl	24(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 48(%rsp)
	movl	28(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 52(%rsp)
	movl	32(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 56(%rsp)
	movl	36(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 60(%rsp)
	movl	40(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 64(%rsp)
	movl	44(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 68(%rsp)
	movl	48(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 72(%rsp)
	movl	52(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 76(%rsp)
	movl	56(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 80(%rsp)
	movl	60(%r8,%rsi,4), %r9d
	bswapl	%r9d
	movl	%r9d, 84(%rsp)
	addq	$16, %rsi
	movq	%rsi, (%rsp)
	movq	%r8, 8(%rsp)
	movl	80(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	60(%rsp), %r8d
	movl	28(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	24(%rsp), %r8d
	movl	%r8d, 88(%rsp)
	movl	84(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	64(%rsp), %r8d
	movl	32(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	28(%rsp), %r8d
	movl	%r8d, 92(%rsp)
	movl	88(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	68(%rsp), %r8d
	movl	36(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	32(%rsp), %r8d
	movl	%r8d, 96(%rsp)
	movl	92(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	72(%rsp), %r8d
	movl	40(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	36(%rsp), %r8d
	movl	%r8d, 100(%rsp)
	movl	96(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	76(%rsp), %r8d
	movl	44(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	40(%rsp), %r8d
	movl	%r8d, 104(%rsp)
	movl	100(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	80(%rsp), %r8d
	movl	48(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	44(%rsp), %r8d
	movl	%r8d, 108(%rsp)
	movl	104(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	84(%rsp), %r8d
	movl	52(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	48(%rsp), %r8d
	movl	%r8d, 112(%rsp)
	movl	108(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	88(%rsp), %r8d
	movl	56(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	52(%rsp), %r8d
	movl	%r8d, 116(%rsp)
	movl	112(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	92(%rsp), %r8d
	movl	60(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	56(%rsp), %r8d
	movl	%r8d, 120(%rsp)
	movl	116(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	96(%rsp), %r8d
	movl	64(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	60(%rsp), %r8d
	movl	%r8d, 124(%rsp)
	movl	120(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	100(%rsp), %r8d
	movl	68(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	64(%rsp), %r8d
	movl	%r8d, 128(%rsp)
	movl	124(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	104(%rsp), %r8d
	movl	72(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	68(%rsp), %r8d
	movl	%r8d, 132(%rsp)
	movl	128(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	108(%rsp), %r8d
	movl	76(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	72(%rsp), %r8d
	movl	%r8d, 136(%rsp)
	movl	132(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	112(%rsp), %r8d
	movl	80(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	76(%rsp), %r8d
	movl	%r8d, 140(%rsp)
	movl	136(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	116(%rsp), %r8d
	movl	84(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	80(%rsp), %r8d
	movl	%r8d, 144(%rsp)
	movl	140(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	120(%rsp), %r8d
	movl	88(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	84(%rsp), %r8d
	movl	%r8d, 148(%rsp)
	movl	144(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	124(%rsp), %r8d
	movl	92(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	88(%rsp), %r8d
	movl	%r8d, 152(%rsp)
	movl	148(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	128(%rsp), %r8d
	movl	96(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	92(%rsp), %r8d
	movl	%r8d, 156(%rsp)
	movl	152(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	132(%rsp), %r8d
	movl	100(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	96(%rsp), %r8d
	movl	%r8d, 160(%rsp)
	movl	156(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	136(%rsp), %r8d
	movl	104(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	100(%rsp), %r8d
	movl	%r8d, 164(%rsp)
	movl	160(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	140(%rsp), %r8d
	movl	108(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	104(%rsp), %r8d
	movl	%r8d, 168(%rsp)
	movl	164(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	144(%rsp), %r8d
	movl	112(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	108(%rsp), %r8d
	movl	%r8d, 172(%rsp)
	movl	168(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	148(%rsp), %r8d
	movl	116(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	112(%rsp), %r8d
	movl	%r8d, 176(%rsp)
	movl	172(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	152(%rsp), %r8d
	movl	120(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	116(%rsp), %r8d
	movl	%r8d, 180(%rsp)
	movl	176(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	156(%rsp), %r8d
	movl	124(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	120(%rsp), %r8d
	movl	%r8d, 184(%rsp)
	movl	180(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	160(%rsp), %r8d
	movl	128(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	124(%rsp), %r8d
	movl	%r8d, 188(%rsp)
	movl	184(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	164(%rsp), %r8d
	movl	132(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	128(%rsp), %r8d
	movl	%r8d, 192(%rsp)
	movl	188(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	168(%rsp), %r8d
	movl	136(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	132(%rsp), %r8d
	movl	%r8d, 196(%rsp)
	movl	192(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	172(%rsp), %r8d
	movl	140(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	136(%rsp), %r8d
	movl	%r8d, 200(%rsp)
	movl	196(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	176(%rsp), %r8d
	movl	144(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	140(%rsp), %r8d
	movl	%r8d, 204(%rsp)
	movl	200(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	180(%rsp), %r8d
	movl	148(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	144(%rsp), %r8d
	movl	%r8d, 208(%rsp)
	movl	204(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	184(%rsp), %r8d
	movl	152(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	148(%rsp), %r8d
	movl	%r8d, 212(%rsp)
	movl	208(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	188(%rsp), %r8d
	movl	156(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	152(%rsp), %r8d
	movl	%r8d, 216(%rsp)
	movl	212(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	192(%rsp), %r8d
	movl	160(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	156(%rsp), %r8d
	movl	%r8d, 220(%rsp)
	movl	216(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	196(%rsp), %r8d
	movl	164(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	160(%rsp), %r8d
	movl	%r8d, 224(%rsp)
	movl	220(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	200(%rsp), %r8d
	movl	168(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	164(%rsp), %r8d
	movl	%r8d, 228(%rsp)
	movl	224(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	204(%rsp), %r8d
	movl	172(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	168(%rsp), %r8d
	movl	%r8d, 232(%rsp)
	movl	228(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	208(%rsp), %r8d
	movl	176(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	172(%rsp), %r8d
	movl	%r8d, 236(%rsp)
	movl	232(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	212(%rsp), %r8d
	movl	180(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	176(%rsp), %r8d
	movl	%r8d, 240(%rsp)
	movl	236(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	216(%rsp), %r8d
	movl	184(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	180(%rsp), %r8d
	movl	%r8d, 244(%rsp)
	movl	240(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	220(%rsp), %r8d
	movl	188(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	184(%rsp), %r8d
	movl	%r8d, 248(%rsp)
	movl	244(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	224(%rsp), %r8d
	movl	192(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	188(%rsp), %r8d
	movl	%r8d, 252(%rsp)
	movl	248(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	228(%rsp), %r8d
	movl	196(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	192(%rsp), %r8d
	movl	%r8d, 256(%rsp)
	movl	252(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	232(%rsp), %r8d
	movl	200(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	196(%rsp), %r8d
	movl	%r8d, 260(%rsp)
	movl	256(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	236(%rsp), %r8d
	movl	204(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	200(%rsp), %r8d
	movl	%r8d, 264(%rsp)
	movl	260(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	240(%rsp), %r8d
	movl	208(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	204(%rsp), %r8d
	movl	%r8d, 268(%rsp)
	movl	264(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	244(%rsp), %r8d
	movl	212(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	208(%rsp), %r8d
	movl	%r8d, 272(%rsp)
	movl	268(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	248(%rsp), %r8d
	movl	216(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	212(%rsp), %r8d
	movl	%r8d, 276(%rsp)
	movl	(%rdi), %r14d
	movl	4(%rdi), %esi
	movl	8(%rdi), %r8d
	movl	12(%rdi), %r9d
	movl	16(%rdi), %r13d
	movl	20(%rdi), %r10d
	movl	24(%rdi), %r11d
	movl	28(%rdi), %r12d
	movq	%rdi, 16(%rsp)
	movq	$0, %rdi
	jmp 	L_blocks_1_ref$4
L_blocks_1_ref$5:
	movl	%r12d, %ebx
	movl	%r13d, %ebp
	rorl	$6, %ebp
	movl	%r13d, %r12d
	rorl	$11, %r12d
	xorl	%r12d, %ebp
	movl	%r13d, %r12d
	rorl	$25, %r12d
	xorl	%r12d, %ebp
	addl	%ebp, %ebx
	movl	%r13d, %ebp
	andl	%r10d, %ebp
	movl	%r13d, %r12d
	notl	%r12d
	andl	%r11d, %r12d
	xorl	%r12d, %ebp
	addl	%ebp, %ebx
	addl	(%rcx,%rdi,4), %ebx
	addl	24(%rsp,%rdi,4), %ebx
	movl	%r14d, %ebp
	rorl	$2, %ebp
	movl	%r14d, %r12d
	rorl	$13, %r12d
	xorl	%r12d, %ebp
	movl	%r14d, %r12d
	rorl	$22, %r12d
	xorl	%r12d, %ebp
	movl	%r14d, %r12d
	andl	%esi, %r12d
	movl	%r14d, %r15d
	andl	%r8d, %r15d
	xorl	%r15d, %r12d
	movl	%esi, %r15d
	andl	%r8d, %r15d
	xorl	%r15d, %r12d
	addl	%r12d, %ebp
	movl	%r11d, %r12d
	movl	%r10d, %r11d
	movl	%r13d, %r10d
	movl	%r9d, %r13d
	addl	%ebx, %r13d
	movl	%r8d, %r9d
	movl	%esi, %r8d
	movl	%r14d, %esi
	movl	%ebx, %r14d
	addl	%ebp, %r14d
	incq	%rdi
L_blocks_1_ref$4:
	cmpq	$64, %rdi
	jb  	L_blocks_1_ref$5
	movq	16(%rsp), %rdi
	addl	(%rdi), %r14d
	addl	4(%rdi), %esi
	addl	8(%rdi), %r8d
	addl	12(%rdi), %r9d
	addl	16(%rdi), %r13d
	addl	20(%rdi), %r10d
	addl	24(%rdi), %r11d
	addl	28(%rdi), %r12d
	movl	%r14d, (%rdi)
	movl	%esi, 4(%rdi)
	movl	%r8d, 8(%rdi)
	movl	%r9d, 12(%rdi)
	movl	%r13d, 16(%rdi)
	movl	%r10d, 20(%rdi)
	movl	%r11d, 24(%rdi)
	movl	%r12d, 28(%rdi)
	movq	8(%rsp), %r8
	movq	(%rsp), %rsi
	addq	$-1, %rax
L_blocks_1_ref$2:
	cmpq	$0, %rax
	jnbe	L_blocks_1_ref$3
	jmp 	*%rdx
L_blocks_0_ref$1:
	leaq	glob_data + 0(%rip), %rax
	movq	%rdi, (%rsp)
	movq	(%rsp), %rdi
	jmp 	L_blocks_0_ref$2
L_blocks_0_ref$3:
	movl	(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 16(%rsp)
	movl	4(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 20(%rsp)
	movl	8(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 24(%rsp)
	movl	12(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 28(%rsp)
	movl	16(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 32(%rsp)
	movl	20(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 36(%rsp)
	movl	24(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 40(%rsp)
	movl	28(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 44(%rsp)
	movl	32(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 48(%rsp)
	movl	36(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 52(%rsp)
	movl	40(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 56(%rsp)
	movl	44(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 60(%rsp)
	movl	48(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 64(%rsp)
	movl	52(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 68(%rsp)
	movl	56(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 72(%rsp)
	movl	60(%rsi), %r8d
	bswapl	%r8d
	movl	%r8d, 76(%rsp)
	movq	%rsi, (%rsp)
	movl	72(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	52(%rsp), %r8d
	movl	20(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	16(%rsp), %r8d
	movl	%r8d, 80(%rsp)
	movl	76(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	56(%rsp), %r8d
	movl	24(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	20(%rsp), %r8d
	movl	%r8d, 84(%rsp)
	movl	80(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	60(%rsp), %r8d
	movl	28(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	24(%rsp), %r8d
	movl	%r8d, 88(%rsp)
	movl	84(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	64(%rsp), %r8d
	movl	32(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	28(%rsp), %r8d
	movl	%r8d, 92(%rsp)
	movl	88(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	68(%rsp), %r8d
	movl	36(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	32(%rsp), %r8d
	movl	%r8d, 96(%rsp)
	movl	92(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	72(%rsp), %r8d
	movl	40(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	36(%rsp), %r8d
	movl	%r8d, 100(%rsp)
	movl	96(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	76(%rsp), %r8d
	movl	44(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	40(%rsp), %r8d
	movl	%r8d, 104(%rsp)
	movl	100(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	80(%rsp), %r8d
	movl	48(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	44(%rsp), %r8d
	movl	%r8d, 108(%rsp)
	movl	104(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	84(%rsp), %r8d
	movl	52(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	48(%rsp), %r8d
	movl	%r8d, 112(%rsp)
	movl	108(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	88(%rsp), %r8d
	movl	56(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	52(%rsp), %r8d
	movl	%r8d, 116(%rsp)
	movl	112(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	92(%rsp), %r8d
	movl	60(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	56(%rsp), %r8d
	movl	%r8d, 120(%rsp)
	movl	116(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	96(%rsp), %r8d
	movl	64(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	60(%rsp), %r8d
	movl	%r8d, 124(%rsp)
	movl	120(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	100(%rsp), %r8d
	movl	68(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	64(%rsp), %r8d
	movl	%r8d, 128(%rsp)
	movl	124(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	104(%rsp), %r8d
	movl	72(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	68(%rsp), %r8d
	movl	%r8d, 132(%rsp)
	movl	128(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	108(%rsp), %r8d
	movl	76(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	72(%rsp), %r8d
	movl	%r8d, 136(%rsp)
	movl	132(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	112(%rsp), %r8d
	movl	80(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	76(%rsp), %r8d
	movl	%r8d, 140(%rsp)
	movl	136(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	116(%rsp), %r8d
	movl	84(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	80(%rsp), %r8d
	movl	%r8d, 144(%rsp)
	movl	140(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	120(%rsp), %r8d
	movl	88(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	84(%rsp), %r8d
	movl	%r8d, 148(%rsp)
	movl	144(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	124(%rsp), %r8d
	movl	92(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	88(%rsp), %r8d
	movl	%r8d, 152(%rsp)
	movl	148(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	128(%rsp), %r8d
	movl	96(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	92(%rsp), %r8d
	movl	%r8d, 156(%rsp)
	movl	152(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	132(%rsp), %r8d
	movl	100(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	96(%rsp), %r8d
	movl	%r8d, 160(%rsp)
	movl	156(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	136(%rsp), %r8d
	movl	104(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	100(%rsp), %r8d
	movl	%r8d, 164(%rsp)
	movl	160(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	140(%rsp), %r8d
	movl	108(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	104(%rsp), %r8d
	movl	%r8d, 168(%rsp)
	movl	164(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	144(%rsp), %r8d
	movl	112(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	108(%rsp), %r8d
	movl	%r8d, 172(%rsp)
	movl	168(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	148(%rsp), %r8d
	movl	116(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	112(%rsp), %r8d
	movl	%r8d, 176(%rsp)
	movl	172(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	152(%rsp), %r8d
	movl	120(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	116(%rsp), %r8d
	movl	%r8d, 180(%rsp)
	movl	176(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	156(%rsp), %r8d
	movl	124(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	120(%rsp), %r8d
	movl	%r8d, 184(%rsp)
	movl	180(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	160(%rsp), %r8d
	movl	128(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	124(%rsp), %r8d
	movl	%r8d, 188(%rsp)
	movl	184(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	164(%rsp), %r8d
	movl	132(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	128(%rsp), %r8d
	movl	%r8d, 192(%rsp)
	movl	188(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	168(%rsp), %r8d
	movl	136(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	132(%rsp), %r8d
	movl	%r8d, 196(%rsp)
	movl	192(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	172(%rsp), %r8d
	movl	140(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	136(%rsp), %r8d
	movl	%r8d, 200(%rsp)
	movl	196(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	176(%rsp), %r8d
	movl	144(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	140(%rsp), %r8d
	movl	%r8d, 204(%rsp)
	movl	200(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	180(%rsp), %r8d
	movl	148(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	144(%rsp), %r8d
	movl	%r8d, 208(%rsp)
	movl	204(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	184(%rsp), %r8d
	movl	152(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	148(%rsp), %r8d
	movl	%r8d, 212(%rsp)
	movl	208(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	188(%rsp), %r8d
	movl	156(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	152(%rsp), %r8d
	movl	%r8d, 216(%rsp)
	movl	212(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	192(%rsp), %r8d
	movl	160(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	156(%rsp), %r8d
	movl	%r8d, 220(%rsp)
	movl	216(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	196(%rsp), %r8d
	movl	164(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	160(%rsp), %r8d
	movl	%r8d, 224(%rsp)
	movl	220(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	200(%rsp), %r8d
	movl	168(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	164(%rsp), %r8d
	movl	%r8d, 228(%rsp)
	movl	224(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	204(%rsp), %r8d
	movl	172(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	168(%rsp), %r8d
	movl	%r8d, 232(%rsp)
	movl	228(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	208(%rsp), %r8d
	movl	176(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	172(%rsp), %r8d
	movl	%r8d, 236(%rsp)
	movl	232(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	212(%rsp), %r8d
	movl	180(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	176(%rsp), %r8d
	movl	%r8d, 240(%rsp)
	movl	236(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	216(%rsp), %r8d
	movl	184(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	180(%rsp), %r8d
	movl	%r8d, 244(%rsp)
	movl	240(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	220(%rsp), %r8d
	movl	188(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	184(%rsp), %r8d
	movl	%r8d, 248(%rsp)
	movl	244(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	224(%rsp), %r8d
	movl	192(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	188(%rsp), %r8d
	movl	%r8d, 252(%rsp)
	movl	248(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	228(%rsp), %r8d
	movl	196(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	192(%rsp), %r8d
	movl	%r8d, 256(%rsp)
	movl	252(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	232(%rsp), %r8d
	movl	200(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	196(%rsp), %r8d
	movl	%r8d, 260(%rsp)
	movl	256(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	236(%rsp), %r8d
	movl	204(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	200(%rsp), %r8d
	movl	%r8d, 264(%rsp)
	movl	260(%rsp), %esi
	movl	%esi, %r8d
	rorl	$17, %r8d
	movl	%esi, %r9d
	rorl	$19, %r9d
	xorl	%r9d, %r8d
	shrl	$10, %esi
	xorl	%esi, %r8d
	addl	240(%rsp), %r8d
	movl	208(%rsp), %esi
	movl	%esi, %r9d
	rorl	$7, %r9d
	movl	%esi, %r10d
	rorl	$18, %r10d
	xorl	%r10d, %r9d
	shrl	$3, %esi
	xorl	%esi, %r9d
	addl	%r9d, %r8d
	addl	204(%rsp), %r8d
	movl	%r8d, 268(%rsp)
	movl	(%rdi), %r14d
	movl	4(%rdi), %esi
	movl	8(%rdi), %r8d
	movl	12(%rdi), %r9d
	movl	16(%rdi), %r13d
	movl	20(%rdi), %r10d
	movl	24(%rdi), %r11d
	movl	28(%rdi), %r12d
	movq	%rdi, 8(%rsp)
	movq	$0, %rdi
	jmp 	L_blocks_0_ref$4
L_blocks_0_ref$5:
	movl	%r12d, %ebx
	movl	%r13d, %ebp
	rorl	$6, %ebp
	movl	%r13d, %r12d
	rorl	$11, %r12d
	xorl	%r12d, %ebp
	movl	%r13d, %r12d
	rorl	$25, %r12d
	xorl	%r12d, %ebp
	addl	%ebp, %ebx
	movl	%r13d, %ebp
	andl	%r10d, %ebp
	movl	%r13d, %r12d
	notl	%r12d
	andl	%r11d, %r12d
	xorl	%r12d, %ebp
	addl	%ebp, %ebx
	addl	(%rax,%rdi,4), %ebx
	addl	16(%rsp,%rdi,4), %ebx
	movl	%r14d, %ebp
	rorl	$2, %ebp
	movl	%r14d, %r12d
	rorl	$13, %r12d
	xorl	%r12d, %ebp
	movl	%r14d, %r12d
	rorl	$22, %r12d
	xorl	%r12d, %ebp
	movl	%r14d, %r12d
	andl	%esi, %r12d
	movl	%r14d, %r15d
	andl	%r8d, %r15d
	xorl	%r15d, %r12d
	movl	%esi, %r15d
	andl	%r8d, %r15d
	xorl	%r15d, %r12d
	addl	%r12d, %ebp
	movl	%r11d, %r12d
	movl	%r10d, %r11d
	movl	%r13d, %r10d
	movl	%r9d, %r13d
	addl	%ebx, %r13d
	movl	%r8d, %r9d
	movl	%esi, %r8d
	movl	%r14d, %esi
	movl	%ebx, %r14d
	addl	%ebp, %r14d
	incq	%rdi
L_blocks_0_ref$4:
	cmpq	$64, %rdi
	jb  	L_blocks_0_ref$5
	movq	8(%rsp), %rdi
	addl	(%rdi), %r14d
	addl	4(%rdi), %esi
	addl	8(%rdi), %r8d
	addl	12(%rdi), %r9d
	addl	16(%rdi), %r13d
	addl	20(%rdi), %r10d
	addl	24(%rdi), %r11d
	addl	28(%rdi), %r12d
	movl	%r14d, (%rdi)
	movl	%esi, 4(%rdi)
	movl	%r8d, 8(%rdi)
	movl	%r9d, 12(%rdi)
	movl	%r13d, 16(%rdi)
	movl	%r10d, 20(%rdi)
	movl	%r11d, 24(%rdi)
	movl	%r12d, 28(%rdi)
	movq	(%rsp), %rsi
	addq	$64, %rsi
	addq	$-64, %rdx
L_blocks_0_ref$2:
	cmpq	$64, %rdx
	jnb 	L_blocks_0_ref$3
	movq	%rdi, %r9
	jmp 	*%rcx
	.data
	.p2align	5
_glob_data:
glob_data:
      .byte -104
      .byte 47
      .byte -118
      .byte 66
      .byte -111
      .byte 68
      .byte 55
      .byte 113
      .byte -49
      .byte -5
      .byte -64
      .byte -75
      .byte -91
      .byte -37
      .byte -75
      .byte -23
      .byte 91
      .byte -62
      .byte 86
      .byte 57
      .byte -15
      .byte 17
      .byte -15
      .byte 89
      .byte -92
      .byte -126
      .byte 63
      .byte -110
      .byte -43
      .byte 94
      .byte 28
      .byte -85
      .byte -104
      .byte -86
      .byte 7
      .byte -40
      .byte 1
      .byte 91
      .byte -125
      .byte 18
      .byte -66
      .byte -123
      .byte 49
      .byte 36
      .byte -61
      .byte 125
      .byte 12
      .byte 85
      .byte 116
      .byte 93
      .byte -66
      .byte 114
      .byte -2
      .byte -79
      .byte -34
      .byte -128
      .byte -89
      .byte 6
      .byte -36
      .byte -101
      .byte 116
      .byte -15
      .byte -101
      .byte -63
      .byte -63
      .byte 105
      .byte -101
      .byte -28
      .byte -122
      .byte 71
      .byte -66
      .byte -17
      .byte -58
      .byte -99
      .byte -63
      .byte 15
      .byte -52
      .byte -95
      .byte 12
      .byte 36
      .byte 111
      .byte 44
      .byte -23
      .byte 45
      .byte -86
      .byte -124
      .byte 116
      .byte 74
      .byte -36
      .byte -87
      .byte -80
      .byte 92
      .byte -38
      .byte -120
      .byte -7
      .byte 118
      .byte 82
      .byte 81
      .byte 62
      .byte -104
      .byte 109
      .byte -58
      .byte 49
      .byte -88
      .byte -56
      .byte 39
      .byte 3
      .byte -80
      .byte -57
      .byte 127
      .byte 89
      .byte -65
      .byte -13
      .byte 11
      .byte -32
      .byte -58
      .byte 71
      .byte -111
      .byte -89
      .byte -43
      .byte 81
      .byte 99
      .byte -54
      .byte 6
      .byte 103
      .byte 41
      .byte 41
      .byte 20
      .byte -123
      .byte 10
      .byte -73
      .byte 39
      .byte 56
      .byte 33
      .byte 27
      .byte 46
      .byte -4
      .byte 109
      .byte 44
      .byte 77
      .byte 19
      .byte 13
      .byte 56
      .byte 83
      .byte 84
      .byte 115
      .byte 10
      .byte 101
      .byte -69
      .byte 10
      .byte 106
      .byte 118
      .byte 46
      .byte -55
      .byte -62
      .byte -127
      .byte -123
      .byte 44
      .byte 114
      .byte -110
      .byte -95
      .byte -24
      .byte -65
      .byte -94
      .byte 75
      .byte 102
      .byte 26
      .byte -88
      .byte 112
      .byte -117
      .byte 75
      .byte -62
      .byte -93
      .byte 81
      .byte 108
      .byte -57
      .byte 25
      .byte -24
      .byte -110
      .byte -47
      .byte 36
      .byte 6
      .byte -103
      .byte -42
      .byte -123
      .byte 53
      .byte 14
      .byte -12
      .byte 112
      .byte -96
      .byte 106
      .byte 16
      .byte 22
      .byte -63
      .byte -92
      .byte 25
      .byte 8
      .byte 108
      .byte 55
      .byte 30
      .byte 76
      .byte 119
      .byte 72
      .byte 39
      .byte -75
      .byte -68
      .byte -80
      .byte 52
      .byte -77
      .byte 12
      .byte 28
      .byte 57
      .byte 74
      .byte -86
      .byte -40
      .byte 78
      .byte 79
      .byte -54
      .byte -100
      .byte 91
      .byte -13
      .byte 111
      .byte 46
      .byte 104
      .byte -18
      .byte -126
      .byte -113
      .byte 116
      .byte 111
      .byte 99
      .byte -91
      .byte 120
      .byte 20
      .byte 120
      .byte -56
      .byte -124
      .byte 8
      .byte 2
      .byte -57
      .byte -116
      .byte -6
      .byte -1
      .byte -66
      .byte -112
      .byte -21
      .byte 108
      .byte 80
      .byte -92
      .byte -9
      .byte -93
      .byte -7
      .byte -66
      .byte -14
      .byte 120
      .byte 113
      .byte -58
