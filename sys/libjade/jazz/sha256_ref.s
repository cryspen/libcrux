	.att_syntax
	.text
	.p2align	5
	.globl	_jade_hash_sha256_amd64_ref
	.globl	jade_hash_sha256_amd64_ref
_jade_hash_sha256_amd64_ref:
jade_hash_sha256_amd64_ref:
	movq	%rsp, %rax
	leaq	-224(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rax, 216(%rsp)
	movq	%r14, 176(%rsp)
	movq	%r13, 184(%rsp)
	movq	%r12, 192(%rsp)
	movq	%rbp, 200(%rsp)
	movq	%rbx, 208(%rsp)
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
	leaq	16(%rsp), %rcx
	leaq	-272(%rsp), %rsp
	call	L_blocks_0_ref$1
Ljade_hash_sha256_amd64_ref$8:
	leaq	272(%rsp), %rsp
	movq	8(%rsp), %rcx
	movq	$0, %rax
	movl	%eax, 48(%rsp)
	movl	%eax, 52(%rsp)
	movl	%eax, 56(%rsp)
	movl	%eax, 60(%rsp)
	movl	%eax, 64(%rsp)
	movl	%eax, 68(%rsp)
	movl	%eax, 72(%rsp)
	movl	%eax, 76(%rsp)
	movl	%eax, 80(%rsp)
	movl	%eax, 84(%rsp)
	movl	%eax, 88(%rsp)
	movl	%eax, 92(%rsp)
	movl	%eax, 96(%rsp)
	movl	%eax, 100(%rsp)
	movl	%eax, 104(%rsp)
	movl	%eax, 108(%rsp)
	movl	%eax, 112(%rsp)
	movl	%eax, 116(%rsp)
	movl	%eax, 120(%rsp)
	movl	%eax, 124(%rsp)
	movl	%eax, 128(%rsp)
	movl	%eax, 132(%rsp)
	movl	%eax, 136(%rsp)
	movl	%eax, 140(%rsp)
	movl	%eax, 144(%rsp)
	movl	%eax, 148(%rsp)
	movl	%eax, 152(%rsp)
	movl	%eax, 156(%rsp)
	movl	%eax, 160(%rsp)
	movl	%eax, 164(%rsp)
	movl	%eax, 168(%rsp)
	movl	%eax, 172(%rsp)
	jmp 	Ljade_hash_sha256_amd64_ref$6
Ljade_hash_sha256_amd64_ref$7:
	movb	(%rsi,%rax), %dil
	movb	%dil, 48(%rsp,%rax)
	incq	%rax
Ljade_hash_sha256_amd64_ref$6:
	cmpq	%rdx, %rax
	jb  	Ljade_hash_sha256_amd64_ref$7
	movb	$-128, 48(%rsp,%rax)
	cmpq	$56, %rdx
	jb  	Ljade_hash_sha256_amd64_ref$4
	movq	$120, %rsi
	movq	$2, %rax
	movq	$127, %rdx
	jmp 	Ljade_hash_sha256_amd64_ref$2
Ljade_hash_sha256_amd64_ref$4:
	movq	$56, %rsi
	movq	$1, %rax
	movq	$63, %rdx
Ljade_hash_sha256_amd64_ref$5:
	jmp 	Ljade_hash_sha256_amd64_ref$2
Ljade_hash_sha256_amd64_ref$3:
	movb	%cl, 48(%rsp,%rdx)
	shrq	$8, %rcx
	addq	$-1, %rdx
Ljade_hash_sha256_amd64_ref$2:
	cmpq	%rsi, %rdx
	jnb 	Ljade_hash_sha256_amd64_ref$3
	leaq	48(%rsp), %rdi
	leaq	-280(%rsp), %rsp
	call	L_blocks_1_ref$1
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
	movq	176(%rsp), %r14
	movq	184(%rsp), %r13
	movq	192(%rsp), %r12
	movq	200(%rsp), %rbp
	movq	208(%rsp), %rbx
	movq	216(%rsp), %rsp
	ret 
L_blocks_1_ref$1:
	leaq	glob_data + 0(%rip), %rcx
	movq	%r8, 8(%rsp)
	movq	$0, %rdx
	movq	8(%rsp), %rsi
	jmp 	L_blocks_1_ref$2
L_blocks_1_ref$3:
	movq	%rdx, 8(%rsp)
	shlq	$4, %rdx
	movl	(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 32(%rsp)
	movl	4(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 36(%rsp)
	movl	8(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 40(%rsp)
	movl	12(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 44(%rsp)
	movl	16(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 48(%rsp)
	movl	20(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 52(%rsp)
	movl	24(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 56(%rsp)
	movl	28(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 60(%rsp)
	movl	32(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 64(%rsp)
	movl	36(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 68(%rsp)
	movl	40(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 72(%rsp)
	movl	44(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 76(%rsp)
	movl	48(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 80(%rsp)
	movl	52(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 84(%rsp)
	movl	56(%rdi,%rdx,4), %r8d
	bswapl	%r8d
	movl	%r8d, 88(%rsp)
	movl	60(%rdi,%rdx,4), %edx
	bswapl	%edx
	movl	%edx, 92(%rsp)
	movq	%rdi, 16(%rsp)
	movl	88(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	68(%rsp), %edi
	movl	36(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	32(%rsp), %edi
	movl	%edi, 96(%rsp)
	movl	92(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	72(%rsp), %edi
	movl	40(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	36(%rsp), %edi
	movl	%edi, 100(%rsp)
	movl	96(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	76(%rsp), %edi
	movl	44(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	40(%rsp), %edi
	movl	%edi, 104(%rsp)
	movl	100(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	80(%rsp), %edi
	movl	48(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	44(%rsp), %edi
	movl	%edi, 108(%rsp)
	movl	104(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	84(%rsp), %edi
	movl	52(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	48(%rsp), %edi
	movl	%edi, 112(%rsp)
	movl	108(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	88(%rsp), %edi
	movl	56(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	52(%rsp), %edi
	movl	%edi, 116(%rsp)
	movl	112(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	92(%rsp), %edi
	movl	60(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	56(%rsp), %edi
	movl	%edi, 120(%rsp)
	movl	116(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	96(%rsp), %edi
	movl	64(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	60(%rsp), %edi
	movl	%edi, 124(%rsp)
	movl	120(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	100(%rsp), %edi
	movl	68(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	64(%rsp), %edi
	movl	%edi, 128(%rsp)
	movl	124(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	104(%rsp), %edi
	movl	72(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	68(%rsp), %edi
	movl	%edi, 132(%rsp)
	movl	128(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	108(%rsp), %edi
	movl	76(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	72(%rsp), %edi
	movl	%edi, 136(%rsp)
	movl	132(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	112(%rsp), %edi
	movl	80(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	76(%rsp), %edi
	movl	%edi, 140(%rsp)
	movl	136(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	116(%rsp), %edi
	movl	84(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	80(%rsp), %edi
	movl	%edi, 144(%rsp)
	movl	140(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	120(%rsp), %edi
	movl	88(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	84(%rsp), %edi
	movl	%edi, 148(%rsp)
	movl	144(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	124(%rsp), %edi
	movl	92(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	88(%rsp), %edi
	movl	%edi, 152(%rsp)
	movl	148(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	128(%rsp), %edi
	movl	96(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	92(%rsp), %edi
	movl	%edi, 156(%rsp)
	movl	152(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	132(%rsp), %edi
	movl	100(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	96(%rsp), %edi
	movl	%edi, 160(%rsp)
	movl	156(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	136(%rsp), %edi
	movl	104(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	100(%rsp), %edi
	movl	%edi, 164(%rsp)
	movl	160(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	140(%rsp), %edi
	movl	108(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	104(%rsp), %edi
	movl	%edi, 168(%rsp)
	movl	164(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	144(%rsp), %edi
	movl	112(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	108(%rsp), %edi
	movl	%edi, 172(%rsp)
	movl	168(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	148(%rsp), %edi
	movl	116(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	112(%rsp), %edi
	movl	%edi, 176(%rsp)
	movl	172(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	152(%rsp), %edi
	movl	120(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	116(%rsp), %edi
	movl	%edi, 180(%rsp)
	movl	176(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	156(%rsp), %edi
	movl	124(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	120(%rsp), %edi
	movl	%edi, 184(%rsp)
	movl	180(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	160(%rsp), %edi
	movl	128(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	124(%rsp), %edi
	movl	%edi, 188(%rsp)
	movl	184(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	164(%rsp), %edi
	movl	132(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	128(%rsp), %edi
	movl	%edi, 192(%rsp)
	movl	188(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	168(%rsp), %edi
	movl	136(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	132(%rsp), %edi
	movl	%edi, 196(%rsp)
	movl	192(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	172(%rsp), %edi
	movl	140(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	136(%rsp), %edi
	movl	%edi, 200(%rsp)
	movl	196(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	176(%rsp), %edi
	movl	144(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	140(%rsp), %edi
	movl	%edi, 204(%rsp)
	movl	200(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	180(%rsp), %edi
	movl	148(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	144(%rsp), %edi
	movl	%edi, 208(%rsp)
	movl	204(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	184(%rsp), %edi
	movl	152(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	148(%rsp), %edi
	movl	%edi, 212(%rsp)
	movl	208(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	188(%rsp), %edi
	movl	156(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	152(%rsp), %edi
	movl	%edi, 216(%rsp)
	movl	212(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	192(%rsp), %edi
	movl	160(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	156(%rsp), %edi
	movl	%edi, 220(%rsp)
	movl	216(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	196(%rsp), %edi
	movl	164(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	160(%rsp), %edi
	movl	%edi, 224(%rsp)
	movl	220(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	200(%rsp), %edi
	movl	168(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	164(%rsp), %edi
	movl	%edi, 228(%rsp)
	movl	224(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	204(%rsp), %edi
	movl	172(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	168(%rsp), %edi
	movl	%edi, 232(%rsp)
	movl	228(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	208(%rsp), %edi
	movl	176(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	172(%rsp), %edi
	movl	%edi, 236(%rsp)
	movl	232(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	212(%rsp), %edi
	movl	180(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	176(%rsp), %edi
	movl	%edi, 240(%rsp)
	movl	236(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	216(%rsp), %edi
	movl	184(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	180(%rsp), %edi
	movl	%edi, 244(%rsp)
	movl	240(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	220(%rsp), %edi
	movl	188(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	184(%rsp), %edi
	movl	%edi, 248(%rsp)
	movl	244(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	224(%rsp), %edi
	movl	192(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	188(%rsp), %edi
	movl	%edi, 252(%rsp)
	movl	248(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	228(%rsp), %edi
	movl	196(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	192(%rsp), %edi
	movl	%edi, 256(%rsp)
	movl	252(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	232(%rsp), %edi
	movl	200(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	196(%rsp), %edi
	movl	%edi, 260(%rsp)
	movl	256(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	236(%rsp), %edi
	movl	204(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	200(%rsp), %edi
	movl	%edi, 264(%rsp)
	movl	260(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	240(%rsp), %edi
	movl	208(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	204(%rsp), %edi
	movl	%edi, 268(%rsp)
	movl	264(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	244(%rsp), %edi
	movl	212(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	208(%rsp), %edi
	movl	%edi, 272(%rsp)
	movl	268(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	248(%rsp), %edi
	movl	216(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	212(%rsp), %edi
	movl	%edi, 276(%rsp)
	movl	272(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	252(%rsp), %edi
	movl	220(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	216(%rsp), %edi
	movl	%edi, 280(%rsp)
	movl	276(%rsp), %edx
	movl	%edx, %edi
	rorl	$17, %edi
	movl	%edx, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %edx
	xorl	%edx, %edi
	addl	256(%rsp), %edi
	movl	224(%rsp), %edx
	movl	%edx, %r8d
	rorl	$7, %r8d
	movl	%edx, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %edx
	xorl	%edx, %r8d
	addl	%r8d, %edi
	addl	220(%rsp), %edi
	movl	%edi, 284(%rsp)
	movl	(%rsi), %r12d
	movl	4(%rsi), %edx
	movl	8(%rsi), %edi
	movl	12(%rsi), %r8d
	movl	16(%rsi), %ebp
	movl	20(%rsi), %r9d
	movl	24(%rsi), %r10d
	movl	28(%rsi), %r13d
	movq	%rsi, 24(%rsp)
	movq	$0, %rsi
	jmp 	L_blocks_1_ref$4
L_blocks_1_ref$5:
	movl	%r13d, %r11d
	movl	%ebp, %ebx
	rorl	$6, %ebx
	movl	%ebp, %r13d
	rorl	$11, %r13d
	xorl	%r13d, %ebx
	movl	%ebp, %r13d
	rorl	$25, %r13d
	xorl	%r13d, %ebx
	addl	%ebx, %r11d
	movl	%ebp, %ebx
	andl	%r9d, %ebx
	movl	%ebp, %r13d
	notl	%r13d
	andl	%r10d, %r13d
	xorl	%r13d, %ebx
	addl	%ebx, %r11d
	addl	(%rcx,%rsi,4), %r11d
	addl	32(%rsp,%rsi,4), %r11d
	movl	%r12d, %ebx
	rorl	$2, %ebx
	movl	%r12d, %r13d
	rorl	$13, %r13d
	xorl	%r13d, %ebx
	movl	%r12d, %r13d
	rorl	$22, %r13d
	xorl	%r13d, %ebx
	movl	%r12d, %r13d
	andl	%edx, %r13d
	movl	%r12d, %r14d
	andl	%edi, %r14d
	xorl	%r14d, %r13d
	movl	%edx, %r14d
	andl	%edi, %r14d
	xorl	%r14d, %r13d
	addl	%r13d, %ebx
	movl	%r10d, %r13d
	movl	%r9d, %r10d
	movl	%ebp, %r9d
	movl	%r8d, %ebp
	addl	%r11d, %ebp
	movl	%edi, %r8d
	movl	%edx, %edi
	movl	%r12d, %edx
	movl	%r11d, %r12d
	addl	%ebx, %r12d
	incq	%rsi
L_blocks_1_ref$4:
	cmpq	$64, %rsi
	jb  	L_blocks_1_ref$5
	movq	24(%rsp), %rsi
	addl	(%rsi), %r12d
	addl	4(%rsi), %edx
	addl	8(%rsi), %edi
	addl	12(%rsi), %r8d
	addl	16(%rsi), %ebp
	addl	20(%rsi), %r9d
	addl	24(%rsi), %r10d
	addl	28(%rsi), %r13d
	movl	%r12d, (%rsi)
	movl	%edx, 4(%rsi)
	movl	%edi, 8(%rsi)
	movl	%r8d, 12(%rsi)
	movl	%ebp, 16(%rsi)
	movl	%r9d, 20(%rsi)
	movl	%r10d, 24(%rsi)
	movl	%r13d, 28(%rsi)
	movq	16(%rsp), %rdi
	movq	8(%rsp), %rdx
	incq	%rdx
L_blocks_1_ref$2:
	cmpq	%rax, %rdx
	jb  	L_blocks_1_ref$3
	ret 
L_blocks_0_ref$1:
	leaq	glob_data + 0(%rip), %rax
	movq	%rcx, 8(%rsp)
	movq	8(%rsp), %rcx
	jmp 	L_blocks_0_ref$2
L_blocks_0_ref$3:
	movl	(%rsi), %edi
	bswapl	%edi
	movl	%edi, 24(%rsp)
	movl	4(%rsi), %edi
	bswapl	%edi
	movl	%edi, 28(%rsp)
	movl	8(%rsi), %edi
	bswapl	%edi
	movl	%edi, 32(%rsp)
	movl	12(%rsi), %edi
	bswapl	%edi
	movl	%edi, 36(%rsp)
	movl	16(%rsi), %edi
	bswapl	%edi
	movl	%edi, 40(%rsp)
	movl	20(%rsi), %edi
	bswapl	%edi
	movl	%edi, 44(%rsp)
	movl	24(%rsi), %edi
	bswapl	%edi
	movl	%edi, 48(%rsp)
	movl	28(%rsi), %edi
	bswapl	%edi
	movl	%edi, 52(%rsp)
	movl	32(%rsi), %edi
	bswapl	%edi
	movl	%edi, 56(%rsp)
	movl	36(%rsi), %edi
	bswapl	%edi
	movl	%edi, 60(%rsp)
	movl	40(%rsi), %edi
	bswapl	%edi
	movl	%edi, 64(%rsp)
	movl	44(%rsi), %edi
	bswapl	%edi
	movl	%edi, 68(%rsp)
	movl	48(%rsi), %edi
	bswapl	%edi
	movl	%edi, 72(%rsp)
	movl	52(%rsi), %edi
	bswapl	%edi
	movl	%edi, 76(%rsp)
	movl	56(%rsi), %edi
	bswapl	%edi
	movl	%edi, 80(%rsp)
	movl	60(%rsi), %edi
	bswapl	%edi
	movl	%edi, 84(%rsp)
	movq	%rsi, 8(%rsp)
	movl	80(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	60(%rsp), %edi
	movl	28(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	24(%rsp), %edi
	movl	%edi, 88(%rsp)
	movl	84(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	64(%rsp), %edi
	movl	32(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	28(%rsp), %edi
	movl	%edi, 92(%rsp)
	movl	88(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	68(%rsp), %edi
	movl	36(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	32(%rsp), %edi
	movl	%edi, 96(%rsp)
	movl	92(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	72(%rsp), %edi
	movl	40(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	36(%rsp), %edi
	movl	%edi, 100(%rsp)
	movl	96(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	76(%rsp), %edi
	movl	44(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	40(%rsp), %edi
	movl	%edi, 104(%rsp)
	movl	100(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	80(%rsp), %edi
	movl	48(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	44(%rsp), %edi
	movl	%edi, 108(%rsp)
	movl	104(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	84(%rsp), %edi
	movl	52(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	48(%rsp), %edi
	movl	%edi, 112(%rsp)
	movl	108(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	88(%rsp), %edi
	movl	56(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	52(%rsp), %edi
	movl	%edi, 116(%rsp)
	movl	112(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	92(%rsp), %edi
	movl	60(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	56(%rsp), %edi
	movl	%edi, 120(%rsp)
	movl	116(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	96(%rsp), %edi
	movl	64(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	60(%rsp), %edi
	movl	%edi, 124(%rsp)
	movl	120(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	100(%rsp), %edi
	movl	68(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	64(%rsp), %edi
	movl	%edi, 128(%rsp)
	movl	124(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	104(%rsp), %edi
	movl	72(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	68(%rsp), %edi
	movl	%edi, 132(%rsp)
	movl	128(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	108(%rsp), %edi
	movl	76(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	72(%rsp), %edi
	movl	%edi, 136(%rsp)
	movl	132(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	112(%rsp), %edi
	movl	80(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	76(%rsp), %edi
	movl	%edi, 140(%rsp)
	movl	136(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	116(%rsp), %edi
	movl	84(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	80(%rsp), %edi
	movl	%edi, 144(%rsp)
	movl	140(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	120(%rsp), %edi
	movl	88(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	84(%rsp), %edi
	movl	%edi, 148(%rsp)
	movl	144(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	124(%rsp), %edi
	movl	92(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	88(%rsp), %edi
	movl	%edi, 152(%rsp)
	movl	148(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	128(%rsp), %edi
	movl	96(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	92(%rsp), %edi
	movl	%edi, 156(%rsp)
	movl	152(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	132(%rsp), %edi
	movl	100(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	96(%rsp), %edi
	movl	%edi, 160(%rsp)
	movl	156(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	136(%rsp), %edi
	movl	104(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	100(%rsp), %edi
	movl	%edi, 164(%rsp)
	movl	160(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	140(%rsp), %edi
	movl	108(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	104(%rsp), %edi
	movl	%edi, 168(%rsp)
	movl	164(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	144(%rsp), %edi
	movl	112(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	108(%rsp), %edi
	movl	%edi, 172(%rsp)
	movl	168(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	148(%rsp), %edi
	movl	116(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	112(%rsp), %edi
	movl	%edi, 176(%rsp)
	movl	172(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	152(%rsp), %edi
	movl	120(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	116(%rsp), %edi
	movl	%edi, 180(%rsp)
	movl	176(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	156(%rsp), %edi
	movl	124(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	120(%rsp), %edi
	movl	%edi, 184(%rsp)
	movl	180(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	160(%rsp), %edi
	movl	128(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	124(%rsp), %edi
	movl	%edi, 188(%rsp)
	movl	184(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	164(%rsp), %edi
	movl	132(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	128(%rsp), %edi
	movl	%edi, 192(%rsp)
	movl	188(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	168(%rsp), %edi
	movl	136(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	132(%rsp), %edi
	movl	%edi, 196(%rsp)
	movl	192(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	172(%rsp), %edi
	movl	140(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	136(%rsp), %edi
	movl	%edi, 200(%rsp)
	movl	196(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	176(%rsp), %edi
	movl	144(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	140(%rsp), %edi
	movl	%edi, 204(%rsp)
	movl	200(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	180(%rsp), %edi
	movl	148(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	144(%rsp), %edi
	movl	%edi, 208(%rsp)
	movl	204(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	184(%rsp), %edi
	movl	152(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	148(%rsp), %edi
	movl	%edi, 212(%rsp)
	movl	208(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	188(%rsp), %edi
	movl	156(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	152(%rsp), %edi
	movl	%edi, 216(%rsp)
	movl	212(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	192(%rsp), %edi
	movl	160(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	156(%rsp), %edi
	movl	%edi, 220(%rsp)
	movl	216(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	196(%rsp), %edi
	movl	164(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	160(%rsp), %edi
	movl	%edi, 224(%rsp)
	movl	220(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	200(%rsp), %edi
	movl	168(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	164(%rsp), %edi
	movl	%edi, 228(%rsp)
	movl	224(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	204(%rsp), %edi
	movl	172(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	168(%rsp), %edi
	movl	%edi, 232(%rsp)
	movl	228(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	208(%rsp), %edi
	movl	176(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	172(%rsp), %edi
	movl	%edi, 236(%rsp)
	movl	232(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	212(%rsp), %edi
	movl	180(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	176(%rsp), %edi
	movl	%edi, 240(%rsp)
	movl	236(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	216(%rsp), %edi
	movl	184(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	180(%rsp), %edi
	movl	%edi, 244(%rsp)
	movl	240(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	220(%rsp), %edi
	movl	188(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	184(%rsp), %edi
	movl	%edi, 248(%rsp)
	movl	244(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	224(%rsp), %edi
	movl	192(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	188(%rsp), %edi
	movl	%edi, 252(%rsp)
	movl	248(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	228(%rsp), %edi
	movl	196(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	192(%rsp), %edi
	movl	%edi, 256(%rsp)
	movl	252(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	232(%rsp), %edi
	movl	200(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	196(%rsp), %edi
	movl	%edi, 260(%rsp)
	movl	256(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	236(%rsp), %edi
	movl	204(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	200(%rsp), %edi
	movl	%edi, 264(%rsp)
	movl	260(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	240(%rsp), %edi
	movl	208(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	204(%rsp), %edi
	movl	%edi, 268(%rsp)
	movl	264(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	244(%rsp), %edi
	movl	212(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	208(%rsp), %edi
	movl	%edi, 272(%rsp)
	movl	268(%rsp), %esi
	movl	%esi, %edi
	rorl	$17, %edi
	movl	%esi, %r8d
	rorl	$19, %r8d
	xorl	%r8d, %edi
	shrl	$10, %esi
	xorl	%esi, %edi
	addl	248(%rsp), %edi
	movl	216(%rsp), %esi
	movl	%esi, %r8d
	rorl	$7, %r8d
	movl	%esi, %r9d
	rorl	$18, %r9d
	xorl	%r9d, %r8d
	shrl	$3, %esi
	xorl	%esi, %r8d
	addl	%r8d, %edi
	addl	212(%rsp), %edi
	movl	%edi, 276(%rsp)
	movl	(%rcx), %r12d
	movl	4(%rcx), %esi
	movl	8(%rcx), %edi
	movl	12(%rcx), %r8d
	movl	16(%rcx), %ebp
	movl	20(%rcx), %r9d
	movl	24(%rcx), %r10d
	movl	28(%rcx), %r13d
	movq	%rcx, 16(%rsp)
	movq	$0, %rcx
	jmp 	L_blocks_0_ref$4
L_blocks_0_ref$5:
	movl	%r13d, %r11d
	movl	%ebp, %ebx
	rorl	$6, %ebx
	movl	%ebp, %r13d
	rorl	$11, %r13d
	xorl	%r13d, %ebx
	movl	%ebp, %r13d
	rorl	$25, %r13d
	xorl	%r13d, %ebx
	addl	%ebx, %r11d
	movl	%ebp, %ebx
	andl	%r9d, %ebx
	movl	%ebp, %r13d
	notl	%r13d
	andl	%r10d, %r13d
	xorl	%r13d, %ebx
	addl	%ebx, %r11d
	addl	(%rax,%rcx,4), %r11d
	addl	24(%rsp,%rcx,4), %r11d
	movl	%r12d, %ebx
	rorl	$2, %ebx
	movl	%r12d, %r13d
	rorl	$13, %r13d
	xorl	%r13d, %ebx
	movl	%r12d, %r13d
	rorl	$22, %r13d
	xorl	%r13d, %ebx
	movl	%r12d, %r13d
	andl	%esi, %r13d
	movl	%r12d, %r14d
	andl	%edi, %r14d
	xorl	%r14d, %r13d
	movl	%esi, %r14d
	andl	%edi, %r14d
	xorl	%r14d, %r13d
	addl	%r13d, %ebx
	movl	%r10d, %r13d
	movl	%r9d, %r10d
	movl	%ebp, %r9d
	movl	%r8d, %ebp
	addl	%r11d, %ebp
	movl	%edi, %r8d
	movl	%esi, %edi
	movl	%r12d, %esi
	movl	%r11d, %r12d
	addl	%ebx, %r12d
	incq	%rcx
L_blocks_0_ref$4:
	cmpq	$64, %rcx
	jb  	L_blocks_0_ref$5
	movq	16(%rsp), %rcx
	addl	(%rcx), %r12d
	addl	4(%rcx), %esi
	addl	8(%rcx), %edi
	addl	12(%rcx), %r8d
	addl	16(%rcx), %ebp
	addl	20(%rcx), %r9d
	addl	24(%rcx), %r10d
	addl	28(%rcx), %r13d
	movl	%r12d, (%rcx)
	movl	%esi, 4(%rcx)
	movl	%edi, 8(%rcx)
	movl	%r8d, 12(%rcx)
	movl	%ebp, 16(%rcx)
	movl	%r9d, 20(%rcx)
	movl	%r10d, 24(%rcx)
	movl	%r13d, 28(%rcx)
	movq	8(%rsp), %rsi
	addq	$64, %rsi
	addq	$-64, %rdx
L_blocks_0_ref$2:
	cmpq	$64, %rdx
	jnb 	L_blocks_0_ref$3
	movq	%rcx, %r8
	ret 
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
