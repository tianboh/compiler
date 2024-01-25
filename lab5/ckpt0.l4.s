	.file	"../tests/l5-checkpoint/ckpt0.l4.s"
	.text
	.globl _c0_gcd1, _c0_gcd2, _c0_main
_c0_gcd1:
	push %rbp
	movq %rsp, %rbp
	subq $0, %rsp	//redundant
_pro_gcd1_15:
	movq %rbx, %rcx	//optimize callee saved register.
	movq %r12, %r8	//if they are not assigned, then do not
	movq %r13, %r10 //need to save them
	movq %r14, %r9
	movq %r15, %rbx
	movl %edi, %edx
	movl %esi, %edi
_body_gcd1_17:
	jmp _loop_stop_7
_loop_start_6:
	movl %edx, %r12d
	movl %edi, %r11d
	xorq %rax, %rax
	cmpl %r11d, %r12d
	setg %al
	movq %rax, %rsi
	movl $1, %eax
	cmpl %eax, %esi
	je _if_true_4
	jmp _if_false_3
_if_false_3:
	movl %edi, %esi
	movl %edx, %eax
	movl %esi, %edi	//SSA
	subl %eax, %edi
	jmp _if_conv_5
_if_true_4:
	movl %edx, %esi
	movl %edi, %eax
	movl %esi, %edx // edx -> esi, esi->edx. need optimize
	subl %eax, %edx
_if_conv_5:
_loop_stop_7:
	movl %edx, %r11d
	movl %edi, %esi
	xorq %rax, %rax
	cmpl %esi, %r11d
	setne %al
	movq %rax, %r12
	movl $1, %eax
	cmpl %eax, %r12d
	je _loop_start_6
	jmp _loop_dummy_8 //needless jump. just fall through.
_loop_dummy_8:		  //also, change the jump order if necessary.
	movl %edx, %esi
	movl %esi, %eax
	jmp _epi_gcd1_16  //needless jump.
_epi_gcd1_16:
	movq %rbx, %r15
	movq %r9, %r14
	movq %r10, %r13
	movq %r8, %r12
	movq %rcx, %rbx
	movq %rbp, %rsp  //redundant restore callee registers.
	pop %rbp
	ret
_c0_gcd2:
	push %rbp
	movq %rsp, %rbp
	subq $32, %rsp
_pro_gcd2_18:
	movq %rbx, -8(%rbp)
	movq %r12, -16(%rbp)
	movq %r13, -24(%rbp)
	movq %r14, %r12
	movq %r15, %rbx
	movl %edi, %edx
	movl %esi, %ecx
_body_gcd2_20:
	movl %ecx, %r8d
	movl $0, %esi
	xorq %rax, %rax
	cmpl %esi, %r8d
	sete %al
	movq %rax, %rdi
	movl $1, %eax
	cmpl %eax, %edi
	je _if_true_10
	jmp _if_false_9 //fall through
_if_false_9:
	movl %edx, %edi
	movl %ecx, %r8d
	movl %edi, %eax
	movl %r8d, %r15d
	cdq
	idivl %r15d
	movl %edx, %esi
	movl %esi, %eax //edx -> eax. copy propagation.
	movl %ecx, %edx
	movl %eax, %esi
	movl %edx, %edi //ecx -> edi
	call _c0_gcd2
	movl %eax, %edx
	movl %edx, %ecx
	movl %ecx, %eax
	jmp _epi_gcd2_19
	jmp _if_conv_11
_if_true_10:
	movl %edx, %ecx
	movl %ecx, %eax
	jmp _epi_gcd2_19
_if_conv_11:		 //Eliminate empty block, and jump.
_epi_gcd2_19:
	movq %rbx, %r15
	movq %r12, %r14
	movq -24(%rbp), %r13
	movq -16(%rbp), %r12
	movq -8(%rbp), %rbx
	movq %rbp, %rsp
	pop %rbp
	ret
_c0_main:
	push %rbp
	movq %rsp, %rbp
	subq $32, %rsp
_pro_main_21:
	movq %rbx, -8(%rbp)
	movq %r12, -16(%rbp)
	movq %r13, -32(%rbp)
	movq %r14, -24(%rbp) //useless callee save.
	movq %r15, %rbx
_body_main_23:
	movl $104, %r12d	//SSA+const propagation
	movl $65, %r13d		//SSA+const propagation
	movl %r13d, %eax
	movl %r12d, %ecx
	movl %eax, %esi
	movl %ecx, %edi
	call _c0_gcd1
	movl %eax, %r14d
	movl %r13d, %eax
	movl %r12d, %ecx
	movl %eax, %esi
	movl %ecx, %edi
	call _c0_gcd2
	movl %eax, %ecx
	movl %r14d, %edx
	movl %ecx, %esi
	xorq %rax, %rax
	cmpl %esi, %edx
	sete %al
	movq %rax, %rcx
	movl $1, %eax
	cmpl %eax, %ecx
	je _terop_true_12
	jmp _terop_false_13
_terop_true_12:
	movl $1, %eax
	jmp _terop_end_14
_terop_false_13:
	movl $0, %eax
_terop_end_14:
	movl %eax, %ecx
	movl %ecx, %eax
	jmp _epi_main_22
_epi_main_22:
	movq %rbx, %r15
	movq -24(%rbp), %r14
	movq -32(%rbp), %r13
	movq -16(%rbp), %r12
	movq -8(%rbp), %rbx
	movq %rbp, %rsp
	pop %rbp
	ret
_raise:
	push %rbp
	movq %rsp, %rbp
	subq $32, %rsp
_pro_raise_24:
	movq %rbx, -8(%rbp)
	movq %r12, -16(%rbp)
	movq %r13, -24(%rbp)
	movq %r14, %r12
	movq %r15, %rbx
	movl %edi, %ecx
_body_raise_26:
	movl %ecx, %eax
	movl %eax, %edi
	call raise
_epi_raise_25:
	movq %rbx, %r15
	movq %r12, %r14
	movq -24(%rbp), %r13
	movq -16(%rbp), %r12
	movq -8(%rbp), %rbx
	movq %rbp, %rsp
	pop %rbp
	ret
