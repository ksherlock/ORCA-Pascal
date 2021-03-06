	mcopy symbols.macros
****************************************************************
*
*  EnterId - Enter an identifier in the symbol table
*
*  Inputs:
*	fcp - pointer to the identifier record
*
****************************************************************
*
EnterId	start
	using GetCom
lcp	equ	1	local identifier pointer
lcpl	equ	5	last lcp
lleft	equ	9	left link?
p1	equ	13	work pointers
p2	equ	17

	sub	(4:fcp),20

	ldx	#displaySize	lcp := display[top].fname;
	lda	TOP
	jsl	~mul2
	clc
	adc	#display_fname
	tax
	lda	DISPLAY,X
	sta	lcp
	lda	DISPLAY+2,X
	sta	lcp+2
	ora	lcp	if lcp = nil then
	bne	lb1
	lda	fcp	  display[top].fname := fcp
	sta	DISPLAY,X
	lda	fcp+2
	sta	DISPLAY+2,X
	brl	lb10	else begin
lb1	anop		  repeat
	move4 lcp,lcpl	    lcpl := lcp;
	ldy	#2	    comp :=
	lda	[lcp],Y	      compnames(lcp^.name^,fcp^.name^);
	pha
	lda	[lcp]
	pha
	lda	[fcp],Y
	pha
	lda	[fcp]
	pha
	jsl	CompNames
	tax		    if comp = 0 then begin
 	bne	lb4	      {name conflict, follow right link}
	listerror #30	      error(30);
!			      lcp := lcp^.rlink;
!			      lleft := false;
	bra	lb5	      end
lb4	bpl	lb6	    else if comp < 0 then begin
lb5	ldy	#identifier_rlink	      lcp := lcp^.rlink;
	lda	[lcp],Y
	tax
	iny
	iny
	lda	[lcp],Y
	sta	lcp+2
	stx	lcp
	stz	lleft	      lleft := false;
	bra	lb7	      end
lb6	anop		    else begin
	ldy	#identifier_llink	      lcp := lcp^.llink;
	lda	[lcp],Y
	tax
	iny
	iny
	lda	[lcp],Y
	sta	lcp+2
	stx	lcp
	lda	#true	      lleft := true;
	sta	lleft
!			      end
lb7	lda	lcp	  until lcp = nil;
	ora	lcp+2
	bne	lb1
	lda	lleft	  if lleft then
	beq	lb8
	ldy	#identifier_llink	    lcpl^.llink := fcp
	bra	lb9	  else
lb8	ldy	#identifier_rlink	    lcpl^.rlink := fcp
lb9	lda	fcp
	sta	[lcpl],Y
	iny
	iny
	lda	fcp+2
	sta	[lcpl],Y
lb10	anop		  end;
	ldy	#identifier_llink	fcp^.llink := nil;
	lda	#0	fcp^.rlink := nil;
	sta	[fcp],Y
	iny
	iny
	sta	[fcp],Y
	iny
	iny
	sta	[fcp],Y
	iny
	iny
	sta	[fcp],Y

	ret
	end
 
****************************************************************
*
*  MarkAsUsed - Insert a name into the list of names used from other levels
*
*  Inputs:
*	name - pointer to name used
*	top - index to display for the proper used list
*
****************************************************************
*
MarkAsUsed private
	using GetCom
p1	equ	1	work pointer
p2	equ	5
p3	equ	9

	sub	(4:name),12

	lda	TOP	p1 := @display[top].labsused;
	ldx	#DisplaySize
	jsl	~mul2
	clc
	adc	#display_labsused
	adc	#display
	sta	p1
	lda	#^display
	sta	p1+2
	ldy	#2	p2 := p1^;
	lda	[p1]
	sta	p2
	lda	[p1],Y
	sta	p2+2
lb1	lda	p2	while p2 <> nil do begin
	ora	p2+2
	beq	lb3
	ldy	#ltype_name	  if p2^.name = name then
	lda	[p2],Y
	cmp	name
	bne	lb2
	iny
	iny
	lda	[p2],Y
	cmp	name+2
	beq	lb4	    goto 1;

lb2	ldy	#ltype_next	  p2 := p2^.next;
	lda	[p2],Y
	tax
	iny
	iny
	lda	[p2],Y
	sta	p2+2
	stx	p2
	bra	lb1	  end;
lb3	ph2	#ltypeSize	new(p3);
	jsl	Malloc
	sta	p3
	stx	p3+2
	ldy	#ltype_name	p3^.name := name;
	lda	name
	sta	[p3],Y
	iny
	iny
	lda	name+2
	sta	[p3],Y
	ldy	#ltype_next	p3^.next := p1^;
	lda	[p1]
	sta	[p3],Y
	ldy	#2
	lda	[p1],Y
	ldy	#ltype_next+2
	sta	[p3],Y
	ldy	#ltype_disx	p3^.disx := disx;
	lda	DISX
	sta	[p3],Y
	lda	p3	p1^ := p3;
	sta	[p1]
	ldy	#2
	lda	p3+2
	sta	[p1],Y
lb4	anop		1:

	ret
	end

****************************************************************
*
*  SearchId - find an identifier
*
*  Inputs:
*	fidcls - set of allowable identifiers
*	fcp - address to place pointer to identifier found
*
****************************************************************
*
SearchId start
	using GetCom
lcp	equ	1	pointer to current symbol
ldisx	equ	5	address of display record being searched
len	equ	9	length of the string
p1	equ	11

!DISX	pointer	display level where the symbol is found
typesSet equ	1	set masks for elements of idclass
konstSet equ	2
varsmSet equ	4
fieldSet equ	8
procSet	equ	16

;	sub	(1:fidcls,4:fcp),14	Pascal 1.x
	sub	(2:fidcls,4:fcp),14	Pascal 2.x

	lda	id	len := length(ID)+1;
	and	#$00FF
	inc	a
	sta	len
	lda	TOP	for ldisx := top downto 0 do begin
	sta	DISX	  disx := ldisx;
	ldx	#displaySize
	jsl	~mul2
	clc
	adc	#DISPLAY
	sta	ldisx
	lda	#^DISPLAY
	adc	#0
	sta	ldisx+2
lb1	ldy	#display_fname	  lcp := display[disx].fname;
	lda	[ldisx],Y
	sta	lcp
	iny
	iny
	lda	[ldisx],Y
	sta	lcp+2
lb2	lda	lcp	  while lcp <> nil do begin
	ora	lcp+2
	beq	lb12
	ldy	#2	    comp := compnames(lcp^.name^,id);
	lda	[lcp],Y
	pha
	lda	[lcp]
	pha
	ph4	#id
	jsl	CompNames
	tax
	bne	lb8	    if comp = 0 then
	ldy	#identifier_klass	      if lcp^.klass in fidcls then begin
	lda	[lcp],Y
	tax
	lda	#0
	sec
lb5	rol	A
	dbpl	X,lb5
	and	fidcls
	beq	lb6
	lda	[ldisx]		gispacked :=
	sta	GISPACKED		  display[disx].ispacked;
	lda	TOP		if top <> disx then
	cmp	DISX
	beq	lb5a
	ph4	p1		  MarkAsUsed(lcp^.name);
	jsl	MarkAsUsed
lb5a	brl	lab1		goto 1;
!				end
lb6	anop		      else begin
	lda	PRTERR		if prterr then
	beq	lb7
	listerror #32		  error(32);
lb7	bra	lb9		lcp := lcp^.rlink
!				end
lb8	bpl	lb10	    else if comp < 0 then
lb9	ldy	#identifier_rlink	      lcp := lcp^.rlink
	bra	lb11	    else
lb10	ldy	#identifier_llink	      lcp := lcp^.llink
lb11	lda	[lcp],Y
	tax
	iny
	iny
	lda	[lcp],Y
	sta	lcp+2
	stx	lcp
	bra	lb2	    end; {while}
lb12	sub4	ldisx,#displaySize	  end; {for}
	dec	DISX
	jpl	lb1
	lda	PRTERR	if prterr then begin
	beq	lab1
	listerror #33	  error(33);
	lda	fidcls	  {to avoid returning nil, reference
	bit	#typesSet	   an entry for an undeclared id of
	beq	la1	   appropriate class
	ldx	UTYPPTR+2	   --> procedure enterundecl}
!			  {types,konst,varsm,field,proc,func,
	lda	UTYPPTR	   directive,prog}
	bra	la6	  if types in fidcls then
la1	bit	#varsmSet	    lcp := utypptr
	beq	la2	  else if varsm in fidcls then
	ldx	UVARPTR+2	    lcp := uvarptr
	lda	UVARPTR
	bra	la6	  else if field in fidcls then
la2	bit	#fieldSet	    lcp := ufldptr
	beq	la3
	ldx	UFLDPTR+2
	lda	UFLDPTR
	bra	la6
la3	bit	#konstSet	  else if konst in fidcls then
	beq	la4	    lcp := ucstptr
	ldx	UCSTPTR+2
	lda	UCSTPTR
	bra	la6
la4	bit	#procSet	  else if proc in fidcls then
	beq	la5	    lcp := uprcptr
	ldx	UPRCPTR+2
	lda	UPRCPTR
	bra	la6
la5	ldx	UFCTPTR+2	  else
	lda	UFCTPTR	    lcp := ufctptr;
la6	sta	lcp	  end;
	stx	<lcp+2
lab1	anop		1:
	ldy	#2	fcp := lcp
	lda	lcp
	sta	[fcp]
	lda	lcp+2
	sta	[fcp],Y

la7	ret
	end

****************************************************************
*
*  SearchSection - find record fields and forward declared proc id's
*
*  Inputs:
*	fcp - top of identifier chain
*
*  Outputs:
*	fcpl - output identifier
*
****************************************************************
*
SearchSection start
	using GetCom
	longa on
	longi on
p1	equ	1	work pointer

	sub	(4:fcp,4:fcpl),4

lb1	lda	fcp	while fcp <> nil do begin
	ora	fcp+2
	beq	lb6
	ldy	#2	  comp := compnames(fcp^.name^,id);
	lda	[fcp],Y
	pha
	lda	[fcp]
	pha
	ph4	#id
	jsl	CompNames
	tax
	beq	lb6	  if comp = 0 then
!			    goto 1
	bpl	lb4	  else if comp < 0 then
	ldy	#identifier_rlink	    fcp := fcp^.rlink
	bra	lb5	  else
lb4	ldy	#identifier_llink	    fcp := fcp^.llink;
lb5	lda	[fcp],Y
	tax
	iny
	iny
	lda	[fcp],Y
	sta	fcp+2
	stx	fcp
	bra	lb1	  end;
lb6	anop		1:
	ldy	#2	fcpl := fcp
	lda	fcp
	sta	[fcpl]
	lda	fcp+2
	sta	[fcpl],Y

	ret
	end
 
