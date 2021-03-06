****************************************************************
*
*  InitLabels - initialize the labels array
*
*  Outputs:
*        labelTab - initialized
*        intLabel - initialized
*
****************************************************************
*
InitLabels start
maxLabel equ   2400

!                                       with labelTab[0] do begin
         lda   #-1                         val := -1;
         sta   labelTab+6
         sta   labelTab+8
         stz   labelTab                    defined := false;
         stz   labelTab+2                  chain := nil;
         stz   labelTab+4
!                                          end; {with}
         ldx   #labelTab                for i := 1 to maxLabel do
         ldy   #labelTab+10                labelTab[i] := labelTab[0];
         lda   #maxLabel*10-1
         mvn   labelTab,labelTab
         stz   intLabel                 intLabel := 0;
         rtl
         end
