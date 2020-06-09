(X86ISA::X86-HLT)
(X86ISA::X86P-OF-X86-HLT (7 7 (:TYPE-PRESCRIPTION X86ISA::X86-HLT)))
(X86ISA::X86-CMC/CLC/STC/CLD/STD
 (432 16
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
 (91 13
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-CR0BITS-P))
 (61 61 (:REWRITE DEFAULT-<-2))
 (61 61 (:REWRITE DEFAULT-<-1))
 (58 58
     (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (48 16
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
 (48 16
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
 (48 16
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
 (48 16
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
 (48 16
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
 (48 16
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
 (48 16
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
 (48 16
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
 (28 4
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-PREFIXES-P))
 (24 24
     (:TYPE-PRESCRIPTION X86ISA::CR0BITS-P$INLINE))
 (24 12
     (:REWRITE X86ISA::CR0BITS-P-WHEN-UNSIGNED-BYTE-P))
 (16 16
     (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
 (16 16
     (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
 (16 16
     (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
 (16 16
     (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
 (16 16
     (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
 (16 16
     (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
 (16 16 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
 (16 8
     (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (16 8
     (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (16 8
     (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (16 8
     (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
 (16 8
     (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (16 8
     (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (16 8
     (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
 (11 3
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-PREFIXES-P))
 (11 3
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-32BITS-P))
 (6 6 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (6 6
    (:REWRITE
         X86ISA::!RFLAGSBITS->CF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (6 6
    (:REWRITE X86ISA::!RFLAGSBITS->CF$INLINE-OF-BFIX-CF-NORMALIZE-CONST))
 (4 4
    (:TYPE-PRESCRIPTION X86ISA::EVEX-PREFIXES-P$INLINE))
 (4 4 (:TYPE-PRESCRIPTION X86ISA::32BITS-P))
 (4 4
    (:REWRITE X86ISA::RFLAGSBITS->CF-OF-WRITE-WITH-MASK))
 (4 4
    (:REWRITE
         X86ISA::RFLAGSBITS->CF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (4 4
    (:REWRITE
         X86ISA::!RFLAGSBITS->DF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (4 4
    (:REWRITE X86ISA::!RFLAGSBITS->DF$INLINE-OF-BFIX-DF-NORMALIZE-CONST))
 (4 2
    (:REWRITE X86ISA::EVEX-PREFIXES-P-WHEN-UNSIGNED-BYTE-P))
 (4 2
    (:REWRITE X86ISA::32BITS-P-WHEN-UNSIGNED-BYTE-P)))
(X86ISA::X86P-OF-X86-CMC/CLC/STC/CLD/STD
 (7 7
    (:TYPE-PRESCRIPTION X86ISA::X86-CMC/CLC/STC/CLD/STD))
 (3 3
    (:REWRITE
         X86ISA::!RFLAGSBITS->CF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (3 3
    (:REWRITE X86ISA::!RFLAGSBITS->CF$INLINE-OF-BFIX-CF-NORMALIZE-CONST))
 (3 1 (:REWRITE X86ISA::X86P-OF-WRITE-*IP))
 (2 2
    (:REWRITE
         X86ISA::!RFLAGSBITS->DF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE X86ISA::!RFLAGSBITS->DF$INLINE-OF-BFIX-DF-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::RFLAGSBITS->CF-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE
         X86ISA::RFLAGSBITS->CF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST)))
(X86ISA::X86-SAHF
 (448 18
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
 (182 2 (:REWRITE LOGTAIL-IDENTITY))
 (65 63 (:REWRITE DEFAULT-<-1))
 (64 18
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
 (64 18
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
 (64 18
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
 (64 18
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
 (64 18
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
 (64 18
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
 (64 18
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
 (64 18
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
 (63 63 (:REWRITE DEFAULT-<-2))
 (60 60
     (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (28 4
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-PREFIXES-P))
 (27 5
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-CR0BITS-P))
 (24 12 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (20 20
     (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
 (20 20
     (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
 (20 20
     (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
 (20 20
     (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
 (20 20
     (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
 (20 20
     (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
 (20 20 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
 (20 10
     (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (20 10
     (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (20 10
     (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (20 10
     (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
 (20 10
     (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (20 10
     (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (20 10
     (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
 (11 3
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-PREFIXES-P))
 (11 3
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-32BITS-P))
 (8 8
    (:TYPE-PRESCRIPTION X86ISA::CR0BITS-P$INLINE))
 (8 4
    (:REWRITE X86ISA::CR0BITS-P-WHEN-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (4 4
    (:TYPE-PRESCRIPTION X86ISA::EVEX-PREFIXES-P$INLINE))
 (4 4 (:TYPE-PRESCRIPTION X86ISA::32BITS-P))
 (4 2
    (:REWRITE X86ISA::EVEX-PREFIXES-P-WHEN-UNSIGNED-BYTE-P))
 (4 2
    (:REWRITE X86ISA::32BITS-P-WHEN-UNSIGNED-BYTE-P))
 (2 2
    (:REWRITE X86ISA::RFLAGSBITS->ZF-OF-WRITE-WITH-MASK))
 (2 2
    (:REWRITE
         X86ISA::RFLAGSBITS->ZF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE X86ISA::RFLAGSBITS->SF-OF-WRITE-WITH-MASK))
 (2 2
    (:REWRITE
         X86ISA::RFLAGSBITS->SF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE X86ISA::RFLAGSBITS->PF-OF-WRITE-WITH-MASK))
 (2 2
    (:REWRITE
         X86ISA::RFLAGSBITS->PF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE X86ISA::RFLAGSBITS->CF-OF-WRITE-WITH-MASK))
 (2 2
    (:REWRITE
         X86ISA::RFLAGSBITS->CF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE X86ISA::RFLAGSBITS->AF-OF-WRITE-WITH-MASK))
 (2 2
    (:REWRITE
         X86ISA::RFLAGSBITS->AF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE
         X86ISA::!RFLAGSBITS->ZF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE X86ISA::!RFLAGSBITS->ZF$INLINE-OF-BFIX-ZF-NORMALIZE-CONST))
 (2 2
    (:REWRITE
         X86ISA::!RFLAGSBITS->SF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE X86ISA::!RFLAGSBITS->SF$INLINE-OF-BFIX-SF-NORMALIZE-CONST))
 (2 2
    (:REWRITE
         X86ISA::!RFLAGSBITS->PF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE X86ISA::!RFLAGSBITS->PF$INLINE-OF-BFIX-PF-NORMALIZE-CONST))
 (2 2
    (:REWRITE
         X86ISA::!RFLAGSBITS->CF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE X86ISA::!RFLAGSBITS->CF$INLINE-OF-BFIX-CF-NORMALIZE-CONST))
 (2 2
    (:REWRITE
         X86ISA::!RFLAGSBITS->AF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE X86ISA::!RFLAGSBITS->AF$INLINE-OF-BFIX-AF-NORMALIZE-CONST)))
(X86ISA::X86P-OF-X86-SAHF
 (91 1 (:REWRITE LOGTAIL-IDENTITY))
 (37 37
     (:TYPE-PRESCRIPTION X86ISA::N16P-RR16))
 (16 1 (:DEFINITION UNSIGNED-BYTE-P))
 (15 1 (:DEFINITION INTEGER-RANGE-P))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
 (7 7 (:TYPE-PRESCRIPTION X86ISA::X86-SAHF))
 (5 2 (:LINEAR X86ISA::N16P-RR16))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::SIB-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::MODR/M-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
 (2 2 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
 (2 1
    (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE X86ISA::SIB-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE X86ISA::MODR/M-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (2 1 (:REWRITE DEFAULT-<-1))
 (2 1
    (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
 (1 1
    (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (1 1
    (:REWRITE X86ISA::RFLAGSBITS->ZF-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE
         X86ISA::RFLAGSBITS->ZF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::RFLAGSBITS->SF-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE
         X86ISA::RFLAGSBITS->SF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::RFLAGSBITS->PF-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE
         X86ISA::RFLAGSBITS->PF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::RFLAGSBITS->CF-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE
         X86ISA::RFLAGSBITS->CF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::RFLAGSBITS->AF-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE
         X86ISA::RFLAGSBITS->AF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1
    (:REWRITE
         X86ISA::!RFLAGSBITS->ZF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->ZF$INLINE-OF-BFIX-ZF-NORMALIZE-CONST))
 (1 1
    (:REWRITE
         X86ISA::!RFLAGSBITS->SF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->SF$INLINE-OF-BFIX-SF-NORMALIZE-CONST))
 (1 1
    (:REWRITE
         X86ISA::!RFLAGSBITS->PF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->PF$INLINE-OF-BFIX-PF-NORMALIZE-CONST))
 (1 1
    (:REWRITE
         X86ISA::!RFLAGSBITS->CF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->CF$INLINE-OF-BFIX-CF-NORMALIZE-CONST))
 (1 1
    (:REWRITE
         X86ISA::!RFLAGSBITS->AF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->AF$INLINE-OF-BFIX-AF-NORMALIZE-CONST)))
(X86ISA::UNSIGNED-BYTE-P-8-OF-RFLAGSBITS-FOR-LAHF
     (2256 352
           (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
     (1328 14 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (352 352 (:TYPE-PRESCRIPTION POSP))
     (254 254
          (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
     (186 18
          (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
     (150 6 (:DEFINITION UNSIGNED-BYTE-P**))
     (120 6
          (:REWRITE BITOPS::UNSIGNED-BYTE-P-OF-0-X))
     (60 30
         (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (59 7 (:REWRITE BFIX-WHEN-NOT-1))
     (47 1 (:LINEAR BITOPS::BFIX-BOUND))
     (42 42 (:TYPE-PRESCRIPTION BITP))
     (32 7 (:REWRITE BFIX-WHEN-NOT-BITP))
     (30 30 (:TYPE-PRESCRIPTION NATP))
     (30 30 (:TYPE-PRESCRIPTION LOGCDR-TYPE))
     (24 24 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
     (24 6 (:REWRITE BFIX-BITP))
     (18 18 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (14 7 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
     (14 7 (:REWRITE BFIX-WHEN-BIT->BOOL))
     (12 12
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (2 1 (:REWRITE DEFAULT-<-1))
     (2 1 (:REWRITE BFIX-EQUAL-1))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:DEFINITION BIT->BOOL$INLINE)))
(X86ISA::X86-LAHF
 (248 248
      (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (248 124 (:REWRITE BFIX-WHEN-NOT-BITP))
 (248 124 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (248 124 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (184 4 (:REWRITE LOGHEAD-IDENTITY))
 (164 124 (:REWRITE BFIX-WHEN-NOT-1))
 (82 22
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
 (82 22
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
 (82 22
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
 (82 22
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
 (82 22
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
 (82 22
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
 (82 22
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
 (82 22
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-ZF-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-VM-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-VIP-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-VIF-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-TF-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-SF-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-RF-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-RES4-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-RES3-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-RES2-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-RES1-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-PF-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-OF-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-NT-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-INTF-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-ID-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-DF-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-CF-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-AF-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-BFIX-AC-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-2BITS-FIX-IOPL-NORMALIZE-CONST))
 (72 72
     (:REWRITE X86ISA::RFLAGSBITS$INLINE-OF-10BITS-FIX-RES5-NORMALIZE-CONST))
 (65 63 (:REWRITE DEFAULT-<-1))
 (63 63 (:REWRITE DEFAULT-<-2))
 (58 58
     (:REWRITE X86ISA::RFLAGSBITS->SF-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->VM-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->VIP-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->VIF-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->TF-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->RF-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->RES5-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->RES4-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->OF-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->NT-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->IOPL-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->INTF-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->ID-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->DF-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->CF-OF-WRITE-WITH-MASK))
 (56 56
     (:REWRITE X86ISA::RFLAGSBITS->AC-OF-WRITE-WITH-MASK))
 (52 52
     (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (52 52
     (:REWRITE X86ISA::RFLAGSBITS->RES1-OF-WRITE-WITH-MASK))
 (52 52
     (:REWRITE X86ISA::RFLAGSBITS->PF-OF-WRITE-WITH-MASK))
 (48 48
     (:REWRITE X86ISA::RFLAGSBITS->RES2-OF-WRITE-WITH-MASK))
 (48 48
     (:REWRITE X86ISA::RFLAGSBITS->AF-OF-WRITE-WITH-MASK))
 (44 44
     (:REWRITE X86ISA::RFLAGSBITS->ZF-OF-WRITE-WITH-MASK))
 (44 44
     (:REWRITE X86ISA::RFLAGSBITS->RES3-OF-WRITE-WITH-MASK))
 (28 4
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-PREFIXES-P))
 (24 24
     (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
 (24 24
     (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
 (24 24
     (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
 (24 24
     (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
 (24 24
     (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
 (24 24
     (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
 (24 24 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
 (24 12
     (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (24 12
     (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (24 12
     (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (24 12
     (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
 (24 12
     (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (24 12
     (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (24 12
     (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
 (24 4 (:REWRITE ASH-0))
 (14 2 (:REWRITE ZIP-OPEN))
 (11 3
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-RFLAGSBITS-P))
 (11 3
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-PREFIXES-P))
 (11 3
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-CR0BITS-P))
 (11 3
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-32BITS-P))
 (10 4 (:LINEAR X86ISA::N16P-RR16))
 (6 6 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (6 4 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (6 4
    (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (4 4
    (:TYPE-PRESCRIPTION X86ISA::RFLAGSBITS-P$INLINE))
 (4 4
    (:TYPE-PRESCRIPTION X86ISA::EVEX-PREFIXES-P$INLINE))
 (4 4
    (:TYPE-PRESCRIPTION X86ISA::CR0BITS-P$INLINE))
 (4 4 (:TYPE-PRESCRIPTION X86ISA::32BITS-P))
 (4 4
    (:REWRITE X86ISA::LOGHEAD-ZERO-SMALLER))
 (4 2
    (:REWRITE X86ISA::EVEX-PREFIXES-P-WHEN-UNSIGNED-BYTE-P))
 (4 2
    (:REWRITE X86ISA::CR0BITS-P-WHEN-UNSIGNED-BYTE-P))
 (4 2
    (:REWRITE X86ISA::32BITS-P-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:TYPE-PRESCRIPTION ZIP))
 (2 2 (:TYPE-PRESCRIPTION IFIX))
 (2 2
    (:REWRITE
         X86ISA::RFLAGSBITS->ZF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE
         X86ISA::RFLAGSBITS->SF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE
         X86ISA::RFLAGSBITS->PF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE
         X86ISA::RFLAGSBITS->CF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE
         X86ISA::RFLAGSBITS->AF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST)))
(X86ISA::X86P-OF-X86-LAHF
 (91 1 (:REWRITE LOGHEAD-IDENTITY))
 (37 37
     (:TYPE-PRESCRIPTION X86ISA::N16P-RR16))
 (16 1 (:DEFINITION UNSIGNED-BYTE-P))
 (15 1 (:DEFINITION INTEGER-RANGE-P))
 (11 1 (:REWRITE ASH-0))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (8 8
    (:TYPE-PRESCRIPTION X86ISA::!RFLAGSBITS->CF$INLINE))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SIB-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
 (8 1
    (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
 (7 7 (:TYPE-PRESCRIPTION X86ISA::X86-LAHF))
 (7 1 (:REWRITE ZIP-OPEN))
 (5 2 (:LINEAR X86ISA::N16P-RR16))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::SIB-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::MODR/M-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
 (2 2
    (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
 (2 2 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
 (2 1
    (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE X86ISA::SIB-P-WHEN-UNSIGNED-BYTE-P))
 (2 1 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
 (2 1
    (:REWRITE X86ISA::MODR/M-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
 (2 1
    (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (2 1
    (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (2 1 (:REWRITE DEFAULT-<-1))
 (2 1
    (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:TYPE-PRESCRIPTION ZIP))
 (1 1 (:TYPE-PRESCRIPTION IFIX))
 (1 1
    (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (1 1
    (:REWRITE X86ISA::RFLAGSBITS->ZF-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE
         X86ISA::RFLAGSBITS->ZF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::RFLAGSBITS->SF-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE
         X86ISA::RFLAGSBITS->SF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::RFLAGSBITS->PF-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE
         X86ISA::RFLAGSBITS->PF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::RFLAGSBITS->CF-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE
         X86ISA::RFLAGSBITS->CF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::RFLAGSBITS->AF-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE
         X86ISA::RFLAGSBITS->AF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::LOGHEAD-ZERO-SMALLER))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1
    (:REWRITE
         X86ISA::!RFLAGSBITS->ZF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->ZF$INLINE-OF-BFIX-ZF-NORMALIZE-CONST))
 (1 1
    (:REWRITE
         X86ISA::!RFLAGSBITS->SF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->SF$INLINE-OF-BFIX-SF-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
       X86ISA::!RFLAGSBITS->RES3$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->RES3$INLINE-OF-BFIX-RES3-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
       X86ISA::!RFLAGSBITS->RES2$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->RES2$INLINE-OF-BFIX-RES2-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
       X86ISA::!RFLAGSBITS->RES1$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->RES1$INLINE-OF-BFIX-RES1-NORMALIZE-CONST))
 (1 1
    (:REWRITE
         X86ISA::!RFLAGSBITS->PF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->PF$INLINE-OF-BFIX-PF-NORMALIZE-CONST))
 (1 1
    (:REWRITE
         X86ISA::!RFLAGSBITS->CF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->CF$INLINE-OF-BFIX-CF-NORMALIZE-CONST))
 (1 1
    (:REWRITE
         X86ISA::!RFLAGSBITS->AF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::!RFLAGSBITS->AF$INLINE-OF-BFIX-AF-NORMALIZE-CONST)))
(X86ISA::X86-RDRAND
 (2832 2832 (:TYPE-PRESCRIPTION X86ISA::XW))
 (2166 318
       (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (1159 1159 (:REWRITE DEFAULT-<-2))
 (1159 1159 (:REWRITE DEFAULT-<-1))
 (784 216
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-CR0BITS-P))
 (780 780
      (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (494 494 (:TYPE-PRESCRIPTION BITP))
 (214 66
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-PREFIXES-P))
 (214 66
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-32BITS-P))
 (194 194
      (:TYPE-PRESCRIPTION X86ISA::CR0BITS-P$INLINE))
 (194 97
      (:REWRITE X86ISA::CR0BITS-P-WHEN-UNSIGNED-BYTE-P))
 (188
  60
  (:REWRITE
    X86ISA::UNSIGNED-BYTE-P-WHEN-SYSTEM-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS-P))
 (188 60
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-SEGMENT-SELECTORBITS-P))
 (188
  60
  (:REWRITE
   X86ISA::UNSIGNED-BYTE-P-WHEN-INTERRUPT/TRAP-GATE-DESCRIPTOR-ATTRIBUTESBITS-P))
 (188
  60
  (:REWRITE
      X86ISA::UNSIGNED-BYTE-P-WHEN-DATA-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS-P))
 (188
  60
  (:REWRITE
      X86ISA::UNSIGNED-BYTE-P-WHEN-CODE-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS-P))
 (188
    60
    (:REWRITE
         X86ISA::UNSIGNED-BYTE-P-WHEN-CALL-GATE-DESCRIPTOR-ATTRIBUTESBITS-P))
 (188 60
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-16BITS-P))
 (122 34
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P))
 (122 34
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P))
 (122 34
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P))
 (122 34
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P))
 (122 34
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P))
 (122 34
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P))
 (122 34
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P))
 (122 34
      (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P))
 (96 8
     (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (94 30
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-XCR0BITS-P))
 (94 30
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-IA32E-PML4EBITS-P))
 (94 30
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-IA32E-PDPTE-PG-DIRBITS-P))
 (94 30
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-IA32E-PDPTE-1GB-PAGEBITS-P))
 (94 30
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-IA32E-PDE-PG-TABLEBITS-P))
 (94 30
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-IA32E-PDE-2MB-PAGEBITS-P))
 (94 30
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-IA32E-PAGE-TABLESBITS-P))
 (94 30
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-DATA-SEGMENT-DESCRIPTORBITS-P))
 (94 30
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-CR3BITS-P))
 (94 30
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-CODE-SEGMENT-DESCRIPTORBITS-P))
 (94 30
     (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-64BITS-P))
 (90 90 (:REWRITE X86ISA::XR-XW-INTER-FIELD))
 (74 74
     (:TYPE-PRESCRIPTION X86ISA::EVEX-PREFIXES-P$INLINE))
 (74 74
     (:TYPE-PRESCRIPTION X86ISA::32BITS-P))
 (74 37
     (:REWRITE X86ISA::EVEX-PREFIXES-P-WHEN-UNSIGNED-BYTE-P))
 (74 37
     (:REWRITE X86ISA::32BITS-P-WHEN-UNSIGNED-BYTE-P))
 (64 64
     (:TYPE-PRESCRIPTION X86ISA::SYSTEM-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS-P))
 (64 64
     (:TYPE-PRESCRIPTION X86ISA::SEGMENT-SELECTORBITS-P))
 (64 64
     (:TYPE-PRESCRIPTION
          X86ISA::INTERRUPT/TRAP-GATE-DESCRIPTOR-ATTRIBUTESBITS-P))
 (64 64
     (:TYPE-PRESCRIPTION X86ISA::DATA-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS-P))
 (64 64
     (:TYPE-PRESCRIPTION X86ISA::CODE-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS-P))
 (64 64
     (:TYPE-PRESCRIPTION X86ISA::CALL-GATE-DESCRIPTOR-ATTRIBUTESBITS-P))
 (64 64
     (:TYPE-PRESCRIPTION X86ISA::16BITS-P))
 (64
  32
  (:REWRITE
    X86ISA::SYSTEM-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS-P-WHEN-UNSIGNED-BYTE-P))
 (64 32
     (:REWRITE X86ISA::SEGMENT-SELECTORBITS-P-WHEN-UNSIGNED-BYTE-P))
 (64
  32
  (:REWRITE
   X86ISA::INTERRUPT/TRAP-GATE-DESCRIPTOR-ATTRIBUTESBITS-P-WHEN-UNSIGNED-BYTE-P))
 (64
  32
  (:REWRITE
      X86ISA::DATA-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS-P-WHEN-UNSIGNED-BYTE-P))
 (64
  32
  (:REWRITE
      X86ISA::CODE-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS-P-WHEN-UNSIGNED-BYTE-P))
 (64
    32
    (:REWRITE
         X86ISA::CALL-GATE-DESCRIPTOR-ATTRIBUTESBITS-P-WHEN-UNSIGNED-BYTE-P))
 (64 32
     (:REWRITE X86ISA::16BITS-P-WHEN-UNSIGNED-BYTE-P))
 (44 44
     (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE2-P$INLINE))
 (44 44
     (:TYPE-PRESCRIPTION X86ISA::VEX3-BYTE1-P$INLINE))
 (44 44
     (:TYPE-PRESCRIPTION X86ISA::VEX2-BYTE1-P$INLINE))
 (44 44
     (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE3-P$INLINE))
 (44 44
     (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE2-P$INLINE))
 (44 44
     (:TYPE-PRESCRIPTION X86ISA::EVEX-BYTE1-P$INLINE))
 (44 44 (:TYPE-PRESCRIPTION X86ISA::8BITS-P))
 (44 22
     (:REWRITE X86ISA::VEX3-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (44 22
     (:REWRITE X86ISA::VEX3-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (44 22
     (:REWRITE X86ISA::VEX2-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (44 22
     (:REWRITE X86ISA::EVEX-BYTE3-P-WHEN-UNSIGNED-BYTE-P))
 (44 22
     (:REWRITE X86ISA::EVEX-BYTE2-P-WHEN-UNSIGNED-BYTE-P))
 (44 22
     (:REWRITE X86ISA::EVEX-BYTE1-P-WHEN-UNSIGNED-BYTE-P))
 (44 22
     (:REWRITE X86ISA::8BITS-P-WHEN-UNSIGNED-BYTE-P))
 (32 32
     (:TYPE-PRESCRIPTION X86ISA::XCR0BITS-P$INLINE))
 (32 32
     (:TYPE-PRESCRIPTION X86ISA::IA32E-PML4EBITS-P))
 (32 32
     (:TYPE-PRESCRIPTION X86ISA::IA32E-PDPTE-PG-DIRBITS-P))
 (32 32
     (:TYPE-PRESCRIPTION X86ISA::IA32E-PDPTE-1GB-PAGEBITS-P))
 (32 32
     (:TYPE-PRESCRIPTION X86ISA::IA32E-PDE-PG-TABLEBITS-P))
 (32 32
     (:TYPE-PRESCRIPTION X86ISA::IA32E-PDE-2MB-PAGEBITS-P))
 (32 32
     (:TYPE-PRESCRIPTION X86ISA::IA32E-PAGE-TABLESBITS-P))
 (32 32
     (:TYPE-PRESCRIPTION X86ISA::DATA-SEGMENT-DESCRIPTORBITS-P))
 (32 32
     (:TYPE-PRESCRIPTION X86ISA::CR3BITS-P$INLINE))
 (32 32
     (:TYPE-PRESCRIPTION X86ISA::CODE-SEGMENT-DESCRIPTORBITS-P))
 (32 32
     (:TYPE-PRESCRIPTION X86ISA::64BITS-P))
 (32 16
     (:REWRITE X86ISA::XCR0BITS-P-WHEN-UNSIGNED-BYTE-P))
 (32 16
     (:REWRITE X86ISA::IA32E-PML4EBITS-P-WHEN-UNSIGNED-BYTE-P))
 (32 16
     (:REWRITE X86ISA::IA32E-PDPTE-PG-DIRBITS-P-WHEN-UNSIGNED-BYTE-P))
 (32 16
     (:REWRITE X86ISA::IA32E-PDPTE-1GB-PAGEBITS-P-WHEN-UNSIGNED-BYTE-P))
 (32 16
     (:REWRITE X86ISA::IA32E-PDE-PG-TABLEBITS-P-WHEN-UNSIGNED-BYTE-P))
 (32 16
     (:REWRITE X86ISA::IA32E-PDE-2MB-PAGEBITS-P-WHEN-UNSIGNED-BYTE-P))
 (32 16
     (:REWRITE X86ISA::IA32E-PAGE-TABLESBITS-P-WHEN-UNSIGNED-BYTE-P))
 (32 16
     (:REWRITE X86ISA::DATA-SEGMENT-DESCRIPTORBITS-P-WHEN-UNSIGNED-BYTE-P))
 (32 16
     (:REWRITE X86ISA::CR3BITS-P-WHEN-UNSIGNED-BYTE-P))
 (32 16
     (:REWRITE X86ISA::CODE-SEGMENT-DESCRIPTORBITS-P-WHEN-UNSIGNED-BYTE-P))
 (32 16
     (:REWRITE X86ISA::64BITS-P-WHEN-UNSIGNED-BYTE-P))
 (24 8
     (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (20
    20
    (:REWRITE
         X86ISA::!RFLAGSBITS->ZF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (20 20
     (:REWRITE X86ISA::!RFLAGSBITS->ZF$INLINE-OF-BFIX-ZF-NORMALIZE-CONST))
 (20
    20
    (:REWRITE
         X86ISA::!RFLAGSBITS->SF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (20 20
     (:REWRITE X86ISA::!RFLAGSBITS->SF$INLINE-OF-BFIX-SF-NORMALIZE-CONST))
 (20
    20
    (:REWRITE
         X86ISA::!RFLAGSBITS->PF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (20 20
     (:REWRITE X86ISA::!RFLAGSBITS->PF$INLINE-OF-BFIX-PF-NORMALIZE-CONST))
 (20
    20
    (:REWRITE
         X86ISA::!RFLAGSBITS->CF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (20 20
     (:REWRITE X86ISA::!RFLAGSBITS->CF$INLINE-OF-BFIX-CF-NORMALIZE-CONST))
 (20
    20
    (:REWRITE
         X86ISA::!RFLAGSBITS->AF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (20 20
     (:REWRITE X86ISA::!RFLAGSBITS->AF$INLINE-OF-BFIX-AF-NORMALIZE-CONST))
 (16 16 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (14 14
     (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (14 14
     (:REWRITE X86ISA::MODR/M->REG-OF-WRITE-WITH-MASK))
 (14 14
     (:REWRITE X86ISA::MODR/M->REG$INLINE-OF-MODR/M-FIX-X-NORMALIZE-CONST))
 (11 11
     (:REWRITE X86ISA::PREFIXES->OPR-OF-WRITE-WITH-MASK))
 (11
   11
   (:REWRITE X86ISA::PREFIXES->OPR$INLINE-OF-PREFIXES-FIX-X-NORMALIZE-CONST))
 (10
    10
    (:REWRITE
         X86ISA::!RFLAGSBITS->OF$INLINE-OF-RFLAGSBITS-FIX-X-NORMALIZE-CONST))
 (10 10
     (:REWRITE X86ISA::!RFLAGSBITS->OF$INLINE-OF-BFIX-OF-NORMALIZE-CONST))
 (8 8
    (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (5
  5
  (:REWRITE
       X86ISA::CODE-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS->D-OF-WRITE-WITH-MASK))
 (5
  5
  (:REWRITE
   X86ISA::CODE-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS->D$INLINE-OF-CODE-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE X86ISA::MODR/M->R/M-OF-WRITE-WITH-MASK))
 (2 2
    (:REWRITE X86ISA::MODR/M->R/M$INLINE-OF-MODR/M-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE X86ISA::MODR/M->MOD-OF-WRITE-WITH-MASK))
 (2 2
    (:REWRITE X86ISA::MODR/M->MOD$INLINE-OF-MODR/M-FIX-X-NORMALIZE-CONST)))
(X86ISA::X86P-OF-X86-RDRAND
 (14 1
     (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
 (11 1
     (:REWRITE FTY::BITP-WHEN-UNSIGNED-BYTE-P-1))
 (6 1 (:DEFINITION UNSIGNED-BYTE-P))
 (5 1 (:DEFINITION INTEGER-RANGE-P))
 (3 3 (:TYPE-PRESCRIPTION BITP))
 (3 1
    (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (2 2 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (2 2
    (:REWRITE X86ISA::PREFIXES->OPR-OF-WRITE-WITH-MASK))
 (2
   2
   (:REWRITE X86ISA::PREFIXES->OPR$INLINE-OF-PREFIXES-FIX-X-NORMALIZE-CONST))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 1
    (:REWRITE FTY::UNSIGNED-BYTE-P-1-WHEN-BITP))
 (1 1 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (1 1
    (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (1 1
    (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (1 1
    (:REWRITE X86ISA::MODR/M->REG-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE X86ISA::MODR/M->REG$INLINE-OF-MODR/M-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::MODR/M->R/M-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE X86ISA::MODR/M->R/M$INLINE-OF-MODR/M-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE X86ISA::MODR/M->MOD-OF-WRITE-WITH-MASK))
 (1 1
    (:REWRITE X86ISA::MODR/M->MOD$INLINE-OF-MODR/M-FIX-X-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
       X86ISA::CODE-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS->D-OF-WRITE-WITH-MASK))
 (1
  1
  (:REWRITE
   X86ISA::CODE-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS->D$INLINE-OF-CODE-SEGMENT-DESCRIPTOR-ATTRIBUTESBITS-FIX-X-NORMALIZE-CONST)))
(X86ISA::X86-STEP-UNIMPLEMENTED)
(X86ISA::X86P-OF-X86-STEP-UNIMPLEMENTED
     (7 7
        (:TYPE-PRESCRIPTION X86ISA::X86-STEP-UNIMPLEMENTED)))
(X86ISA::X86-ILLEGAL-INSTRUCTION)
(X86ISA::X86P-OF-X86-ILLEGAL-INSTRUCTION
     (12 2 (:DEFINITION SIGNED-BYTE-P))
     (11 1
         (:REWRITE X86ISA::CANONICAL-ADDRESS-P-AND-LOGEXT-48))
     (10 2 (:DEFINITION INTEGER-RANGE-P))
     (10 1 (:REWRITE LOGEXT-IDENTITY))
     (9 1
        (:DEFINITION X86ISA::CANONICAL-ADDRESS-P$INLINE))
     (7 7
        (:TYPE-PRESCRIPTION X86ISA::X86-ILLEGAL-INSTRUCTION))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (2 2 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (1 1 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
     (1 1
        (:TYPE-PRESCRIPTION X86ISA::CANONICAL-ADDRESS-P$INLINE))
     (1 1 (:REWRITE X86ISA::XR-XW-INTER-FIELD)))
(X86ISA::X86-GENERAL-PROTECTION)
(X86ISA::X86P-OF-X86-GENERAL-PROTECTION
     (12 2 (:DEFINITION SIGNED-BYTE-P))
     (11 1
         (:REWRITE X86ISA::CANONICAL-ADDRESS-P-AND-LOGEXT-48))
     (10 2 (:DEFINITION INTEGER-RANGE-P))
     (10 1 (:REWRITE LOGEXT-IDENTITY))
     (9 1
        (:DEFINITION X86ISA::CANONICAL-ADDRESS-P$INLINE))
     (7 7
        (:TYPE-PRESCRIPTION X86ISA::X86-GENERAL-PROTECTION))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (2 2 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (1 1 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
     (1 1
        (:TYPE-PRESCRIPTION X86ISA::CANONICAL-ADDRESS-P$INLINE))
     (1 1 (:REWRITE X86ISA::XR-XW-INTER-FIELD)))
(X86ISA::X86-DEVICE-NOT-AVAILABLE)
(X86ISA::X86P-OF-X86-DEVICE-NOT-AVAILABLE
     (12 2 (:DEFINITION SIGNED-BYTE-P))
     (11 1
         (:REWRITE X86ISA::CANONICAL-ADDRESS-P-AND-LOGEXT-48))
     (10 2 (:DEFINITION INTEGER-RANGE-P))
     (10 1 (:REWRITE LOGEXT-IDENTITY))
     (9 1
        (:DEFINITION X86ISA::CANONICAL-ADDRESS-P$INLINE))
     (7 7
        (:TYPE-PRESCRIPTION X86ISA::X86-DEVICE-NOT-AVAILABLE))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (2 2
        (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
     (2 2 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
     (1 1 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
     (1 1
        (:TYPE-PRESCRIPTION X86ISA::CANONICAL-ADDRESS-P$INLINE))
     (1 1 (:REWRITE X86ISA::XR-XW-INTER-FIELD)))
(X86ISA::SHOW-INST-DECODING-AND-SPEC-FN)