Require Import Kami.All.

Definition Xlen := 32.
Definition Addr := Bit Xlen.

Definition PhyAddrSz := 22. (* 2-MB physical memory *)
Definition PseudoAddrSz := 25.  (* AXI address width size *)
Definition LgClutSz := Eval compute in (PseudoAddrSz - PhyAddrSz). (* Log of number of entries in the Clut *)

Definition PhyAddr := Bit PhyAddrSz.
Definition PseudoAddr := Bit PseudoAddrSz.
Definition ClutIdx := Bit LgClutSz.
Definition ClutSz := Eval compute in (Nat.pow 2 LgClutSz).

Definition ClutEntry := STRUCT_TYPE {
                            "top" :: PhyAddr ;
                            "base" :: PhyAddr ;
                            "ReadPerm" :: Bool ;
                            "WritePerm" :: Bool }.

Definition DmaReq := STRUCT_TYPE {
                         "addr" :: PseudoAddr ;
                         "size" :: PhyAddr ;
                         "isWrite" :: Bool }.

Definition prefix := "Clut".
Local Notation "@^ x" := (prefix ++ "_" ++ x)%string (at level 0).
Section Clut.
  Variable ty: Kind -> Type.

  Section Insert.
    Variable entry: ClutEntry @# ty.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    (* Insert bounds and perms entry into the Clut. Will be invoked from the driver SW *)
    Definition insert: ActionT ty (Bit (LgClutSz + 1)) :=
      ( (* Find an empty slot in freeIndex. Highest bit of freeIndex is 1 if no empty slot is found *)
        Read valids: Array ClutSz Bool <- @^"valids";
        LET freeIndex: Bit (LgClutSz + 1) <- countLeadingZeros (LgClutSz + 1) (~ (pack #valids));
        LET freeIndexValue: ClutIdx <- TruncLsbTo LgClutSz 1 #freeIndex;
        LET freeIndexInvalid: Bool <- unpack Bool (TruncMsbTo 1 LgClutSz #freeIndex);

        (* If an empty slot is found, update the Clut entry for that slot *)
        If (!#freeIndexInvalid)
        then ( Call @^"write"(STRUCT { "addr" ::= #freeIndexValue; "data" ::= ARRAY {entry} }: _);
               Retv );

        (* Return the empty slot if found with MSB 0. If MSB is 1, then no empty slot found *)
        Ret #freeIndex ).
  End Insert.

  Section Remove.
    Variable clutIdx: ClutIdx @# ty.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    (* Remove a clut entry. Will be invoked from the driver SW *)
    Definition remove: ActionT ty Void :=
      ( Read valids: Array ClutSz Bool <- @^"valids";
        Write @^"valids": Array ClutSz Bool <- #valids @[ clutIdx <- $$false ];
        Retv ).
  End Remove.

  Section Check.
    Variable dmaReq: DmaReq @# ty.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    (* Will be invoked from the outstanding transaction of a DMA engine HW protected by the clut *)
    Definition checkAccess: ActionT ty Bool :=
      ( (* Split the incoming address into Clut index and Physical address *)
        LET clutIdx: ClutIdx <- TruncMsbTo LgClutSz PhyAddrSz (dmaReq @% "addr");
        LET phyAddr: PhyAddr <- TruncLsbTo PhyAddrSz LgClutSz (dmaReq @% "addr");

        (* Read corresponding Clut Entry using Clut index *)
        Call entryArray: Array 1 ClutEntry <- @^"read"(#clutIdx: ClutIdx);
        LET entry: ClutEntry <- ReadArrayConst #entryArray (Fin.F1);

        (* Check for bounds: base <= addr <= top *)
        LET bounds: Bool <- ((#entry @% "base") <= #phyAddr) && (#phyAddr + (dmaReq @% "size") <= (#entry @% "top"));
        LET perms: Bool <- ITE (dmaReq @% "isWrite") (#entry @% "WritePerm") (#entry @% "ReadPerm");
        Ret (#bounds && #perms)).
  End Check.

  Section Rules.
    Definition ReqAddrSz := Eval compute in (max PhyAddrSz (LgClutSz + 1)).
    Definition ReqAddr := Bit ReqAddrSz.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    (* This defines the protocol with the DMA and processor.
       If the DMA has a valid request, then check for access rights.
       Only if DMA does not have a valid request, check for driver requests to insert/delete,
            and puts it in DmaAccessValid register.
       The protocol for the driver requests has ValidReq and ValidResp CSRs.
       If request from the processor is pending, ValidReq is true.
       If a response to the processor is pending, ValidResp is true,
          which will be cleared after the processor reads the response.
       The Clut processes the request only if ValidReq is true and ValidResp is false
           (i.e. pending request, and no outstanding response).
       *)
    Definition protocol: ActionT ty Void :=
      ( (* Read a CSR that says if a request is valid *)
        Read ValidProcReq: Bool <- @^"ValidProcReq";

        (* Read the CSRs for actual request *)
        Read isInsert: Bool <- @^"isInsert";

        (* top and Clut Idx share the same CSR *)
        Read topOrClutIdx: ReqAddr <- @^"topOrClutIdx";
        LET top: PhyAddr <- ZeroExtendTruncLsb PhyAddrSz #topOrClutIdx;
        LET clutIdx: ClutIdx <- ZeroExtendTruncLsb LgClutSz #topOrClutIdx;
        Read base: PhyAddr <- @^"base";
        Read ReadPerm: Bool <- @^"ReadPerm";
        Read WritePerm: Bool <- @^"WritePerm";

        (* Read the CSR which says whether a previous response has been read back *)
        Read ValidProcResp: Bool <- @^"ValidProcResp";

        (* Read the valids *)
        Read valids: Array ClutSz Bool <- @^"valids";

        (* Get the DmaReq (addr, size, write/read) from DMA *)
        Call dmaReq: Maybe DmaReq <- @^"dmaAccess"();

        (* If valid DMA request, then check for access rights *)
        If (#dmaReq @% "valid")
        then ( LETA isValid: Bool <- checkAccess (#dmaReq @% "data");
               Write @^"DmaAccessValid": Bool <- #isValid;
               Retv )
        else (
            (* Else if valid driver request, without a pending response not acknowledged by the driver,
               process driver request *)
            If (#ValidProcReq && !#ValidProcResp)
            then ( Write @^"ValidProcReq": Bool <- $$false;
                   Write @^"ValidProcResp": Bool <- $$true;
                   If (!#isInsert)
                   then ( remove #clutIdx )
                   else ( LETA newClutIdx <- insert (STRUCT {"top" ::= #top;
                                                              "base" ::= #base;
                                                              "ReadPerm" ::= #ReadPerm;
                                                              "WritePerm" ::= #WritePerm});
                          Write @^"topOrClutIdx": ReqAddr <- ZeroExtendTo (size ReqAddr) #newClutIdx;
                          Retv
                        );
                   Retv );
                 Retv);
        Retv).
  End Rules.
End Clut.

(* The SRAM containing the Clut entries *)
Definition ClutRegFile := {|rfIsWrMask := false;
                            rfNum := 1;
                            rfDataArray := "clutEntries";
                            rfRead := Async ["read"];
                            rfWrite := "write";
                            rfIdxNum := LgClutSz;
                            rfData := ClutEntry;
                            rfInit := RFNonFile _ None |}.

(* The Clut module containing all the registers and the single protocol rule *)
Definition Clut: Mod :=
  MODULE {
      Register @^"valids" : Array ClutSz Bool <- (ConstArray (fun _ => ConstBool false))
      with Register @^"ValidProcReq": Bool <- false
        with Register @^"ValidProcResp": Bool <- false
          with RegisterU @^"isInsert": Bool
            with RegisterU @^"topOrClutIdx": ReqAddr
              with RegisterU @^"base": PhyAddr
                with RegisterU @^"ReadPerm": Bool
                  with RegisterU @^"WritePerm": Bool
                    with Register @^"DmaAccessValid": Bool <- false
                      with Rule @^"protocol" := protocol _
    }.

(* The combination of the Clut module and SRAM *)
Definition FullClut := HideMeth (HideMeth (ConcatMod Clut (BaseRegFile ClutRegFile)) @^"write") @^"read".

Set Extraction Output Directory "./extraction".

Separate Extraction

  getFins
  Fin.to_nat
  fullFormatHex
  fullFormatBinary
  fullFormatDecimal
  readReqName
  readResName
  readRegName
  rfIsWrMask
  rfNum
  rfDataArray
  rfRead
  rfWrite
  rfIdxNum
  rfData
  rfInit
  pack
  unpack

  FullClut.
