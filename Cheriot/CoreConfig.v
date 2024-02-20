Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.InstSpec ProcKami.Cheriot.SpecRun.

Definition CapStruct : Kind :=
  (STRUCT_TYPE {
       "R" :: Bit 1;
       "p" :: Bit 6;
       "oType" :: Bit 3;
       "E" :: Bit 4;
       "B" :: Bit 9;
       "T" :: Bit 9 })%kami_expr.

Section CapHelpers.
  Local Notation AddrSz := 32.
  Section ty.
    Variable ty: Kind -> Type.
    Local Open Scope kami_expr.
    Definition decodePerms (rawPerms: Array 6 Bool @# ty) : CapPerms @# ty :=
      (IF rawPerms ![4]
       then (IF rawPerms ![3]
             then (STRUCT {
                       "U0" ::= $$false;
                       "SE" ::= $$false;
                       "US" ::= $$false;
                       "EX" ::= $$false;
                       "SR" ::= $$false;
                       "MC" ::= $$true;
                       "LD" ::= $$true;
                       "SL" ::= rawPerms ![2];
                       "LM" ::= rawPerms ![1];
                       "SD" ::= $$true;
                       "LG" ::= rawPerms ![0];
                       "GL" ::= rawPerms ![5] })
             else (IF rawPerms ![2]
                   then (STRUCT {
                             "U0" ::= $$false;
                             "SE" ::= $$false;
                             "US" ::= $$false;
                             "EX" ::= $$false;
                             "SR" ::= $$false;
                             "MC" ::= $$true;
                             "LD" ::= $$true;
                             "SL" ::= $$false;
                             "LM" ::= rawPerms ![1];
                             "SD" ::= $$false;
                             "LG" ::= rawPerms ![0];
                             "GL" ::= rawPerms ![5] })
                   else (IF !(rawPerms ![1]) && !(rawPerms ![0])
                         then (STRUCT {
                                   "U0" ::= $$false;
                                   "SE" ::= $$false;
                                   "US" ::= $$false;
                                   "EX" ::= $$false;
                                   "SR" ::= $$false;
                                   "MC" ::= $$true;
                                   "LD" ::= $$false;
                                   "SL" ::= $$false;
                                   "LM" ::= $$false;
                                   "SD" ::= $$true;
                                   "LG" ::= $$false;
                                   "GL" ::= rawPerms ![5] })
                         else (STRUCT {
                                   "U0" ::= $$false;
                                   "SE" ::= $$false;
                                   "US" ::= $$false;
                                   "EX" ::= $$false;
                                   "SR" ::= $$false;
                                   "MC" ::= $$false;
                                   "LD" ::= rawPerms ![1];
                                   "SL" ::= $$false;
                                   "LM" ::= $$false;
                                   "SD" ::= rawPerms ![0];
                                   "LG" ::= $$false;
                                   "GL" ::= rawPerms ![5] }))))
       else (IF rawPerms ![3]
             then (STRUCT {
                       "U0" ::= $$false;
                       "SE" ::= $$false;
                       "US" ::= $$false;
                       "EX" ::= $$true;
                       "SR" ::= rawPerms ![2];
                       "MC" ::= $$true;
                       "LD" ::= $$true;
                       "SL" ::= $$false;
                       "LM" ::= rawPerms ![1];
                       "SD" ::= $$false;
                       "LG" ::= rawPerms ![0];
                       "GL" ::= rawPerms ![5] })
             else (STRUCT {
                       "U0" ::= rawPerms ![2];
                       "SE" ::= rawPerms ![1];
                       "US" ::= rawPerms ![0];
                       "EX" ::= $$false;
                       "SR" ::= $$false;
                       "MC" ::= $$false;
                       "LD" ::= $$false;
                       "SL" ::= $$false;
                       "LM" ::= $$false;
                       "SD" ::= $$false;
                       "LG" ::= $$false;
                       "GL" ::= rawPerms ![5] }))).
    
    Definition encodePerms (perms: CapPerms @# ty) : Bit 6 @# ty :=
      {< pack (perms @% "GL"),
        ( IF perms @% "EX" && perms @% "LD" && perms @% "MC"
          then {< Const ty (2'b"01"), pack (perms @% "SR"), pack (perms @% "LM"), pack (perms @% "LG") >}
          else (IF perms @% "LD" && perms @% "MC" && perms @% "SD"
                then {< Const ty (2'b"11"), pack (perms @% "SL"), pack (perms @% "LM"), pack (perms @% "LG") >}
                else (IF perms @% "LD" && perms @% "MC"
                      then {< Const ty (3'b"101"), pack (perms @% "LM"), pack (perms @% "LG") >}
                      else (IF perms @% "SD" && perms @% "MC"
                            then Const ty (5'b"10000")
                            else (IF perms @% "LD" || perms @% "SD"
                                  then {< Const ty (3'b"100"), pack (perms @% "LD"), pack (perms @% "SD") >}
                                  else {< Const ty (2'b"00"), pack (perms @% "U0"), pack (perms @% "SE"), pack (perms @% "US") >})))))%kami_expr >}.
    
    Definition capExpFromE (E: Bit 4 @# ty) : Bit (Nat.log2_up AddrSz) @# ty :=  ITE (E == Const ty (wones _)) $24 (ZeroExtendTruncLsb _ E).
    
    Definition capBaseTop (cap: Bit (size CapStruct) @# ty) (addr: Bit AddrSz @# ty) :=
      ( LETC B <- (unpack CapStruct cap) @% "B";
        LETC T <- (unpack CapStruct cap) @% "T";
        LETC E <- (unpack CapStruct cap) @% "E";
        LETC exp <- capExpFromE #E;
        LETC aMidTop <- addr >> #exp;
        LETC aMid <- UniBit (TruncLsb 9 (AddrSz - 9)) #aMidTop;
        LETC aTop <- UniBit (TruncMsb 9 (AddrSz - 9)) #aMidTop;
        LETC aHi <- ITE (#aMid < #B) $1 $0;
        LETC tHi <- ITE (#T < #B) $1 $0;
        LETC aTopBase <- #aTop - #aHi;
        LETC aTopTop <- (ZeroExtend 1 #aTopBase) + #tHi;
        LETC base <- ZeroExtendTruncLsb AddrSz ({< #aTopBase, #B >}) << #exp;
        LETC top <- ZeroExtendTruncLsb (AddrSz + 1) ({< #aTopTop, #T >}) << #exp;
        RetE (STRUCT {
                  "base" ::= #base;
                  "top" ::= #top;
                  "aTopBase" ::= #aTopBase } : (STRUCT_TYPE { "base" :: Bit AddrSz ;
                                                              "top"  :: Bit (AddrSz + 1) ;
                                                              "aTopBase" :: Bit (AddrSz - 9) }) @# ty) ).
    
    Definition capBounds (base: Bit AddrSz @# ty) (length: Bit AddrSz @# ty) :=
      ( LETC top : Bit (AddrSz + 1) <- ZeroExtend 1 base + ZeroExtend 1 length;
        LETC expInit : Bit (Nat.log2_up AddrSz) <- $23 - (countLeadingZeros _ (ZeroExtendTruncMsb 23 length));
        LETC isInitSatExpInitSat : Pair Bool (Bit (Nat.log2_up AddrSz)) <-
                                     ITE (#expInit > $14) (STRUCT { "fst" ::= $$true; "snd" ::= $$(wones 5) })
                                       (STRUCT { "fst" ::= $$false; "snd" ::= #expInit });
        LETC isInitSat <- #isInitSatExpInitSat @% "fst";
        LETC expInitSat <- #isInitSatExpInitSat @% "snd";
        LETC lostTopInit <- isNotZero (#top << ($AddrSz - #expInitSat));
        LETC lengthShifted <- ZeroExtendTruncLsb 9 (length >> #expInitSat);
        LETC lengthShiftedAllOnes <- isAllOnes #lengthShifted;
        LETC exp : Bit (Nat.log2_up AddrSz) <- ITE (#lostTopInit && #lengthShiftedAllOnes && !#isInitSat)
                                                 (#expInitSat + $1) (#expInitSat);
        LETC B <- ZeroExtendTruncLsb 9 (base >> #exp);
        LETC lostTop <- isNotZero (#top << ($AddrSz - #exp));
        LETC TInit <- ZeroExtendTruncLsb 9 (#top >> #exp);
        LETC T <- ITE #lostTop (#TInit + $1) #TInit;
        LETC lostBase <- isNotZero (base << ($AddrSz - #exp));
        RetE (STRUCT {
                  "B" ::= #B;
                  "T" ::= #T;
                  "exp" ::= #exp;
                  "exact?" ::= (#lostBase || #lostTop) } : STRUCT_TYPE { "B" :: Bit 9;
                                                                         "T" :: Bit 9;
                                                                         "exp" :: Bit (Nat.log2_up AddrSz);
                                                                         "exact?" :: Bool } @# ty)).

    Definition capPerms cap :=
      (RetE decodePerms (unpack (Array 6 Bool) ((unpack (ty := ty) CapStruct cap) @% "p"))).
  End ty.
  
  Definition capAccessorsInit : CapAccessors _ _ :=
    {|getCapR ty cap := (unpack CapStruct cap) @% "R";
      setCapR ty val cap := pack ((unpack CapStruct cap) @%[ "R" <- val]);
      getCapP ty cap := (unpack CapStruct cap) @% "p";
      setCapP ty val cap := pack ((unpack CapStruct cap) @%[ "p" <- val]);
      getCapOType ty cap := (unpack CapStruct cap) @% "oType";
      setCapOType ty val cap := pack ((unpack CapStruct cap) @%[ "oType" <- val]);
      getCapE ty cap := (unpack CapStruct cap) @% "E";
      setCapE ty val cap := pack ((unpack CapStruct cap) @%[ "E" <- val]);
      getCapB ty cap := (unpack CapStruct cap) @% "B";
      setCapB ty val cap := pack ((unpack CapStruct cap) @%[ "B" <- val]);
      getCapT ty cap := (unpack CapStruct cap) @% "T";
      setCapT ty val cap := pack ((unpack CapStruct cap) @%[ "T" <- val]);
      getCapEFromExp ty exp := ITE (exp >= Const ty (_ 'h"e")) $$(4'h"f") (ZeroExtendTruncLsb _ exp);
      getCapExpFromE ty E := capExpFromE E;
      isSealed t cap := (unpack CapStruct cap) @% "oType" != $0;
      isSentry t cap := let oType := (unpack CapStruct cap) @% "oType" in (oType <= $3) && (oType >= $1);
      isIeSentry t cap := (unpack CapStruct cap) @% "oType" == $2;
      isIdSentry t cap := (unpack CapStruct cap) @% "oType" == $3;
      getOTypeFromIe ty ie := ITE ie $2 $3;
      seal ty val cap := pack ((unpack CapStruct cap) @%[ "oType" <- val]);
      unseal ty cap := pack ((unpack CapStruct cap) @%[ "oType" <- $$(natToWord 3 0)]);
      isSealAddr ty addr isExec := ITE isExec
                                     (((addr >= $1) && (addr <= $3)) || addr == $6 || addr == $7)
                                     ((addr >= $9) && (addr <= $15));
      getCapPerms ty cap := capPerms cap;
      setCapPerms ty perms cap :=
        ( LETC arr : Bit 6 <- encodePerms perms;
          RetE (pack ((unpack CapStruct cap) @%[ "p" <- pack #arr ])) );
      getCapBaseTop ty cap addr := capBaseTop cap addr;
      getCapBounds ty base length := capBounds base length;
    |}%kami_expr.

  Definition ExecRootCapInit := evalExpr (@pack _ CapStruct
                                            (STRUCT {
                                                 "R" ::= Const _ (wzero _);
                                                 "p" ::= Const _ ('b"101111");
                                                 "oType" ::= Const _ (wzero _);
                                                 "E" ::= Const _ (wones _);
                                                 "B" ::= Const _ (wzero _);
                                                 "T" ::= Const _ (_ 'h"100") })%kami_expr).

  Definition DataRootCapInit := evalExpr (@pack _ CapStruct
                                            ( STRUCT {
                                                  "R" ::= Const _ (wzero _);
                                                  "p" ::= Const _ ('b"111111");
                                                  "oType" ::= Const _ (wzero _);
                                                  "E" ::= Const _ (wones _);
                                                  "B" ::= Const _ (wzero _);
                                                  "T" ::= Const _ (_ 'h"100") })%kami_expr).

  Definition SealRootCapInit := evalExpr (@pack _ CapStruct
                                            (STRUCT {
                                                 "R" ::= Const _ (wzero _);
                                                 "p" ::= Const _ ('b"100111");
                                                 "oType" ::= Const _ (wzero _);
                                                 "E" ::= Const _ (wones _);
                                                 "B" ::= Const _ (wzero _);
                                                 "T" ::= Const _ (_ 'h"100") })%kami_expr).

  Definition MtccValInit := (AddrSz 'h"6000").
  Definition MtdcValInit := (AddrSz 'h"2000").
End CapHelpers.

Definition FullCapWithTagKind := STRUCT_TYPE { "tag" :: Bool;
                                               "cap" :: Bit 32;
                                               "val" :: Bit 32 }.

Class CoreConfigParams := {
    prefix : string;
    LgNumMemBytesVal: nat;
    memInitVal: Fin.t (Nat.pow 2 LgNumMemBytesVal * 8) -> word 8;
    regsInitVal: Fin.t 32 -> type FullCapWithTagKind;
    pcCapInitVal: word 32;
    pcCapValidThm: PcCapValid capAccessorsInit pcCapInitVal;
    pcValInitVal: word 32;
    pcValValidThm: truncLsb pcValInitVal = ZToWord 2 0;
    hasTrapVal: bool }.

Section Prefix.
  Context `{coreConfigParams: CoreConfigParams}.
  Lemma pccValidThm: PccValid capAccessorsInit pcCapInitVal pcValInitVal false.
  Proof.
    destruct coreConfigParams.
    constructor; try intro; auto.
  Qed.

  Local Notation "@^ x" := (prefix ++ "_" ++ x)%string (at level 0).
  Local Notation stringify x n := (prefix ++ "_" ++ (x ++ "_" ++ natToHexStr n)%string)%string.

  Definition createMemRFParam (n: nat) : MemBankInit :=
    {|instRqName := stringify "instRq" n;
      loadRqName := stringify "loadRq" n;
      storeRqName := stringify "storeRq" n;
      memArrayName := stringify "memArray" n;
      memRfString := stringify "memArrayFile" n |}.

  Instance procParams : ProcParams :=
    {|Xlen := 32;
      xlenIs32_or_64 := or_introl eq_refl;
      capAccessors := capAccessorsInit;
      pccValid := pccValidThm;
      ExecRootCap := ExecRootCapInit;
      DataRootCap := DataRootCapInit;
      SealRootCap := SealRootCapInit;
      MtccVal := MtccValInit;
      MtdcVal := MtdcValInit;
      IeInit := false;
      MeieInit := false;
      MtieInit := false;
      MsieInit := false;
      supportedExts := [Base];
      extsHasBase := or_introl eq_refl;
      RegIdSz := 5;
      regIdSzIs4_or5 := or_intror eq_refl;
      memBankInits := map createMemRFParam (zeroToN 8);
      lengthMemBankInits := eq_refl;
      isMemAscii := false;
      isMemRfArg := true;
      memInit := memInitVal;
      procName := prefix;
      pcCapReg := @^"pcCap";
      pcValReg := @^"pcVal";
      prevPcCapReg := @^"prevPcCap";
      prevPcValReg := @^"prevPcVal";
      justFenceIReg := @^"justFenceIReg";
      startFenceIReg := @^"startFenceIReg";
      reqJustFenceIReg := @^"reqJustFenceIReg";
      tagRead := @^"tagRead";
      tagWrite := @^"tagWrite";
      tagArray := @^"tagArray";
      memArray := @^"memArray";
      regsRead1 := @^"regsRead1";
      regsRead2 := @^"regsRead2";
      regsWrite := @^"regsWrite";
      regsArray := @^"regsArray";
      isRegsAscii := false;
      isRegsRfArg := true;
      regsRfString := @^"regsArrayFile";
      regsInit := convConstArrayToFunConst regsInitVal;
      hasTrap := hasTrapVal |}.

  Definition getInstEntrySpec (fe: FuncEntry) : list (InstEntry FullOutput) :=
    map (fun ie => {|instName := instName ie;
                     uniqId := uniqId ie;
                     immEncoder := immEncoder ie;
                     spec := fun ty pcc inst cs1 cs2 scr csr =>
                               (LETE val <- spec ie pcc inst cs1 cs2 scr csr;
                                localFunc fe #val)%kami_expr;
                     instProperties := instProperties ie;
                     goodInstEncode := goodInstEncode ie;
                     goodImmEncode := goodImmEncode ie |}) (insts fe).

  Definition specInstEntries := concat (map getInstEntrySpec specFuncUnits).

  Definition specRules : list (forall ty, ActionT ty Void) :=
    specInstBoundsException ::
      (fun ty => specInstIllegalException ty specInstEntries) ::
      map (fun ie ty => specDecExecRule ty scrList csrList ie) specInstEntries.

  Definition specRegs : list RegInitT :=
    (pcCapReg, existT _ (SyntaxKind (Bit CapSz)) (Some (SyntaxConst pcCapInitVal))) ::
      (pcValReg, existT _ (SyntaxKind Addr) (Some (SyntaxConst pcValInitVal))) ::
      (prevPcCapReg, existT _ (SyntaxKind (Bit CapSz)) (Some (SyntaxConst $0))) ::
      (prevPcValReg, existT _ (SyntaxKind Addr) (Some (SyntaxConst $0))) ::
      (regsArray, existT _ _ (Some (SyntaxConst (@convTypeToConst (Array 32 FullCapWithTagKind) regsInitVal)))) ::
      (memArray, existT _ _ (Some (SyntaxConst (@convTypeToConst (Array (NumMemBytes * NumBanks) (Bit 8))
                                                  memInitVal)))) ::
      (tagArray, existT _ _ (Some (SyntaxConst (ConstArray (fun (i: Fin.t NumMemBytes) => false))))) ::
      (map (fun x => (regName (scrRegInfo x), existT _ _ (regInit (scrRegInfo x)))) scrList) ++
      (map (fun x => (regName (csrRegInfo x), existT _ _ (regInit (csrRegInfo x)))) csrList).
End Prefix.
