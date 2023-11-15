Require Import Kami.AllNotations ProcKami.Cheriot.Types ProcKami.Cheriot.BankedMem.

Section Run.
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Variable uncompressFn: CompInst @# ty -> Maybe Inst @# ty.

  Notation "'LETAE' name <- act ; cont " :=
    (LetAction (convertLetExprSyntax_ActionT act) (fun name => cont))
      (at level 13, right associativity, name at level 99) : kami_action_scope.
  Notation "'LETAE' name : t <- act ; cont " :=
    (LetAction (k := t) (convertLetExprSyntax_ActionT act) (fun name => cont))
      (at level 13, right associativity, name at level 99) : kami_action_scope.
  
  Definition fetch: ActionT ty (Maybe Inst) :=
    ( Read pcCap : Cap <- pcCapReg;
      Read pcVal : Addr <- pcValReg;
      LETA rawInst <- instReq #pcVal;
      LET notCompressed <- isInstNotCompressed #rawInst;
      LETAE baseTop <- getCapBaseTop capAccessors #pcCap #pcVal;
      LET baseBound <- #pcVal >= (#baseTop @% "base");
      LET topBound <- ZeroExtend 1 #pcVal + (ITE #notCompressed $4 $2) <= (#baseTop @% "top");
      Ret (STRUCT { "valid" ::= #baseBound && #topBound;
                    "data" ::= #rawInst }: Maybe Inst @# _) ).

  Definition UncompressOut := STRUCT_TYPE {
                                  "inst" :: Inst;
                                  "exception?" :: Bool;
                                  "exceptionCause" :: Data }.

  Definition uncompressValid (maybeInst: Maybe Inst @# ty) : ActionT ty UncompressOut :=
    ( LET notCompressed <- isInstNotCompressed (maybeInst @% "data");      
      LET maybeUncompressedInst <- uncompressFn (ZeroExtendTruncLsb CompInstSz (maybeInst @% "data"));
      Ret (STRUCT { "inst" ::= ITE #notCompressed (maybeInst @% "data") (#maybeUncompressedInst @% "data");
                    "exception?" ::= !((maybeInst @% "valid") &&
                                         (#notCompressed || (#maybeUncompressedInst @% "valid")));
                    "exceptionCause" ::= (ITE (maybeInst @% "valid") $InstIllegal $CapBoundsViolation) }
          : UncompressOut @# _)).

  Definition uncompressInvalid (maybeInst: Maybe Inst @# ty) : ActionT ty UncompressOut :=
    ( LET notCompressed <- isInstNotCompressed (maybeInst @% "data");
      Ret (STRUCT { "inst" ::= maybeInst @% "data";
                    "exception?" ::= !((maybeInst @% "valid") && #notCompressed);
                    "exceptionCause" ::= (ITE (maybeInst @% "valid") $InstIllegal $CapBoundsViolation) }
          : UncompressOut @# _)).

  Definition uncompress (maybeInst: Maybe Inst @# ty): ActionT ty UncompressOut :=
    if compressed
    then uncompressValid maybeInst
    else uncompressInvalid maybeInst.
End Run.
