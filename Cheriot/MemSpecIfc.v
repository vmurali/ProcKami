Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.

Section MemSpecIfc.
  Context `{procParams: ProcParams}.

  Definition InstRet := STRUCT_TYPE {
                            "inst" :: Inst;
                            "badLower16?" :: Bool;
                            "error?" :: Bool;
                            "fault?" :: Bool;
                            "justFenceI?" :: Bool }.

  Definition DataRet := STRUCT_TYPE {
                            "data" :: FullCapWithTag;
                            "lowestByte" :: Bit (Nat.log2_up NumBanks);
                            "dataError?" :: Bool;
                            "dataFault?" :: Bool;
                            "tagError?" :: Bool;
                            "tagFault?" :: Bool }.

  Class MemSpecIfc := {
      instReq: forall ty, Addr @# ty -> ActionT ty InstRet;
      loadStoreReq: forall ty, Bool @# ty (* isStore *) -> Addr @# ty -> MemSize @# ty ->
                               Bool @# ty (* isCap *) -> FullCapWithTag @# ty -> Bool @# ty (* signed *) ->
                               ActionT ty DataRet }.
End MemSpecIfc.      
