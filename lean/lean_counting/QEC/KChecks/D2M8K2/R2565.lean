import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10260 = true := by
  decide +kernel

theorem tot10260 : totK PD2M8K2 D2M8K2.t10260 = [0, 0, 193116888813, 479730783189, 224813970619, 10549918326, 0, 0] := by
  decide +kernel

theorem rows10261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10261 = true := by
  decide +kernel

theorem tot10261 : totK PD2M8K2 D2M8K2.t10261 = [0, 0, 19691318959, 351992481244, 460835182934, 69035073432, 0, 0] := by
  decide +kernel

theorem rows10262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10262 = true := by
  decide +kernel

theorem tot10262 : totK PD2M8K2 D2M8K2.t10262 = [0, 24628393174, 31501293142, 175233072928, 451489299105, 183393117114, 6672335165, 0] := by
  decide +kernel

theorem rows10263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10263 = true := by
  decide +kernel

theorem tot10263 : totK PD2M8K2 D2M8K2.t10263 = [0, 212851275856, 480554904716, 188220587073, 7625838032, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
