import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10168 = true := by
  decide +kernel

theorem tot10168 : totK PD2M8K2 D2M8K2.t10168 = [0, 177429949355, 454489634525, 253747596300, 18280866868, 0, 0, 0] := by
  decide +kernel

theorem rows10169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10169 = true := by
  decide +kernel

theorem tot10169 : totK PD2M8K2 D2M8K2.t10169 = [0, 72217345795, 335877459661, 413539482114, 89759270481, 1198073392, 0, 0] := by
  decide +kernel

theorem rows10170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10170 = true := by
  decide +kernel

theorem tot10170 : totK PD2M8K2 D2M8K2.t10170 = [0, 0, 211241973610, 471902565253, 186207261930, 12010829577, 0, 0] := by
  decide +kernel

theorem rows10171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10171 = true := by
  decide +kernel

theorem tot10171 : totK PD2M8K2 D2M8K2.t10171 = [0, 172675080252, 451742511454, 269314515689, 36491971766, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
