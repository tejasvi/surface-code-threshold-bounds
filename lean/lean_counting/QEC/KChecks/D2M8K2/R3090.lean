import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12360 = true := by
  decide +kernel

theorem tot12360 : totK PD2M8K2 D2M8K2.t12360 = [0, 0, 304538717238, 495651539248, 91244940480, 1096505104, 0, 0] := by
  decide +kernel

theorem rows12361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12361 = true := by
  decide +kernel

theorem tot12361 : totK PD2M8K2 D2M8K2.t12361 = [0, 86868443710, 301564955086, 388705488079, 110153910190, 3884009855, 0, 0] := by
  decide +kernel

theorem rows12362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12362 = true := by
  decide +kernel

theorem tot12362 : totK PD2M8K2 D2M8K2.t12362 = [0, 162639029444, 484294677542, 235806194042, 6599752875, 0, 0, 0] := by
  decide +kernel

theorem rows12363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12363 = true := by
  decide +kernel

theorem tot12363 : totK PD2M8K2 D2M8K2.t12363 = [0, 72316683187, 331498736024, 392131192678, 80443292936, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
