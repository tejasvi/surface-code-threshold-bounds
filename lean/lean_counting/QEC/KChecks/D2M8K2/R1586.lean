import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6344 = true := by
  decide +kernel

theorem tot6344 : totK PD2M8K2 D2M8K2.t6344 = [0, 155788554387, 435045465690, 285406245256, 39688938144, 0, 0, 0] := by
  decide +kernel

theorem rows6345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6345 = true := by
  decide +kernel

theorem tot6345 : totK PD2M8K2 D2M8K2.t6345 = [0, 164018256128, 444261762467, 263222304409, 22880576093, 0, 0, 0] := by
  decide +kernel

theorem rows6346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6346 = true := by
  decide +kernel

theorem tot6346 : totK PD2M8K2 D2M8K2.t6346 = [0, 90848937699, 411659141111, 361631488296, 41177765898, 0, 0, 0] := by
  decide +kernel

theorem rows6347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6347 = true := by
  decide +kernel

theorem tot6347 : totK PD2M8K2 D2M8K2.t6347 = [0, 35000067963, 277650803209, 466690898663, 119252229851, 3880716147, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
