import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15288 = true := by
  decide +kernel

theorem tot15288 : totK PD2M8K2 D2M8K2.t15288 = [0, 0, 168570250111, 469517166739, 248966374801, 12290298881, 0, 0] := by
  decide +kernel

theorem rows15289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15289 = true := by
  decide +kernel

theorem tot15289 : totK PD2M8K2 D2M8K2.t15289 = [0, 0, 176255007393, 467325038248, 236685962576, 12526962336, 0, 0] := by
  decide +kernel

theorem rows15290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15290 = true := by
  decide +kernel

theorem tot15290 : totK PD2M8K2 D2M8K2.t15290 = [0, 0, 0, 295960334043, 515049799341, 73896097177, 1096505104, 0] := by
  decide +kernel

theorem rows15291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15291 = true := by
  decide +kernel

theorem tot15291 : totK PD2M8K2 D2M8K2.t15291 = [0, 0, 166428564004, 454176680427, 263935273943, 22219374086, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
