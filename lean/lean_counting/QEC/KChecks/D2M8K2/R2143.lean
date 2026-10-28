import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8572 = true := by
  decide +kernel

theorem tot8572 : totK PD2M8K2 D2M8K2.t8572 = [77545050390, 327430618112, 370612834387, 98927239531, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows8573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8573 = true := by
  decide +kernel

theorem tot8573 : totK PD2M8K2 D2M8K2.t8573 = [175954106784, 432465192426, 265811305197, 30172243562, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8574 = true := by
  decide +kernel

theorem tot8574 : totK PD2M8K2 D2M8K2.t8574 = [155067254286, 462100856508, 266863617584, 18533599098, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8575 = true := by
  decide +kernel

theorem tot8575 : totK PD2M8K2 D2M8K2.t8575 = [0, 283972651401, 517556937931, 103591757145, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
