import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8308 = true := by
  decide +kernel

theorem tot8308 : totK PD2M8K2 D2M8K2.t8308 = [0, 0, 239416420794, 476313159942, 156758476514, 8462178015, 0, 0] := by
  decide +kernel

theorem rows8309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8309 = true := by
  decide +kernel

theorem tot8309 : totK PD2M8K2 D2M8K2.t8309 = [0, 112539209047, 354489248771, 319074563895, 80030919671, 3472187823, 0, 0] := by
  decide +kernel

theorem rows8310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8310 = true := by
  decide +kernel

theorem tot8310 : totK PD2M8K2 D2M8K2.t8310 = [0, 201098925063, 474098695032, 210569245099, 13258498675, 0, 0, 0] := by
  decide +kernel

theorem rows8311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8311 = true := by
  decide +kernel

theorem tot8311 : totK PD2M8K2 D2M8K2.t8311 = [0, 90563211903, 397355581879, 332250259852, 43266001661, 1053411165, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
