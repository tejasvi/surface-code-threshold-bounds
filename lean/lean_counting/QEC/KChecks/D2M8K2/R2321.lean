import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9284 = true := by
  decide +kernel

theorem tot9284 : totK PD2M8K2 D2M8K2.t9284 = [0, 179935757967, 468795662367, 235370671787, 13176583453, 0, 0, 0] := by
  decide +kernel

theorem rows9285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9285 = true := by
  decide +kernel

theorem tot9285 : totK PD2M8K2 D2M8K2.t9285 = [0, 0, 316781402287, 458067413486, 73122882152, 1053411165, 0, 0] := by
  decide +kernel

theorem rows9286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9286 = true := by
  decide +kernel

theorem tot9286 : totK PD2M8K2 D2M8K2.t9286 = [0, 80954891220, 331470063022, 356414451292, 86887055972, 3667207281, 0, 0] := by
  decide +kernel

theorem rows9287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9287 = true := by
  decide +kernel

theorem tot9287 : totK PD2M8K2 D2M8K2.t9287 = [0, 174320196350, 448732106297, 275531205444, 27889506977, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
