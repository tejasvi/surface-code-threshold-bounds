import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8580 = true := by
  decide +kernel

theorem tot8580 : totK PD2M8K2 D2M8K2.t8580 = [0, 186702968659, 467707904875, 216171824346, 17064697274, 0, 0, 0] := by
  decide +kernel

theorem rows8581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8581 = true := by
  decide +kernel

theorem tot8581 : totK PD2M8K2 D2M8K2.t8581 = [0, 187949819902, 482818002036, 215810807240, 9934316065, 0, 0, 0] := by
  decide +kernel

theorem rows8582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8582 = true := by
  decide +kernel

theorem tot8582 : totK PD2M8K2 D2M8K2.t8582 = [0, 83973255428, 363109588110, 359499703178, 64382808057, 1239866073, 0, 0] := by
  decide +kernel

theorem rows8583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8583 = true := by
  decide +kernel

theorem tot8583 : totK PD2M8K2 D2M8K2.t8583 = [0, 93391851717, 382190267184, 384892450328, 42549630685, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
