import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3400 = true := by
  decide +kernel

theorem tot3400 : totK PD2M8K2 D2M8K2.t3400 = [0, 184499509902, 450651831429, 252555854705, 27096379411, 0, 0, 0] := by
  decide +kernel

theorem rows3401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3401 = true := by
  decide +kernel

theorem tot3401 : totK PD2M8K2 D2M8K2.t3401 = [0, 194778771198, 472173248503, 227563223423, 14674320615, 0, 0, 0] := by
  decide +kernel

theorem rows3402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3402 = true := by
  decide +kernel

theorem tot3402 : totK PD2M8K2 D2M8K2.t3402 = [0, 56674804355, 328514491610, 413825755550, 96100055403, 1268739303, 0, 0] := by
  decide +kernel

theorem rows3403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3403 = true := by
  decide +kernel

theorem tot3403 : totK PD2M8K2 D2M8K2.t3403 = [0, 0, 219565602585, 484553170424, 171655399952, 7375937412, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
