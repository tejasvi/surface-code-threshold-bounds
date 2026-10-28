import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14040 = true := by
  decide +kernel

theorem tot14040 : totK PD2M8K2 D2M8K2.t14040 = [0, 19168591844, 335069042392, 456334160025, 83652989383, 1096505104, 0, 0] := by
  decide +kernel

theorem rows14041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14041 = true := by
  decide +kernel

theorem tot14041 : totK PD2M8K2 D2M8K2.t14041 = [0, 78759588782, 313800159312, 382551068084, 108306719192, 3884009855, 0, 0] := by
  decide +kernel

theorem rows14042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14042 = true := by
  decide +kernel

theorem tot14042 : totK PD2M8K2 D2M8K2.t14042 = [0, 158639843840, 451227965281, 277537373362, 27553238446, 0, 0, 0] := by
  decide +kernel

theorem rows14043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14043 = true := by
  decide +kernel

theorem tot14043 : totK PD2M8K2 D2M8K2.t14043 = [0, 181257342552, 467855012343, 249957388437, 16151432619, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
