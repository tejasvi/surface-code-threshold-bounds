import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15900 = true := by
  decide +kernel

theorem tot15900 : totK PD2M8K2 D2M8K2.t15900 = [0, 176145016691, 439006912060, 262306424382, 29912490296, 0, 0, 0] := by
  decide +kernel

theorem rows15901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15901 = true := by
  decide +kernel

theorem tot15901 : totK PD2M8K2 D2M8K2.t15901 = [0, 144292785163, 458283447308, 280284518655, 19973335067, 0, 0, 0] := by
  decide +kernel

theorem rows15902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15902 = true := by
  decide +kernel

theorem tot15902 : totK PD2M8K2 D2M8K2.t15902 = [0, 0, 283720344966, 518938710780, 101431294381, 1096505104, 0, 0] := by
  decide +kernel

theorem rows15903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15903 = true := by
  decide +kernel

theorem tot15903 : totK PD2M8K2 D2M8K2.t15903 = [0, 0, 204477645831, 495598461928, 178475516941, 5253830308, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
