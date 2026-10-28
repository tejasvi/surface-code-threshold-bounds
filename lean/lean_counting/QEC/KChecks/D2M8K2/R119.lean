import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t476 = true := by
  decide +kernel

theorem tot476 : totK PD2M8K2 D2M8K2.t476 = [0, 0, 0, 310033202808, 435435988423, 81190752622, 1275377855, 0] := by
  decide +kernel

theorem rows477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t477 = true := by
  decide +kernel

theorem tot477 : totK PD2M8K2 D2M8K2.t477 = [0, 0, 161650129653, 466805077430, 236590010853, 14537615011, 0, 0] := by
  decide +kernel

theorem rows478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t478 = true := by
  decide +kernel

theorem tot478 : totK PD2M8K2 D2M8K2.t478 = [0, 0, 186035409889, 466319780649, 205607570970, 12174977592, 0, 0] := by
  decide +kernel

theorem rows479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t479 = true := by
  decide +kernel

theorem tot479 : totK PD2M8K2 D2M8K2.t479 = [0, 0, 207034052494, 480799622101, 189162491138, 10088849077, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
