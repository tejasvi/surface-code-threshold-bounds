import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11356 = true := by
  decide +kernel

theorem tot11356 : totK PD2M8K2 D2M8K2.t11356 = [0, 92584149739, 392970994427, 333974343910, 51708691675, 1095107716, 0, 0] := by
  decide +kernel

theorem rows11357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11357 = true := by
  decide +kernel

theorem tot11357 : totK PD2M8K2 D2M8K2.t11357 = [0, 0, 325496568235, 477691857403, 76025116258, 0, 0, 0] := by
  decide +kernel

theorem rows11358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11358 = true := by
  decide +kernel

theorem tot11358 : totK PD2M8K2 D2M8K2.t11358 = [161815727532, 336030775393, 207702164284, 134390402966, 71419506712, 3882006667, 0, 0] := by
  decide +kernel

theorem rows11359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11359 = true := by
  decide +kernel

theorem tot11359 : totK PD2M8K2 D2M8K2.t11359 = [178263329755, 468624665062, 237899553091, 16263981531, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
