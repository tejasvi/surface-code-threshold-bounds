import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t732 = true := by
  decide +kernel

theorem tot732 : totK PD2M8K2 D2M8K2.t732 = [0, 209711071395, 489508595845, 178534326246, 9569386829, 0, 0, 0] := by
  decide +kernel

theorem rows733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t733 = true := by
  decide +kernel

theorem tot733 : totK PD2M8K2 D2M8K2.t733 = [171501308715, 447691895816, 263151285809, 29639382207, 0, 0, 0, 0] := by
  decide +kernel

theorem rows734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t734 = true := by
  decide +kernel

theorem tot734 : totK PD2M8K2 D2M8K2.t734 = [163452225702, 435067156993, 277280442215, 29733725516, 0, 0, 0, 0] := by
  decide +kernel

theorem rows735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t735 = true := by
  decide +kernel

theorem tot735 : totK PD2M8K2 D2M8K2.t735 = [89753051296, 372374910175, 369148310058, 63168648690, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
