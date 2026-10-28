import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8328 = true := by
  decide +kernel

theorem tot8328 : totK PD2M8K2 D2M8K2.t8328 = [156922691767, 459369005120, 273002733981, 18722719276, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8329 = true := by
  decide +kernel

theorem tot8329 : totK PD2M8K2 D2M8K2.t8329 = [0, 225662191335, 498721333573, 158381939031, 3544300177, 0, 0, 0] := by
  decide +kernel

theorem rows8330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8330 = true := by
  decide +kernel

theorem tot8330 : totK PD2M8K2 D2M8K2.t8330 = [86654048599, 282771731512, 372699228984, 135782297297, 9706385084, 0, 0, 0] := by
  decide +kernel

theorem rows8331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8331 = true := by
  decide +kernel

theorem tot8331 : totK PD2M8K2 D2M8K2.t8331 = [168581110379, 459503082075, 255233630288, 20974417125, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
