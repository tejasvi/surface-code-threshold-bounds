import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t500 = true := by
  decide +kernel

theorem tot500 : totK PD2M8K2 D2M8K2.t500 = [0, 0, 212329331437, 493422092339, 177783399744, 6177034858, 0, 0] := by
  decide +kernel

theorem rows501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t501 = true := by
  decide +kernel

theorem tot501 : totK PD2M8K2 D2M8K2.t501 = [0, 179150813341, 404722584379, 213560670656, 91036459569, 10382715737, 0, 0] := by
  decide +kernel

theorem rows502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t502 = true := by
  decide +kernel

theorem tot502 : totK PD2M8K2 D2M8K2.t502 = [0, 172653135873, 453475125349, 228068872696, 14902632746, 0, 0, 0] := by
  decide +kernel

theorem rows503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t503 = true := by
  decide +kernel

theorem tot503 : totK PD2M8K2 D2M8K2.t503 = [0, 64379915147, 329050803800, 409716588051, 82702775872, 1334361349, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
