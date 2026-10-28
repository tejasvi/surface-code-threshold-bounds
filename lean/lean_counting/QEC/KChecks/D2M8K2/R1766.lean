import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7064 = true := by
  decide +kernel

theorem tot7064 : totK PD2M8K2 D2M8K2.t7064 = [0, 0, 279767396017, 509699120213, 97471056071, 1096505104, 0, 0] := by
  decide +kernel

theorem rows7065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7065 = true := by
  decide +kernel

theorem tot7065 : totK PD2M8K2 D2M8K2.t7065 = [0, 103483345677, 344962334495, 347721154874, 95925078918, 3884009855, 0, 0] := by
  decide +kernel

theorem rows7066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7066 = true := by
  decide +kernel

theorem tot7066 : totK PD2M8K2 D2M8K2.t7066 = [0, 175575105670, 438169911754, 249058125084, 25444392879, 0, 0, 0] := by
  decide +kernel

theorem rows7067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7067 = true := by
  decide +kernel

theorem tot7067 : totK PD2M8K2 D2M8K2.t7067 = [0, 136201632296, 439751402327, 304534183123, 26497149627, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
