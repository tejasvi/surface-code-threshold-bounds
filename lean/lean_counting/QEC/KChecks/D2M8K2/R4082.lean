import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16328 = true := by
  decide +kernel

theorem tot16328 : totK PD2M8K2 D2M8K2.t16328 = [0, 0, 159570784420, 418771836785, 271967983603, 35424330136, 1096505104, 0] := by
  decide +kernel

theorem rows16329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16329 = true := by
  decide +kernel

theorem tot16329 : totK PD2M8K2 D2M8K2.t16329 = [0, 0, 84833159912, 390600757805, 386931852299, 43670617546, 0, 0] := by
  decide +kernel

theorem rows16330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16330 = true := by
  decide +kernel

theorem tot16330 : totK PD2M8K2 D2M8K2.t16330 = [0, 0, 160092021320, 455940169965, 263536374265, 23400535109, 0, 0] := by
  decide +kernel

theorem rows16331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16331 = true := by
  decide +kernel

theorem tot16331 : totK PD2M8K2 D2M8K2.t16331 = [0, 0, 182261201038, 467188332773, 251528757169, 17857893232, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
