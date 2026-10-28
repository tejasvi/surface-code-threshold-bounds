import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13256 = true := by
  decide +kernel

theorem tot13256 : totK PD2M8K2 D2M8K2.t13256 = [0, 157178836392, 442300145064, 281878261675, 40287006199, 1503593968, 0, 0] := by
  decide +kernel

theorem rows13257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13257 = true := by
  decide +kernel

theorem tot13257 : totK PD2M8K2 D2M8K2.t13257 = [0, 177860025660, 449983035356, 256292948451, 18401906518, 0, 0, 0] := by
  decide +kernel

theorem rows13258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13258 = true := by
  decide +kernel

theorem tot13258 : totK PD2M8K2 D2M8K2.t13258 = [0, 78976767030, 349454944820, 382544155337, 79683553073, 1197396724, 0, 0] := by
  decide +kernel

theorem rows13259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13259 = true := by
  decide +kernel

theorem tot13259 : totK PD2M8K2 D2M8K2.t13259 = [0, 0, 228606380472, 483054446290, 165350795310, 9473607896, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
