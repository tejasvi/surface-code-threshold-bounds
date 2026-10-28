import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7540 = true := by
  decide +kernel

theorem tot7540 : totK PD2M8K2 D2M8K2.t7540 = [0, 0, 0, 338044850963, 509346037702, 67192213626, 0, 0] := by
  decide +kernel

theorem rows7541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7541 = true := by
  decide +kernel

theorem tot7541 : totK PD2M8K2 D2M8K2.t7541 = [0, 0, 157866674996, 406600476303, 285054589091, 64770193485, 1415142070, 0] := by
  decide +kernel

theorem rows7542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7542 = true := by
  decide +kernel

theorem tot7542 : totK PD2M8K2 D2M8K2.t7542 = [0, 0, 197822947137, 460024122597, 225335784999, 15006926277, 0, 0] := by
  decide +kernel

theorem rows7543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7543 = true := by
  decide +kernel

theorem tot7543 : totK PD2M8K2 D2M8K2.t7543 = [0, 0, 60268117739, 406416057167, 389591750385, 51543803657, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
