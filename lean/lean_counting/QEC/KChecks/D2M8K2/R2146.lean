import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8584 = true := by
  decide +kernel

theorem tot8584 : totK PD2M8K2 D2M8K2.t8584 = [0, 161633475954, 448996417066, 286724277883, 27147899983, 0, 0, 0] := by
  decide +kernel

theorem rows8585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8585 = true := by
  decide +kernel

theorem tot8585 : totK PD2M8K2 D2M8K2.t8585 = [0, 174018067377, 477596296789, 238847386284, 12501355884, 0, 0, 0] := by
  decide +kernel

theorem rows8586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8586 = true := by
  decide +kernel

theorem tot8586 : totK PD2M8K2 D2M8K2.t8586 = [0, 172262746753, 455973920861, 261195786966, 23938647543, 0, 0, 0] := by
  decide +kernel

theorem rows8587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8587 = true := by
  decide +kernel

theorem tot8587 : totK PD2M8K2 D2M8K2.t8587 = [0, 179665237015, 474463169833, 233122302181, 14561578123, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
