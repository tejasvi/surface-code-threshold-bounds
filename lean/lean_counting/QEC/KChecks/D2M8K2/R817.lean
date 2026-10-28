import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3268 = true := by
  decide +kernel

theorem tot3268 : totK PD2M8K2 D2M8K2.t3268 = [0, 172547771176, 446538101586, 267228127031, 24835268271, 0, 0, 0] := by
  decide +kernel

theorem rows3269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3269 = true := by
  decide +kernel

theorem tot3269 : totK PD2M8K2 D2M8K2.t3269 = [0, 181693712562, 476546511727, 248545492672, 12868511826, 0, 0, 0] := by
  decide +kernel

theorem rows3270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3270 = true := by
  decide +kernel

theorem tot3270 : totK PD2M8K2 D2M8K2.t3270 = [0, 0, 256329288871, 483292373449, 126978227235, 2243379097, 0, 0] := by
  decide +kernel

theorem rows3271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3271 = true := by
  decide +kernel

theorem tot3271 : totK PD2M8K2 D2M8K2.t3271 = [0, 0, 177435023298, 468096595163, 206487663542, 9903560961, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
