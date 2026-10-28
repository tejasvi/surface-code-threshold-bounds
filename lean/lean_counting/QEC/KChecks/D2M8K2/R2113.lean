import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8452 = true := by
  decide +kernel

theorem tot8452 : totK PD2M8K2 D2M8K2.t8452 = [0, 174028750943, 397757039197, 217778201735, 83874987784, 8757608180, 0, 0] := by
  decide +kernel

theorem rows8453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8453 = true := by
  decide +kernel

theorem tot8453 : totK PD2M8K2 D2M8K2.t8453 = [0, 173239196915, 460688238026, 238403355524, 17044607505, 0, 0, 0] := by
  decide +kernel

theorem rows8454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8454 = true := by
  decide +kernel

theorem tot8454 : totK PD2M8K2 D2M8K2.t8454 = [0, 70056195118, 315536846414, 393487848473, 92457548296, 1369150432, 0, 0] := by
  decide +kernel

theorem rows8455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8455 = true := by
  decide +kernel

theorem tot8455 : totK PD2M8K2 D2M8K2.t8455 = [0, 25919952959, 331997911866, 475246586063, 61773758501, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
