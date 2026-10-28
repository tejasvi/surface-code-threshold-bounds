import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8628 = true := by
  decide +kernel

theorem tot8628 : totK PD2M8K2 D2M8K2.t8628 = [0, 0, 338729317161, 472613506501, 70802279214, 0, 0, 0] := by
  decide +kernel

theorem rows8629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8629 = true := by
  decide +kernel

theorem tot8629 : totK PD2M8K2 D2M8K2.t8629 = [154132651746, 379554926295, 163390525948, 109907448211, 71419506712, 3882006667, 0, 0] := by
  decide +kernel

theorem rows8630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8630 = true := by
  decide +kernel

theorem tot8630 : totK PD2M8K2 D2M8K2.t8630 = [172720967628, 455530246756, 267210654252, 22271361525, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8631 = true := by
  decide +kernel

theorem tot8631 : totK PD2M8K2 D2M8K2.t8631 = [0, 278658566084, 506124810801, 110983972062, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
