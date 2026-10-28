import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13380 = true := by
  decide +kernel

theorem tot13380 : totK PD2M8K2 D2M8K2.t13380 = [0, 0, 175637012910, 485530172898, 228907423004, 14633607569, 0, 0] := by
  decide +kernel

theorem rows13381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13381 = true := by
  decide +kernel

theorem tot13381 : totK PD2M8K2 D2M8K2.t13381 = [0, 0, 191392459095, 477397826883, 211799337833, 6604758981, 0, 0] := by
  decide +kernel

theorem rows13382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13382 = true := by
  decide +kernel

theorem tot13382 : totK PD2M8K2 D2M8K2.t13382 = [0, 0, 177354339808, 466567577503, 243736446461, 18246066036, 0, 0] := by
  decide +kernel

theorem rows13383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13383 = true := by
  decide +kernel

theorem tot13383 : totK PD2M8K2 D2M8K2.t13383 = [0, 0, 203693634974, 477373878802, 190552817390, 7651299259, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
