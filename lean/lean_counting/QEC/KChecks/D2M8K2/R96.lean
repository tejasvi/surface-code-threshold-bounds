import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t384 = true := by
  decide +kernel

theorem tot384 : totK PD2M8K2 D2M8K2.t384 = [54719687369, 213513445215, 397189318429, 225031919179, 17449007145, 0, 0, 0] := by
  decide +kernel

theorem rows385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t385 = true := by
  decide +kernel

theorem tot385 : totK PD2M8K2 D2M8K2.t385 = [195605201685, 478714377854, 208532713325, 9852138406, 0, 0, 0, 0] := by
  decide +kernel

theorem rows386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t386 = true := by
  decide +kernel

theorem tot386 : totK PD2M8K2 D2M8K2.t386 = [159278365545, 455685739992, 255260798414, 16433749035, 0, 0, 0, 0] := by
  decide +kernel

theorem rows387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t387 = true := by
  decide +kernel

theorem tot387 : totK PD2M8K2 D2M8K2.t387 = [0, 273358090270, 499738948535, 113514508249, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
