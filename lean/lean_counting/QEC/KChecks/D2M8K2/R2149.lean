import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8596 = true := by
  decide +kernel

theorem tot8596 : totK PD2M8K2 D2M8K2.t8596 = [152780043054, 356087120397, 244738085958, 124397021282, 13552632951, 0, 0, 0] := by
  decide +kernel

theorem rows8597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8597 = true := by
  decide +kernel

theorem tot8597 : totK PD2M8K2 D2M8K2.t8597 = [170821955368, 463360618961, 246218379367, 17044607505, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8598 = true := by
  decide +kernel

theorem tot8598 : totK PD2M8K2 D2M8K2.t8598 = [0, 270410381847, 509342670083, 108938247518, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows8599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8599 = true := by
  decide +kernel

theorem tot8599 : totK PD2M8K2 D2M8K2.t8599 = [179148547845, 429005574109, 277173918414, 34651170248, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
