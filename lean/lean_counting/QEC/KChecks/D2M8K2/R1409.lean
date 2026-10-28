import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5636 = true := by
  decide +kernel

theorem tot5636 : totK PD2M8K2 D2M8K2.t5636 = [194625098643, 464820635725, 202720992168, 13744464328, 19249816803, 2814597007, 0, 0] := by
  decide +kernel

theorem rows5637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5637 = true := by
  decide +kernel

theorem tot5637 : totK PD2M8K2 D2M8K2.t5637 = [198460510156, 461967563262, 208748408376, 12526078277, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5638 = true := by
  decide +kernel

theorem tot5638 : totK PD2M8K2 D2M8K2.t5638 = [23491738873, 311877154532, 459599117942, 100239170603, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows5639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5639 = true := by
  decide +kernel

theorem tot5639 : totK PD2M8K2 D2M8K2.t5639 = [81414278263, 360031575749, 416354649140, 54490680700, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
