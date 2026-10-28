import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9956 = true := by
  decide +kernel

theorem tot9956 : totK PD2M8K2 D2M8K2.t9956 = [0, 0, 57044925816, 324739767020, 424957510331, 83088332890, 1369150432, 0] := by
  decide +kernel

theorem rows9957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9957 = true := by
  decide +kernel

theorem tot9957 : totK PD2M8K2 D2M8K2.t9957 = [0, 0, 72166536374, 371447286714, 410761421687, 37333913254, 0, 0] := by
  decide +kernel

theorem rows9958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9958 = true := by
  decide +kernel

theorem tot9958 : totK PD2M8K2 D2M8K2.t9958 = [0, 0, 180888637223, 474267567737, 250444635243, 12959196712, 0, 0] := by
  decide +kernel

theorem rows9959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9959 = true := by
  decide +kernel

theorem tot9959 : totK PD2M8K2 D2M8K2.t9959 = [0, 0, 171376929702, 467054714318, 235696119697, 13535101234, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
