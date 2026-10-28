import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9728 = true := by
  decide +kernel

theorem tot9728 : totK PD2M8K2 D2M8K2.t9728 = [0, 125944722637, 400294168756, 361953306186, 44779196478, 0, 0, 0] := by
  decide +kernel

theorem rows9729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9729 = true := by
  decide +kernel

theorem tot9729 : totK PD2M8K2 D2M8K2.t9729 = [0, 182550177998, 454272621618, 233998823932, 15486256252, 0, 0, 0] := by
  decide +kernel

theorem rows9730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9730 = true := by
  decide +kernel

theorem tot9730 : totK PD2M8K2 D2M8K2.t9730 = [0, 112057722785, 438979652473, 336795890164, 37100678404, 0, 0, 0] := by
  decide +kernel

theorem rows9731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9731 = true := by
  decide +kernel

theorem tot9731 : totK PD2M8K2 D2M8K2.t9731 = [0, 0, 172444594106, 439381599458, 250959326713, 21156369654, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
