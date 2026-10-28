import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3172 = true := by
  decide +kernel

theorem tot3172 : totK PA10K2 A10K2.t3172 = [0, 0, 0, 0, 860045703075, 2258742507671, 1496472402890, 224116381574, 6439430839, 0] := by
  decide +kernel

theorem rows3173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3173 = true := by
  decide +kernel

theorem tot3173 : totK PA10K2 A10K2.t3173 = [0, 0, 0, 548781731263, 1836482784751, 1800398476626, 602980204462, 60816768629, 0, 0] := by
  decide +kernel

theorem rows3174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3174 = true := by
  decide +kernel

theorem tot3174 : totK PA10K2 A10K2.t3174 = [0, 0, 0, 328627686157, 1511950483921, 2130334812719, 865273735906, 62012163500, 0, 0] := by
  decide +kernel

theorem rows3175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3175 = true := by
  decide +kernel

theorem tot3175 : totK PA10K2 A10K2.t3175 = [0, 0, 0, 0, 602750094231, 2026159118991, 1823677322607, 387463442136, 12132367858, 0] := by
  decide +kernel

end QECKChecks.A10K2
