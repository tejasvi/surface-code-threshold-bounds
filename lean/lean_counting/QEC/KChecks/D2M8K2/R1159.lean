import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4636 = true := by
  decide +kernel

theorem tot4636 : totK PD2M8K2 D2M8K2.t4636 = [0, 0, 167860605786, 449054242764, 279358195821, 24056297969, 0, 0] := by
  decide +kernel

theorem rows4637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4637 = true := by
  decide +kernel

theorem tot4637 : totK PD2M8K2 D2M8K2.t4637 = [0, 0, 159406523291, 469423859883, 276058585170, 20416537321, 0, 0] := by
  decide +kernel

theorem rows4638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4638 = true := by
  decide +kernel

theorem tot4638 : totK PD2M8K2 D2M8K2.t4638 = [0, 0, 0, 171736080876, 446159871690, 252308834846, 23322377560, 0] := by
  decide +kernel

theorem rows4639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4639 = true := by
  decide +kernel

theorem tot4639 : totK PD2M8K2 D2M8K2.t4639 = [0, 0, 0, 238956842805, 511703889275, 160374782813, 2655503019, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
