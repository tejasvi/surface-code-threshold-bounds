import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9504 = true := by
  decide +kernel

theorem tot9504 : totK PD2M8K2 D2M8K2.t9504 = [0, 152755763334, 434871416137, 298007982708, 25601794067, 0, 0, 0] := by
  decide +kernel

theorem rows9505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9505 = true := by
  decide +kernel

theorem tot9505 : totK PD2M8K2 D2M8K2.t9505 = [0, 87009114645, 410037224521, 380835518385, 43254345953, 0, 0, 0] := by
  decide +kernel

theorem rows9506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9506 = true := by
  decide +kernel

theorem tot9506 : totK PD2M8K2 D2M8K2.t9506 = [0, 82779818473, 336315389842, 384000169634, 92063326591, 1415142070, 0, 0] := by
  decide +kernel

theorem rows9507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9507 = true := by
  decide +kernel

theorem tot9507 : totK PD2M8K2 D2M8K2.t9507 = [0, 163437005136, 444267810398, 277685592289, 28294506119, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
