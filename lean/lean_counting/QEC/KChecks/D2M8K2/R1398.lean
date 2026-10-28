import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5592 = true := by
  decide +kernel

theorem tot5592 : totK PD2M8K2 D2M8K2.t5592 = [0, 0, 284092386124, 485543365563, 82700472680, 1239866073, 0, 0] := by
  decide +kernel

theorem rows5593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5593 = true := by
  decide +kernel

theorem tot5593 : totK PD2M8K2 D2M8K2.t5593 = [0, 159547220069, 457388821138, 264100332812, 24496742831, 0, 0, 0] := by
  decide +kernel

theorem rows5594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5594 = true := by
  decide +kernel

theorem tot5594 : totK PD2M8K2 D2M8K2.t5594 = [0, 177409773268, 444053750821, 252942228637, 20986626046, 0, 0, 0] := by
  decide +kernel

theorem rows5595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5595 = true := by
  decide +kernel

theorem tot5595 : totK PD2M8K2 D2M8K2.t5595 = [0, 86744073879, 362924503129, 350815504510, 63847269547, 1171084559, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
