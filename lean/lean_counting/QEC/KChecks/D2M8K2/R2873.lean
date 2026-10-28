import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11492 = true := by
  decide +kernel

theorem tot11492 : totK PD2M8K2 D2M8K2.t11492 = [0, 0, 178017608236, 480273330692, 224748995917, 10874830660, 0, 0] := by
  decide +kernel

theorem rows11493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11493 = true := by
  decide +kernel

theorem tot11493 : totK PD2M8K2 D2M8K2.t11493 = [0, 0, 0, 388180732074, 446900788599, 42078563695, 0, 0] := by
  decide +kernel

theorem rows11494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11494 = true := by
  decide +kernel

theorem tot11494 : totK PD2M8K2 D2M8K2.t11494 = [0, 0, 152075873407, 376100230491, 284875203988, 65239599075, 1271866555, 0] := by
  decide +kernel

theorem rows11495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11495 = true := by
  decide +kernel

theorem tot11495 : totK PD2M8K2 D2M8K2.t11495 = [0, 0, 165965302331, 443085944627, 274946603111, 17769301722, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
