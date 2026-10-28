import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t604 = true := by
  decide +kernel

theorem tot604 : totK PD2M8K2 D2M8K2.t604 = [148396324619, 451822438978, 289992823619, 23636470495, 0, 0, 0, 0] := by
  decide +kernel

theorem rows605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t605 = true := by
  decide +kernel

theorem tot605 : totK PD2M8K2 D2M8K2.t605 = [0, 209127312404, 491090202959, 174611759889, 4967996017, 0, 0, 0] := by
  decide +kernel

theorem rows606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t606 = true := by
  decide +kernel

theorem tot606 : totK PD2M8K2 D2M8K2.t606 = [0, 189647970073, 455186825643, 223933482889, 17080783126, 0, 0, 0] := by
  decide +kernel

theorem rows607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t607 = true := by
  decide +kernel

theorem tot607 : totK PD2M8K2 D2M8K2.t607 = [0, 199599910824, 484651716039, 196300907887, 9610913563, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
