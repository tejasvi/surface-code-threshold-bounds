import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8504 = true := by
  decide +kernel

theorem tot8504 : totK PD2M8K2 D2M8K2.t8504 = [183935492724, 458610537847, 236810957037, 16863238017, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8505 = true := by
  decide +kernel

theorem tot8505 : totK PD2M8K2 D2M8K2.t8505 = [3950786586, 328706828620, 467553352001, 89351364282, 1092001298, 0, 0, 0] := by
  decide +kernel

theorem rows8506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8506 = true := by
  decide +kernel

theorem tot8506 : totK PD2M8K2 D2M8K2.t8506 = [66761380721, 294651097303, 414869480860, 111732798169, 3867150671, 0, 0, 0] := by
  decide +kernel

theorem rows8507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8507 = true := by
  decide +kernel

theorem tot8507 : totK PD2M8K2 D2M8K2.t8507 = [176348708448, 455129170213, 259764226770, 24307713668, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
