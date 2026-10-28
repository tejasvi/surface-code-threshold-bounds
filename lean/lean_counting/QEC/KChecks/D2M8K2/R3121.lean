import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12484 = true := by
  decide +kernel

theorem tot12484 : totK PD2M8K2 D2M8K2.t12484 = [0, 162867068856, 452962305465, 262523632358, 22246498675, 0, 0, 0] := by
  decide +kernel

theorem rows12485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12485 = true := by
  decide +kernel

theorem tot12485 : totK PD2M8K2 D2M8K2.t12485 = [0, 0, 212970129959, 494171616558, 156326508762, 4967996017, 0, 0] := by
  decide +kernel

theorem rows12486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12486 = true := by
  decide +kernel

theorem tot12486 : totK PD2M8K2 D2M8K2.t12486 = [0, 0, 178983758574, 451636084020, 215228255831, 17080783126, 0, 0] := by
  decide +kernel

theorem rows12487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12487 = true := by
  decide +kernel

theorem tot12487 : totK PD2M8K2 D2M8K2.t12487 = [0, 0, 204174165168, 486537127653, 193573059180, 9610913563, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
