import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t552 = true := by
  decide +kernel

theorem tot552 : totK PD2M8K2 D2M8K2.t552 = [0, 170456618683, 438954955725, 270471686595, 29490723574, 0, 0, 0] := by
  decide +kernel

theorem rows553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t553 = true := by
  decide +kernel

theorem tot553 : totK PD2M8K2 D2M8K2.t553 = [0, 175009442817, 469574020940, 241094604885, 13810676078, 0, 0, 0] := by
  decide +kernel

theorem rows554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t554 = true := by
  decide +kernel

theorem tot554 : totK PD2M8K2 D2M8K2.t554 = [0, 0, 288314463951, 505963656409, 99292835584, 1096505104, 0, 0] := by
  decide +kernel

theorem rows555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t555 = true := by
  decide +kernel

theorem tot555 : totK PD2M8K2 D2M8K2.t555 = [0, 0, 211387776332, 497783659897, 169514565906, 5253830308, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
