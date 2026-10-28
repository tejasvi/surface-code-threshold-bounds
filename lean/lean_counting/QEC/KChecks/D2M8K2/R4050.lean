import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16200 = true := by
  decide +kernel

theorem tot16200 : totK PD2M8K2 D2M8K2.t16200 = [0, 19497166104, 314224409948, 465183051766, 99070327122, 1369150432, 0, 0] := by
  decide +kernel

theorem rows16201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16201 = true := by
  decide +kernel

theorem tot16201 : totK PD2M8K2 D2M8K2.t16201 = [0, 93348984190, 366287104981, 408106422787, 50524132146, 0, 0, 0] := by
  decide +kernel

theorem rows16202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16202 = true := by
  decide +kernel

theorem tot16202 : totK PD2M8K2 D2M8K2.t16202 = [0, 155888890441, 442400098474, 283111276252, 30205380374, 0, 0, 0] := by
  decide +kernel

theorem rows16203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16203 = true := by
  decide +kernel

theorem tot16203 : totK PD2M8K2 D2M8K2.t16203 = [0, 174570358767, 490235505125, 246075634687, 10795241395, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
