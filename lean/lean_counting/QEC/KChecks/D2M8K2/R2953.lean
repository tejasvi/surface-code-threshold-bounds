import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11812 = true := by
  decide +kernel

theorem tot11812 : totK PD2M8K2 D2M8K2.t11812 = [0, 0, 0, 303740147944, 450194813093, 79826093797, 1021600638, 0] := by
  decide +kernel

theorem rows11813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11813 = true := by
  decide +kernel

theorem tot11813 : totK PD2M8K2 D2M8K2.t11813 = [0, 0, 168319464383, 386992869962, 229296057419, 64256412501, 3552795014, 0] := by
  decide +kernel

theorem rows11814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11814 = true := by
  decide +kernel

theorem tot11814 : totK PD2M8K2 D2M8K2.t11814 = [0, 0, 210471719662, 466806255464, 208969526692, 10514363019, 0, 0] := by
  decide +kernel

theorem rows11815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11815 = true := by
  decide +kernel

theorem tot11815 : totK PD2M8K2 D2M8K2.t11815 = [0, 175422674038, 377336010235, 233033107072, 101174954830, 8935385149, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
