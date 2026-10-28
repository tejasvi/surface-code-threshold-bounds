import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2172 = true := by
  decide +kernel

theorem tot2172 : totK PD2M8K2 D2M8K2.t2172 = [0, 0, 172019482865, 484285897964, 216696187675, 7992090037, 0, 0] := by
  decide +kernel

theorem rows2173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2173 = true := by
  decide +kernel

theorem tot2173 : totK PD2M8K2 D2M8K2.t2173 = [0, 144535997026, 369473426538, 279559670240, 107757554946, 5656105375, 0, 0] := by
  decide +kernel

theorem rows2174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2174 = true := by
  decide +kernel

theorem tot2174 : totK PD2M8K2 D2M8K2.t2174 = [0, 169649602774, 439844146635, 276684369087, 29568678322, 0, 0, 0] := by
  decide +kernel

theorem rows2175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2175 = true := by
  decide +kernel

theorem tot2175 : totK PD2M8K2 D2M8K2.t2175 = [0, 119796374314, 439259441550, 309336102712, 24183942440, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
