import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16340 = true := by
  decide +kernel

theorem tot16340 : totK PD2M8K2 D2M8K2.t16340 = [0, 0, 0, 200376877742, 483489655806, 190000680283, 7810684838, 0] := by
  decide +kernel

theorem rows16341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16341 = true := by
  decide +kernel

theorem tot16341 : totK PD2M8K2 D2M8K2.t16341 = [0, 0, 0, 15862962898, 321057116607, 435565084406, 75869220346, 1135526696] := by
  decide +kernel

theorem rows16342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16342 = true := by
  decide +kernel

theorem tot16342 : totK PD2M8K2 D2M8K2.t16342 = [0, 0, 0, 77311754148, 332187651579, 341774222246, 89390036971, 4028038878] := by
  decide +kernel

theorem rows16343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16343 = true := by
  decide +kernel

theorem tot16343 : totK PD2M8K2 D2M8K2.t16343 = [0, 0, 0, 320804804994, 472166301805, 91065886868, 1343192240, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
