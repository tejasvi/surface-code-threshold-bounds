import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12452 = true := by
  decide +kernel

theorem tot12452 : totK PD2M8K2 D2M8K2.t12452 = [0, 0, 301693208722, 527618397485, 92348171687, 0, 0, 0] := by
  decide +kernel

theorem rows12453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12453 = true := by
  decide +kernel

theorem tot12453 : totK PD2M8K2 D2M8K2.t12453 = [0, 0, 209193361217, 497056189552, 172987208490, 5253830308, 0, 0] := by
  decide +kernel

theorem rows12454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12454 = true := by
  decide +kernel

theorem tot12454 : totK PD2M8K2 D2M8K2.t12454 = [0, 0, 182603501746, 458205372266, 202464298913, 16680312209, 0, 0] := by
  decide +kernel

theorem rows12455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12455 = true := by
  decide +kernel

theorem tot12455 : totK PD2M8K2 D2M8K2.t12455 = [0, 0, 64403308893, 361304892559, 341407820534, 59689376480, 1138244013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
