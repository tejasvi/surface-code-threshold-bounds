import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2452 = true := by
  decide +kernel

theorem tot2452 : totK PD2M8K2 D2M8K2.t2452 = [0, 285988165873, 515227900075, 100482796770, 1000146243, 0, 0, 0] := by
  decide +kernel

theorem rows2453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2453 = true := by
  decide +kernel

theorem tot2453 : totK PD2M8K2 D2M8K2.t2453 = [87572808389, 333482118251, 374817131876, 101051484163, 3867150671, 0, 0, 0] := by
  decide +kernel

theorem rows2454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2454 = true := by
  decide +kernel

theorem tot2454 : totK PD2M8K2 D2M8K2.t2454 = [169993707872, 440795460261, 275865641048, 30191107111, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2455 = true := by
  decide +kernel

theorem tot2455 : totK PD2M8K2 D2M8K2.t2455 = [163930573481, 462061034602, 265708022135, 21883372984, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
