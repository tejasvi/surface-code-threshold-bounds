import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2472 = true := by
  decide +kernel

theorem tot2472 : totK PD2M8K2 D2M8K2.t2472 = [0, 162053763936, 474359211997, 248759185423, 13548827107, 0, 0, 0] := by
  decide +kernel

theorem rows2473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2473 = true := by
  decide +kernel

theorem tot2473 : totK PD2M8K2 D2M8K2.t2473 = [0, 0, 326738449529, 517829779523, 67648050538, 0, 0, 0] := by
  decide +kernel

theorem rows2474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2474 = true := by
  decide +kernel

theorem tot2474 : totK PD2M8K2 D2M8K2.t2474 = [0, 157758791320, 391587492596, 285250793576, 77167866859, 1415142070, 0, 0] := by
  decide +kernel

theorem rows2475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2475 = true := by
  decide +kernel

theorem tot2475 : totK PD2M8K2 D2M8K2.t2475 = [0, 173130873977, 444744240105, 264117705030, 21150403311, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
