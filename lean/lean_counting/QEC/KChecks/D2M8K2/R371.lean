import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1484 = true := by
  decide +kernel

theorem tot1484 : totK PD2M8K2 D2M8K2.t1484 = [0, 0, 270428014421, 509658734332, 122319454311, 1268739303, 0, 0] := by
  decide +kernel

theorem rows1485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1485 = true := by
  decide +kernel

theorem tot1485 : totK PD2M8K2 D2M8K2.t1485 = [0, 0, 200046013632, 488168142844, 190128286078, 7442000727, 0, 0] := by
  decide +kernel

theorem rows1486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1486 = true := by
  decide +kernel

theorem tot1486 : totK PD2M8K2 D2M8K2.t1486 = [0, 0, 174279972177, 456050918136, 227350626319, 15859045170, 0, 0] := by
  decide +kernel

theorem rows1487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1487 = true := by
  decide +kernel

theorem tot1487 : totK PD2M8K2 D2M8K2.t1487 = [0, 0, 182204760517, 471894617518, 191247892194, 7799949799, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
