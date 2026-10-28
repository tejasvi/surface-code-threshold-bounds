import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12460 = true := by
  decide +kernel

theorem tot12460 : totK PD2M8K2 D2M8K2.t12460 = [0, 0, 236301836884, 466313925067, 170008648864, 11147507285, 0, 0] := by
  decide +kernel

theorem rows12461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12461 = true := by
  decide +kernel

theorem tot12461 : totK PD2M8K2 D2M8K2.t12461 = [0, 0, 177144304621, 481792655273, 212417297031, 11997996789, 0, 0] := by
  decide +kernel

theorem rows12462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12462 = true := by
  decide +kernel

theorem tot12462 : totK PD2M8K2 D2M8K2.t12462 = [0, 0, 221280054677, 475133455786, 181940565209, 11210740469, 0, 0] := by
  decide +kernel

theorem rows12463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12463 = true := by
  decide +kernel

theorem tot12463 : totK PD2M8K2 D2M8K2.t12463 = [0, 0, 186314465699, 469699687660, 217764639566, 15817296786, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
