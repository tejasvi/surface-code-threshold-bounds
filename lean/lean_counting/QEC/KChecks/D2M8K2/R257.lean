import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1028 = true := by
  decide +kernel

theorem tot1028 : totK PD2M8K2 D2M8K2.t1028 = [190275221039, 448258940496, 238137017636, 17115888737, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1029 = true := by
  decide +kernel

theorem tot1029 : totK PD2M8K2 D2M8K2.t1029 = [67100904544, 363748669672, 370545932183, 73968647540, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows1030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1030 = true := by
  decide +kernel

theorem tot1030 : totK PD2M8K2 D2M8K2.t1030 = [0, 312085428217, 514452339402, 74708538587, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1031 = true := by
  decide +kernel

theorem tot1031 : totK PD2M8K2 D2M8K2.t1031 = [177828434186, 436151143032, 270089930515, 33625667918, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
