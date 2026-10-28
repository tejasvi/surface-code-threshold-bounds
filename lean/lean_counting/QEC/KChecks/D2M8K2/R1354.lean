import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5416 = true := by
  decide +kernel

theorem tot5416 : totK PD2M8K2 D2M8K2.t5416 = [0, 0, 201425110770, 480940333136, 224956851590, 13578042146, 0, 0] := by
  decide +kernel

theorem rows5417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5417 = true := by
  decide +kernel

theorem tot5417 : totK PD2M8K2 D2M8K2.t5417 = [0, 0, 92395783567, 420431062891, 351944601822, 49410645045, 0, 0] := by
  decide +kernel

theorem rows5418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5418 = true := by
  decide +kernel

theorem tot5418 : totK PD2M8K2 D2M8K2.t5418 = [0, 0, 0, 158847178819, 444512077016, 269852304346, 23329198674, 0] := by
  decide +kernel

theorem rows5419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5419 = true := by
  decide +kernel

theorem tot5419 : totK PD2M8K2 D2M8K2.t5419 = [0, 0, 29588901100, 202154665696, 450443382640, 202276772304, 9435633141, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
