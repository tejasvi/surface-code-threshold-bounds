import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2476 = true := by
  decide +kernel

theorem tot2476 : totK PD2M8K2 D2M8K2.t2476 = [0, 92515481918, 434999644357, 352916533056, 38689498187, 0, 0, 0] := by
  decide +kernel

theorem rows2477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2477 = true := by
  decide +kernel

theorem tot2477 : totK PD2M8K2 D2M8K2.t2477 = [0, 0, 227590327779, 502106811741, 150648437196, 2484078857, 0, 0] := by
  decide +kernel

theorem rows2478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2478 = true := by
  decide +kernel

theorem tot2478 : totK PD2M8K2 D2M8K2.t2478 = [159221153091, 304722408551, 143033631820, 178206137432, 101807103217, 6818291842, 0, 0] := by
  decide +kernel

theorem rows2479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2479 = true := by
  decide +kernel

theorem tot2479 : totK PD2M8K2 D2M8K2.t2479 = [163632999621, 463110315431, 246898447998, 13644692975, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
