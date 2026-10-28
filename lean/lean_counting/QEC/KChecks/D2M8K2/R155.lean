import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t620 = true := by
  decide +kernel

theorem tot620 : totK PD2M8K2 D2M8K2.t620 = [190442278098, 476320670482, 229388015002, 15394097451, 0, 0, 0, 0] := by
  decide +kernel

theorem rows621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t621 = true := by
  decide +kernel

theorem tot621 : totK PD2M8K2 D2M8K2.t621 = [87970577784, 393127120192, 369391180252, 65504600492, 3626128243, 0, 0, 0] := by
  decide +kernel

theorem rows622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t622 = true := by
  decide +kernel

theorem tot622 : totK PD2M8K2 D2M8K2.t622 = [0, 161783423932, 447185373826, 272422854476, 22931114674, 0, 0, 0] := by
  decide +kernel

theorem rows623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t623 = true := by
  decide +kernel

theorem tot623 : totK PD2M8K2 D2M8K2.t623 = [3735470318, 173485604438, 473133937590, 229919607621, 9359077587, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
