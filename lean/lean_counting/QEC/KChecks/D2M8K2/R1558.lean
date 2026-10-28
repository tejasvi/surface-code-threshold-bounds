import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6232 = true := by
  decide +kernel

theorem tot6232 : totK PD2M8K2 D2M8K2.t6232 = [173094692276, 471459313479, 229342870110, 11038245751, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6233 = true := by
  decide +kernel

theorem tot6233 : totK PD2M8K2 D2M8K2.t6233 = [154453482306, 450051348722, 258879390420, 17739311140, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6234 = true := by
  decide +kernel

theorem tot6234 : totK PD2M8K2 D2M8K2.t6234 = [0, 266493985208, 493831719186, 116879067219, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows6235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6235 = true := by
  decide +kernel

theorem tot6235 : totK PD2M8K2 D2M8K2.t6235 = [103813599404, 379044486233, 388800356987, 50042246848, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
