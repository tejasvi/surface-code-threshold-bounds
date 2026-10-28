import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6488 = true := by
  decide +kernel

theorem tot6488 : totK PD2M8K2 D2M8K2.t6488 = [132249069452, 436942303996, 311627338942, 39380423806, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6489 = true := by
  decide +kernel

theorem tot6489 : totK PD2M8K2 D2M8K2.t6489 = [0, 228467060576, 494774834378, 172198663220, 6286513735, 0, 0, 0] := by
  decide +kernel

theorem rows6490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6490 = true := by
  decide +kernel

theorem tot6490 : totK PD2M8K2 D2M8K2.t6490 = [0, 160062236945, 432694782380, 287344503572, 35270139864, 0, 0, 0] := by
  decide +kernel

theorem rows6491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6491 = true := by
  decide +kernel

theorem tot6491 : totK PD2M8K2 D2M8K2.t6491 = [0, 182187747105, 469995976217, 240507863718, 12940973730, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
