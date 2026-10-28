import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8424 = true := by
  decide +kernel

theorem tot8424 : totK PD2M8K2 D2M8K2.t8424 = [0, 0, 203528857732, 465952464749, 186899346197, 11885407614, 0, 0] := by
  decide +kernel

theorem rows8425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8425 = true := by
  decide +kernel

theorem tot8425 : totK PD2M8K2 D2M8K2.t8425 = [0, 153001941291, 430481603216, 283701511469, 33892084177, 0, 0, 0] := by
  decide +kernel

theorem rows8426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8426 = true := by
  decide +kernel

theorem tot8426 : totK PD2M8K2 D2M8K2.t8426 = [0, 171615806211, 440647670101, 255643465933, 21209405188, 0, 0, 0] := by
  decide +kernel

theorem rows8427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8427 = true := by
  decide +kernel

theorem tot8427 : totK PD2M8K2 D2M8K2.t8427 = [0, 72331704639, 349267609106, 387294005314, 70185560380, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
