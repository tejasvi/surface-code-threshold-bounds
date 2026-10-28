import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows36 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t36 = true := by
  decide +kernel

theorem tot36 : totK PD2M8K2 D2M8K2.t36 = [19567392089, 327211390076, 504824387471, 65101330788, 0, 0, 0, 0] := by
  decide +kernel

theorem rows37 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t37 = true := by
  decide +kernel

theorem tot37 : totK PD2M8K2 D2M8K2.t37 = [174007439586, 447205777551, 264595498389, 27465480285, 0, 0, 0, 0] := by
  decide +kernel

theorem rows38 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t38 = true := by
  decide +kernel

theorem tot38 : totK PD2M8K2 D2M8K2.t38 = [134132156144, 431101808182, 306920436287, 33018109911, 0, 0, 0, 0] := by
  decide +kernel

theorem rows39 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t39 = true := by
  decide +kernel

theorem tot39 : totK PD2M8K2 D2M8K2.t39 = [0, 187830677876, 447749167855, 235375148547, 22492124391, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
