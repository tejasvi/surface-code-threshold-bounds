import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12516 = true := by
  decide +kernel

theorem tot12516 : totK PD2M8K2 D2M8K2.t12516 = [0, 162053559089, 460262159367, 259412480254, 16613131043, 0, 0, 0] := by
  decide +kernel

theorem rows12517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12517 = true := by
  decide +kernel

theorem tot12517 : totK PD2M8K2 D2M8K2.t12517 = [0, 0, 270759585699, 497919275148, 120946346366, 1268739303, 0, 0] := by
  decide +kernel

theorem rows12518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12518 = true := by
  decide +kernel

theorem tot12518 : totK PD2M8K2 D2M8K2.t12518 = [0, 0, 196512172861, 473010183909, 198188394814, 12680714061, 0, 0] := by
  decide +kernel

theorem rows12519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12519 = true := by
  decide +kernel

theorem tot12519 : totK PD2M8K2 D2M8K2.t12519 = [0, 0, 194284796774, 483335609952, 202186581467, 9840992866, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
