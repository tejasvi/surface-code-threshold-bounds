import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2788 = true := by
  decide +kernel

theorem tot2788 : totK PD2M8K2 D2M8K2.t2788 = [0, 0, 154822114785, 453418282456, 269718338304, 18701401629, 0, 0] := by
  decide +kernel

theorem rows2789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2789 = true := by
  decide +kernel

theorem tot2789 : totK PD2M8K2 D2M8K2.t2789 = [0, 0, 0, 317853600527, 471928741741, 84108172525, 1332468113, 0] := by
  decide +kernel

theorem rows2790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2790 = true := by
  decide +kernel

theorem tot2790 : totK PD2M8K2 D2M8K2.t2790 = [0, 0, 168807573778, 445241760870, 268921577973, 29389117999, 0, 0] := by
  decide +kernel

theorem rows2791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2791 = true := by
  decide +kernel

theorem tot2791 : totK PD2M8K2 D2M8K2.t2791 = [0, 0, 170473899286, 442764666323, 252648583853, 14396381792, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
