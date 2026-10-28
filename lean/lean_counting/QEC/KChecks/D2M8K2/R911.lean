import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3644 = true := by
  decide +kernel

theorem tot3644 : totK PD2M8K2 D2M8K2.t3644 = [0, 80989279708, 353854283217, 371807992366, 104429030622, 8332571741, 0, 0] := by
  decide +kernel

theorem rows3645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3645 = true := by
  decide +kernel

theorem tot3645 : totK PD2M8K2 D2M8K2.t3645 = [0, 0, 244984005263, 496320924687, 171985724734, 5324200119, 0, 0] := by
  decide +kernel

theorem rows3646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3646 = true := by
  decide +kernel

theorem tot3646 : totK PD2M8K2 D2M8K2.t3646 = [0, 137090600943, 364382866438, 307546464253, 86384248143, 1409560813, 0, 0] := by
  decide +kernel

theorem rows3647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3647 = true := by
  decide +kernel

theorem tot3647 : totK PD2M8K2 D2M8K2.t3647 = [0, 165510503909, 448939544562, 282661344229, 29986382230, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
