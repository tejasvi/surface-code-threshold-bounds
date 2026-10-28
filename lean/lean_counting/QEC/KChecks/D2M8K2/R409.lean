import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1636 = true := by
  decide +kernel

theorem tot1636 : totK PD2M8K2 D2M8K2.t1636 = [0, 0, 188551882738, 460520340184, 221341344657, 15308414975, 0, 0] := by
  decide +kernel

theorem rows1637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1637 = true := by
  decide +kernel

theorem tot1637 : totK PD2M8K2 D2M8K2.t1637 = [0, 0, 106395408461, 429671151932, 307784760767, 27005494330, 0, 0] := by
  decide +kernel

theorem rows1638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1638 = true := by
  decide +kernel

theorem tot1638 : totK PD2M8K2 D2M8K2.t1638 = [0, 0, 0, 311849854264, 460700626556, 82266376913, 1095107716, 0] := by
  decide +kernel

theorem rows1639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1639 = true := by
  decide +kernel

theorem tot1639 : totK PD2M8K2 D2M8K2.t1639 = [0, 176791677709, 369822514279, 136468055537, 132012200809, 71199664796, 3882006667, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
