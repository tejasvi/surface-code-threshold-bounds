import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7808 = true := by
  decide +kernel

theorem tot7808 : totK PD2M8K2 D2M8K2.t7808 = [0, 0, 189971440914, 466986808736, 205027909278, 12403393969, 0, 0] := by
  decide +kernel

theorem rows7809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7809 = true := by
  decide +kernel

theorem tot7809 : totK PD2M8K2 D2M8K2.t7809 = [0, 0, 170308663638, 491368977516, 219515004278, 6409132796, 0, 0] := by
  decide +kernel

theorem rows7810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7810 = true := by
  decide +kernel

theorem tot7810 : totK PD2M8K2 D2M8K2.t7810 = [0, 94305354095, 312882824723, 374061609058, 141714760566, 9054957427, 0, 0] := by
  decide +kernel

theorem rows7811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7811 = true := by
  decide +kernel

theorem tot7811 : totK PD2M8K2 D2M8K2.t7811 = [0, 174828614286, 451691083671, 253961319477, 21483438142, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
