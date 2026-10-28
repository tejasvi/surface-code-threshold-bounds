import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2780 = true := by
  decide +kernel

theorem tot2780 : totK PD2M8K2 D2M8K2.t2780 = [0, 0, 284572965181, 504601690493, 113098458174, 1369820453, 0, 0] := by
  decide +kernel

theorem rows2781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2781 = true := by
  decide +kernel

theorem tot2781 : totK PD2M8K2 D2M8K2.t2781 = [0, 0, 178730082202, 439508385945, 268257840965, 25922543633, 0, 0] := by
  decide +kernel

theorem rows2782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2782 = true := by
  decide +kernel

theorem tot2782 : totK PD2M8K2 D2M8K2.t2782 = [0, 0, 208983042185, 482749017646, 208141580885, 6553345076, 0, 0] := by
  decide +kernel

theorem rows2783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2783 = true := by
  decide +kernel

theorem tot2783 : totK PD2M8K2 D2M8K2.t2783 = [0, 0, 200799874324, 472832820113, 219623860009, 12408192946, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
