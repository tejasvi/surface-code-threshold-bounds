import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7460 = true := by
  decide +kernel

theorem tot7460 : totK PD2M8K2 D2M8K2.t7460 = [0, 0, 156622574833, 469939826476, 264333049788, 14390508009, 0, 0] := by
  decide +kernel

theorem rows7461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7461 = true := by
  decide +kernel

theorem tot7461 : totK PD2M8K2 D2M8K2.t7461 = [0, 0, 0, 285498597737, 506412240345, 88693366319, 1310285577, 0] := by
  decide +kernel

theorem rows7462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7462 = true := by
  decide +kernel

theorem tot7462 : totK PD2M8K2 D2M8K2.t7462 = [0, 0, 180298466249, 431423036213, 279500642425, 34628788584, 0, 0] := by
  decide +kernel

theorem rows7463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7463 = true := by
  decide +kernel

theorem tot7463 : totK PD2M8K2 D2M8K2.t7463 = [0, 0, 157464226444, 476379720999, 252454920464, 11940640293, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
