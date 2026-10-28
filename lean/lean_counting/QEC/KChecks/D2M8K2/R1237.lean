import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4948 = true := by
  decide +kernel

theorem tot4948 : totK PD2M8K2 D2M8K2.t4948 = [0, 171422536039, 442522015162, 257343573870, 19670495933, 0, 0, 0] := by
  decide +kernel

theorem rows4949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4949 = true := by
  decide +kernel

theorem tot4949 : totK PD2M8K2 D2M8K2.t4949 = [0, 91637619653, 364660758661, 369218350272, 67925461845, 1096505104, 0, 0] := by
  decide +kernel

theorem rows4950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4950 = true := by
  decide +kernel

theorem tot4950 : totK PD2M8K2 D2M8K2.t4950 = [0, 0, 295259805048, 508447823665, 94535054426, 1069412848, 0, 0] := by
  decide +kernel

theorem rows4951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4951 = true := by
  decide +kernel

theorem tot4951 : totK PD2M8K2 D2M8K2.t4951 = [0, 0, 176345943235, 475934306101, 213805744852, 12425510570, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
