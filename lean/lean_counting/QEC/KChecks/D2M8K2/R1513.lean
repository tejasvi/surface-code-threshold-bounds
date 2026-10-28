import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6052 = true := by
  decide +kernel

theorem tot6052 : totK PD2M8K2 D2M8K2.t6052 = [0, 0, 175872595392, 475570002088, 234407165762, 12273019076, 0, 0] := by
  decide +kernel

theorem rows6053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6053 = true := by
  decide +kernel

theorem tot6053 : totK PD2M8K2 D2M8K2.t6053 = [0, 0, 156949554444, 465529956339, 253773522849, 13812171087, 0, 0] := by
  decide +kernel

theorem rows6054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6054 = true := by
  decide +kernel

theorem tot6054 : totK PD2M8K2 D2M8K2.t6054 = [0, 0, 0, 333242659896, 481267531737, 59143265197, 0, 0] := by
  decide +kernel

theorem rows6055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6055 = true := by
  decide +kernel

theorem tot6055 : totK PD2M8K2 D2M8K2.t6055 = [0, 0, 180957591743, 393859724933, 267188153386, 52172661342, 1271866555, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
