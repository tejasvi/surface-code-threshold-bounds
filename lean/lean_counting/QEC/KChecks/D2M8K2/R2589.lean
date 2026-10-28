import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10356 = true := by
  decide +kernel

theorem tot10356 : totK PD2M8K2 D2M8K2.t10356 = [0, 0, 92889055109, 387971940471, 389128982739, 40042590735, 0, 0] := by
  decide +kernel

theorem rows10357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10357 = true := by
  decide +kernel

theorem tot10357 : totK PD2M8K2 D2M8K2.t10357 = [0, 0, 166389149733, 448314985584, 265824229902, 19202224197, 0, 0] := by
  decide +kernel

theorem rows10358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10358 = true := by
  decide +kernel

theorem tot10358 : totK PD2M8K2 D2M8K2.t10358 = [0, 0, 203654494296, 478216899071, 225279115284, 14654432671, 0, 0] := by
  decide +kernel

theorem rows10359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10359 = true := by
  decide +kernel

theorem tot10359 : totK PD2M8K2 D2M8K2.t10359 = [0, 0, 188052379609, 468611557968, 233155102826, 19263069006, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
