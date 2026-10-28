import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8720 = true := by
  decide +kernel

theorem tot8720 : totK PD2M8K2 D2M8K2.t8720 = [0, 192197394513, 449017419371, 236928715452, 38273521381, 2814597007, 0, 0] := by
  decide +kernel

theorem rows8721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8721 = true := by
  decide +kernel

theorem tot8721 : totK PD2M8K2 D2M8K2.t8721 = [0, 201574086660, 469995499613, 220819066141, 13909773282, 0, 0, 0] := by
  decide +kernel

theorem rows8722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8722 = true := by
  decide +kernel

theorem tot8722 : totK PD2M8K2 D2M8K2.t8722 = [0, 12005493123, 308247160450, 472559874648, 104187294459, 1232398321, 0, 0] := by
  decide +kernel

theorem rows8723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8723 = true := by
  decide +kernel

theorem tot8723 : totK PD2M8K2 D2M8K2.t8723 = [0, 0, 212516804223, 495564595183, 175206012019, 4990385724, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
