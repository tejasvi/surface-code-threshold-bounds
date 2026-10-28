import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t320 = true := by
  decide +kernel

theorem tot320 : totK PD2M8K2 D2M8K2.t320 = [182492669781, 472761461807, 256332812043, 23261692605, 0, 0, 0, 0] := by
  decide +kernel

theorem rows321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t321 = true := by
  decide +kernel

theorem tot321 : totK PD2M8K2 D2M8K2.t321 = [172353248025, 465966395792, 243312987594, 13594348774, 0, 0, 0, 0] := by
  decide +kernel

theorem rows322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t322 = true := by
  decide +kernel

theorem tot322 : totK PD2M8K2 D2M8K2.t322 = [0, 290837734017, 504588014989, 109372069393, 1163840124, 0, 0, 0] := by
  decide +kernel

theorem rows323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t323 = true := by
  decide +kernel

theorem tot323 : totK PD2M8K2 D2M8K2.t323 = [10857751158, 193658408957, 465260212913, 190118738286, 11873025674, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
