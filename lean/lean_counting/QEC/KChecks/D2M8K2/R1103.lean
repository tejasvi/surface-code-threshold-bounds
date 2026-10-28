import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4412 = true := by
  decide +kernel

theorem tot4412 : totK PD2M8K2 D2M8K2.t4412 = [0, 0, 186056489933, 448447451047, 254035793963, 29314379906, 0, 0] := by
  decide +kernel

theorem rows4413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4413 = true := by
  decide +kernel

theorem tot4413 : totK PD2M8K2 D2M8K2.t4413 = [0, 0, 173675841623, 456932390283, 271523232588, 17316578553, 0, 0] := by
  decide +kernel

theorem rows4414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4414 = true := by
  decide +kernel

theorem tot4414 : totK PD2M8K2 D2M8K2.t4414 = [0, 0, 176187340286, 477246175921, 251509829742, 13316415971, 0, 0] := by
  decide +kernel

theorem rows4415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4415 = true := by
  decide +kernel

theorem tot4415 : totK PD2M8K2 D2M8K2.t4415 = [0, 0, 0, 172295076697, 447873683141, 254655444825, 25191558099, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
