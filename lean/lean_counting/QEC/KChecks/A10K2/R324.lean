import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1296 = true := by
  decide +kernel

theorem tot1296 : totK PA10K2 A10K2.t1296 = [0, 403863162034, 1727648502068, 2189304364004, 757545320190, 45618503689, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1297 = true := by
  decide +kernel

theorem tot1297 : totK PA10K2 A10K2.t1297 = [0, 120270905406, 873137475321, 2124486172927, 1674685743623, 310333739532, 8047840951, 0, 0, 0] := by
  decide +kernel

theorem rows1298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1298 = true := by
  decide +kernel

theorem tot1298 : totK PA10K2 A10K2.t1298 = [0, 553242846269, 1952563945113, 2015049544015, 566355632209, 32786541850, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1299 = true := by
  decide +kernel

theorem tot1299 : totK PA10K2 A10K2.t1299 = [0, 121146523123, 1000495017100, 2180437787382, 1553305670931, 290107772229, 6851704726, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
