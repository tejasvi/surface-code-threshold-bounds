import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1272 = true := by
  decide +kernel

theorem tot1272 : totK PA10K2 A10K2.t1272 = [0, 0, 343536269674, 1581407345043, 2096078709538, 651849792788, 33547703232, 0, 0, 0] := by
  decide +kernel

theorem rows1273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1273 = true := by
  decide +kernel

theorem tot1273 : totK PA10K2 A10K2.t1273 = [0, 0, 271912620389, 1197055353624, 1898767285375, 1085440587430, 175454074125, 6034215561, 0, 0] := by
  decide +kernel

theorem rows1274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1274 = true := by
  decide +kernel

theorem tot1274 : totK PA10K2 A10K2.t1274 = [0, 0, 508170014892, 1661501104793, 1737967141354, 574359636221, 51963961291, 0, 0, 0] := by
  decide +kernel

theorem rows1275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1275 = true := by
  decide +kernel

theorem tot1275 : totK PA10K2 A10K2.t1275 = [0, 0, 40274886064, 1126419142504, 2315857527193, 1037177158047, 85815161317, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
