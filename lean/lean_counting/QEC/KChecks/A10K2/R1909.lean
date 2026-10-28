import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7636 = true := by
  decide +kernel

theorem tot7636 : totK PA10K2 A10K2.t7636 = [0, 0, 0, 578620096636, 1977046984521, 1777979857791, 435857934142, 25734533292, 0, 0] := by
  decide +kernel

theorem rows7637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7637 = true := by
  decide +kernel

theorem tot7637 : totK PA10K2 A10K2.t7637 = [0, 0, 412332156094, 1472224390561, 1743536077848, 968074434227, 181917064037, 6034215561, 0, 0] := by
  decide +kernel

theorem rows7638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7638 = true := by
  decide +kernel

theorem tot7638 : totK PA10K2 A10K2.t7638 = [0, 0, 271285846837, 1504591953219, 2107464236701, 684142665782, 39254201957, 0, 0, 0] := by
  decide +kernel

theorem rows7639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7639 = true := by
  decide +kernel

theorem tot7639 : totK PA10K2 A10K2.t7639 = [0, 0, 177412673197, 999699204636, 2041723560451, 1326199511145, 204898801994, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
