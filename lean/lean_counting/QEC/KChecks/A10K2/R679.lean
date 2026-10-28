import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2716 = true := by
  decide +kernel

theorem tot2716 : totK PA10K2 A10K2.t2716 = [0, 0, 448579188712, 1553522604894, 1740339702034, 860295757851, 147388456701, 5517381808, 0, 0] := by
  decide +kernel

theorem rows2717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2717 = true := by
  decide +kernel

theorem tot2717 : totK PA10K2 A10K2.t2717 = [0, 0, 328463760028, 1624411716586, 2090915587725, 628688402038, 38254334585, 0, 0, 0] := by
  decide +kernel

theorem rows2718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2718 = true := by
  decide +kernel

theorem tot2718 : totK PA10K2 A10K2.t2718 = [0, 0, 111936990840, 867656521469, 2072578470254, 1333155125949, 207168357728, 6121173289, 0, 0] := by
  decide +kernel

theorem rows2719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2719 = true := by
  decide +kernel

theorem tot2719 : totK PA10K2 A10K2.t2719 = [0, 162078939081, 752715982198, 1806517111162, 1855178337350, 500083361311, 27250992027, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
