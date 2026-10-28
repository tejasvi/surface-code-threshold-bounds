import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3236 = true := by
  decide +kernel

theorem tot3236 : totK PA10K2 A10K2.t3236 = [0, 0, 257414766556, 1444404578780, 2092090406233, 676384976334, 28114425419, 0, 0, 0] := by
  decide +kernel

theorem rows3237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3237 = true := by
  decide +kernel

theorem tot3237 : totK PA10K2 A10K2.t3237 = [0, 0, 372495326728, 1370257447545, 1837812555000, 997432305613, 137841269177, 5460492893, 0, 0] := by
  decide +kernel

theorem rows3238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3238 = true := by
  decide +kernel

theorem tot3238 : totK PA10K2 A10K2.t3238 = [0, 0, 431332874765, 1789415668933, 2106494220357, 648566122989, 41248950376, 0, 0, 0] := by
  decide +kernel

theorem rows3239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3239 = true := by
  decide +kernel

theorem tot3239 : totK PA10K2 A10K2.t3239 = [0, 0, 0, 467221231162, 1897428461826, 1899096478428, 437731884077, 25734533292, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
