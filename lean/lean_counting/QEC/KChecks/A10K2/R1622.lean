import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6488 = true := by
  decide +kernel

theorem tot6488 : totK PA10K2 A10K2.t6488 = [0, 0, 367263799603, 1687080755422, 2110736332561, 675897653250, 40588570868, 0, 0, 0] := by
  decide +kernel

theorem rows6489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6489 = true := by
  decide +kernel

theorem tot6489 : totK PA10K2 A10K2.t6489 = [0, 0, 0, 452304819220, 1805839160578, 1837431053168, 452342735896, 25565504801, 0, 0] := by
  decide +kernel

theorem rows6490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6490 = true := by
  decide +kernel

theorem tot6490 : totK PA10K2 A10K2.t6490 = [0, 0, 411974265533, 1607265695257, 1886695397533, 720682918979, 111013870728, 5517381808, 0, 0] := by
  decide +kernel

theorem rows6491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6491 = true := by
  decide +kernel

theorem tot6491 : totK PA10K2 A10K2.t6491 = [0, 0, 271022365149, 1443896275202, 2023975357362, 691070171493, 44621684296, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
