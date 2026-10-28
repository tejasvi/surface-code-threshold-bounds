import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6900 = true := by
  decide +kernel

theorem tot6900 : totK PA10K2 A10K2.t6900 = [0, 0, 818962859450, 2239564289250, 1627882792808, 339296439297, 12681556880, 0, 0, 0] := by
  decide +kernel

theorem rows6901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6901 = true := by
  decide +kernel

theorem tot6901 : totK PA10K2 A10K2.t6901 = [0, 426592152996, 1637186045864, 1979465928825, 833446325949, 87901507087, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6902 = true := by
  decide +kernel

theorem tot6902 : totK PA10K2 A10K2.t6902 = [0, 441902469423, 1766997531566, 2134053337012, 669624616187, 30656617274, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6903 = true := by
  decide +kernel

theorem tot6903 : totK PA10K2 A10K2.t6903 = [0, 0, 539176525088, 1963753077902, 1977999959963, 461581477300, 13816090359, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
