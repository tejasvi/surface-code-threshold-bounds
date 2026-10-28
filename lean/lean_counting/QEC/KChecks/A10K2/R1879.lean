import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7516 = true := by
  decide +kernel

theorem tot7516 : totK PA10K2 A10K2.t7516 = [0, 0, 365488769478, 1659305372396, 2056279946731, 606204133677, 32877822373, 0, 0, 0] := by
  decide +kernel

theorem rows7517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7517 = true := by
  decide +kernel

theorem tot7517 : totK PA10K2 A10K2.t7517 = [0, 0, 113610237831, 875656046180, 2116649705885, 1343454831628, 195778155918, 6121173289, 0, 0] := by
  decide +kernel

theorem rows7518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7518 = true := by
  decide +kernel

theorem tot7518 : totK PA10K2 A10K2.t7518 = [0, 0, 479193317821, 1872596769692, 2100666340410, 628287345223, 32712955001, 0, 0, 0] := by
  decide +kernel

theorem rows7519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7519 = true := by
  decide +kernel

theorem tot7519 : totK PA10K2 A10K2.t7519 = [0, 561156172308, 1813477113326, 1645852543475, 569982278068, 239941268139, 30195939839, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
