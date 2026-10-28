import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3072 = true := by
  decide +kernel

theorem tot3072 : totK PA10K2 A10K2.t3072 = [0, 0, 550323501940, 1947200083659, 1987069832358, 553904124177, 32848078363, 0, 0, 0] := by
  decide +kernel

theorem rows3073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3073 = true := by
  decide +kernel

theorem tot3073 : totK PA10K2 A10K2.t3073 = [0, 0, 226651756384, 1272707391823, 2217923847942, 1239180359926, 156688424702, 0, 0, 0] := by
  decide +kernel

theorem rows3074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3074 = true := by
  decide +kernel

theorem tot3074 : totK PA10K2 A10K2.t3074 = [0, 0, 0, 494912170594, 1936295210970, 2050740774023, 484682939285, 12926121504, 0, 0] := by
  decide +kernel

theorem rows3075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3075 = true := by
  decide +kernel

theorem tot3075 : totK PA10K2 A10K2.t3075 = [0, 0, 0, 557865444014, 1812962922647, 1739018048282, 594924670226, 54397938383, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
