import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7080 = true := by
  decide +kernel

theorem tot7080 : totK PA10K2 A10K2.t7080 = [0, 0, 0, 608964449560, 1984703671370, 1905066871411, 427470625955, 13653259670, 0, 0] := by
  decide +kernel

theorem rows7081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7081 = true := by
  decide +kernel

theorem tot7081 : totK PA10K2 A10K2.t7081 = [0, 0, 0, 306887902792, 1534202386316, 2179427681988, 788525452471, 60880363483, 0, 0] := by
  decide +kernel

theorem rows7082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7082 = true := by
  decide +kernel

theorem tot7082 : totK PA10K2 A10K2.t7082 = [0, 0, 0, 443651323567, 1694278717601, 1986087464469, 729659987648, 62156421873, 0, 0] := by
  decide +kernel

theorem rows7083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7083 = true := by
  decide +kernel

theorem tot7083 : totK PA10K2 A10K2.t7083 = [0, 0, 0, 182832140154, 1040555288380, 2048112704719, 1264921420548, 208668881916, 6318667960, 0] := by
  decide +kernel

end QECKChecks.A10K2
