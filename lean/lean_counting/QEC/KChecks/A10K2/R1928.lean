import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7712 = true := by
  decide +kernel

theorem tot7712 : totK PA10K2 A10K2.t7712 = [0, 0, 0, 723852723391, 2102328629733, 1644135661435, 335708285015, 25734533292, 0, 0] := by
  decide +kernel

theorem rows7713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7713 = true := by
  decide +kernel

theorem tot7713 : totK PA10K2 A10K2.t7713 = [0, 0, 239541746934, 1095899990863, 1914704581653, 1248700900279, 203201120478, 6034215561, 0, 0] := by
  decide +kernel

theorem rows7714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7714 = true := by
  decide +kernel

theorem tot7714 : totK PA10K2 A10K2.t7714 = [0, 0, 581282690114, 1939679910644, 1763514406864, 477044501560, 31941609474, 0, 0, 0] := by
  decide +kernel

theorem rows7715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7715 = true := by
  decide +kernel

theorem tot7715 : totK PA10K2 A10K2.t7715 = [0, 0, 0, 949702440381, 2380199009968, 1238523690454, 107174052748, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
