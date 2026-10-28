import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2448 = true := by
  decide +kernel

theorem tot2448 : totK PA10K2 A10K2.t2448 = [454381702260, 1672946062605, 1930871579896, 755340578256, 120217982966, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2449 = true := by
  decide +kernel

theorem tot2449 : totK PA10K2 A10K2.t2449 = [94501703929, 975562940970, 1972788505208, 1372133744596, 358224094057, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2450 = true := by
  decide +kernel

theorem tot2450 : totK PA10K2 A10K2.t2450 = [324551272586, 1217734915626, 1853195146753, 1169688468450, 196467966429, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2451 = true := by
  decide +kernel

theorem tot2451 : totK PA10K2 A10K2.t2451 = [494005546338, 1856158895537, 1834260510135, 457042229098, 26521581199, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
