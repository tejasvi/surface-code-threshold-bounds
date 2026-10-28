import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7060 = true := by
  decide +kernel

theorem tot7060 : totK PA10K2 A10K2.t7060 = [0, 0, 310599358184, 1159665894551, 1599744480440, 1367057113186, 534623210458, 50425690648, 0, 0] := by
  decide +kernel

theorem rows7061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7061 = true := by
  decide +kernel

theorem tot7061 : totK PA10K2 A10K2.t7061 = [0, 0, 498399812810, 1777261871124, 1919680689077, 599583722824, 38152999591, 0, 0, 0] := by
  decide +kernel

theorem rows7062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7062 = true := by
  decide +kernel

theorem tot7062 : totK PA10K2 A10K2.t7062 = [0, 0, 0, 700396592667, 2057646316621, 1707520211152, 366196883613, 12696458652, 0, 0] := by
  decide +kernel

theorem rows7063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7063 = true := by
  decide +kernel

theorem tot7063 : totK PA10K2 A10K2.t7063 = [0, 0, 272840970372, 1241819115202, 2028319627311, 1159432571337, 135582917911, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
