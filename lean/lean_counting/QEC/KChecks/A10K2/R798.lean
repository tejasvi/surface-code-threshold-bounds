import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3192 = true := by
  decide +kernel

theorem tot3192 : totK PA10K2 A10K2.t3192 = [0, 272368017072, 997827290031, 1563240067051, 1376115488423, 548442962900, 48370132650, 0, 0, 0] := by
  decide +kernel

theorem rows3193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3193 = true := by
  decide +kernel

theorem tot3193 : totK PA10K2 A10K2.t3193 = [0, 151987658739, 1131128038121, 2028383251775, 1034370718838, 158870606948, 5300418178, 0, 0, 0] := by
  decide +kernel

theorem rows3194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3194 = true := by
  decide +kernel

theorem tot3194 : totK PA10K2 A10K2.t3194 = [0, 477984308118, 1528394140602, 1727524743138, 906460950806, 155512643476, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows3195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3195 = true := by
  decide +kernel

theorem tot3195 : totK PA10K2 A10K2.t3195 = [0, 325843893375, 1613316060492, 2193455826494, 811811675217, 70794459365, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
