import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7900 = true := by
  decide +kernel

theorem tot7900 : totK PA10K2 A10K2.t7900 = [0, 328596557822, 1547422839545, 2088345958425, 846432423862, 77916206695, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7901 = true := by
  decide +kernel

theorem tot7901 : totK PA10K2 A10K2.t7901 = [0, 0, 500577921421, 1815444703446, 1754560681480, 457259411563, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows7902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7902 = true := by
  decide +kernel

theorem tot7902 : totK PA10K2 A10K2.t7902 = [0, 441487391689, 1679530378629, 1936746094870, 748590235052, 71189193115, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7903 = true := by
  decide +kernel

theorem tot7903 : totK PA10K2 A10K2.t7903 = [0, 291093484992, 1355651643655, 2037215584895, 974168196003, 100969743445, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
