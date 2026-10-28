import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7088 = true := by
  decide +kernel

theorem tot7088 : totK PA10K2 A10K2.t7088 = [0, 0, 0, 0, 588774073993, 1973650050245, 1808735620620, 388129396822, 12132367858, 0] := by
  decide +kernel

theorem rows7089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7089 = true := by
  decide +kernel

theorem tot7089 : totK PA10K2 A10K2.t7089 = [0, 321107158991, 869680282452, 549821226374, 285889170108, 1016438926655, 1341419641509, 522012413546, 48886019071, 0] := by
  decide +kernel

theorem rows7090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7090 = true := by
  decide +kernel

theorem tot7090 : totK PA10K2 A10K2.t7090 = [0, 488361756309, 1771788392619, 1921791317641, 539382512238, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7091 = true := by
  decide +kernel

theorem tot7091 : totK PA10K2 A10K2.t7091 = [0, 60431206685, 842901836785, 2077986246838, 1533947117232, 358606288742, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
