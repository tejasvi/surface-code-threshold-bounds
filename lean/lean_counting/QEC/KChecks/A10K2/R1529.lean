import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6116 = true := by
  decide +kernel

theorem tot6116 : totK PA10K2 A10K2.t6116 = [0, 0, 485723205089, 1850660147969, 2142606085106, 571149688111, 12746179907, 0, 0, 0] := by
  decide +kernel

theorem rows6117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6117 = true := by
  decide +kernel

theorem tot6117 : totK PA10K2 A10K2.t6117 = [0, 0, 537414476405, 1785430242663, 1816384059846, 627646780409, 60319339828, 0, 0, 0] := by
  decide +kernel

theorem rows6118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6118 = true := by
  decide +kernel

theorem tot6118 : totK PA10K2 A10K2.t6118 = [0, 0, 327954541848, 1636889706400, 2142904669438, 736660438857, 55083815889, 0, 0, 0] := by
  decide +kernel

theorem rows6119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6119 = true := by
  decide +kernel

theorem tot6119 : totK PA10K2 A10K2.t6119 = [0, 0, 0, 519398961267, 1773432874475, 1707718975478, 467981582673, 30650496230, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
