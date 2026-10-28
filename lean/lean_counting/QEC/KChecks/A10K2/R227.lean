import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t908 = true := by
  decide +kernel

theorem tot908 : totK PA10K2 A10K2.t908 = [0, 0, 535651322330, 1942327482597, 2071265403764, 565387955095, 25068640818, 0, 0, 0] := by
  decide +kernel

theorem rows909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t909 = true := by
  decide +kernel

theorem tot909 : totK PA10K2 A10K2.t909 = [0, 447860701715, 1438283652353, 1596624653427, 951405696705, 376850790674, 43720954405, 0, 0, 0] := by
  decide +kernel

theorem rows910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t910 = true := by
  decide +kernel

theorem tot910 : totK PA10K2 A10K2.t910 = [0, 332777923914, 1596581780337, 2168235666290, 875659991086, 77534402549, 0, 0, 0, 0] := by
  decide +kernel

theorem rows911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t911 = true := by
  decide +kernel

theorem tot911 : totK PA10K2 A10K2.t911 = [0, 0, 536735109074, 1932718214608, 1858771204699, 488073825521, 31306924438, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
