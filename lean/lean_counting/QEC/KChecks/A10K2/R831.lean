import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3324 = true := by
  decide +kernel

theorem tot3324 : totK PA10K2 A10K2.t3324 = [0, 0, 432323684451, 1830460709964, 2207333551239, 681476380848, 25738944239, 0, 0, 0] := by
  decide +kernel

theorem rows3325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3325 = true := by
  decide +kernel

theorem tot3325 : totK PA10K2 A10K2.t3325 = [0, 550461195332, 1876243866401, 1763033380508, 492578711445, 115453555207, 31812225529, 0, 0, 0] := by
  decide +kernel

theorem rows3326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3326 = true := by
  decide +kernel

theorem tot3326 : totK PA10K2 A10K2.t3326 = [0, 296440474885, 1435538179134, 2201869646351, 974998427389, 84152717924, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3327 = true := by
  decide +kernel

theorem tot3327 : totK PA10K2 A10K2.t3327 = [0, 0, 495936105780, 1854870278302, 1902191055325, 512406087651, 31768748853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
