import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1196 = true := by
  decide +kernel

theorem tot1196 : totK PA10K2 A10K2.t1196 = [0, 0, 0, 96890305222, 895869033374, 1946997729048, 1416054337999, 358352176653, 25239774317, 0] := by
  decide +kernel

theorem rows1197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1197 = true := by
  decide +kernel

theorem tot1197 : totK PA10K2 A10K2.t1197 = [0, 0, 0, 287930791013, 1167831950392, 1826440204277, 1114835598066, 186084294959, 5365973533, 0] := by
  decide +kernel

theorem rows1198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1198 = true := by
  decide +kernel

theorem tot1198 : totK PA10K2 A10K2.t1198 = [0, 0, 0, 426063404824, 1736128410003, 1838362914534, 479840845538, 30954851499, 0, 0] := by
  decide +kernel

theorem rows1199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1199 = true := by
  decide +kernel

theorem tot1199 : totK PA10K2 A10K2.t1199 = [0, 0, 0, 0, 862771994499, 2300476858355, 1160063257177, 103210728899, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
