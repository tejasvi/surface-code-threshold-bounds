import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5196 = true := by
  decide +kernel

theorem tot5196 : totK PA10K2 A10K2.t5196 = [0, 267823935912, 1341450644631, 2085343226170, 942861218736, 99780911415, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5197 = true := by
  decide +kernel

theorem tot5197 : totK PA10K2 A10K2.t5197 = [0, 279363014200, 1102186222309, 1644956358006, 1269938820107, 371668845606, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows5198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5198 = true := by
  decide +kernel

theorem tot5198 : totK PA10K2 A10K2.t5198 = [0, 510219037452, 1674051024210, 1768184387727, 626552663898, 52232171148, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5199 = true := by
  decide +kernel

theorem tot5199 : totK PA10K2 A10K2.t5199 = [0, 0, 1017106720882, 2375426041185, 1162250257248, 107853694943, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
