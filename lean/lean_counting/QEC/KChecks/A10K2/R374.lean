import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1496 = true := by
  decide +kernel

theorem tot1496 : totK PA10K2 A10K2.t1496 = [0, 0, 0, 289478139766, 1323674727612, 1935820772105, 1044408672646, 191596822650, 5179162207, 0] := by
  decide +kernel

theorem rows1497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1497 = true := by
  decide +kernel

theorem tot1497 : totK PA10K2 A10K2.t1497 = [0, 0, 0, 555160199446, 1826995082508, 1782720736603, 473138288105, 31688770306, 0, 0] := by
  decide +kernel

theorem rows1498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1498 = true := by
  decide +kernel

theorem tot1498 : totK PA10K2 A10K2.t1498 = [0, 0, 0, 520043516364, 2097464892721, 2137002589828, 448342102139, 20066671367, 0, 0] := by
  decide +kernel

theorem rows1499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1499 = true := by
  decide +kernel

theorem tot1499 : totK PA10K2 A10K2.t1499 = [0, 0, 509119267445, 1582441639887, 1608475940733, 940802935969, 408779399407, 42627403517, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
