import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5424 = true := by
  decide +kernel

theorem tot5424 : totK PA10K2 A10K2.t5424 = [0, 0, 0, 441261093887, 1695571668822, 1840906157027, 630089315797, 112753681009, 5453062850, 0] := by
  decide +kernel

theorem rows5425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5425 = true := by
  decide +kernel

theorem tot5425 : totK PA10K2 A10K2.t5425 = [0, 0, 0, 279666710650, 1498107201086, 2039917596479, 683660230235, 44427577536, 0, 0] := by
  decide +kernel

theorem rows5426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5426 = true := by
  decide +kernel

theorem tot5426 : totK PA10K2 A10K2.t5426 = [0, 0, 0, 354475418339, 1258344223579, 1834957163070, 1041340735116, 166709727041, 5685526223, 0] := by
  decide +kernel

theorem rows5427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5427 = true := by
  decide +kernel

theorem tot5427 : totK PA10K2 A10K2.t5427 = [0, 0, 103649551945, 594059293195, 1736495308110, 1957031475076, 622044432747, 50566590589, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
