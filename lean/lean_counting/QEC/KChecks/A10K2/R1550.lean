import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6200 = true := by
  decide +kernel

theorem tot6200 : totK PA10K2 A10K2.t6200 = [0, 39188486879, 912723303174, 2076488025515, 1409057376964, 314520183329, 25299471099, 0, 0, 0] := by
  decide +kernel

theorem rows6201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6201 = true := by
  decide +kernel

theorem tot6201 : totK PA10K2 A10K2.t6201 = [0, 374747736440, 1310490811444, 1756207839358, 1069117301249, 180515164561, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows6202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6202 = true := by
  decide +kernel

theorem tot6202 : totK PA10K2 A10K2.t6202 = [0, 445153241330, 1776489344926, 1958137086437, 513382852517, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6203 = true := by
  decide +kernel

theorem tot6203 : totK PA10K2 A10K2.t6203 = [0, 0, 815660459553, 2282373387657, 1421400344762, 155178628942, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
