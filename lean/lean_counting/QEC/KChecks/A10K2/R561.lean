import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2244 = true := by
  decide +kernel

theorem tot2244 : totK PA10K2 A10K2.t2244 = [0, 0, 479327340802, 1837991772023, 2016481402655, 628054649320, 49180423016, 0, 0, 0] := by
  decide +kernel

theorem rows2245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2245 = true := by
  decide +kernel

theorem tot2245 : totK PA10K2 A10K2.t2245 = [0, 0, 370119675733, 1613466652072, 2120091403349, 828012480561, 62417866085, 0, 0, 0] := by
  decide +kernel

theorem rows2246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2246 = true := by
  decide +kernel

theorem tot2246 : totK PA10K2 A10K2.t2246 = [0, 0, 258065526149, 1085084388419, 1949486300419, 1364430407738, 222225963357, 6318667960, 0, 0] := by
  decide +kernel

theorem rows2247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2247 = true := by
  decide +kernel

theorem tot2247 : totK PA10K2 A10K2.t2247 = [0, 0, 524171185244, 1959597008447, 2032646839958, 488777320872, 12224988158, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
