import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2144 = true := by
  decide +kernel

theorem tot2144 : totK PA10K2 A10K2.t2144 = [0, 468566045184, 1807270221409, 1981700916162, 554430721080, 32470943963, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2145 = true := by
  decide +kernel

theorem tot2145 : totK PA10K2 A10K2.t2145 = [0, 511375925591, 1772286027011, 1792165854404, 488870519681, 31607162994, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2146 = true := by
  decide +kernel

theorem tot2146 : totK PA10K2 A10K2.t2146 = [0, 306484836393, 1499709986740, 2046970141775, 730738657589, 57778438788, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2147 = true := by
  decide +kernel

theorem tot2147 : totK PA10K2 A10K2.t2147 = [0, 211144047225, 1015774025063, 1932240977792, 1215438523384, 233528391130, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
