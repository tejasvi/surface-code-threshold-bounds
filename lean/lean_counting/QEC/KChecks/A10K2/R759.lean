import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3036 = true := by
  decide +kernel

theorem tot3036 : totK PA10K2 A10K2.t3036 = [0, 0, 0, 529445687351, 1809376401953, 1750875551204, 475117929303, 31082886609, 0, 0] := by
  decide +kernel

theorem rows3037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3037 = true := by
  decide +kernel

theorem tot3037 : totK PA10K2 A10K2.t3037 = [0, 0, 435104128367, 1582375611073, 1980853285690, 779797660448, 70941582563, 0, 0, 0] := by
  decide +kernel

theorem rows3038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3038 = true := by
  decide +kernel

theorem tot3038 : totK PA10K2 A10K2.t3038 = [0, 0, 207856169637, 1420076453689, 2206912467125, 809190452443, 51697930226, 0, 0, 0] := by
  decide +kernel

theorem rows3039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3039 = true := by
  decide +kernel

theorem tot3039 : totK PA10K2 A10K2.t3039 = [0, 0, 484754278681, 1546454244536, 1760145298799, 897581048098, 155968788410, 5885702948, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
