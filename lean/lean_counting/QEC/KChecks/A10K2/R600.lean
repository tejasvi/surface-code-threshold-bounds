import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2400 = true := by
  decide +kernel

theorem tot2400 : totK PA10K2 A10K2.t2400 = [0, 296440474885, 1450013805604, 2195094091252, 966870736045, 84152717924, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2401 = true := by
  decide +kernel

theorem tot2401 : totK PA10K2 A10K2.t2401 = [0, 0, 469341309745, 1820519442347, 1924216970919, 510751560097, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows2402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2402 = true := by
  decide +kernel

theorem tot2402 : totK PA10K2 A10K2.t2402 = [0, 554851874388, 1786147438504, 1800588826355, 680705214647, 65283187088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2403 = true := by
  decide +kernel

theorem tot2403 : totK PA10K2 A10K2.t2403 = [0, 0, 903003651191, 2322513320364, 1303202951230, 127046362769, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
