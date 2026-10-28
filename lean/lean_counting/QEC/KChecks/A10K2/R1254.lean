import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5016 = true := by
  decide +kernel

theorem tot5016 : totK PA10K2 A10K2.t5016 = [0, 0, 654227645947, 1985459922111, 1648870959681, 397330561561, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows5017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5017 = true := by
  decide +kernel

theorem tot5017 : totK PA10K2 A10K2.t5017 = [0, 314342126396, 1102619679823, 1810408789094, 1242925878502, 209965670489, 5718040558, 0, 0, 0] := by
  decide +kernel

theorem rows5018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5018 = true := by
  decide +kernel

theorem tot5018 : totK PA10K2 A10K2.t5018 = [0, 470624164805, 1888548861232, 1938105667372, 488084505216, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5019 = true := by
  decide +kernel

theorem tot5019 : totK PA10K2 A10K2.t5019 = [0, 0, 857367734989, 2380631441598, 1360090653694, 133428564204, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
