import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6176 = true := by
  decide +kernel

theorem tot6176 : totK PA10K2 A10K2.t6176 = [0, 0, 390892848874, 1676970529920, 2081894144317, 707422874841, 46999956509, 0, 0, 0] := by
  decide +kernel

theorem rows6177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6177 = true := by
  decide +kernel

theorem tot6177 : totK PA10K2 A10K2.t6177 = [0, 0, 15945489470, 685695315595, 2174552404573, 1655135693324, 325002390847, 20058242317, 0, 0] := by
  decide +kernel

theorem rows6178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6178 = true := by
  decide +kernel

theorem tot6178 : totK PA10K2 A10K2.t6178 = [0, 0, 669352801391, 2024546211961, 1793569460428, 586299636244, 50543460435, 0, 0, 0] := by
  decide +kernel

theorem rows6179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6179 = true := by
  decide +kernel

theorem tot6179 : totK PA10K2 A10K2.t6179 = [0, 0, 547135428343, 1992290587037, 2020067008795, 523448837436, 21929649243, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
