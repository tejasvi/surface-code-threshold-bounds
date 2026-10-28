import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2492 = true := by
  decide +kernel

theorem tot2492 : totK PA10K2 A10K2.t2492 = [0, 775856380721, 2317654235460, 1750940448019, 323763843535, 6962742351, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2493 = true := by
  decide +kernel

theorem tot2493 : totK PA10K2 A10K2.t2493 = [0, 611821954803, 1966557428947, 1860696792222, 579308436302, 48289658145, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2494 = true := by
  decide +kernel

theorem tot2494 : totK PA10K2 A10K2.t2494 = [0, 438345101869, 1784864411932, 2011341458974, 554376224827, 32523532663, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2495 = true := by
  decide +kernel

theorem tot2495 : totK PA10K2 A10K2.t2495 = [0, 99865853507, 881715706504, 2027328926515, 1472624165285, 347370402244, 25565504801, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
