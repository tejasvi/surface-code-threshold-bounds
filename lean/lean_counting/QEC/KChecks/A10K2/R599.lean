import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2396 = true := by
  decide +kernel

theorem tot2396 : totK PA10K2 A10K2.t2396 = [0, 0, 294077333717, 1479460433063, 2218555443520, 968754882161, 92818760178, 0, 0, 0] := by
  decide +kernel

theorem rows2397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2397 = true := by
  decide +kernel

theorem tot2397 : totK PA10K2 A10K2.t2397 = [0, 0, 361581015905, 1408260627265, 1902387728368, 1069457011302, 205250237772, 7237400819, 0, 0] := by
  decide +kernel

theorem rows2398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2398 = true := by
  decide +kernel

theorem tot2398 : totK PA10K2 A10K2.t2398 = [0, 0, 430820431812, 1793493615085, 2200100267610, 704409234770, 31503120867, 0, 0, 0] := by
  decide +kernel

theorem rows2399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2399 = true := by
  decide +kernel

theorem tot2399 : totK PA10K2 A10K2.t2399 = [0, 548589231577, 1894262495136, 1788124627311, 472123435392, 82598101020, 26048048901, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
