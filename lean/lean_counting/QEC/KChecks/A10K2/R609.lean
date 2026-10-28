import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2436 = true := by
  decide +kernel

theorem tot2436 : totK PA10K2 A10K2.t2436 = [404033483427, 1400772468302, 1803324224500, 1029627770668, 199803129821, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2437 = true := by
  decide +kernel

theorem tot2437 : totK PA10K2 A10K2.t2437 = [189869214249, 1186068306247, 2151059233985, 1346701506979, 232640472054, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2438 = true := by
  decide +kernel

theorem tot2438 : totK PA10K2 A10K2.t2438 = [0, 582891561939, 1933749218493, 1897713043419, 591842584033, 49047233835, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2439 = true := by
  decide +kernel

theorem tot2439 : totK PA10K2 A10K2.t2439 = [0, 427909425314, 1798475743286, 2012573990028, 521810924092, 31222411477, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
