import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7352 = true := by
  decide +kernel

theorem tot7352 : totK PA10K2 A10K2.t7352 = [0, 0, 0, 360813814892, 1312711964365, 1886103740086, 973685640766, 150009337512, 5460492893, 0] := by
  decide +kernel

theorem rows7353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7353 = true := by
  decide +kernel

theorem tot7353 : totK PA10K2 A10K2.t7353 = [0, 0, 0, 510967298234, 1844887973937, 1887065563167, 491742947056, 31614405859, 0, 0] := by
  decide +kernel

theorem rows7354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7354 = true := by
  decide +kernel

theorem tot7354 : totK PA10K2 A10K2.t7354 = [0, 0, 0, 112121117221, 1290643277996, 2258532461914, 885459509433, 59149238308, 0, 0] := by
  decide +kernel

theorem rows7355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7355 = true := by
  decide +kernel

theorem tot7355 : totK PA10K2 A10K2.t7355 = [0, 0, 0, 350047210121, 1301745424221, 1904877290997, 1026412084517, 162449221314, 6354482628, 0] := by
  decide +kernel

end QECKChecks.A10K2
