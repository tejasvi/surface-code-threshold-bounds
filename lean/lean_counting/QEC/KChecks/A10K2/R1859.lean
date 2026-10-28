import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7436 = true := by
  decide +kernel

theorem tot7436 : totK PA10K2 A10K2.t7436 = [0, 0, 320437926777, 1520026675058, 2129746539863, 857598364469, 75408522201, 0, 0, 0] := by
  decide +kernel

theorem rows7437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7437 = true := by
  decide +kernel

theorem tot7437 : totK PA10K2 A10K2.t7437 = [0, 0, 548517348802, 1922610150644, 1903046370509, 464400762165, 12917769548, 0, 0, 0] := by
  decide +kernel

theorem rows7438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7438 = true := by
  decide +kernel

theorem tot7438 : totK PA10K2 A10K2.t7438 = [0, 0, 0, 651265371163, 2007461832716, 1621804888172, 391413943146, 25565504801, 0, 0] := by
  decide +kernel

theorem rows7439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7439 = true := by
  decide +kernel

theorem tot7439 : totK PA10K2 A10K2.t7439 = [0, 0, 380936229014, 1351417299883, 1733286176456, 999159783468, 178995699509, 5517381808, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
