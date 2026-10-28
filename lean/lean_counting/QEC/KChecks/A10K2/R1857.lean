import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7428 = true := by
  decide +kernel

theorem tot7428 : totK PA10K2 A10K2.t7428 = [0, 549999419660, 1844708167659, 1819578387044, 530910115528, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7429 = true := by
  decide +kernel

theorem tot7429 : totK PA10K2 A10K2.t7429 = [0, 0, 709556952574, 2096598167638, 1696161886046, 398234123747, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows7430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7430 = true := by
  decide +kernel

theorem tot7430 : totK PA10K2 A10K2.t7430 = [0, 117220615846, 894761628572, 1950756573225, 1450761126322, 244526670997, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows7431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7431 = true := by
  decide +kernel

theorem tot7431 : totK PA10K2 A10K2.t7431 = [0, 566401075718, 1821531850010, 1757550766238, 522935553658, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
