import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5488 = true := by
  decide +kernel

theorem tot5488 : totK PA10K2 A10K2.t5488 = [0, 0, 276491011440, 1189583608504, 1921444440027, 1169333274171, 177776125405, 5447185874, 0, 0] := by
  decide +kernel

theorem rows5489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5489 = true := by
  decide +kernel

theorem tot5489 : totK PA10K2 A10K2.t5489 = [0, 0, 500180958923, 1851475991022, 1899731985077, 507846533524, 31174170042, 0, 0, 0] := by
  decide +kernel

theorem rows5490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5490 = true := by
  decide +kernel

theorem tot5490 : totK PA10K2 A10K2.t5490 = [0, 0, 0, 819890846263, 2362456644302, 1385154868590, 147894094937, 0, 0, 0] := by
  decide +kernel

theorem rows5491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5491 = true := by
  decide +kernel

theorem tot5491 : totK PA10K2 A10K2.t5491 = [0, 0, 536977226750, 1653665601917, 1714395278518, 749079379130, 153150958960, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
