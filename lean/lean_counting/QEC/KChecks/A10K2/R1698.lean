import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6792 = true := by
  decide +kernel

theorem tot6792 : totK PA10K2 A10K2.t6792 = [0, 509925155316, 1730957221883, 1771928130213, 613166275528, 62981882744, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6793 = true := by
  decide +kernel

theorem tot6793 : totK PA10K2 A10K2.t6793 = [0, 297007965898, 1503493104142, 2178538438086, 828869770354, 60544467592, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6794 = true := by
  decide +kernel

theorem tot6794 : totK PA10K2 A10K2.t6794 = [0, 0, 488724061216, 1768108351924, 1757718987168, 476793114234, 30650496230, 0, 0, 0] := by
  decide +kernel

theorem rows6795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6795 = true := by
  decide +kernel

theorem tot6795 : totK PA10K2 A10K2.t6795 = [0, 439243362846, 1704074536452, 1911941656057, 614635611367, 57163933948, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
