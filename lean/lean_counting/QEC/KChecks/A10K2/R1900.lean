import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7600 = true := by
  decide +kernel

theorem tot7600 : totK PA10K2 A10K2.t7600 = [0, 0, 0, 479850183922, 1743191834856, 1956965493719, 684843009812, 56620251112, 0, 0] := by
  decide +kernel

theorem rows7601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7601 = true := by
  decide +kernel

theorem tot7601 : totK PA10K2 A10K2.t7601 = [0, 0, 0, 295773208175, 1515436031956, 2253311846496, 895901020354, 65128938376, 0, 0] := by
  decide +kernel

theorem rows7602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7602 = true := by
  decide +kernel

theorem tot7602 : totK PA10K2 A10K2.t7602 = [0, 0, 0, 284564927155, 1334838713096, 2022643578729, 1089091191261, 173913626682, 7007974415, 0] := by
  decide +kernel

theorem rows7603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7603 = true := by
  decide +kernel

theorem tot7603 : totK PA10K2 A10K2.t7603 = [0, 0, 0, 539273461554, 2029005998713, 2150805509258, 487962165240, 13099660728, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
