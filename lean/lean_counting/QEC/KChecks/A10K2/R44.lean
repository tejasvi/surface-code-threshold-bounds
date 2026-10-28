import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t176 = true := by
  decide +kernel

theorem tot176 : totK PA10K2 A10K2.t176 = [0, 57479399761, 737116559042, 2127742234301, 1627335320986, 285588936065, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t177 = true := by
  decide +kernel

theorem tot177 : totK PA10K2 A10K2.t177 = [0, 569743507729, 2008403791016, 1958938544478, 496940444117, 25853956325, 0, 0, 0, 0] := by
  decide +kernel

theorem rows178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t178 = true := by
  decide +kernel

theorem tot178 : totK PA10K2 A10K2.t178 = [0, 0, 813982523826, 2261117392693, 1618820593218, 269694839587, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t179 = true := by
  decide +kernel

theorem tot179 : totK PA10K2 A10K2.t179 = [0, 542321336211, 1868376998289, 1864566816986, 600044861512, 50403516269, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
