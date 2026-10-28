import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7364 = true := by
  decide +kernel

theorem tot7364 : totK PA10K2 A10K2.t7364 = [0, 0, 112037851608, 693526138644, 1861284417201, 1669713173191, 363427434719, 15885829643, 0, 0] := by
  decide +kernel

theorem rows7365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7365 = true := by
  decide +kernel

theorem tot7365 : totK PA10K2 A10K2.t7365 = [0, 0, 482295539168, 1817747389841, 1927054551070, 524898732349, 31614405859, 0, 0, 0] := by
  decide +kernel

theorem rows7366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7366 = true := by
  decide +kernel

theorem tot7366 : totK PA10K2 A10K2.t7366 = [0, 0, 145986839570, 1286844158227, 2275533661283, 947129089771, 65956421278, 0, 0, 0] := by
  decide +kernel

theorem rows7367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7367 = true := by
  decide +kernel

theorem tot7367 : totK PA10K2 A10K2.t7367 = [0, 0, 297392362862, 1258294528843, 1907102932169, 1095103497863, 174654832750, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
