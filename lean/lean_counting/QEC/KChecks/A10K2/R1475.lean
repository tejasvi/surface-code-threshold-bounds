import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5900 = true := by
  decide +kernel

theorem tot5900 : totK PA10K2 A10K2.t5900 = [321107158991, 896443492795, 584076478167, 73857469276, 0, 374263588326, 1233212591026, 990914908768, 213642913445, 6354482628] := by
  decide +kernel

theorem rows5901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5901 = true := by
  decide +kernel

theorem tot5901 : totK PA10K2 A10K2.t5901 = [504086846167, 1786987598697, 1883182132294, 529599529477, 32040661968, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5902 = true := by
  decide +kernel

theorem tot5902 : totK PA10K2 A10K2.t5902 = [44706116827, 813914727413, 2093455025086, 1570143114427, 366317013569, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5903 = true := by
  decide +kernel

theorem tot5903 : totK PA10K2 A10K2.t5903 = [188737155786, 956669661604, 1952634764291, 1415684234415, 236806179955, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
