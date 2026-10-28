import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7220 = true := by
  decide +kernel

theorem tot7220 : totK PA10K2 A10K2.t7220 = [0, 0, 524584402786, 1965620620162, 2119085064315, 537353375321, 19707287507, 0, 0, 0] := by
  decide +kernel

theorem rows7221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7221 = true := by
  decide +kernel

theorem tot7221 : totK PA10K2 A10K2.t7221 = [0, 0, 430576545565, 1648257067782, 2009185621116, 754410953257, 68939555567, 0, 0, 0] := by
  decide +kernel

theorem rows7222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7222 = true := by
  decide +kernel

theorem tot7222 : totK PA10K2 A10K2.t7222 = [0, 0, 400811964952, 1725046822230, 2043101673163, 607517397279, 34548791282, 0, 0, 0] := by
  decide +kernel

theorem rows7223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7223 = true := by
  decide +kernel

theorem tot7223 : totK PA10K2 A10K2.t7223 = [0, 0, 0, 455503680426, 1711572147958, 1756648174808, 488117855432, 30650496230, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
