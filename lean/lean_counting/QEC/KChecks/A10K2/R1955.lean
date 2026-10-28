import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7820 = true := by
  decide +kernel

theorem tot7820 : totK PA10K2 A10K2.t7820 = [0, 0, 0, 455451555154, 1819123395787, 1981567063596, 514062079332, 31756067336, 0, 0] := by
  decide +kernel

theorem rows7821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7821 = true := by
  decide +kernel

theorem tot7821 : totK PA10K2 A10K2.t7821 = [0, 0, 0, 552306878858, 1901627096785, 1841118072595, 450689638718, 17528101294, 0, 0] := by
  decide +kernel

theorem rows7822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7822 = true := by
  decide +kernel

theorem tot7822 : totK PA10K2 A10K2.t7822 = [0, 0, 474573491002, 1485002891503, 1703324385001, 974847097670, 192750335334, 6356241174, 0, 0] := by
  decide +kernel

theorem rows7823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7823 = true := by
  decide +kernel

theorem tot7823 : totK PA10K2 A10K2.t7823 = [0, 0, 304479794002, 1577004908946, 2157035026364, 847846798400, 71230386845, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
