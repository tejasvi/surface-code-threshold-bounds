import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7908 = true := by
  decide +kernel

theorem tot7908 : totK PA10K2 A10K2.t7908 = [0, 0, 297007965898, 1396086066597, 2131972516151, 1057783096363, 104071152193, 0, 0, 0] := by
  decide +kernel

theorem rows7909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7909 = true := by
  decide +kernel

theorem tot7909 : totK PA10K2 A10K2.t7909 = [0, 0, 125480006751, 791103049887, 1738979572918, 1493828068342, 383127327636, 18459763130, 0, 0] := by
  decide +kernel

theorem rows7910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7910 = true := by
  decide +kernel

theorem tot7910 : totK PA10K2 A10K2.t7910 = [0, 0, 300727260569, 1560491197039, 2079081552542, 709694779940, 52225481209, 0, 0, 0] := by
  decide +kernel

theorem rows7911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7911 = true := by
  decide +kernel

theorem tot7911 : totK PA10K2 A10K2.t7911 = [0, 0, 449610349265, 1581189037525, 1908544637568, 803969387336, 93856404604, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
