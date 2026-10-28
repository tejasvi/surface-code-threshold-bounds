import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8084 = true := by
  decide +kernel

theorem tot8084 : totK PA10K2 A10K2.t8084 = [0, 0, 0, 0, 460201269034, 1815976004790, 2067897937268, 596505745684, 23361545837, 0] := by
  decide +kernel

theorem rows8085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8085 = true := by
  decide +kernel

theorem tot8085 : totK PA10K2 A10K2.t8085 = [0, 0, 0, 552913550463, 1878619695137, 1729116439831, 489681943501, 127940411264, 31681621791, 0] := by
  decide +kernel

theorem rows8086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8086 = true := by
  decide +kernel

theorem tot8086 : totK PA10K2 A10K2.t8086 = [0, 0, 0, 292221444102, 1456574550915, 2171001744664, 934795313930, 74544239664, 0, 0] := by
  decide +kernel

theorem rows8087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8087 = true := by
  decide +kernel

theorem tot8087 : totK PA10K2 A10K2.t8087 = [0, 0, 0, 0, 565342156694, 2033729842245, 1827781550780, 376716038081, 13576218110, 0] := by
  decide +kernel

end QECKChecks.A10K2
