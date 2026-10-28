import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1348 = true := by
  decide +kernel

theorem tot1348 : totK PA10K2 A10K2.t1348 = [0, 0, 0, 383851902785, 1617123620360, 2073117161514, 785853096026, 61177778713, 0, 0] := by
  decide +kernel

theorem rows1349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1349 = true := by
  decide +kernel

theorem tot1349 : totK PA10K2 A10K2.t1349 = [0, 0, 0, 475463374944, 1790857280119, 2007863670636, 662997519965, 42548192499, 0, 0] := by
  decide +kernel

theorem rows1350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1350 = true := by
  decide +kernel

theorem tot1350 : totK PA10K2 A10K2.t1350 = [0, 0, 0, 107718095036, 918191493179, 2211656302120, 1416667583597, 214398535481, 6318667960, 0] := by
  decide +kernel

theorem rows1351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1351 = true := by
  decide +kernel

theorem tot1351 : totK PA10K2 A10K2.t1351 = [0, 0, 0, 661723575343, 1971130491724, 1781216488565, 587845743498, 50414133861, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
