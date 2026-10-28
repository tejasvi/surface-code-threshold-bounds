import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1244 = true := by
  decide +kernel

theorem tot1244 : totK PA10K2 A10K2.t1244 = [0, 440075106148, 1805059361139, 1999217155184, 607515804265, 44340342341, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1245 = true := by
  decide +kernel

theorem tot1245 : totK PA10K2 A10K2.t1245 = [0, 0, 465917001974, 1896238710350, 1867849642430, 428402327926, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows1246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1246 = true := by
  decide +kernel

theorem tot1246 : totK PA10K2 A10K2.t1246 = [0, 479886617282, 1581057648656, 1776694348187, 746238491870, 141866440587, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows1247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1247 = true := by
  decide +kernel

theorem tot1247 : totK PA10K2 A10K2.t1247 = [0, 105065813562, 1033522390599, 1982528600069, 1249106046537, 290161809499, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
