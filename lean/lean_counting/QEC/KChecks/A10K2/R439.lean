import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1756 = true := by
  decide +kernel

theorem tot1756 : totK PA10K2 A10K2.t1756 = [0, 0, 511932739568, 1758752805072, 1789344318554, 580563299126, 52567449820, 0, 0, 0] := by
  decide +kernel

theorem rows1757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1757 = true := by
  decide +kernel

theorem tot1757 : totK PA10K2 A10K2.t1757 = [0, 0, 304062355366, 1537825669400, 2088773963758, 724027409231, 39144606383, 0, 0, 0] := by
  decide +kernel

theorem rows1758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1758 = true := by
  decide +kernel

theorem tot1758 : totK PA10K2 A10K2.t1758 = [0, 0, 0, 676377178190, 2154110967328, 1575610637402, 262931578621, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1759 = true := by
  decide +kernel

theorem tot1759 : totK PA10K2 A10K2.t1759 = [0, 0, 0, 462231311472, 1820526153108, 1977876122529, 458330383710, 17013136330, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
