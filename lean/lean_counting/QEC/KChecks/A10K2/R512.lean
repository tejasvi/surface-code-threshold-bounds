import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2048 = true := by
  decide +kernel

theorem tot2048 : totK PA10K2 A10K2.t2048 = [477984308118, 1467115207638, 1721462612098, 951180071585, 160634622618, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2049 = true := by
  decide +kernel

theorem tot2049 : totK PA10K2 A10K2.t2049 = [325843893375, 1627463957438, 2179221493014, 810952472813, 70794459365, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2050 = true := by
  decide +kernel

theorem tot2050 : totK PA10K2 A10K2.t2050 = [0, 474221362135, 1839330305162, 1921452970855, 504543508877, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2051 = true := by
  decide +kernel

theorem tot2051 : totK PA10K2 A10K2.t2051 = [476246592928, 1645164295708, 1769373834428, 717614396495, 83775891897, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
