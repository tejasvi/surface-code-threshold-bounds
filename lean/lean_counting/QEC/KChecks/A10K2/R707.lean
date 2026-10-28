import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2828 = true := by
  decide +kernel

theorem tot2828 : totK PA10K2 A10K2.t2828 = [308899695994, 1168253240289, 1635524277895, 1368883848178, 547617322660, 50499610055, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2829 = true := by
  decide +kernel

theorem tot2829 : totK PA10K2 A10K2.t2829 = [487594984600, 1813191789593, 2010861041901, 596576556513, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2830 = true := by
  decide +kernel

theorem tot2830 : totK PA10K2 A10K2.t2830 = [0, 647758098801, 2066863541520, 1780562946388, 420246654801, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2831 = true := by
  decide +kernel

theorem tot2831 : totK PA10K2 A10K2.t2831 = [282932941769, 1128124313420, 1853724734572, 1313935622645, 233537392366, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
