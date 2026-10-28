import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6904 = true := by
  decide +kernel

theorem tot6904 : totK PA10K2 A10K2.t6904 = [0, 0, 574864650674, 1876212845337, 1893203426759, 602478477487, 49180423016, 0, 0, 0] := by
  decide +kernel

theorem rows6905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6905 = true := by
  decide +kernel

theorem tot6905 : totK PA10K2 A10K2.t6905 = [0, 0, 544583080767, 1896916998862, 1885430574020, 513149783268, 31080743953, 0, 0, 0] := by
  decide +kernel

theorem rows6906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6906 = true := by
  decide +kernel

theorem tot6906 : totK PA10K2 A10K2.t6906 = [0, 0, 0, 806340477447, 2280397597817, 1585720457925, 268480765259, 6904928264, 0, 0] := by
  decide +kernel

theorem rows6907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6907 = true := by
  decide +kernel

theorem tot6907 : totK PA10K2 A10K2.t6907 = [0, 0, 283437181451, 1422328515001, 2160901208848, 960537592646, 80231944999, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
