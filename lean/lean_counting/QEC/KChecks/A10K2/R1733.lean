import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6932 = true := by
  decide +kernel

theorem tot6932 : totK PA10K2 A10K2.t6932 = [0, 0, 0, 675660449391, 2071626056525, 1716108473882, 364010602211, 12473006693, 0, 0] := by
  decide +kernel

theorem rows6933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6933 = true := by
  decide +kernel

theorem tot6933 : totK PA10K2 A10K2.t6933 = [0, 0, 545310583547, 1815266904880, 1896976739697, 702377231084, 57873648507, 0, 0, 0] := by
  decide +kernel

theorem rows6934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6934 = true := by
  decide +kernel

theorem tot6934 : totK PA10K2 A10K2.t6934 = [0, 0, 45277493360, 933735533832, 2308759359057, 1544121092192, 229985399186, 6860445330, 0, 0] := by
  decide +kernel

theorem rows6935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6935 = true := by
  decide +kernel

theorem tot6935 : totK PA10K2 A10K2.t6935 = [0, 0, 540757303387, 1762136982844, 1881283707368, 720082387291, 68099212795, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
