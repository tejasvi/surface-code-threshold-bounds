import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7804 = true := by
  decide +kernel

theorem tot7804 : totK PA10K2 A10K2.t7804 = [0, 0, 483220809128, 1687230336327, 1922313445838, 703502022177, 60637426455, 0, 0, 0] := by
  decide +kernel

theorem rows7805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7805 = true := by
  decide +kernel

theorem tot7805 : totK PA10K2 A10K2.t7805 = [0, 0, 99260196026, 1132878556332, 2236511690291, 1005065445725, 92431429569, 0, 0, 0] := by
  decide +kernel

theorem rows7806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7806 = true := by
  decide +kernel

theorem tot7806 : totK PA10K2 A10K2.t7806 = [0, 0, 488352769765, 1685161108838, 1843765301089, 782610736493, 133798624358, 5705019915, 0, 0] := by
  decide +kernel

theorem rows7807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7807 = true := by
  decide +kernel

theorem tot7807 : totK PA10K2 A10K2.t7807 = [0, 0, 314008318368, 1487864756759, 2155391916902, 951619447845, 83540878628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
