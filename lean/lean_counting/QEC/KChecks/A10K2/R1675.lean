import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6700 = true := by
  decide +kernel

theorem tot6700 : totK PA10K2 A10K2.t6700 = [0, 282722822571, 1503412990715, 2156627733674, 765801116481, 52575000838, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6701 = true := by
  decide +kernel

theorem tot6701 : totK PA10K2 A10K2.t6701 = [0, 0, 651862228393, 2112850187059, 1696439269158, 286830152235, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6702 = true := by
  decide +kernel

theorem tot6702 : totK PA10K2 A10K2.t6702 = [0, 0, 455451555154, 1769424304553, 1957526879491, 583503507637, 38551375656, 0, 0, 0] := by
  decide +kernel

theorem rows6703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6703 = true := by
  decide +kernel

theorem tot6703 : totK PA10K2 A10K2.t6703 = [0, 0, 555167666339, 1928801738665, 1815019054642, 418286091966, 24733829849, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
