import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7236 = true := by
  decide +kernel

theorem tot7236 : totK PA10K2 A10K2.t7236 = [0, 0, 504994073445, 1907485749158, 2069860554049, 678014069528, 52400351334, 0, 0, 0] := by
  decide +kernel

theorem rows7237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7237 = true := by
  decide +kernel

theorem tot7237 : totK PA10K2 A10K2.t7237 = [0, 113839911969, 552765066325, 1511210783711, 1997411259262, 834158887353, 69194875693, 0, 0, 0] := by
  decide +kernel

theorem rows7238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7238 = true := by
  decide +kernel

theorem tot7238 : totK PA10K2 A10K2.t7238 = [0, 513218372034, 1841089923963, 1891591612477, 511862672192, 31863753596, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7239 = true := by
  decide +kernel

theorem tot7239 : totK PA10K2 A10K2.t7239 = [0, 136105507251, 1075168274089, 2119270886128, 1358358818441, 275400896274, 20029934272, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
