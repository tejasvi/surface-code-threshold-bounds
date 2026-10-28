import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1840 = true := by
  decide +kernel

theorem tot1840 : totK PA10K2 A10K2.t1840 = [0, 275897505342, 1520555879762, 2202557568833, 879520713708, 74294849262, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1841 = true := by
  decide +kernel

theorem tot1841 : totK PA10K2 A10K2.t1841 = [0, 0, 509677806286, 1894542218765, 1843424477242, 485476602699, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows1842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1842 = true := by
  decide +kernel

theorem tot1842 : totK PA10K2 A10K2.t1842 = [0, 490963330377, 1732599072222, 1898327972288, 702605031935, 68016314281, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1843 = true := by
  decide +kernel

theorem tot1843 : totK PA10K2 A10K2.t1843 = [0, 236337365920, 1430890917212, 2175776641779, 838824634477, 45545545079, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
