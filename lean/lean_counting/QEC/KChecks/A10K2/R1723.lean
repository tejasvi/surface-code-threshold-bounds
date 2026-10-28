import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6892 = true := by
  decide +kernel

theorem tot6892 : totK PA10K2 A10K2.t6892 = [0, 0, 781267890454, 2197208303365, 1475396917483, 248247668465, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6893 = true := by
  decide +kernel

theorem tot6893 : totK PA10K2 A10K2.t6893 = [0, 0, 497197013438, 1917086212188, 1869933164971, 436680424165, 25633273041, 0, 0, 0] := by
  decide +kernel

theorem rows6894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6894 = true := by
  decide +kernel

theorem tot6894 : totK PA10K2 A10K2.t6894 = [0, 0, 494506769503, 1798803720577, 2028635883198, 578463342498, 37505681260, 0, 0, 0] := by
  decide +kernel

theorem rows6895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6895 = true := by
  decide +kernel

theorem tot6895 : totK PA10K2 A10K2.t6895 = [0, 0, 265896857807, 1491170531585, 2107553349462, 738168836423, 57537222032, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
