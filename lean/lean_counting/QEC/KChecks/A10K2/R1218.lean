import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4872 = true := by
  decide +kernel

theorem tot4872 : totK PA10K2 A10K2.t4872 = [0, 0, 287679457275, 1152632319452, 1818937798906, 1114835598066, 186084294959, 5365973533, 0, 0] := by
  decide +kernel

theorem rows4873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4873 = true := by
  decide +kernel

theorem tot4873 : totK PA10K2 A10K2.t4873 = [0, 0, 452890738341, 1796478752735, 1868161521640, 473196447321, 30954851499, 0, 0, 0] := by
  decide +kernel

theorem rows4874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4874 = true := by
  decide +kernel

theorem tot4874 : totK PA10K2 A10K2.t4874 = [0, 0, 0, 905283791125, 2350069298795, 1128467176222, 97111396872, 0, 0, 0] := by
  decide +kernel

theorem rows4875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4875 = true := by
  decide +kernel

theorem tot4875 : totK PA10K2 A10K2.t4875 = [0, 0, 622765862201, 1905888726811, 1688067190440, 550629576688, 114566238167, 5528811039, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
