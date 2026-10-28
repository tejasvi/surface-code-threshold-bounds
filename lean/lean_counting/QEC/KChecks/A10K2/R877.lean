import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3508 = true := by
  decide +kernel

theorem tot3508 : totK PA10K2 A10K2.t3508 = [0, 0, 0, 55204874504, 590820811106, 1842946658518, 1721803710018, 462124450139, 31452573850, 0] := by
  decide +kernel

theorem rows3509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3509 = true := by
  decide +kernel

theorem tot3509 : totK PA10K2 A10K2.t3509 = [0, 0, 0, 479585650632, 1776829167697, 1831344921606, 552276085917, 37254374173, 0, 0] := by
  decide +kernel

theorem rows3510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3510 = true := by
  decide +kernel

theorem tot3510 : totK PA10K2 A10K2.t3510 = [0, 0, 0, 212249636950, 1397866482329, 2214379052081, 851215604666, 52270131726, 0, 0] := by
  decide +kernel

theorem rows3511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3511 = true := by
  decide +kernel

theorem tot3511 : totK PA10K2 A10K2.t3511 = [0, 0, 0, 296591568744, 1210586578864, 1864060469074, 1138766339388, 203437793984, 6354482628, 0] := by
  decide +kernel

end QECKChecks.A10K2
