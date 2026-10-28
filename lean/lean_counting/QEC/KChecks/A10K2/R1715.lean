import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6860 = true := by
  decide +kernel

theorem tot6860 : totK PA10K2 A10K2.t6860 = [0, 0, 573948339552, 2005499989927, 1832486322422, 387263209878, 12219140272, 0, 0, 0] := by
  decide +kernel

theorem rows6861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6861 = true := by
  decide +kernel

theorem tot6861 : totK PA10K2 A10K2.t6861 = [0, 390246659287, 1562828697834, 2053390276781, 915024885783, 90120369798, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6862 = true := by
  decide +kernel

theorem tot6862 : totK PA10K2 A10K2.t6862 = [0, 504204779070, 1909471478324, 2031774825878, 561522584543, 23755459583, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6863 = true := by
  decide +kernel

theorem tot6863 : totK PA10K2 A10K2.t6863 = [0, 0, 683429617342, 2194777702755, 1807892248105, 292792895752, 6772895877, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
