import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4640 = true := by
  decide +kernel

theorem tot4640 : totK PA10K2 A10K2.t4640 = [0, 477476970137, 1777931446344, 1927787456442, 664492253338, 65072729335, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4641 = true := by
  decide +kernel

theorem tot4641 : totK PA10K2 A10K2.t4641 = [0, 306418931549, 1444217020107, 2196468934622, 1017880873810, 84605316068, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4642 = true := by
  decide +kernel

theorem tot4642 : totK PA10K2 A10K2.t4642 = [0, 105375790585, 718522183214, 1875217688377, 1757134028287, 393236082500, 12219140272, 0, 0, 0] := by
  decide +kernel

theorem rows4643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4643 = true := by
  decide +kernel

theorem tot4643 : totK PA10K2 A10K2.t4643 = [0, 517900140226, 1847790754351, 2006801514297, 605222946261, 33478807015, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
