import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8740 = true := by
  decide +kernel

theorem tot8740 : totK PD2M8K2 D2M8K2.t8740 = [0, 191813967115, 479197485164, 222253695750, 12374132423, 0, 0, 0] := by
  decide +kernel

theorem rows8741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8741 = true := by
  decide +kernel

theorem tot8741 : totK PD2M8K2 D2M8K2.t8741 = [0, 19382938638, 261910631355, 419266411821, 191778933681, 21393864572, 0, 0] := by
  decide +kernel

theorem rows8742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8742 = true := by
  decide +kernel

theorem tot8742 : totK PD2M8K2 D2M8K2.t8742 = [0, 0, 204203030557, 485570224989, 199136427788, 7926071017, 0, 0] := by
  decide +kernel

theorem rows8743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8743 = true := by
  decide +kernel

theorem tot8743 : totK PD2M8K2 D2M8K2.t8743 = [0, 83047329000, 269269613346, 357958512215, 171841159547, 8165763945, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
