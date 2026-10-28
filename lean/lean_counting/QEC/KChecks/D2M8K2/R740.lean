import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2960 = true := by
  decide +kernel

theorem tot2960 : totK PD2M8K2 D2M8K2.t2960 = [0, 194774450497, 470634553635, 240644036003, 20855590267, 0, 0, 0] := by
  decide +kernel

theorem rows2961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2961 = true := by
  decide +kernel

theorem tot2961 : totK PD2M8K2 D2M8K2.t2961 = [0, 107565863211, 410998705458, 347071621048, 36982091642, 0, 0, 0] := by
  decide +kernel

theorem rows2962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2962 = true := by
  decide +kernel

theorem tot2962 : totK PD2M8K2 D2M8K2.t2962 = [0, 0, 254883372683, 485464551865, 137580960019, 4931404646, 0, 0] := by
  decide +kernel

theorem rows2963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2963 = true := by
  decide +kernel

theorem tot2963 : totK PD2M8K2 D2M8K2.t2963 = [0, 183944966428, 449763985138, 245963683835, 24491231681, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
