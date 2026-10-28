import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11688 = true := by
  decide +kernel

theorem tot11688 : totK PD2M8K2 D2M8K2.t11688 = [0, 65215932497, 353030627720, 364543748494, 63763375733, 1138244013, 0, 0] := by
  decide +kernel

theorem rows11689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11689 = true := by
  decide +kernel

theorem tot11689 : totK PD2M8K2 D2M8K2.t11689 = [0, 92859452576, 414551921183, 347808294136, 36439246183, 0, 0, 0] := by
  decide +kernel

theorem rows11690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11690 = true := by
  decide +kernel

theorem tot11690 : totK PD2M8K2 D2M8K2.t11690 = [0, 167702888163, 461803572172, 257424685803, 20732967584, 0, 0, 0] := by
  decide +kernel

theorem rows11691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11691 = true := by
  decide +kernel

theorem tot11691 : totK PD2M8K2 D2M8K2.t11691 = [0, 175323285333, 463023691330, 245889100551, 16975570248, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
