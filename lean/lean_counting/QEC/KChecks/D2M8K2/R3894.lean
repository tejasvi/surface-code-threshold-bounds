import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15576 = true := by
  decide +kernel

theorem tot15576 : totK PD2M8K2 D2M8K2.t15576 = [0, 93301704879, 382242883235, 389462725168, 44030752496, 0, 0, 0] := by
  decide +kernel

theorem rows15577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15577 = true := by
  decide +kernel

theorem tot15577 : totK PD2M8K2 D2M8K2.t15577 = [0, 157709213066, 446902669837, 291989289527, 30468211203, 0, 0, 0] := by
  decide +kernel

theorem rows15578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15578 = true := by
  decide +kernel

theorem tot15578 : totK PD2M8K2 D2M8K2.t15578 = [0, 172532957301, 463305022014, 239608884625, 12461938336, 0, 0, 0] := by
  decide +kernel

theorem rows15579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15579 = true := by
  decide +kernel

theorem tot15579 : totK PD2M8K2 D2M8K2.t15579 = [0, 0, 201606382626, 469247609731, 225495068074, 21156758932, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
