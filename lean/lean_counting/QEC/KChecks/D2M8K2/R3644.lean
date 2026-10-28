import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14576 = true := by
  decide +kernel

theorem tot14576 : totK PD2M8K2 D2M8K2.t14576 = [156893719422, 407933443703, 283482257348, 61592200087, 2567510802, 0, 0, 0] := by
  decide +kernel

theorem rows14577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14577 = true := by
  decide +kernel

theorem tot14577 : totK PD2M8K2 D2M8K2.t14577 = [173371806802, 449640741550, 272787446923, 28476205713, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14578 = true := by
  decide +kernel

theorem tot14578 : totK PD2M8K2 D2M8K2.t14578 = [112771130407, 428475680329, 342852547780, 30328117773, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14579 = true := by
  decide +kernel

theorem tot14579 : totK PD2M8K2 D2M8K2.t14579 = [0, 216619879603, 496450806053, 174683890157, 4967996017, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
