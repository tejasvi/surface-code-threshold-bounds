import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3564 = true := by
  decide +kernel

theorem tot3564 : totK PD2M8K2 D2M8K2.t3564 = [0, 93184785870, 414693811964, 354215968570, 38604271807, 0, 0, 0] := by
  decide +kernel

theorem rows3565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3565 = true := by
  decide +kernel

theorem tot3565 : totK PD2M8K2 D2M8K2.t3565 = [0, 173764452113, 455467440971, 250900604900, 20708744937, 0, 0, 0] := by
  decide +kernel

theorem rows3566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3566 = true := by
  decide +kernel

theorem tot3566 : totK PD2M8K2 D2M8K2.t3566 = [0, 195255017286, 476945622803, 227486882349, 12284615083, 0, 0, 0] := by
  decide +kernel

theorem rows3567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3567 = true := by
  decide +kernel

theorem tot3567 : totK PD2M8K2 D2M8K2.t3567 = [0, 192353814996, 472221285714, 219359252465, 11051716772, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
