import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t444 = true := by
  decide +kernel

theorem tot444 : totK PD2M8K2 D2M8K2.t444 = [0, 171772590286, 435318972778, 266942507239, 27824195375, 0, 0, 0] := by
  decide +kernel

theorem rows445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t445 = true := by
  decide +kernel

theorem tot445 : totK PD2M8K2 D2M8K2.t445 = [0, 114583742660, 429885897770, 318551744070, 24939523957, 0, 0, 0] := by
  decide +kernel

theorem rows446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t446 = true := by
  decide +kernel

theorem tot446 : totK PD2M8K2 D2M8K2.t446 = [0, 0, 238045533150, 476380789909, 138763760627, 4879840392, 0, 0] := by
  decide +kernel

theorem rows447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t447 = true := by
  decide +kernel

theorem tot447 : totK PD2M8K2 D2M8K2.t447 = [0, 152040728086, 436944604582, 288198593712, 32377756673, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
