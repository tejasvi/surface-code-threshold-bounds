import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6648 = true := by
  decide +kernel

theorem tot6648 : totK PD2M8K2 D2M8K2.t6648 = [0, 185521629093, 472626860241, 231650007532, 12459280195, 0, 0, 0] := by
  decide +kernel

theorem rows6649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6649 = true := by
  decide +kernel

theorem tot6649 : totK PD2M8K2 D2M8K2.t6649 = [0, 29761960362, 353599595367, 457319388517, 71454431354, 0, 0, 0] := by
  decide +kernel

theorem rows6650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6650 = true := by
  decide +kernel

theorem tot6650 : totK PD2M8K2 D2M8K2.t6650 = [0, 51100556257, 227039171097, 407948099954, 178016010486, 12040273252, 0, 0] := by
  decide +kernel

theorem rows6651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6651 = true := by
  decide +kernel

theorem tot6651 : totK PD2M8K2 D2M8K2.t6651 = [0, 194380853917, 463150515497, 243292839394, 23368436261, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
