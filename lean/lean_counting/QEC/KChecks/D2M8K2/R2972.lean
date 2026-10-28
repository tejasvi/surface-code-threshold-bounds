import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11888 = true := by
  decide +kernel

theorem tot11888 : totK PD2M8K2 D2M8K2.t11888 = [0, 164579717034, 483523783888, 248892996098, 11572547963, 0, 0, 0] := by
  decide +kernel

theorem rows11889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11889 = true := by
  decide +kernel

theorem tot11889 : totK PD2M8K2 D2M8K2.t11889 = [0, 170680097054, 466500448563, 227912422598, 10117172567, 0, 0, 0] := by
  decide +kernel

theorem rows11890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11890 = true := by
  decide +kernel

theorem tot11890 : totK PD2M8K2 D2M8K2.t11890 = [0, 223431555225, 485784578337, 185206267061, 7727483130, 0, 0, 0] := by
  decide +kernel

theorem rows11891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11891 = true := by
  decide +kernel

theorem tot11891 : totK PD2M8K2 D2M8K2.t11891 = [0, 187425437543, 448210229406, 221079048596, 16861767938, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
