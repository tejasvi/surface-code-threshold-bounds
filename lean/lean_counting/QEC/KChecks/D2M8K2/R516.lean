import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2064 = true := by
  decide +kernel

theorem tot2064 : totK PD2M8K2 D2M8K2.t2064 = [0, 0, 177728455467, 485561269267, 219007522011, 9876698288, 0, 0] := by
  decide +kernel

theorem rows2065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2065 = true := by
  decide +kernel

theorem tot2065 : totK PD2M8K2 D2M8K2.t2065 = [0, 0, 200410675831, 484888793463, 190045006570, 5176625437, 0, 0] := by
  decide +kernel

theorem rows2066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2066 = true := by
  decide +kernel

theorem tot2066 : totK PD2M8K2 D2M8K2.t2066 = [0, 0, 182074651052, 459751965208, 245582189022, 18333014298, 0, 0] := by
  decide +kernel

theorem rows2067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2067 = true := by
  decide +kernel

theorem tot2067 : totK PD2M8K2 D2M8K2.t2067 = [0, 0, 178679631938, 478713205600, 216198235258, 8981806757, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
