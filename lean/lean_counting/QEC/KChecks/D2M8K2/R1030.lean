import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4120 = true := by
  decide +kernel

theorem tot4120 : totK PD2M8K2 D2M8K2.t4120 = [0, 0, 0, 205033708429, 457409589150, 182352701255, 9135329004, 0] := by
  decide +kernel

theorem rows4121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4121 = true := by
  decide +kernel

theorem tot4121 : totK PD2M8K2 D2M8K2.t4121 = [0, 0, 163281325637, 454963943762, 259998368279, 23796424228, 0, 0] := by
  decide +kernel

theorem rows4122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4122 = true := by
  decide +kernel

theorem tot4122 : totK PD2M8K2 D2M8K2.t4122 = [0, 0, 198950048013, 469931792761, 223226861994, 12263912603, 0, 0] := by
  decide +kernel

theorem rows4123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4123 = true := by
  decide +kernel

theorem tot4123 : totK PD2M8K2 D2M8K2.t4123 = [0, 0, 47457741299, 372618949057, 408116623127, 43523303818, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
