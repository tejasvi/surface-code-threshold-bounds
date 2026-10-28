import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t372 = true := by
  decide +kernel

theorem tot372 : totK PD2M8K2 D2M8K2.t372 = [0, 114792651817, 397353839205, 352702725553, 40842252607, 0, 0, 0] := by
  decide +kernel

theorem rows373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t373 = true := by
  decide +kernel

theorem tot373 : totK PD2M8K2 D2M8K2.t373 = [0, 203641453154, 490076988641, 200200561461, 8500385581, 0, 0, 0] := by
  decide +kernel

theorem rows374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t374 = true := by
  decide +kernel

theorem tot374 : totK PD2M8K2 D2M8K2.t374 = [0, 172742953658, 458912166927, 236916016490, 15504798387, 0, 0, 0] := by
  decide +kernel

theorem rows375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t375 = true := by
  decide +kernel

theorem tot375 : totK PD2M8K2 D2M8K2.t375 = [0, 181914472712, 469749888465, 251406612834, 19360283137, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
