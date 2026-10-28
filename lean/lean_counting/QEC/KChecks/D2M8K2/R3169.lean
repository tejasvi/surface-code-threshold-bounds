import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12676 = true := by
  decide +kernel

theorem tot12676 : totK PD2M8K2 D2M8K2.t12676 = [0, 0, 206375787870, 496334703603, 200295826643, 7693277698, 0, 0] := by
  decide +kernel

theorem rows12677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12677 = true := by
  decide +kernel

theorem tot12677 : totK PD2M8K2 D2M8K2.t12677 = [0, 0, 177496362101, 464018645266, 259814495342, 16915303391, 0, 0] := by
  decide +kernel

theorem rows12678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12678 = true := by
  decide +kernel

theorem tot12678 : totK PD2M8K2 D2M8K2.t12678 = [0, 0, 171618738591, 463442088477, 240137233550, 13576758655, 0, 0] := by
  decide +kernel

theorem rows12679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12679 = true := by
  decide +kernel

theorem tot12679 : totK PD2M8K2 D2M8K2.t12679 = [0, 0, 0, 288182100291, 507393656096, 103589610651, 1178750802, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
