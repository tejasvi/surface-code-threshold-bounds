import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12056 = true := by
  decide +kernel

theorem tot12056 : totK PD2M8K2 D2M8K2.t12056 = [0, 0, 14689906303, 329938866712, 431024790988, 58982621819, 0, 0] := by
  decide +kernel

theorem rows12057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12057 = true := by
  decide +kernel

theorem tot12057 : totK PD2M8K2 D2M8K2.t12057 = [0, 0, 216334963637, 498762961067, 153009473624, 2519764721, 0, 0] := by
  decide +kernel

theorem rows12058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12058 = true := by
  decide +kernel

theorem tot12058 : totK PD2M8K2 D2M8K2.t12058 = [0, 0, 224006687332, 496264402538, 159914326922, 2447226230, 0, 0] := by
  decide +kernel

theorem rows12059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12059 = true := by
  decide +kernel

theorem tot12059 : totK PD2M8K2 D2M8K2.t12059 = [0, 0, 197540113661, 462959554894, 210510932223, 12652156324, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
