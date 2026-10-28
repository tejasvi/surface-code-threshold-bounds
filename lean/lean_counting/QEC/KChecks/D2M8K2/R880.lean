import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3520 = true := by
  decide +kernel

theorem tot3520 : totK PD2M8K2 D2M8K2.t3520 = [19168591844, 324677826618, 452429313622, 84812092419, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows3521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3521 = true := by
  decide +kernel

theorem tot3521 : totK PD2M8K2 D2M8K2.t3521 = [48780887785, 290081511008, 438638246750, 121014152540, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows3522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3522 = true := by
  decide +kernel

theorem tot3522 : totK PD2M8K2 D2M8K2.t3522 = [193141851550, 465492336658, 248674009543, 23160146176, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3523 = true := by
  decide +kernel

theorem tot3523 : totK PD2M8K2 D2M8K2.t3523 = [88251644990, 372410801345, 371539678443, 65959357637, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
