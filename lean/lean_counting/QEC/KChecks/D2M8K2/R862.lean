import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3448 = true := by
  decide +kernel

theorem tot3448 : totK PD2M8K2 D2M8K2.t3448 = [194580748544, 471731905123, 232696764389, 16417880149, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3449 = true := by
  decide +kernel

theorem tot3449 : totK PD2M8K2 D2M8K2.t3449 = [19592696079, 314230310165, 459174851751, 114744481715, 3593478102, 0, 0, 0] := by
  decide +kernel

theorem rows3450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3450 = true := by
  decide +kernel

theorem tot3450 : totK PD2M8K2 D2M8K2.t3450 = [0, 193223254253, 463027437610, 222735458589, 16773298702, 0, 0, 0] := by
  decide +kernel

theorem rows3451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3451 = true := by
  decide +kernel

theorem tot3451 : totK PD2M8K2 D2M8K2.t3451 = [0, 162121100112, 450944977917, 282244598605, 28496840222, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
