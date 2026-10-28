import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12512 = true := by
  decide +kernel

theorem tot12512 : totK PD2M8K2 D2M8K2.t12512 = [0, 192416921195, 447942381060, 241354641632, 20844316874, 0, 0, 0] := by
  decide +kernel

theorem rows12513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12513 = true := by
  decide +kernel

theorem tot12513 : totK PD2M8K2 D2M8K2.t12513 = [0, 54772459227, 340288567678, 412452637815, 77523382452, 1096505104, 0, 0] := by
  decide +kernel

theorem rows12514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12514 = true := by
  decide +kernel

theorem tot12514 : totK PD2M8K2 D2M8K2.t12514 = [0, 18464490943, 269496426685, 480844586827, 124539454204, 3884009855, 0, 0] := by
  decide +kernel

theorem rows12515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12515 = true := by
  decide +kernel

theorem tot12515 : totK PD2M8K2 D2M8K2.t12515 = [0, 202594628376, 465604078937, 222987451471, 20013141721, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
