import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12264 = true := by
  decide +kernel

theorem tot12264 : totK PD2M8K2 D2M8K2.t12264 = [0, 157976549808, 449381147633, 285912264665, 21620897446, 0, 0, 0] := by
  decide +kernel

theorem rows12265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12265 = true := by
  decide +kernel

theorem tot12265 : totK PD2M8K2 D2M8K2.t12265 = [0, 195158053246, 474242465230, 220172069912, 13920358448, 0, 0, 0] := by
  decide +kernel

theorem rows12266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12266 = true := by
  decide +kernel

theorem tot12266 : totK PD2M8K2 D2M8K2.t12266 = [0, 185529815738, 473421595417, 232420295523, 16104584588, 0, 0, 0] := by
  decide +kernel

theorem rows12267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12267 = true := by
  decide +kernel

theorem tot12267 : totK PD2M8K2 D2M8K2.t12267 = [0, 185875625106, 479151651061, 218247170009, 12183533023, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
