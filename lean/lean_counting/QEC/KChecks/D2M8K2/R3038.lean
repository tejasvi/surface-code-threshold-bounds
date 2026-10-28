import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12152 = true := by
  decide +kernel

theorem tot12152 : totK PD2M8K2 D2M8K2.t12152 = [0, 181839249304, 427287014285, 165827573916, 62617925412, 38808591981, 2751766863, 0] := by
  decide +kernel

theorem rows12153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12153 = true := by
  decide +kernel

theorem tot12153 : totK PD2M8K2 D2M8K2.t12153 = [0, 198866050594, 462693717300, 208624484496, 12422136039, 0, 0, 0] := by
  decide +kernel

theorem rows12154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12154 = true := by
  decide +kernel

theorem tot12154 : totK PD2M8K2 D2M8K2.t12154 = [0, 11978940098, 299449193358, 476189498154, 95819703874, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12155 = true := by
  decide +kernel

theorem tot12155 : totK PD2M8K2 D2M8K2.t12155 = [0, 92587956914, 378254714159, 385032377316, 54785871227, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
