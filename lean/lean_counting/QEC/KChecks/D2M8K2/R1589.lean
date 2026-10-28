import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6356 = true := by
  decide +kernel

theorem tot6356 : totK PD2M8K2 D2M8K2.t6356 = [0, 164798554074, 451946947846, 286094209885, 30468211203, 0, 0, 0] := by
  decide +kernel

theorem rows6357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6357 = true := by
  decide +kernel

theorem tot6357 : totK PD2M8K2 D2M8K2.t6357 = [0, 208635930768, 486470585986, 199327994379, 8160180456, 0, 0, 0] := by
  decide +kernel

theorem rows6358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6358 = true := by
  decide +kernel

theorem tot6358 : totK PD2M8K2 D2M8K2.t6358 = [0, 0, 261098400510, 463565212866, 173813690989, 14593677817, 0, 0] := by
  decide +kernel

theorem rows6359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6359 = true := by
  decide +kernel

theorem tot6359 : totK PD2M8K2 D2M8K2.t6359 = [0, 0, 206073085230, 498043582404, 187363100275, 5347594677, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
