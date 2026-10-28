import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6260 = true := by
  decide +kernel

theorem tot6260 : totK PD2M8K2 D2M8K2.t6260 = [0, 190093115502, 460850683295, 238600322616, 18333014298, 0, 0, 0] := by
  decide +kernel

theorem rows6261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6261 = true := by
  decide +kernel

theorem tot6261 : totK PD2M8K2 D2M8K2.t6261 = [0, 192430338695, 491605179584, 200909808278, 9723226813, 0, 0, 0] := by
  decide +kernel

theorem rows6262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6262 = true := by
  decide +kernel

theorem tot6262 : totK PD2M8K2 D2M8K2.t6262 = [0, 169652873215, 445638336243, 250883715205, 19418161212, 0, 0, 0] := by
  decide +kernel

theorem rows6263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6263 = true := by
  decide +kernel

theorem tot6263 : totK PD2M8K2 D2M8K2.t6263 = [0, 92498059237, 368880574195, 337520199558, 62565062304, 1095107716, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
