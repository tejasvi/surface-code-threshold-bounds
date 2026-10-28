import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t496 = true := by
  decide +kernel

theorem tot496 : totK PD2M8K2 D2M8K2.t496 = [0, 0, 269340251901, 511153531064, 122024497035, 2154804625, 0, 0] := by
  decide +kernel

theorem rows497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t497 = true := by
  decide +kernel

theorem tot497 : totK PD2M8K2 D2M8K2.t497 = [0, 192299761616, 460560444762, 241254167818, 23194184691, 1725911522, 0, 0] := by
  decide +kernel

theorem rows498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t498 = true := by
  decide +kernel

theorem tot498 : totK PD2M8K2 D2M8K2.t498 = [0, 209671658245, 474015427515, 215816573822, 12876236862, 0, 0, 0] := by
  decide +kernel

theorem rows499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t499 = true := by
  decide +kernel

theorem tot499 : totK PD2M8K2 D2M8K2.t499 = [0, 0, 297264292050, 486546678858, 108281738828, 1231519631, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
