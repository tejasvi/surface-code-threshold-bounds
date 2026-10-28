import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11404 = true := by
  decide +kernel

theorem tot11404 : totK PD2M8K2 D2M8K2.t11404 = [0, 143243288736, 447175139392, 279091577326, 23327762163, 0, 0, 0] := by
  decide +kernel

theorem rows11405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11405 = true := by
  decide +kernel

theorem tot11405 : totK PD2M8K2 D2M8K2.t11405 = [0, 0, 300324002953, 527892160788, 87700503709, 0, 0, 0] := by
  decide +kernel

theorem rows11406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11406 = true := by
  decide +kernel

theorem tot11406 : totK PD2M8K2 D2M8K2.t11406 = [0, 142914169189, 366445422767, 297120687249, 98037423558, 2498823382, 0, 0] := by
  decide +kernel

theorem rows11407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11407 = true := by
  decide +kernel

theorem tot11407 : totK PD2M8K2 D2M8K2.t11407 = [0, 171864565518, 438077495637, 260882506794, 20400422121, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
