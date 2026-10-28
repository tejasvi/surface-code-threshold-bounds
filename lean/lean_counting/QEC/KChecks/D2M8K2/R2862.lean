import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11448 = true := by
  decide +kernel

theorem tot11448 : totK PD2M8K2 D2M8K2.t11448 = [0, 62160131298, 335006156383, 408367788090, 86081039021, 1232398321, 0, 0] := by
  decide +kernel

theorem rows11449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11449 = true := by
  decide +kernel

theorem tot11449 : totK PD2M8K2 D2M8K2.t11449 = [0, 0, 231706818282, 484482379039, 170616157772, 4990385724, 0, 0] := by
  decide +kernel

theorem rows11450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11450 = true := by
  decide +kernel

theorem tot11450 : totK PD2M8K2 D2M8K2.t11450 = [0, 0, 192259072918, 468468360385, 201803530189, 12947917294, 0, 0] := by
  decide +kernel

theorem rows11451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11451 = true := by
  decide +kernel

theorem tot11451 : totK PD2M8K2 D2M8K2.t11451 = [0, 0, 221177850046, 500298917505, 157146739766, 2233847856, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
