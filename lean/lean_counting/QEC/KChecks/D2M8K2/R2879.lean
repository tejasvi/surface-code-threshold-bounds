import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11516 = true := by
  decide +kernel

theorem tot11516 : totK PD2M8K2 D2M8K2.t11516 = [0, 0, 210462901617, 491966304394, 171471431201, 5253830308, 0, 0] := by
  decide +kernel

theorem rows11517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11517 = true := by
  decide +kernel

theorem tot11517 : totK PD2M8K2 D2M8K2.t11517 = [0, 0, 184151435151, 499364431633, 178537679886, 3419955201, 0, 0] := by
  decide +kernel

theorem rows11518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11518 = true := by
  decide +kernel

theorem tot11518 : totK PD2M8K2 D2M8K2.t11518 = [0, 0, 180653325279, 461466655913, 251032052769, 22760291189, 0, 0] := by
  decide +kernel

theorem rows11519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11519 = true := by
  decide +kernel

theorem tot11519 : totK PD2M8K2 D2M8K2.t11519 = [0, 0, 175895175283, 478695039086, 229730480111, 10912527564, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
