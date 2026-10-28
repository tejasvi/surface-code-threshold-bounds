import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4212 = true := by
  decide +kernel

theorem tot4212 : totK PD2M8K2 D2M8K2.t4212 = [0, 0, 37505423682, 351374409172, 443238272383, 68593939360, 0, 0] := by
  decide +kernel

theorem rows4213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4213 = true := by
  decide +kernel

theorem tot4213 : totK PD2M8K2 D2M8K2.t4213 = [0, 0, 48968131978, 288028520020, 437966639422, 114680209939, 2498823382, 0] := by
  decide +kernel

theorem rows4214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4214 = true := by
  decide +kernel

theorem tot4214 : totK PD2M8K2 D2M8K2.t4214 = [0, 0, 193169817828, 478879289384, 236727816157, 22016217787, 0, 0] := by
  decide +kernel

theorem rows4215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4215 = true := by
  decide +kernel

theorem tot4215 : totK PD2M8K2 D2M8K2.t4215 = [0, 0, 179781219229, 463512072535, 239903516068, 16354273117, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
