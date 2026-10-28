import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10400 = true := by
  decide +kernel

theorem tot10400 : totK PD2M8K2 D2M8K2.t10400 = [0, 0, 201241377318, 483343076163, 220195278114, 9704016722, 0, 0] := by
  decide +kernel

theorem rows10401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10401 = true := by
  decide +kernel

theorem tot10401 : totK PD2M8K2 D2M8K2.t10401 = [0, 0, 26450463071, 300878394779, 413620070845, 164295168234, 15073499398, 0] := by
  decide +kernel

theorem rows10402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10402 = true := by
  decide +kernel

theorem tot10402 : totK PD2M8K2 D2M8K2.t10402 = [0, 0, 0, 218761902016, 502539281823, 174889664622, 5430665091, 0] := by
  decide +kernel

theorem rows10403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10403 = true := by
  decide +kernel

theorem tot10403 : totK PD2M8K2 D2M8K2.t10403 = [0, 0, 127922347197, 331873923454, 358268089372, 111426226732, 4239164426, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
