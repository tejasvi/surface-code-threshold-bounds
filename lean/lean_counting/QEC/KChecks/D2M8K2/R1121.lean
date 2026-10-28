import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4484 = true := by
  decide +kernel

theorem tot4484 : totK PD2M8K2 D2M8K2.t4484 = [0, 172390672205, 391730085310, 247482989201, 73947701315, 3581949829, 0, 0] := by
  decide +kernel

theorem rows4485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4485 = true := by
  decide +kernel

theorem tot4485 : totK PD2M8K2 D2M8K2.t4485 = [0, 170607581640, 443345539409, 269327038074, 20944911235, 0, 0, 0] := by
  decide +kernel

theorem rows4486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4486 = true := by
  decide +kernel

theorem tot4486 : totK PD2M8K2 D2M8K2.t4486 = [0, 92722701599, 367531240238, 355321051248, 65707834127, 1096505104, 0, 0] := by
  decide +kernel

theorem rows4487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4487 = true := by
  decide +kernel

theorem tot4487 : totK PD2M8K2 D2M8K2.t4487 = [0, 0, 329032445034, 519379085862, 76330978505, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
