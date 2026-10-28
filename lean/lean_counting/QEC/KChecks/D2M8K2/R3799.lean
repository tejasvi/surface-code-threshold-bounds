import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15196 = true := by
  decide +kernel

theorem tot15196 : totK PD2M8K2 D2M8K2.t15196 = [0, 90206013543, 409748379526, 383014554722, 50926174021, 0, 0, 0] := by
  decide +kernel

theorem rows15197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15197 = true := by
  decide +kernel

theorem tot15197 : totK PD2M8K2 D2M8K2.t15197 = [0, 0, 167532420801, 456706364183, 257755693783, 21912686248, 0, 0] := by
  decide +kernel

theorem rows15198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15198 = true := by
  decide +kernel

theorem tot15198 : totK PD2M8K2 D2M8K2.t15198 = [0, 85227276077, 291595348167, 340034103473, 169463216221, 9434345190, 0, 0] := by
  decide +kernel

theorem rows15199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15199 = true := by
  decide +kernel

theorem tot15199 : totK PD2M8K2 D2M8K2.t15199 = [0, 172418237381, 449535228134, 274196778662, 27731042144, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
