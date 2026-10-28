import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6932 = true := by
  decide +kernel

theorem tot6932 : totK PD2M8K2 D2M8K2.t6932 = [0, 204296889133, 477453793360, 213400196125, 10133688565, 0, 0, 0] := by
  decide +kernel

theorem rows6933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6933 = true := by
  decide +kernel

theorem tot6933 : totK PD2M8K2 D2M8K2.t6933 = [0, 55986240665, 286873842401, 378744405002, 177822232444, 21400436502, 0, 0] := by
  decide +kernel

theorem rows6934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6934 = true := by
  decide +kernel

theorem tot6934 : totK PD2M8K2 D2M8K2.t6934 = [0, 0, 200895808674, 483869091303, 201838135079, 7908366594, 0, 0] := by
  decide +kernel

theorem rows6935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6935 = true := by
  decide +kernel

theorem tot6935 : totK PD2M8K2 D2M8K2.t6935 = [0, 67691909564, 240480233720, 399162789718, 182147328255, 8191853852, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
