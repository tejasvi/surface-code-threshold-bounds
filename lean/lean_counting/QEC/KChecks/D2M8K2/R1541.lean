import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6164 = true := by
  decide +kernel

theorem tot6164 : totK PD2M8K2 D2M8K2.t6164 = [173496440279, 446593047965, 271153467318, 29292131461, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6165 = true := by
  decide +kernel

theorem tot6165 : totK PD2M8K2 D2M8K2.t6165 = [83913843661, 404534460916, 377373421991, 53044044261, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6166 = true := by
  decide +kernel

theorem tot6166 : totK PD2M8K2 D2M8K2.t6166 = [0, 207406290595, 481947082727, 173414562712, 10698315783, 0, 0, 0] := by
  decide +kernel

theorem rows6167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6167 = true := by
  decide +kernel

theorem tot6167 : totK PD2M8K2 D2M8K2.t6167 = [194479703291, 456599060430, 243550620320, 23412915585, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
