import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6048 = true := by
  decide +kernel

theorem tot6048 : totK PD2M8K2 D2M8K2.t6048 = [0, 0, 190868814149, 463510068483, 239554470086, 19854384913, 0, 0] := by
  decide +kernel

theorem rows6049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6049 = true := by
  decide +kernel

theorem tot6049 : totK PD2M8K2 D2M8K2.t6049 = [0, 0, 186028985560, 466029964865, 218967544234, 12363379521, 0, 0] := by
  decide +kernel

theorem rows6050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6050 = true := by
  decide +kernel

theorem tot6050 : totK PD2M8K2 D2M8K2.t6050 = [0, 0, 0, 327027563519, 490657520357, 67290459801, 0, 0] := by
  decide +kernel

theorem rows6051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6051 = true := by
  decide +kernel

theorem tot6051 : totK PD2M8K2 D2M8K2.t6051 = [0, 0, 66305857479, 274757345380, 378191194121, 128644279589, 5352782441, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
