import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15884 = true := by
  decide +kernel

theorem tot15884 : totK PD2M8K2 D2M8K2.t15884 = [0, 0, 0, 298154939283, 470518342110, 78226618596, 1053411165, 0] := by
  decide +kernel

theorem rows15885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15885 = true := by
  decide +kernel

theorem tot15885 : totK PD2M8K2 D2M8K2.t15885 = [0, 0, 139392202069, 367149764825, 275111744874, 73042393677, 3667207281, 0] := by
  decide +kernel

theorem rows15886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15886 = true := by
  decide +kernel

theorem tot15886 : totK PD2M8K2 D2M8K2.t15886 = [0, 0, 190940060987, 456174144672, 247819080587, 23356471282, 0, 0] := by
  decide +kernel

theorem rows15887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15887 = true := by
  decide +kernel

theorem tot15887 : totK PD2M8K2 D2M8K2.t15887 = [0, 89266124844, 216602263517, 342699445739, 238760873783, 22079973395, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
