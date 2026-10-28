import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1940 = true := by
  decide +kernel

theorem tot1940 : totK PD2M8K2 D2M8K2.t1940 = [0, 0, 0, 247602277352, 474771024801, 146357835148, 4811815119, 0] := by
  decide +kernel

theorem rows1941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1941 = true := by
  decide +kernel

theorem tot1941 : totK PD2M8K2 D2M8K2.t1941 = [0, 92082099022, 225189286362, 198739151209, 266813410868, 111541881739, 8974678929, 0] := by
  decide +kernel

theorem rows1942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1942 = true := by
  decide +kernel

theorem tot1942 : totK PD2M8K2 D2M8K2.t1942 = [0, 189174148487, 458346663014, 235846477024, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows1943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1943 = true := by
  decide +kernel

theorem tot1943 : totK PD2M8K2 D2M8K2.t1943 = [0, 156090824362, 456681026734, 271700667865, 18959421031, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
