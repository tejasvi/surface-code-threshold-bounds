import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15860 = true := by
  decide +kernel

theorem tot15860 : totK PD2M8K2 D2M8K2.t15860 = [0, 180465534664, 440833055586, 274451239966, 30360088343, 0, 0, 0] := by
  decide +kernel

theorem rows15861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15861 = true := by
  decide +kernel

theorem tot15861 : totK PD2M8K2 D2M8K2.t15861 = [0, 88945508586, 404304985201, 362280945941, 44650889241, 1198073392, 0, 0] := by
  decide +kernel

theorem rows15862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15862 = true := by
  decide +kernel

theorem tot15862 : totK PD2M8K2 D2M8K2.t15862 = [0, 0, 220534510514, 494779705225, 178940907945, 8470662040, 0, 0] := by
  decide +kernel

theorem rows15863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15863 = true := by
  decide +kernel

theorem tot15863 : totK PD2M8K2 D2M8K2.t15863 = [0, 82984366571, 324275204458, 364243737140, 97629456795, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
