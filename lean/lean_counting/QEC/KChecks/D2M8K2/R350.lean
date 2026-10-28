import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1400 = true := by
  decide +kernel

theorem tot1400 : totK PD2M8K2 D2M8K2.t1400 = [0, 33367265142, 199353137170, 424421175026, 217154439265, 17027268164, 0, 0] := by
  decide +kernel

theorem rows1401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1401 = true := by
  decide +kernel

theorem tot1401 : totK PD2M8K2 D2M8K2.t1401 = [0, 190316963171, 491582002617, 206507752788, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows1402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1402 = true := by
  decide +kernel

theorem tot1402 : totK PD2M8K2 D2M8K2.t1402 = [0, 178884983718, 472139672831, 226048166419, 9203551454, 0, 0, 0] := by
  decide +kernel

theorem rows1403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1403 = true := by
  decide +kernel

theorem tot1403 : totK PD2M8K2 D2M8K2.t1403 = [0, 0, 275923791030, 500168300265, 105027495824, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
