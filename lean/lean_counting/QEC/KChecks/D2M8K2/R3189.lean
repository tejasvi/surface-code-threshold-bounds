import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12756 = true := by
  decide +kernel

theorem tot12756 : totK PD2M8K2 D2M8K2.t12756 = [0, 173381502718, 421856158143, 168512005412, 53159797039, 64886976868, 6818291842, 0] := by
  decide +kernel

theorem rows12757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12757 = true := by
  decide +kernel

theorem tot12757 : totK PD2M8K2 D2M8K2.t12757 = [0, 151493727745, 455200553329, 270021638233, 16375704615, 0, 0, 0] := by
  decide +kernel

theorem rows12758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12758 = true := by
  decide +kernel

theorem tot12758 : totK PD2M8K2 D2M8K2.t12758 = [0, 4294967296, 275026207716, 508077064826, 107803238373, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12759 = true := by
  decide +kernel

theorem tot12759 : totK PD2M8K2 D2M8K2.t12759 = [0, 174881110707, 448939147261, 275249208248, 29020409164, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
