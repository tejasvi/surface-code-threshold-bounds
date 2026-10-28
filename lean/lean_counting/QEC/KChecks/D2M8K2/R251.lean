import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1004 = true := by
  decide +kernel

theorem tot1004 : totK PD2M8K2 D2M8K2.t1004 = [84551724395, 334809922629, 362192055425, 95844379623, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows1005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1005 = true := by
  decide +kernel

theorem tot1005 : totK PD2M8K2 D2M8K2.t1005 = [174139076802, 423339737846, 264683225025, 29622929705, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1006 = true := by
  decide +kernel

theorem tot1006 : totK PD2M8K2 D2M8K2.t1006 = [163263203729, 474830708503, 262009851945, 13916467904, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1007 = true := by
  decide +kernel

theorem tot1007 : totK PD2M8K2 D2M8K2.t1007 = [0, 277582879315, 511290166018, 104129587350, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
