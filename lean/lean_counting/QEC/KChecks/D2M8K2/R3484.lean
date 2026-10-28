import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13936 = true := by
  decide +kernel

theorem tot13936 : totK PD2M8K2 D2M8K2.t13936 = [0, 100262604055, 420374003525, 351901298773, 32594623209, 0, 0, 0] := by
  decide +kernel

theorem rows13937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13937 = true := by
  decide +kernel

theorem tot13937 : totK PD2M8K2 D2M8K2.t13937 = [0, 38429939453, 302009464060, 469411395106, 87168983137, 1310285577, 0, 0] := by
  decide +kernel

theorem rows13938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13938 = true := by
  decide +kernel

theorem tot13938 : totK PD2M8K2 D2M8K2.t13938 = [0, 170735753252, 438767680259, 273478337906, 28520273273, 0, 0, 0] := by
  decide +kernel

theorem rows13939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13939 = true := by
  decide +kernel

theorem tot13939 : totK PD2M8K2 D2M8K2.t13939 = [0, 203965115661, 494644033200, 210218043128, 8100073647, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
