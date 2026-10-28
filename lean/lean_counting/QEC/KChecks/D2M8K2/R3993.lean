import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15972 = true := by
  decide +kernel

theorem tot15972 : totK PD2M8K2 D2M8K2.t15972 = [0, 0, 0, 19320235271, 351053418815, 415503202570, 67045497452, 1310517177] := by
  decide +kernel

theorem rows15973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15973 = true := by
  decide +kernel

theorem tot15973 : totK PD2M8K2 D2M8K2.t15973 = [0, 0, 0, 117771214909, 438971959653, 273937268141, 20151137467, 0] := by
  decide +kernel

theorem rows15974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15974 = true := by
  decide +kernel

theorem tot15974 : totK PD2M8K2 D2M8K2.t15974 = [0, 0, 0, 289243499160, 495398545047, 97747729157, 1150215362, 0] := by
  decide +kernel

theorem rows15975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15975 = true := by
  decide +kernel

theorem tot15975 : totK PD2M8K2 D2M8K2.t15975 = [0, 0, 0, 162145469726, 500825644704, 223159238603, 7152413016, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
