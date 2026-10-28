import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6868 = true := by
  decide +kernel

theorem tot6868 : totK PD2M8K2 D2M8K2.t6868 = [0, 172440977869, 442094115598, 253643578403, 25320643661, 0, 0, 0] := by
  decide +kernel

theorem rows6869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6869 = true := by
  decide +kernel

theorem tot6869 : totK PD2M8K2 D2M8K2.t6869 = [0, 157609217244, 471909283870, 254393316040, 12050047255, 0, 0, 0] := by
  decide +kernel

theorem rows6870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6870 = true := by
  decide +kernel

theorem tot6870 : totK PD2M8K2 D2M8K2.t6870 = [186925295305, 452235698193, 245688039549, 23080323466, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6871 = true := by
  decide +kernel

theorem tot6871 : totK PD2M8K2 D2M8K2.t6871 = [197270878672, 477646483162, 217175257899, 12317784814, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
