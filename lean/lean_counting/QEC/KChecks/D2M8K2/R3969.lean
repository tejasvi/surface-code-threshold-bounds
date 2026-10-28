import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15876 = true := by
  decide +kernel

theorem tot15876 : totK PD2M8K2 D2M8K2.t15876 = [0, 0, 173553959673, 484538516919, 234531111473, 11227416976, 0, 0] := by
  decide +kernel

theorem rows15877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15877 = true := by
  decide +kernel

theorem tot15877 : totK PD2M8K2 D2M8K2.t15877 = [0, 0, 173961799585, 464560824431, 239396830885, 15671754440, 0, 0] := by
  decide +kernel

theorem rows15878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15878 = true := by
  decide +kernel

theorem tot15878 : totK PD2M8K2 D2M8K2.t15878 = [0, 0, 182658487060, 458024090513, 263560109840, 24669294037, 0, 0] := by
  decide +kernel

theorem rows15879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15879 = true := by
  decide +kernel

theorem tot15879 : totK PD2M8K2 D2M8K2.t15879 = [0, 0, 174878768978, 468347341887, 241463072109, 12405924287, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
