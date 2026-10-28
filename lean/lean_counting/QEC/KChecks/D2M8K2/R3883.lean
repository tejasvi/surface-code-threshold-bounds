import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15532 = true := by
  decide +kernel

theorem tot15532 : totK PD2M8K2 D2M8K2.t15532 = [0, 0, 211474301292, 483499998537, 207228911396, 8378253043, 0, 0] := by
  decide +kernel

theorem rows15533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15533 = true := by
  decide +kernel

theorem tot15533 : totK PD2M8K2 D2M8K2.t15533 = [0, 0, 175407017058, 482486560118, 232864749919, 9106999908, 0, 0] := by
  decide +kernel

theorem rows15534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15534 = true := by
  decide +kernel

theorem tot15534 : totK PD2M8K2 D2M8K2.t15534 = [0, 183243395725, 376878223913, 254434049076, 105436732132, 12231389608, 0, 0] := by
  decide +kernel

theorem rows15535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15535 = true := by
  decide +kernel

theorem tot15535 : totK PD2M8K2 D2M8K2.t15535 = [0, 170292154681, 465590446810, 250047299565, 15100243287, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
