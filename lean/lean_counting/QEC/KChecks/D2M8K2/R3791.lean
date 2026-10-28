import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15164 = true := by
  decide +kernel

theorem tot15164 : totK PD2M8K2 D2M8K2.t15164 = [0, 0, 157144615073, 458249367313, 283851905386, 19503339913, 0, 0] := by
  decide +kernel

theorem rows15165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15165 = true := by
  decide +kernel

theorem tot15165 : totK PD2M8K2 D2M8K2.t15165 = [0, 90861460542, 279353618160, 330651674788, 187201686430, 19127502544, 0, 0] := by
  decide +kernel

theorem rows15166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15166 = true := by
  decide +kernel

theorem tot15166 : totK PD2M8K2 D2M8K2.t15166 = [0, 170619713527, 458707996865, 237814637266, 15592170894, 0, 0, 0] := by
  decide +kernel

theorem rows15167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15167 = true := by
  decide +kernel

theorem tot15167 : totK PD2M8K2 D2M8K2.t15167 = [0, 159156319876, 450621440723, 264515656188, 20476387230, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
