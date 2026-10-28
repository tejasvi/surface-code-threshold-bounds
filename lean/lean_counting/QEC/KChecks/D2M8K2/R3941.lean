import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15764 = true := by
  decide +kernel

theorem tot15764 : totK PD2M8K2 D2M8K2.t15764 = [0, 0, 0, 290545160386, 507406140412, 97165246205, 1369150432, 0] := by
  decide +kernel

theorem rows15765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15765 = true := by
  decide +kernel

theorem tot15765 : totK PD2M8K2 D2M8K2.t15765 = [0, 0, 92207005028, 379373103287, 388216333999, 47815772459, 0, 0] := by
  decide +kernel

theorem rows15766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15766 = true := by
  decide +kernel

theorem tot15766 : totK PD2M8K2 D2M8K2.t15766 = [0, 0, 166798232935, 454928399002, 271603577790, 18252992904, 0, 0] := by
  decide +kernel

theorem rows15767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15767 = true := by
  decide +kernel

theorem tot15767 : totK PD2M8K2 D2M8K2.t15767 = [0, 0, 157212655397, 459267154351, 288635061212, 30858885864, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
