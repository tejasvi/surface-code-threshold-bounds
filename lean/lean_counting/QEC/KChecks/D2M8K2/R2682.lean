import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10728 = true := by
  decide +kernel

theorem tot10728 : totK PD2M8K2 D2M8K2.t10728 = [0, 0, 0, 283724921041, 506731002454, 109908463441, 1178750802, 0] := by
  decide +kernel

theorem rows10729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10729 = true := by
  decide +kernel

theorem tot10729 : totK PD2M8K2 D2M8K2.t10729 = [0, 0, 0, 199633562321, 477643138730, 189085938239, 11991925116, 0] := by
  decide +kernel

theorem rows10730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10730 = true := by
  decide +kernel

theorem tot10730 : totK PD2M8K2 D2M8K2.t10730 = [0, 0, 186051861834, 443601259291, 238647969748, 19854332280, 0, 0] := by
  decide +kernel

theorem rows10731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10731 = true := by
  decide +kernel

theorem tot10731 : totK PD2M8K2 D2M8K2.t10731 = [0, 0, 195537584713, 458300674281, 222442110364, 14815553814, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
