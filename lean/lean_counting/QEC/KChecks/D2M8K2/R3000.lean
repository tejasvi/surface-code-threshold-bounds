import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12000 = true := by
  decide +kernel

theorem tot12000 : totK PD2M8K2 D2M8K2.t12000 = [0, 211096498849, 487172318331, 184982745914, 5086124964, 0, 0, 0] := by
  decide +kernel

theorem rows12001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12001 = true := by
  decide +kernel

theorem tot12001 : totK PD2M8K2 D2M8K2.t12001 = [0, 183009142093, 451614726298, 246441240553, 22828318141, 0, 0, 0] := by
  decide +kernel

theorem rows12002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12002 = true := by
  decide +kernel

theorem tot12002 : totK PD2M8K2 D2M8K2.t12002 = [0, 106853892906, 437711012604, 305352194547, 27005494330, 0, 0, 0] := by
  decide +kernel

theorem rows12003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12003 = true := by
  decide +kernel

theorem tot12003 : totK PD2M8K2 D2M8K2.t12003 = [0, 0, 302320915232, 475328817169, 92590515335, 1095107716, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
