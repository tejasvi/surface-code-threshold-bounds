import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11692 = true := by
  decide +kernel

theorem tot11692 : totK PD2M8K2 D2M8K2.t11692 = [0, 202172223875, 478070922118, 216642976009, 11051716772, 0, 0, 0] := by
  decide +kernel

theorem rows11693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11693 = true := by
  decide +kernel

theorem tot11693 : totK PD2M8K2 D2M8K2.t11693 = [0, 185303209904, 476534429876, 222050281290, 12370590376, 0, 0, 0] := by
  decide +kernel

theorem rows11694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11694 = true := by
  decide +kernel

theorem tot11694 : totK PD2M8K2 D2M8K2.t11694 = [0, 180271278495, 482333241528, 219303763578, 10541049727, 0, 0, 0] := by
  decide +kernel

theorem rows11695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11695 = true := by
  decide +kernel

theorem tot11695 : totK PD2M8K2 D2M8K2.t11695 = [0, 176212610246, 469061080529, 247493465121, 13908012088, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
