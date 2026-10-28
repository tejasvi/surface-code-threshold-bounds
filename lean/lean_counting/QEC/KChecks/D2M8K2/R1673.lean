import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6692 = true := by
  decide +kernel

theorem tot6692 : totK PD2M8K2 D2M8K2.t6692 = [0, 33270956665, 276809834800, 467624166331, 122082424814, 3884009855, 0, 0] := by
  decide +kernel

theorem rows6693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6693 = true := by
  decide +kernel

theorem tot6693 : totK PD2M8K2 D2M8K2.t6693 = [0, 188595494274, 480542653868, 207399757083, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows6694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6694 = true := by
  decide +kernel

theorem tot6694 : totK PD2M8K2 D2M8K2.t6694 = [0, 184497058421, 464339017819, 212992944960, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows6695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6695 = true := by
  decide +kernel

theorem tot6695 : totK PD2M8K2 D2M8K2.t6695 = [0, 0, 281866981668, 487426686577, 92984976570, 1326647619, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
