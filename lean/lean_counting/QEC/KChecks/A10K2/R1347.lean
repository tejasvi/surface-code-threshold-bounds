import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5388 = true := by
  decide +kernel

theorem tot5388 : totK PA10K2 A10K2.t5388 = [0, 584442978767, 1757626004294, 1675333310983, 686924745543, 127643692581, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows5389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5389 = true := by
  decide +kernel

theorem tot5389 : totK PA10K2 A10K2.t5389 = [0, 215434075875, 1465809777365, 2306150474125, 903436812997, 73710659642, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5390 = true := by
  decide +kernel

theorem tot5390 : totK PA10K2 A10K2.t5390 = [0, 0, 457173266657, 1798516428731, 1975155972126, 519152191362, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows5391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5391 = true := by
  decide +kernel

theorem tot5391 : totK PA10K2 A10K2.t5391 = [0, 491707397545, 1672942597720, 1790924316944, 711997518012, 80788111800, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
