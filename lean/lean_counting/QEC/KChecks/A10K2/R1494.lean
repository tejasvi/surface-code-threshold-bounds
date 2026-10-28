import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5976 = true := by
  decide +kernel

theorem tot5976 : totK PA10K2 A10K2.t5976 = [0, 0, 555249742634, 1959122141040, 1974021631637, 507364089285, 18191002977, 0, 0, 0] := by
  decide +kernel

theorem rows5977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5977 = true := by
  decide +kernel

theorem tot5977 : totK PA10K2 A10K2.t5977 = [526709715043, 1643666875020, 1541600260309, 524426379344, 354490971558, 251699361102, 37324211964, 0, 0, 0] := by
  decide +kernel

theorem rows5978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5978 = true := by
  decide +kernel

theorem tot5978 : totK PA10K2 A10K2.t5978 = [312694146422, 1542077771644, 2102232753507, 831194760693, 70108919683, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5979 = true := by
  decide +kernel

theorem tot5979 : totK PA10K2 A10K2.t5979 = [0, 490629866103, 1840093161667, 1831720745427, 475714241563, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
