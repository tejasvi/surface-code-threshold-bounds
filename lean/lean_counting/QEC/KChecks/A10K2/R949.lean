import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3796 = true := by
  decide +kernel

theorem tot3796 : totK PA10K2 A10K2.t3796 = [0, 0, 0, 483444569140, 1821751315106, 1981393970220, 543349563431, 32470943963, 0, 0] := by
  decide +kernel

theorem rows3797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3797 = true := by
  decide +kernel

theorem tot3797 : totK PA10K2 A10K2.t3797 = [0, 0, 0, 504218616469, 1840826898745, 1889208438161, 444757477730, 17606126119, 0, 0] := by
  decide +kernel

theorem rows3798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3798 = true := by
  decide +kernel

theorem tot3798 : totK PA10K2 A10K2.t3798 = [0, 0, 0, 302082434609, 1519027509780, 2113823262269, 651226556085, 37324864939, 0, 0] := by
  decide +kernel

theorem rows3799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3799 = true := by
  decide +kernel

theorem tot3799 : totK PA10K2 A10K2.t3799 = [0, 0, 202041260899, 410281139563, 813348179795, 1759680685480, 1202267947159, 218133052917, 6354482628, 0] := by
  decide +kernel

end QECKChecks.A10K2
