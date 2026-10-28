import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3120 = true := by
  decide +kernel

theorem tot3120 : totK PA10K2 A10K2.t3120 = [0, 0, 558567210082, 1926566618084, 1721755567404, 403526747064, 17500500512, 0, 0, 0] := by
  decide +kernel

theorem rows3121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3121 = true := by
  decide +kernel

theorem tot3121 : totK PA10K2 A10K2.t3121 = [0, 460689358819, 1764308434839, 1918411580647, 660412463326, 64958918050, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3122 = true := by
  decide +kernel

theorem tot3122 : totK PA10K2 A10K2.t3122 = [0, 309040822860, 1463609712076, 2213226215146, 976164711034, 77913090667, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3123 = true := by
  decide +kernel

theorem tot3123 : totK PA10K2 A10K2.t3123 = [0, 109233960067, 652259329232, 1816750388649, 1838563746905, 465807142803, 17754888877, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
