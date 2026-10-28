import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5668 = true := by
  decide +kernel

theorem tot5668 : totK PA10K2 A10K2.t5668 = [0, 0, 409772422728, 1607295215120, 2088220521547, 879045168458, 61145654474, 0, 0, 0] := by
  decide +kernel

theorem rows5669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5669 = true := by
  decide +kernel

theorem tot5669 : totK PA10K2 A10K2.t5669 = [0, 0, 185464160331, 1149546061311, 2170768004112, 1319304796504, 198421371556, 6157148557, 0, 0] := by
  decide +kernel

theorem rows5670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5670 = true := by
  decide +kernel

theorem tot5670 : totK PA10K2 A10K2.t5670 = [0, 0, 319639362920, 1473413165916, 2100520044923, 997633612939, 110996054245, 0, 0, 0] := by
  decide +kernel

theorem rows5671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5671 = true := by
  decide +kernel

theorem tot5671 : totK PA10K2 A10K2.t5671 = [0, 0, 526190107232, 1860212337959, 1864051309825, 458309439390, 13113133354, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
