import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3076 = true := by
  decide +kernel

theorem tot3076 : totK PA10K2 A10K2.t3076 = [0, 0, 0, 286581359644, 1526615411040, 2162209835613, 793367254731, 61575158848, 0, 0] := by
  decide +kernel

theorem rows3077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3077 = true := by
  decide +kernel

theorem tot3077 : totK PA10K2 A10K2.t3077 = [0, 0, 0, 197685889441, 1052042235241, 1945092828999, 1315536821395, 248772015325, 7380853412, 0] := by
  decide +kernel

theorem rows3078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3078 = true := by
  decide +kernel

theorem tot3078 : totK PA10K2 A10K2.t3078 = [0, 0, 0, 625408207493, 2043350598825, 1734974052259, 317318580711, 11669104322, 0, 0] := by
  decide +kernel

theorem rows3079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3079 = true := by
  decide +kernel

theorem tot3079 : totK PA10K2 A10K2.t3079 = [0, 0, 0, 606114604001, 2096516628631, 1932296092916, 418922047087, 12677188408, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
