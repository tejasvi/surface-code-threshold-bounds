import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7480 = true := by
  decide +kernel

theorem tot7480 : totK PA10K2 A10K2.t7480 = [0, 0, 0, 222492997860, 1216239093124, 2022859736045, 1149641505025, 247571585157, 20331139758, 0] := by
  decide +kernel

theorem rows7481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7481 = true := by
  decide +kernel

theorem tot7481 : totK PA10K2 A10K2.t7481 = [0, 0, 0, 117179589859, 841031117185, 1792656875332, 1441864856910, 307619639887, 10687427893, 0] := by
  decide +kernel

theorem rows7482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7482 = true := by
  decide +kernel

theorem tot7482 : totK PA10K2 A10K2.t7482 = [0, 0, 0, 559501797500, 1788101167022, 1748176273451, 479660851976, 31821298896, 0, 0] := by
  decide +kernel

theorem rows7483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7483 = true := by
  decide +kernel

theorem tot7483 : totK PA10K2 A10K2.t7483 = [0, 0, 0, 0, 1015361217053, 2352669744847, 1003957973788, 77916801148, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
