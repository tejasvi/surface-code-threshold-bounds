import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4868 = true := by
  decide +kernel

theorem tot4868 : totK PA10K2 A10K2.t4868 = [0, 218975725320, 1193754307294, 2043608563473, 1266634939610, 231619420644, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows4869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4869 = true := by
  decide +kernel

theorem tot4869 : totK PA10K2 A10K2.t4869 = [0, 0, 644226334479, 2000964668880, 1825107255545, 474585556946, 28177825909, 0, 0, 0] := by
  decide +kernel

theorem rows4870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4870 = true := by
  decide +kernel

theorem tot4870 : totK PA10K2 A10K2.t4870 = [0, 0, 430605774746, 1754087531015, 1961642344095, 513093673129, 31222411477, 0, 0, 0] := by
  decide +kernel

theorem rows4871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4871 = true := by
  decide +kernel

theorem tot4871 : totK PA10K2 A10K2.t4871 = [0, 0, 83580751561, 869260881389, 1932320402651, 1416054337999, 358352176653, 25239774317, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
