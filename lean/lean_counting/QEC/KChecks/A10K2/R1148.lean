import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4592 = true := by
  decide +kernel

theorem tot4592 : totK PA10K2 A10K2.t4592 = [0, 0, 0, 1008596362011, 2340968756786, 1089325345153, 97743242395, 0, 0, 0] := by
  decide +kernel

theorem rows4593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4593 = true := by
  decide +kernel

theorem tot4593 : totK PA10K2 A10K2.t4593 = [454243131009, 1499791343207, 1447034571903, 414273423738, 304855305404, 481073231684, 167871307784, 6354482628, 0, 0] := by
  decide +kernel

theorem rows4594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4594 = true := by
  decide +kernel

theorem tot4594 : totK PA10K2 A10K2.t4594 = [391328567830, 1703800698599, 2077263625576, 725482357745, 56225194809, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4595 = true := by
  decide +kernel

theorem tot4595 : totK PA10K2 A10K2.t4595 = [0, 447939967964, 1850776470587, 1920731177067, 454332746279, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
