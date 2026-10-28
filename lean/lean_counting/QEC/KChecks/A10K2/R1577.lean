import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6308 = true := by
  decide +kernel

theorem tot6308 : totK PA10K2 A10K2.t6308 = [0, 84539485306, 927575535141, 2158400653711, 1567599126334, 271191462785, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows6309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6309 = true := by
  decide +kernel

theorem tot6309 : totK PA10K2 A10K2.t6309 = [0, 343933301626, 1516980758144, 2124837033725, 916229002365, 73983819108, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6310 = true := by
  decide +kernel

theorem tot6310 : totK PA10K2 A10K2.t6310 = [0, 501550152162, 1907514756128, 1998913587808, 536927335785, 18513647723, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6311 = true := by
  decide +kernel

theorem tot6311 : totK PA10K2 A10K2.t6311 = [0, 0, 655349283352, 2162950781584, 1876597409451, 334754663146, 6066958478, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
