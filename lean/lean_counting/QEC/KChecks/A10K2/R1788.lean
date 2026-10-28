import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7152 = true := by
  decide +kernel

theorem tot7152 : totK PA10K2 A10K2.t7152 = [0, 0, 214452326151, 1411099718202, 2166040418945, 805490195011, 45545545079, 0, 0, 0] := by
  decide +kernel

theorem rows7153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7153 = true := by
  decide +kernel

theorem tot7153 : totK PA10K2 A10K2.t7153 = [0, 0, 0, 594675690425, 1962943148718, 1651927705603, 366457235394, 26601763172, 0, 0] := by
  decide +kernel

theorem rows7154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7154 = true := by
  decide +kernel

theorem tot7154 : totK PA10K2 A10K2.t7154 = [0, 0, 0, 484473264481, 1834638886642, 1921381540296, 482543688738, 18304095112, 0, 0] := by
  decide +kernel

theorem rows7155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7155 = true := by
  decide +kernel

theorem tot7155 : totK PA10K2 A10K2.t7155 = [0, 0, 0, 526370349136, 1933900628290, 1802734666065, 380598895836, 25553601783, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
