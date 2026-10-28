import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t652 = true := by
  decide +kernel

theorem tot652 : totK PA10K2 A10K2.t652 = [0, 112111361307, 1232346797292, 2303712914069, 997383026868, 73641457032, 0, 0, 0, 0] := by
  decide +kernel

theorem rows653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t653 = true := by
  decide +kernel

theorem tot653 : totK PA10K2 A10K2.t653 = [0, 0, 486755617751, 1865508469771, 1855696455811, 438569456526, 26172145312, 0, 0, 0] := by
  decide +kernel

theorem rows654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t654 = true := by
  decide +kernel

theorem tot654 : totK PA10K2 A10K2.t654 = [0, 0, 581859680969, 1999849345860, 1831870717954, 384420883257, 11740596405, 0, 0, 0] := by
  decide +kernel

theorem rows655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t655 = true := by
  decide +kernel

theorem tot655 : totK PA10K2 A10K2.t655 = [0, 0, 466952373236, 1803568977479, 1982820471845, 550133899042, 32470943963, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
